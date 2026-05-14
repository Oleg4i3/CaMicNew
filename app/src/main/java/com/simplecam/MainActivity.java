package com.simplecam;

import android.Manifest;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.content.Context;
import android.content.pm.PackageManager;
import android.graphics.*;
import android.graphics.drawable.GradientDrawable;
import android.hardware.camera2.*;
import android.hardware.camera2.params.MeteringRectangle;
import android.media.*;
import android.media.MediaCodecInfo.CodecCapabilities;
import android.media.MediaCodecInfo.CodecProfileLevel;
import android.os.*;
import android.view.*;
import android.widget.*;

import android.content.ContentValues;
import android.net.Uri;
import android.os.Environment;
import android.os.ParcelFileDescriptor;
import android.provider.MediaStore;

import android.media.AudioDeviceInfo;
import android.media.AudioManager;
import android.media.audiofx.AutomaticGainControl;
import android.media.audiofx.NoiseSuppressor;
import android.media.audiofx.AcousticEchoCanceler;

import android.media.Image;
import android.media.ImageReader;

import java.io.File;
import java.nio.ByteBuffer;
import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

/**
* SimpleCam — минималистичная камера для горизонтального экрана.
*
* Слева — вертикальный Gain-слайдер (полная высота).
* Справа — рычаг Zoom + появляющийся слайдер Manual Focus.
* Снизу — панель управления с круглой кнопкой REC.
*/
public class MainActivity extends Activity implements SurfaceHolder.Callback {
	
	// ─── Константы ────────────────────────────────────────────────────────────
	private static final int VIDEO_W = 1280;
	private static final int VIDEO_H = 720;
	private static final int VIDEO_BPS_DEFAULT = 6_000_000;
	private static final int VIDEO_FPS = 30;
	private static final int AUDIO_SR = 48000;
	private static final int REQ_PERMS = 1;
	private static final float MAX_ZOOM_SPEED = 0.08f;
	/**
	 * Типичная задержка аппаратного стабилизатора (EIS) в мкс.
	 * Реальный lag зависит от SoC; 500 мс — консервативная оценка.
	 * Добавляется к глубине кольцевого буфера, чтобы пре-запись
	 * всегда содержала кадры, стабилизированные «в прошлом».
	 */
	private static final long EIS_LATENCY_US = 500_000L; // 500 ms
	
	// ─── UI ───────────────────────────────────────────────────────────────────
	private SurfaceView mSv;
	private Spinner mSpinner;
	private VerticalSeekBar mSeekGain;
	private FocusDrumView mFocusDrum; // барабан ручного фокуса
	private TextView mTvGain, mTvStatus, mTvFocus;
	private Button mBtn, mSrcToggleBtn, mBtnPause;
	private volatile boolean mPaused = false;
	private long mPauseStartNano = 0L, mPauseEndNano = 0L;
	private GradientDrawable mBtnBgPause;
	private VuMeterView mVu;
	private OscilloscopeView mOscilloscope;
	private EnvelopeView mEnvelope;
	private SpectrumView mSpectrum;
	private ZoomLeverView mZoomLever;
	private LinearLayout mAudioSrcPanel;
	private CheckBox mCbSoftClip, mCbManualFocus, mCbFocusAssist, mCbEis;
	private boolean mAudioSrcExpanded = false;
	private View mFocusColumn; // контейнер слайдера фокуса
	/** Постоянный оверлей «NC / CUST.NC» поверх спектра — виден при свёрнутых настройках. */
	private TextView mTvNcOverlay;
	
	// Focus Assist: сохранённый зум до ассиста и хэндлер восстановления
	private volatile float mSavedZoomBeforeAssist = 1f;
	private Handler mFocusAssistHandler;
	
	// REC-кнопки фоны
	private GradientDrawable mBtnBgIdle, mBtnBgRec;
	
	// ─── Camera2 ──────────────────────────────────────────────────────────────
	private CameraManager mCamMgr;
	private CameraDevice mCamDev;
	private CameraCaptureSession mCapSess;
	private HandlerThread mCamThread;
	private Handler mCamHandler;
	private boolean mSurfaceReady;
	private boolean mPermsOk;
	private int mSensorOrientation = 90;
	private Rect mSensorRect;
	// PRE_CORRECTION_ACTIVE_ARRAY_SIZE — координатное пространство при EIS=ON
	private Rect mPreCorrRect;
	private float mMaxZoom = 1f;
	private volatile float mZoomLevel = 1f;
	private volatile float mZoomLeverPos = 0f;
	
	// Фокус
	private volatile boolean mManualFocus = false;
	private volatile float mFocusValue = 0f; // 0..1 (0=∞, 1=macro)
	private float mMinFocusDist = 0f; // минимальная дистанция (диоптрии)
	
	// ─── EIS ──────────────────────────────────────────────────────────────────
	/** true — пользователь включил аппаратный EIS */
	private volatile boolean mEisEnabled  = false;
	/** true — железо поддерживает VIDEO_STABILIZATION_MODE_ON */
	private volatile boolean mEisSupported = false;

	// ─── EIS PiP monitor (ImageReader) ────────────────────────────────────────
	/**
	 * Реальный монитор EIS: третья поверхность в capture session.
	 * Получает тот же стабилизированный стрим, что идёт в энкодер.
	 *
	 * Почему именно ImageReader, а не гироскоп:
	 *   HW EIS использует кросс-корреляцию кадров внутри ISP/DSP — алгоритм
	 *   не привязан напрямую к гироскопу и может давать систематические
	 *   смещения (например, в нижний левый угол), которые гироскоп не покажет.
	 *   ImageReader получает кадр ПОСЛЕ стабилизатора — это и есть реальный
	 *   выход в файл.
	 */
	// PiP: live-декодер encoder→SurfaceView (SurfaceView не требует hardware acceleration)
	private SurfaceView  mPipView;
	private Surface      mPipDecSurface;
	private MediaCodec   mPipDec;
	private Thread       mPipDecThread;
	private volatile boolean mPipDecReady = false;
	
	// ─── Запись ───────────────────────────────────────────────────────────────
	private volatile boolean mRecording;
	private volatile float mGain = 1f;
	private volatile boolean mSoftClip = false;
	private volatile int mAudChannels = 2;

	private MediaCodec mVidEnc, mAudEnc;
	private MediaMuxer mMuxer;
	private Surface mEncSurface;
	private AudioRecord mAudRec;
	private Thread mAudThread;

	private int mVidTrack = -1, mAudTrack = -1;
	private volatile boolean mMuxReady;
	private final Object mMuxLock = new Object();

	// ─── MediaStore ───────────────────────────────────────────────────────────
	private Uri mPendingUri;
	private ParcelFileDescriptor mPfd;

	// ─── WAV sidecar (несжатая параллельная дорожка) ─────────────────────────
	private volatile boolean mRecordWav = false;
	private CheckBox mCbRecordWav;
	/** Кольцевой буфер сырого PCM для WAV — зеркалит mAudRing по глубине. */
	private final java.util.ArrayDeque<PcmChunk> mPcmRing = new java.util.ArrayDeque<>();
	private final Object mPcmRingLock = new Object();
	/** 0=RING 1=FLUSH 2=LIVE — точная копия схемы mAudWriteMode */
	private volatile int mPcmWriteMode = 0;
	private final Object mWavLock = new Object();
	private java.nio.channels.FileChannel mWavChannel;
	private long mWavDataBytes = 0;
	private Uri mWavPendingUri;
	private ParcelFileDescriptor mWavPfd;

	// ─── AGC / NC ─────────────────────────────────────────────────────────────
	private volatile boolean mAgcEnabled  = false;
	private volatile boolean mNcEnabled   = false;
	private volatile int     mNcLevel     = 2;   // 0..3 агрессивность
	private boolean mAgcAvailable = false;
	private boolean mNcAvailable  = false;
	private CheckBox  mCbAgc, mCbNc;
	private LinearLayout mNcLevelRow;            // строка слайдера агрессивности
	private TextView mTvNcLevel;

	// ─── Custom NC (DSP-шумоподавление в PCM-потоке) ──────────────────────────
	/** true — кастомное шумоподавление включено (обрабатывается в audioMainLoop) */
	private volatile boolean mCustomNcEnabled = false;
	// ─── Поля гейта с гистерезисом ───────────────────────────────────────────
	private float mNcRmsEst   = 0f;   // скользящий RMS (~5 мс)
	private float mNcFloorEst = 0f;   // оценка шумового пола
	private float mNcGateGain = 1f;   // текущий gain гейта
	private boolean mNcGateOpen = true;
	private float   mNcAttackPhase = 0f; // 0..1, прогресс сигмоидной атаки
	// ── Открытые параметры гейта (регулируются слайдерами) ───────────────────
	/** Множитель порога открытия: openThresh = floor × mNcThreshMult */
	private volatile float mNcThreshMult = 2.0f;  // 1.0 .. 10
	/** Остаточный gain когда гейт закрыт: 0=тишина, 1=без подавления (экспандер) */
	private volatile float mNcResidual   = 0.0f;  // 0.0 .. 1.0
	/** Гистерезис в дБ: closeThresh = openThresh × 10^(mNcHystDb/20) */
	private volatile float mNcHystDb     = -6.0f; // -12 .. 0 dB
	/** Время рилива, мс */
	private volatile int   mNcReleaseMs  = 600;   // 50 .. 3000
	// ── Lookahead: очередь delayed PCM-чанков ────────────────────────────────
	private static final int NC_LOOKAHEAD_MS = 30; // мс опережения
	private final java.util.ArrayDeque<short[]> mNcDelayQ = new java.util.ArrayDeque<>();
	private int mNcDelayedSamples = 0;             // сэмплов в очереди
	private CheckBox mCbCustomNc;
	private CheckBox mCbOsc;   // видимость осциллографа
	private CheckBox mCbSpec;  // видимость спектра
	// NC slider references (нужны для loadPrefs)
	private SeekBar  mSbNcThr, mSbNcHyst, mSbNcRel, mSbNcRes;
	private TextView mTvNcThr, mTvNcHyst, mTvNcRel, mTvNcRes;

	// ─── EQ ───────────────────────────────────────────────────────────────────
	private volatile boolean mEqEnabled = false;
	private Button mBtnEq;
	private View mEqPanel;
	private boolean mEqPanelVisible = false;
	private final List<EqBand> mEqBands = new ArrayList<>();
	private final Object mEqLock = new Object();
	private LinearLayout mEqListView;
	private CheckBox mCbEqEnable;
	private EqOverlayView mEqOverlay;

	// ─── Аудио-источники ──────────────────────────────────────────────────────
	private final List<AudioSrcItem> mSrcList = new ArrayList<>();

	// ─── Аудио-поток ─────────────────────────────────────────────────────────
	private volatile boolean mAudRunning;

	// ═══════════════════════════════════════════════════════════════════════════
	// Pre-buffer: кольцевые буферы закодированных фреймов.
	//
	// Ключевая идея БЕСШОВНОСТИ:
	//   mVidWriteMode / mAudWriteMode — атомарные флаги:
	//     0 = RING  (фреймы идут в кольцо)
	//     1 = FLUSH (дренажный поток сбрасывает кольцо в мюксер, потом LIVE)
	//     2 = LIVE  (фреймы идут прямо в мюксер)
	//   Переключение RING→FLUSH→LIVE делает тот же поток, что дренирует
	//   энкодер, — поэтому между последним фреймом кольца и первым живым
	//   фреймом нет ни одного пропущенного пакета.
	// ═══════════════════════════════════════════════════════════════════════════
	private static class EncodedFrame {
		final byte[] data; final long pts; final int flags;
		EncodedFrame(ByteBuffer src, MediaCodec.BufferInfo bi) {
			data = new byte[bi.size];
			src.position(bi.offset); src.get(data, 0, bi.size);
			pts = bi.presentationTimeUs; flags = bi.flags;
		}
		boolean isKey() { return (flags & MediaCodec.BUFFER_FLAG_KEY_FRAME) != 0; }
	}

	// ── Biquad EQ band ────────────────────────────────────────────────────────
	// HPF/LPF — 2nd order Butterworth (Q=1/√2); Peak — standard RBJ peak EQ biquad.
	// All implemented as Direct Form II Transposed for numerical stability.
	private static class EqBand {
		static final int HPF = 0, LPF = 1, PEAK = 2, LSHELF = 3, HSHELF = 4;
		int     type    = HPF;
		boolean enabled = true;
		float   freq    = 1000f;
		float   q       = 1.0f;   // не используется для HPF/LPF/Shelf
		float   gainDb  = 0f;     // для PEAK, LSHELF, HSHELF
		float   slopeDb = 6f;     // для LSHELF/HSHELF: крутизна переходной зоны (дБ/октаву), 6..24
		// Biquad coefficients (normalized, a0=1):
		double b0 = 1, b1 = 0, b2 = 0, a1 = 0, a2 = 0;
		// Per-channel state
		final double[] x1 = new double[2], x2 = new double[2];
		final double[] y1 = new double[2], y2 = new double[2];

		void computeCoeffs(int sr) {
			double f   = Math.max(20.0, Math.min(18000.0, freq));
			double w0  = 2.0 * Math.PI * f / sr;
			double cw  = Math.cos(w0), sw = Math.sin(w0);
			double rb0, rb1, rb2, ra0, ra1, ra2;
			if (type == HPF) {
				double alpha = sw / Math.sqrt(2.0);
				rb0 =  (1.0 + cw) / 2.0;
				rb1 = -(1.0 + cw);
				rb2 =  (1.0 + cw) / 2.0;
				ra0 =   1.0 + alpha;
				ra1 =  -2.0 * cw;
				ra2 =   1.0 - alpha;
			} else if (type == LPF) {
				double alpha = sw / Math.sqrt(2.0);
				rb0 =  (1.0 - cw) / 2.0;
				rb1 =   1.0 - cw;
				rb2 =  (1.0 - cw) / 2.0;
				ra0 =   1.0 + alpha;
				ra1 =  -2.0 * cw;
				ra2 =   1.0 - alpha;
			} else if (type == PEAK) {
				double Q = Math.max(0.1, q);
				double A = Math.pow(10.0, gainDb / 40.0);
				double alpha = sw / (2.0 * Q);
				rb0 =  1.0 + alpha * A;
				rb1 = -2.0 * cw;
				rb2 =  1.0 - alpha * A;
				ra0 =  1.0 + alpha / A;
				ra1 = -2.0 * cw;
				ra2 =  1.0 - alpha / A;
			} else {
				// LSHELF / HSHELF — RBJ cookbook shelving EQ
				// S = slope параметр: S=1 → максимально крутой Butterworth shelf
				// Отображаем slopeDb (6..24 дБ/окт) → S (0.25..1)
				double A = Math.pow(10.0, gainDb / 40.0);
				double S = Math.max(0.25, Math.min(1.0, slopeDb / 24.0));
				double alpha = sw / 2.0 * Math.sqrt((A + 1.0 / A) * (1.0 / S - 1.0) + 2.0);
				double sqA2  = 2.0 * Math.sqrt(A) * alpha;
				if (type == LSHELF) {
					rb0 =       A * ((A + 1) - (A - 1) * cw + sqA2);
					rb1 =  2.0 * A * ((A - 1) - (A + 1) * cw);
					rb2 =       A * ((A + 1) - (A - 1) * cw - sqA2);
					ra0 =            (A + 1) + (A - 1) * cw + sqA2;
					ra1 = -2.0 *    ((A - 1) + (A + 1) * cw);
					ra2 =            (A + 1) + (A - 1) * cw - sqA2;
				} else { // HSHELF
					rb0 =       A * ((A + 1) + (A - 1) * cw + sqA2);
					rb1 = -2.0 * A * ((A - 1) + (A + 1) * cw);
					rb2 =       A * ((A + 1) + (A - 1) * cw - sqA2);
					ra0 =            (A + 1) - (A - 1) * cw + sqA2;
					ra1 =  2.0 *    ((A - 1) - (A + 1) * cw);
					ra2 =            (A + 1) - (A - 1) * cw - sqA2;
				}
			}
			b0 = rb0 / ra0; b1 = rb1 / ra0; b2 = rb2 / ra0;
			a1 = ra1 / ra0; a2 = ra2 / ra0;
		}

		void resetState() {
			java.util.Arrays.fill(x1, 0); java.util.Arrays.fill(x2, 0);
			java.util.Arrays.fill(y1, 0); java.util.Arrays.fill(y2, 0);
		}
	}
	private final java.util.ArrayDeque<EncodedFrame> mVidRing = new java.util.ArrayDeque<>();
	private final java.util.ArrayDeque<EncodedFrame> mAudRing = new java.util.ArrayDeque<>();
	private final Object mVidRingLock = new Object();
	private final Object mAudRingLock = new Object();
	// 0=RING 1=FLUSH 2=LIVE
	private volatile int mVidWriteMode = 0;
	private volatile int mAudWriteMode = 0;
	private volatile long mMuxBasePts  = 0L;
	/** Единая временная база записи (мкс, System.nanoTime/1000 в момент REC). */
	private volatile long mRecStartUs   = 0L;
	private volatile MediaFormat mVidOutFmt = null;
	private volatile MediaFormat mAudOutFmt = null;
	private volatile boolean mVidLoopRunning = false;

	// ─── Настройки ───────────────────────────────────────────────────────────
	private volatile int  mVideoBps = VIDEO_BPS_DEFAULT;
	private volatile int  mVideoW   = 1920;   // 1280 или 1920
	private volatile int  mVideoH   = 1080;   // 720  или 1080
	private volatile int  mPreBufSecs = 1;          // 1..5 секунд
	private volatile boolean mPreBufferEnabled = true;
	private volatile int  mEvComp = 0;
	private int mEvMin = -6, mEvMax = 6;
	private SeekBar mSeekEv;
	private TextView mTvEv;
	
	// ─── Zoom-цикл ────────────────────────────────────────────────────────────
	private final Runnable mZoomRunnable = new Runnable() {
		@Override
		public void run() {
			float lever = mZoomLeverPos;
			if (Math.abs(lever) > 0.02f) {
				float abs = Math.abs(lever);
				float speed = (float) ((Math.exp(abs * 3.0) - 1.0) / (Math.exp(3.0) - 1.0)) * MAX_ZOOM_SPEED
				* Math.signum(lever);
				mZoomLevel = Math.max(1f, Math.min(mMaxZoom, mZoomLevel + speed));
				buildAndSendRequest();
			}
			if (mCamHandler != null)
			mCamHandler.postDelayed(this, 33);
		}
	};
	
	// =========================================================================
	// Lifecycle
	// =========================================================================
	
	@Override
	protected void onCreate(Bundle saved) {
		super.onCreate(saved);
		getWindow()
		.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON | WindowManager.LayoutParams.FLAG_FULLSCREEN);
		mFocusAssistHandler = new Handler(Looper.getMainLooper());
		setContentView(buildLayout());
		mCamMgr = (CameraManager) getSystemService(CAMERA_SERVICE);
		loadPrefs();
		showAirplaneModeReminder();
		checkPerms();
	}
	
	@Override
	protected void onResume() {
		super.onResume();
		// Перезапускаем PiP только если EIS был включён до паузы
		if (mEisEnabled && mEisSupported) startEisOverlay();
	}

	@Override
	protected void onPause() {
		savePrefs();
		super.onPause();
		if (mRecording) mRecording = false;
		stopEisOverlay(); // освобождаем ImageReader и PiP поток
	}
	
	@Override
	protected void onDestroy() {
		savePrefs();
		super.onDestroy();
		if (mCamHandler != null)
			mCamHandler.removeCallbacks(mZoomRunnable);
		mVidLoopRunning = false;
		stopAudio();
		finalizeMuxer();
		// PiP cleanup
		stopPipDecoder();
		if (mVidEnc!=null){try{mVidEnc.stop();mVidEnc.release();}catch(Exception e){} mVidEnc=null;}
		if (mEncSurface!=null){try{mEncSurface.release();}catch(Exception e){} mEncSurface=null;}
		try {
			if (mCapSess != null)
			mCapSess.close();
			} catch (Exception ignored) {
		}
		try {
			if (mCamDev != null)
			mCamDev.close();
			} catch (Exception ignored) {
		}
		if (mCamThread != null)
		mCamThread.quitSafely();
	}
	
	// =========================================================================
	// Layout
	// =========================================================================
	
	private View buildLayout() {
		FrameLayout root = new FrameLayout(this);
		root.setBackgroundColor(Color.BLACK);
		
		// Превью — сохраняем пропорции 16:9, центрируем в root
		mSv = new SurfaceView(this) {
			@Override
			protected void onMeasure(int wMs, int hMs) {
				int w = MeasureSpec.getSize(wMs);
				int h = MeasureSpec.getSize(hMs);
				int targetH = w * 9 / 16;
				if (targetH > h) {
					int targetW = h * 16 / 9;
					super.onMeasure(
						MeasureSpec.makeMeasureSpec(targetW, MeasureSpec.EXACTLY),
						MeasureSpec.makeMeasureSpec(h, MeasureSpec.EXACTLY));
				} else {
					super.onMeasure(
						MeasureSpec.makeMeasureSpec(w, MeasureSpec.EXACTLY),
						MeasureSpec.makeMeasureSpec(targetH, MeasureSpec.EXACTLY));
				}
			}
		};
		mSv.getHolder().addCallback(this);
		FrameLayout.LayoutParams svLP = new FrameLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
		svLP.gravity = Gravity.CENTER;
		root.addView(mSv, svLP);

		// PiP-монитор: SurfaceView поверх превью, декодер кормит его H.264-фреймами энкодера
		mPipView = new SurfaceView(this);
		// setZOrderMediaOverlay: рисуется поверх mSv (дрожащая рамка видна по краям),
		// но ПОД обычными View — все контролы, кнопки и слайдеры остаются поверх превью.
		mPipView.setZOrderMediaOverlay(true);
		mPipView.setVisibility(View.GONE);
		mPipView.getHolder().addCallback(new SurfaceHolder.Callback() {
			@Override public void surfaceCreated(SurfaceHolder h) {
				mPipDecSurface = h.getSurface();
				MediaFormat fmt;
				synchronized (mVidRingLock) { fmt = mVidOutFmt; }
				if (fmt != null) ensurePipDecoder(fmt);
			}
			@Override public void surfaceChanged(SurfaceHolder h, int fmt, int w, int hh) {}
			@Override public void surfaceDestroyed(SurfaceHolder h) {
				stopPipDecoder();
				mPipDecSurface = null;
			}
		});
		GradientDrawable pipBorder = new GradientDrawable();
		pipBorder.setStroke(dp(2), 0x88FFCC00);
		pipBorder.setColor(0x00000000);
		mPipView.setBackground(pipBorder);
		// Вычисляем размер PiP с сохранением 16:9 по реальному размеру дисплея.
		// Приложение работает в ландшафте: ширина > высоты.
		// Оставляем ~dp(30) с каждой стороны — видна "дрожащая рамка" из mSv.
		{
			android.util.DisplayMetrics dm = new android.util.DisplayMetrics();
			getWindowManager().getDefaultDisplay().getMetrics(dm);
			int scrW = dm.widthPixels;
			int scrH = dm.heightPixels;
			int margin = dp(30);
			int pipH = scrH - 2 * margin;
			int pipW = pipH * 16 / 9;
			if (pipW > scrW - 2 * margin) {
				pipW = scrW - 2 * margin;
				pipH = pipW * 9 / 16;
			}
			FrameLayout.LayoutParams pipLP = new FrameLayout.LayoutParams(pipW, pipH);
			pipLP.gravity = android.view.Gravity.CENTER;
			root.addView(mPipView, pipLP);
		}



		// ── Осциллограф — прозрачный оверлей, верхняя часть кадра ─────────
		mOscilloscope = new OscilloscopeView(this);
		FrameLayout.LayoutParams oscLP = new FrameLayout.LayoutParams(
				ViewGroup.LayoutParams.MATCH_PARENT, dp(130));
		oscLP.gravity = Gravity.TOP | Gravity.LEFT;
		oscLP.leftMargin = dp(50); // не перекрывать Gain-слайдер
		oscLP.rightMargin = dp(60);
		oscLP.topMargin = dp(6);
		root.addView(mOscilloscope, oscLP);
		mOscilloscope.setVisibility(View.GONE);

		// ── Огибающая (бегущий 10-секундный осциллограф) — тот же оверлей ──────
		mEnvelope = new EnvelopeView(this);
		FrameLayout.LayoutParams envLP = new FrameLayout.LayoutParams(
				ViewGroup.LayoutParams.MATCH_PARENT, dp(130));
		envLP.gravity = Gravity.TOP | Gravity.LEFT;
		envLP.leftMargin = dp(50);
		envLP.rightMargin = dp(60);
		envLP.topMargin = dp(6);
		root.addView(mEnvelope, envLP);
		
		mBtnBgIdle  = makeOval(0xFFDDCC00);
		mBtnBgRec   = makeOval(0xFFCC1100);
		mBtnBgPause = makeOval(0xFF1155CC);
		
		// Внешний вертикальный контейнер: рабочая зона + нижняя панель
		LinearLayout outer = new LinearLayout(this);
		outer.setOrientation(LinearLayout.VERTICAL);
		root.addView(outer, mp_mp());
		
		// ── Рабочая зона ──────────────────────────────────────────────────────
		FrameLayout content = new FrameLayout(this);
		outer.addView(content, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f));
		
		// ── Gain-слайдер (слева, ПОЛНАЯ высота экрана включая нижнюю панель) ──
		// Диапазон: -20 dB .. +20 dB (800 шагов), 0 dB = прогресс 400 (середина)
		mSeekGain = new VerticalSeekBar(this);
		mSeekGain.setMax(800);
		mSeekGain.setProgress(400); // 0 dB = середина
		mSeekGain.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
			public void onProgressChanged(SeekBar s, int p, boolean u) {
				// p=0 → -20 dB, p=400 → 0 dB, p=800 → +20 dB
				float db = -20f + p * 40f / 800f;
				mGain = (float) Math.pow(10.0, db / 20.0);
				if (mTvGain != null)
				mTvGain.setText(String.format("%+.1f", db) + "dB");
			}
			
			public void onStartTrackingTouch(SeekBar s) {}
			public void onStopTrackingTouch(SeekBar s) {}
		});
		// Добавляем в root (полная высота экрана), а не в content
		FrameLayout.LayoutParams gainLP = new FrameLayout.LayoutParams(dp(44), ViewGroup.LayoutParams.MATCH_PARENT);
		gainLP.gravity = Gravity.LEFT;
		root.addView(mSeekGain, gainLP);
		
		TextView tvGainLbl = smallLabel("GAIN");
		FrameLayout.LayoutParams gainLblLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT,
		ViewGroup.LayoutParams.WRAP_CONTENT);
		gainLblLP.gravity = Gravity.LEFT | Gravity.TOP;
		gainLblLP.leftMargin = dp(6);
		gainLblLP.topMargin = dp(4);
		root.addView(tvGainLbl, gainLblLP);
		
		mTvGain = smallLabel("+0.0dB");
		FrameLayout.LayoutParams gainValLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT,
		ViewGroup.LayoutParams.WRAP_CONTENT);
		gainValLP.gravity = Gravity.LEFT | Gravity.BOTTOM;
		gainValLP.leftMargin = dp(3);
		// Отступ снизу = высота нижней панели (~165dp) + запас 4dp
		gainValLP.bottomMargin = dp(169);
		root.addView(mTvGain, gainValLP);
		
		// ── Вертикальный VU-метр (справа от Gain-слайдера, полная высота) ──────
		mVu = new VuMeterView(this);
		FrameLayout.LayoutParams vuVertLP = new FrameLayout.LayoutParams(dp(14), ViewGroup.LayoutParams.MATCH_PARENT);
		vuVertLP.gravity = Gravity.LEFT;
		vuVertLP.leftMargin = dp(44);
		root.addView(mVu, vuVertLP);

		// ── Правая колонка: Focus-слайдер + Zoom-рычаг ───────────────────────
		// Добавляем в root (полная высота экрана), а не в content —
		// иначе при открытии панели настроек content сжимается и рычаги «схлопываются»
		LinearLayout rightCol = new LinearLayout(this);
		rightCol.setOrientation(LinearLayout.HORIZONTAL);
		FrameLayout.LayoutParams rightColLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT,
		ViewGroup.LayoutParams.MATCH_PARENT);
		rightColLP.gravity = Gravity.RIGHT;
		root.addView(rightCol, rightColLP);
		
		// Слайдер фокуса (скрыт по умолчанию)
		mFocusColumn = buildFocusColumn();
		mFocusColumn.setVisibility(View.GONE);
		rightCol.addView(mFocusColumn, new LinearLayout.LayoutParams(dp(44), ViewGroup.LayoutParams.MATCH_PARENT));
		
		// Рычаг Zoom
		mZoomLever = new ZoomLeverView(this);
		mZoomLever.setListener(pos -> mZoomLeverPos = pos);
		rightCol.addView(mZoomLever, new LinearLayout.LayoutParams(dp(54), ViewGroup.LayoutParams.MATCH_PARENT));
		
		// ── Нижняя панель ─────────────────────────────────────────────────────
		LinearLayout panel = new LinearLayout(this);
		panel.setOrientation(LinearLayout.VERTICAL);
		panel.setBackgroundColor(0x00000000);
		// Левый паддинг = gain(44) + VU(14) + зазор(4) = 62dp
		panel.setPadding(dp(62), dp(2), dp(8), dp(3));
		outer.addView(panel, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
		ViewGroup.LayoutParams.WRAP_CONTENT));
		
		// Тоггл аудио-источника — шестерёнка СЛЕВА от статуса.
		// panel имеет paddingLeft=52dp (чтобы не заходить за слайдер Gain),
		// поэтому шестерёнка слева не перекрывается ни слайдером, ни рычагом зума справа.
		mSrcToggleBtn = new Button(this);
		mSrcToggleBtn.setText("⚙");
		mSrcToggleBtn.setAllCaps(false);
		mSrcToggleBtn.setTextSize(28);
		mSrcToggleBtn.setTextColor(0xFFBBBBBB);
		mSrcToggleBtn.setBackground(null);
		mSrcToggleBtn.setPadding(0, 0, dp(8), 0);
		mSrcToggleBtn.setOnClickListener(v -> {
			mAudioSrcExpanded = !mAudioSrcExpanded;
			mAudioSrcPanel.setVisibility(mAudioSrcExpanded ? View.VISIBLE : View.GONE);
			mSrcToggleBtn.setText(mAudioSrcExpanded ? "⚙ ▴" : "⚙");
		});

		// EQ кнопка — справа от шестерёнки
		mBtnEq = new Button(this);
		mBtnEq.setText("EQ");
		mBtnEq.setAllCaps(false);
		mBtnEq.setTextSize(14);
		mBtnEq.setTextColor(0xFFBBBBBB);
		mBtnEq.setBackground(null);
		mBtnEq.setPadding(dp(4), 0, dp(8), 0);
		mBtnEq.setOnClickListener(v -> {
			mEqPanelVisible = !mEqPanelVisible;
			mEqPanel.setVisibility(mEqPanelVisible ? View.VISIBLE : View.GONE);
			mBtnEq.setText(mEqPanelVisible ? "EQ ▴" : "EQ");
		});
		
		mTvStatus = new TextView(this);
		mTvStatus.setTextColor(0xFFAAAAAA);
		mTvStatus.setTextSize(11);
		mTvStatus.setText("Ready");
		mTvStatus.setSingleLine(false);
		mTvStatus.setMaxLines(2);
		mTvStatus.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
		// Шестерёнка слева, EQ рядом, статус справа (weight=1)
		panel.addView(hrow(mSrcToggleBtn, mBtnEq, mTvStatus));
		
		// Схлопываемая панель: спиннер + soft clip + manual focus
		// Центрируем по экрану — слайдер Gain слева не перекрывает
		// Схлопываемая панель: два столбца рядом.
		// col1 — основные настройки; col2 — битрейт.
		mAudioSrcPanel = new LinearLayout(this);
		mAudioSrcPanel.setOrientation(LinearLayout.HORIZONTAL);
		mAudioSrcPanel.setVisibility(View.GONE);
		mAudioSrcPanel.setPadding(dp(8), dp(4), dp(8), dp(4));

		LinearLayout settingsCol1 = new LinearLayout(this);
		settingsCol1.setOrientation(LinearLayout.VERTICAL);
		settingsCol1.setPadding(0, 0, dp(16), 0);

		LinearLayout settingsCol2 = new LinearLayout(this);
		settingsCol2.setOrientation(LinearLayout.VERTICAL);
		
		mSpinner = new Spinner(this);
		ArrayAdapter<String> ad = new ArrayAdapter<>(this, android.R.layout.simple_spinner_item,
		new ArrayList<String>());
		ad.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item);
		mSpinner.setAdapter(ad);
		// Фиксированная ширина вместо weight=1 — не тянется на весь экран
		mSpinner.setLayoutParams(new LinearLayout.LayoutParams(dp(200), ViewGroup.LayoutParams.WRAP_CONTENT));
		mSpinner.setOnItemSelectedListener(new AdapterView.OnItemSelectedListener() {
			@Override
			public void onItemSelected(AdapterView<?> p, View v, int pos, long id) {
				if (!mRecording) {
					stopAudio();
					startMonitor();
				}
			}
			
			@Override
			public void onNothingSelected(AdapterView<?> p) {
			}
		});
		
		LinearLayout srcRow = new LinearLayout(this);
		srcRow.setOrientation(LinearLayout.HORIZONTAL);
		srcRow.setGravity(Gravity.CENTER_VERTICAL);
		srcRow.addView(smallLabel("Src: "));
		srcRow.addView(mSpinner);
		settingsCol1.addView(srcRow);
		
		mCbSoftClip = new CheckBox(this);
		mCbSoftClip.setText("Soft clip");
		mCbSoftClip.setTextColor(0xCCCCCCCC);
		mCbSoftClip.setTextSize(12);
		mCbSoftClip.setChecked(true);
		mSoftClip = true;
		mCbSoftClip.setOnCheckedChangeListener((cb, checked) -> mSoftClip = checked);
		
		mCbManualFocus = new CheckBox(this);
		mCbManualFocus.setText("Manual focus");
		mCbManualFocus.setTextColor(0xCCCCCCCC);
		mCbManualFocus.setTextSize(12);
		mCbManualFocus.setOnCheckedChangeListener((cb, checked) -> {
			mManualFocus = checked;
			mFocusColumn.setVisibility(checked ? View.VISIBLE : View.GONE);
			// Сдвигаем кнопку REC влево на полширины когда барабан виден
			// mBtn теперь в root FrameLayout с фиксированным rightMargin — не трогаем
			// Чекбокс Focus Assist — только при ручной фокусировке
			if (mCbFocusAssist != null)
			mCbFocusAssist.setVisibility(checked ? View.VISIBLE : View.GONE);
			if (!checked) {
				// Скрываем ассист и отменяем восстановление зума
				if (mFocusAssistHandler != null) mFocusAssistHandler.removeCallbacksAndMessages(null);
			}
			if (mCamHandler != null)
			mCamHandler.post(this::buildAndSendRequest);
		});
		
		LinearLayout cbRow = new LinearLayout(this);
		cbRow.setOrientation(LinearLayout.HORIZONTAL);
		cbRow.setGravity(Gravity.CENTER_VERTICAL);
		cbRow.addView(mCbSoftClip);
		cbRow.addView(mCbManualFocus);
		settingsCol1.addView(cbRow);

		// ── Hardware EIS ─────────────────────────────────────────────────────
		// Чекбокс EIS: блокируется во время записи, чтобы не сбросить стабилизатор
		// и не нарушить синхронизацию кольцевого буфера.
		mCbEis = new CheckBox(this);
		mCbEis.setText("ImageStab");
		mCbEis.setTextColor(0xCCCCCCCC);
		mCbEis.setTextSize(12);
		mCbEis.setEnabled(false); // разблокируется после openCamera, если устройство поддерживает
		mCbEis.setOnCheckedChangeListener((cb, checked) -> {
			// Запрещаем переключение во время записи — стабилизатор сбросился бы,
			// вызвав визуальный артефакт и возможную рассинхронизацию PTS в пре-буфере.
			if (mRecording) {
				cb.setChecked(!checked);
				status("EIS нельзя изменить во время записи");
				return;
			}
			mEisEnabled = checked;
			if (checked) {
				startEisOverlay();
			} else {
				stopEisOverlay();
			}
			if (mCamHandler != null)
				mCamHandler.post(MainActivity.this::buildAndSendRequest);
		});
		cbRow.addView(mCbEis);

		// Чекбоксы видимости анализаторов
		mCbOsc = new CheckBox(this);
		mCbOsc.setText("Oscilloscope");
		mCbOsc.setTextColor(0xCCCCCCCC);
		mCbOsc.setTextSize(12);
		mCbOsc.setChecked(false);
		mCbOsc.setOnCheckedChangeListener((cb, checked) -> {
			if (mOscilloscope != null) mOscilloscope.setVisibility(checked ? View.VISIBLE : View.GONE);
			if (mEnvelope != null) mEnvelope.setVisibility(checked ? View.GONE : View.VISIBLE);
		});

		mCbSpec = new CheckBox(this);
		mCbSpec.setText("Spectrum analyzer");
		mCbSpec.setTextColor(0xCCCCCCCC);
		mCbSpec.setTextSize(12);
		mCbSpec.setChecked(true);
		mCbSpec.setOnCheckedChangeListener((cb, checked) -> {
			if (mSpectrum != null) mSpectrum.setVisibility(checked ? View.VISIBLE : View.GONE);
		});

		LinearLayout cbRow2 = new LinearLayout(this);
		cbRow2.setOrientation(LinearLayout.HORIZONTAL);
		cbRow2.setGravity(Gravity.CENTER_VERTICAL);
		cbRow2.addView(mCbOsc);
		cbRow2.addView(mCbSpec);
		settingsCol1.addView(cbRow2);
		
		// Focus Assist
		mCbFocusAssist = new CheckBox(this);
		mCbFocusAssist.setText("Focus assist (zoom while focusing)");
		mCbFocusAssist.setTextColor(0xCCCCCCCC);
		mCbFocusAssist.setTextSize(12);
		mCbFocusAssist.setVisibility(View.GONE);
		settingsCol1.addView(mCbFocusAssist);

		// ── EV ──────────────────────────────────────────────────────────────
		mTvEv = smallLabel("EV  0");
		mSeekEv = new SeekBar(this);
		mSeekEv.setMax(mEvMax - mEvMin); mSeekEv.setProgress(-mEvMin);
		mSeekEv.setLayoutParams(new LinearLayout.LayoutParams(dp(160), ViewGroup.LayoutParams.WRAP_CONTENT));
		mSeekEv.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
			public void onProgressChanged(SeekBar s, int p, boolean u) {
				mEvComp = mEvMin + p; updateEvLabel(mEvComp);
				if (mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest);
			}
			public void onStartTrackingTouch(SeekBar s) {}
			public void onStopTrackingTouch(SeekBar s) {}
		});
		LinearLayout evRow = new LinearLayout(this);
		evRow.setOrientation(LinearLayout.HORIZONTAL); evRow.setGravity(Gravity.CENTER_VERTICAL);
		evRow.addView(mTvEv); evRow.addView(mSeekEv);
		settingsCol1.addView(evRow);

		// ── Pre-buffer ───────────────────────────────────────────────────────
		CheckBox cbPB = new CheckBox(this);
		cbPB.setText("Pre-buffer");
		cbPB.setTextColor(0xCCCCCCCC); cbPB.setTextSize(12);
		cbPB.setChecked(true); // включён по умолчанию
		cbPB.setOnCheckedChangeListener((cb, on) -> mPreBufferEnabled = on);
		final TextView tvPBLen = smallLabel("1 s");
		SeekBar sbPB = new SeekBar(this);
		sbPB.setMax(4); sbPB.setProgress(0);
		sbPB.setLayoutParams(new LinearLayout.LayoutParams(dp(110), ViewGroup.LayoutParams.WRAP_CONTENT));
		sbPB.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
			public void onProgressChanged(SeekBar s, int p, boolean u) {
				mPreBufSecs = p + 1; tvPBLen.setText(mPreBufSecs + " s");
			}
			public void onStartTrackingTouch(SeekBar s) {}
			public void onStopTrackingTouch(SeekBar s) {}
		});
		LinearLayout pbRow = new LinearLayout(this);
		pbRow.setOrientation(LinearLayout.HORIZONTAL); pbRow.setGravity(Gravity.CENTER_VERTICAL);
		pbRow.addView(cbPB); pbRow.addView(sbPB); pbRow.addView(tvPBLen);
		settingsCol1.addView(pbRow);

		// ── WAV sidecar ──────────────────────────────────────────────────────
		mCbRecordWav = new CheckBox(this);
		mCbRecordWav.setText("WAV sidecar (uncompressed audio)");
		mCbRecordWav.setTextColor(0xCCCCCCCC);
		mCbRecordWav.setTextSize(12);
		mCbRecordWav.setOnCheckedChangeListener((cb, checked) -> {
			if (mRecording) {
				cb.setChecked(!checked);
				status("WAV нельзя изменить во время записи");
				return;
			}
			mRecordWav = checked;
		});
		settingsCol1.addView(mCbRecordWav);

		// ── Битрейт видео ────────────────────────────────────────────────────
		String[] bpsL={"500 kbps","1 Mbps","2 Mbps","3 Mbps","4 Mbps","6 Mbps (def)","8 Mbps","12 Mbps"};
		int[] bpsV={500_000,1_000_000,2_000_000,3_000_000,4_000_000,6_000_000,8_000_000,12_000_000};
		Spinner spBps = new Spinner(this);
		ArrayAdapter<String> bpsAd = new ArrayAdapter<>(this, android.R.layout.simple_spinner_item, bpsL);
		bpsAd.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item);
		spBps.setAdapter(bpsAd); spBps.setSelection(5); // 6 Mbps
		spBps.setLayoutParams(new LinearLayout.LayoutParams(dp(190), ViewGroup.LayoutParams.WRAP_CONTENT));
		spBps.setOnItemSelectedListener(new AdapterView.OnItemSelectedListener() {
			public void onItemSelected(AdapterView<?> p, View v, int pos, long id) { mVideoBps = bpsV[pos]; }
			public void onNothingSelected(AdapterView<?> p) {}
		});
		LinearLayout bpsRow = new LinearLayout(this);
		bpsRow.setOrientation(LinearLayout.HORIZONTAL); bpsRow.setGravity(Gravity.CENTER_VERTICAL);
		// ── Bps + Res в одной строке ─────────────────────────────────────────
		String[] resL = {"HD 720p", "FHD 1080p"};
		Spinner spRes = new Spinner(this);
		ArrayAdapter<String> resAd = new ArrayAdapter<>(this, android.R.layout.simple_spinner_item, resL);
		resAd.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item);
		spRes.setAdapter(resAd); spRes.setSelection(1);
		spRes.setOnItemSelectedListener(new AdapterView.OnItemSelectedListener() {
			public void onItemSelected(AdapterView<?> p, View v, int pos, long id) {
				int newW = (pos == 0) ? 1280 : 1920;
				int newH = (pos == 0) ? 720  : 1080;
				if (newW == mVideoW && newH == mVideoH) return;
				if (mRecording) return;
				mVideoW = newW; mVideoH = newH;
				if (mVidEnc != null) {
					try { mVidEnc.stop(); mVidEnc.release(); } catch (Exception ignored) {}
					mVidEnc = null;
				}
				if (mEncSurface != null) {
					try { mEncSurface.release(); } catch (Exception ignored) {}
					mEncSurface = null;
				}
				startPreview();
			}
			public void onNothingSelected(AdapterView<?> p) {}
		});
		// Одна строка: [Bps: <spinner>]  [Res: <spinner>]
		LinearLayout spinRow = new LinearLayout(this);
		spinRow.setOrientation(LinearLayout.HORIZONTAL);
		spinRow.setGravity(Gravity.CENTER_VERTICAL);
		spBps.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
		spRes.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
		spinRow.addView(smallLabel("Bps:")); spinRow.addView(spBps);
		spinRow.addView(smallLabel(" Res:")); spinRow.addView(spRes);
		settingsCol2.addView(spinRow);

		// ── AGC / NC (проверяем доступность статически) ──────────────────────
		mAgcAvailable = AutomaticGainControl.isAvailable();
		mNcAvailable  = NoiseSuppressor.isAvailable();

		if (mAgcAvailable || mNcAvailable) {
			LinearLayout fxRow = new LinearLayout(this);
			fxRow.setOrientation(LinearLayout.HORIZONTAL);
			fxRow.setGravity(Gravity.CENTER_VERTICAL);

			if (mAgcAvailable) {
				mCbAgc = new CheckBox(this);
				mCbAgc.setText("AGC");
				mCbAgc.setTextColor(0xCCCCCCCC);
				mCbAgc.setTextSize(12);
				mCbAgc.setChecked(false);
				mCbAgc.setOnCheckedChangeListener((cb, on) -> {
					mAgcEnabled = on;
					applyAudioEffects();
				});
				fxRow.addView(mCbAgc);
			}

			if (mNcAvailable) {
				mCbNc = new CheckBox(this);
				mCbNc.setText("NC");
				mCbNc.setTextColor(0xCCCCCCCC);
				mCbNc.setTextSize(12);
				mCbNc.setChecked(false);
				mCbNc.setOnCheckedChangeListener((cb, on) -> {
					mNcEnabled = on;
					if (mNcLevelRow != null)
						mNcLevelRow.setVisibility((on || mCustomNcEnabled) ? View.VISIBLE : View.GONE);
					updateNcLevelLabel();
					applyAudioEffects();
					updateNcOverlay();
				});
				fxRow.addView(mCbNc);
			}

			// ── Custom NC: DSP-шумоподавление, работает всегда ───────────────
			mCbCustomNc = new CheckBox(this);
			mCbCustomNc.setText("Cust.NC");
			mCbCustomNc.setTextColor(0xCCCCCCCC);
			mCbCustomNc.setTextSize(12);
			mCbCustomNc.setChecked(false);
			mCbCustomNc.setOnCheckedChangeListener((cb, on) -> {
				mCustomNcEnabled = on;
				if (on) { mNcRmsEst=0f; mNcFloorEst=0f; mNcGateGain=1f; mNcGateOpen=true; mNcAttackPhase=0f; mNcDelayQ.clear(); mNcDelayedSamples=0; }
				if (mNcLevelRow != null)
					mNcLevelRow.setVisibility((on || mNcEnabled) ? View.VISIBLE : View.GONE);
				updateNcLevelLabel();
				updateNcOverlay();
			});
			fxRow.addView(mCbCustomNc);

			settingsCol2.addView(fxRow);

			// ── Параметры Custom NC gate (4 слайдера) ───────────────────────
			mNcLevelRow = new LinearLayout(this);
			mNcLevelRow.setOrientation(LinearLayout.VERTICAL);
			mNcLevelRow.setVisibility(View.GONE);

			{
				LinearLayout row = new LinearLayout(this);
				row.setOrientation(LinearLayout.HORIZONTAL);
				row.setGravity(Gravity.CENTER_VERTICAL);
				mTvNcThr = smallLabel("Thr:2.0x");
				mTvNcThr.setMinWidth(dp(52));
				mSbNcThr = new SeekBar(this);
				mSbNcThr.setMax(100);
				mSbNcThr.setProgress(11);
				mSbNcThr.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
				mSbNcThr.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
					public void onProgressChanged(SeekBar s, int p, boolean u) {
						mNcThreshMult = 1.0f + p * 0.09f;
						mTvNcThr.setText(String.format("Thr:%.1fx", mNcThreshMult));
					}
					public void onStartTrackingTouch(SeekBar s) {}
					public void onStopTrackingTouch(SeekBar s) {}
				});
				row.addView(mTvNcThr); row.addView(mSbNcThr);
				mNcLevelRow.addView(row);
			}
			{
				LinearLayout row = new LinearLayout(this);
				row.setOrientation(LinearLayout.HORIZONTAL);
				row.setGravity(Gravity.CENTER_VERTICAL);
				mTvNcHyst = smallLabel("Hyst:-6dB");
				mTvNcHyst.setMinWidth(dp(52));
				mSbNcHyst = new SeekBar(this);
				mSbNcHyst.setMax(120);
				mSbNcHyst.setProgress(60);
				mSbNcHyst.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
				mSbNcHyst.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
					public void onProgressChanged(SeekBar s, int p, boolean u) {
						mNcHystDb = -12f + p * 0.1f;
						mTvNcHyst.setText(String.format("Hyst:%.0fdB", mNcHystDb));
					}
					public void onStartTrackingTouch(SeekBar s) {}
					public void onStopTrackingTouch(SeekBar s) {}
				});
				row.addView(mTvNcHyst); row.addView(mSbNcHyst);
				mNcLevelRow.addView(row);
			}
			{
				LinearLayout row = new LinearLayout(this);
				row.setOrientation(LinearLayout.HORIZONTAL);
				row.setGravity(Gravity.CENTER_VERTICAL);
				mTvNcRel = smallLabel("Rel:600ms");
				mTvNcRel.setMinWidth(dp(52));
				mSbNcRel = new SeekBar(this);
				mSbNcRel.setMax(100);
				mSbNcRel.setProgress(19);
				mSbNcRel.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
				mSbNcRel.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
					public void onProgressChanged(SeekBar s, int p, boolean u) {
						mNcReleaseMs = 50 + Math.round(p * 29.5f);
						mTvNcRel.setText("Rel:" + mNcReleaseMs + "ms");
					}
					public void onStartTrackingTouch(SeekBar s) {}
					public void onStopTrackingTouch(SeekBar s) {}
				});
				row.addView(mTvNcRel); row.addView(mSbNcRel);
				mNcLevelRow.addView(row);
			}
			// ── Residual (экспандер) ─────────────────────────────────────────
			{
				LinearLayout row = new LinearLayout(this);
				row.setOrientation(LinearLayout.HORIZONTAL);
				row.setGravity(Gravity.CENTER_VERTICAL);
				mTvNcRes = smallLabel("Res:0%");
				mTvNcRes.setMinWidth(dp(52));
				mSbNcRes = new SeekBar(this);
				mSbNcRes.setMax(100);
				mSbNcRes.setProgress(0);
				mSbNcRes.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
				mSbNcRes.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
					public void onProgressChanged(SeekBar s, int p, boolean u) {
						mNcResidual = p / 100f;
						mTvNcRes.setText("Res:" + p + "%");
					}
					public void onStartTrackingTouch(SeekBar s) {}
					public void onStopTrackingTouch(SeekBar s) {}
				});
				row.addView(mTvNcRes); row.addView(mSbNcRes);
				mNcLevelRow.addView(row);
			}
			settingsCol2.addView(mNcLevelRow);
		}
		// ────────────────────────────────────────────────────────────────────

		mAudioSrcPanel.addView(settingsCol1);
		mAudioSrcPanel.addView(settingsCol2);

		// ── Спектр всегда виден; настройки накладываются сверху (FrameLayout) ──
		mSpectrum = new SpectrumView(this);
		android.widget.FrameLayout specFrame = new android.widget.FrameLayout(this);
		// Спектр — базовый слой (снизу)
		android.widget.FrameLayout.LayoutParams specFLP =
			new android.widget.FrameLayout.LayoutParams(
				ViewGroup.LayoutParams.MATCH_PARENT, dp(72), Gravity.BOTTOM);
		specFLP.rightMargin = dp(120);
		specFrame.addView(mSpectrum, specFLP);
		// EQ Bode overlay — поверх спектра, тот же размер и margin
		mEqOverlay = new EqOverlayView(this);
		android.widget.FrameLayout.LayoutParams eqOvLP =
			new android.widget.FrameLayout.LayoutParams(
				ViewGroup.LayoutParams.MATCH_PARENT, dp(72), Gravity.BOTTOM);
		eqOvLP.rightMargin = dp(120);
		specFrame.addView(mEqOverlay, eqOvLP);
		// NC status overlay — поверх спектра, виден даже при свёрнутых настройках.
		// Показывает «NC» / «CUST.NC» / «NC  CUST.NC» когда шумоподавление активно.
		mTvNcOverlay = new TextView(this);
		mTvNcOverlay.setTextColor(0xFFFF7744);
		mTvNcOverlay.setTextSize(9);
		mTvNcOverlay.setTypeface(null, android.graphics.Typeface.BOLD);
		mTvNcOverlay.setVisibility(View.GONE);
		android.widget.FrameLayout.LayoutParams ncOvLP =
			new android.widget.FrameLayout.LayoutParams(
				ViewGroup.LayoutParams.WRAP_CONTENT,
				ViewGroup.LayoutParams.WRAP_CONTENT,
				Gravity.BOTTOM | Gravity.LEFT);
		ncOvLP.leftMargin  = dp(4);
		ncOvLP.bottomMargin = dp(32); // не перекрывать нижний край спектра
		specFrame.addView(mTvNcOverlay, ncOvLP);
		// Настройки — поверх (сверху), поэтому addView после спектра
		specFrame.addView(mAudioSrcPanel, new android.widget.FrameLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT,
			Gravity.TOP));
		panel.addView(specFrame);

		// ── REC и PAUSE фиксированы в root (FrameLayout), не сдвигаются ──────
		// REC — большая круглая кнопка, прикреплена к правому нижнему углу
		int recSize = dp(68);
		int recRight = dp(62); // 54dp зум-рычаг + 8dp зазор
		int recBottom = dp(8);

		mBtn = new Button(this);
		mBtn.setText("REC");
		mBtn.setTextColor(Color.WHITE);
		mBtn.setTextSize(13);
		mBtn.setBackground(mBtnBgIdle);
		mBtn.setOnClickListener(v -> onRecordClick());
		FrameLayout.LayoutParams recLP = new FrameLayout.LayoutParams(recSize, recSize);
		recLP.gravity = Gravity.BOTTOM | Gravity.RIGHT;
		recLP.rightMargin = recRight;
		recLP.bottomMargin = recBottom;
		root.addView(mBtn, recLP);

		// PAUSE — маленькая кнопка над REC, видна только во время записи
		mBtnPause = new Button(this);
		mBtnPause.setText("⏸");
		mBtnPause.setTextColor(Color.WHITE);
		mBtnPause.setTextSize(16);
		mBtnPause.setBackground(mBtnBgPause);
		mBtnPause.setVisibility(View.GONE);
		mBtnPause.setOnClickListener(v -> onPauseClick());
		FrameLayout.LayoutParams pauseLP = new FrameLayout.LayoutParams(dp(44), dp(44));
		pauseLP.gravity = Gravity.BOTTOM | Gravity.RIGHT;
		pauseLP.rightMargin = recRight + (recSize - dp(44)) / 2; // центр над REC
		pauseLP.bottomMargin = recBottom + recSize + dp(6);
		root.addView(mBtnPause, pauseLP);

		// ── EQ panel (оверлей поверх превью, от верха экрана вниз — выше спектра) ──
		mEqPanel = buildEqPanel();
		mEqPanel.setVisibility(View.GONE);
		FrameLayout.LayoutParams eqLP = new FrameLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
		eqLP.gravity = Gravity.TOP;
		eqLP.leftMargin  = dp(58); // не перекрывать Gain + VU
		eqLP.rightMargin = dp(54); // не перекрывать Zoom-рычаг
		root.addView(mEqPanel, eqLP);

		return root;
	}
	
	// =========================================================================
	// EQ panel builder
	// =========================================================================

	private View buildEqPanel() {
		LinearLayout panel = new LinearLayout(this);
		panel.setOrientation(LinearLayout.VERTICAL);
		panel.setBackgroundColor(0xF0181818);
		panel.setPadding(dp(8), dp(4), dp(8), dp(8));

		// ── Заголовок: EQ [ON] [+] [✕] ──────────────────────────────────────
		LinearLayout header = new LinearLayout(this);
		header.setOrientation(LinearLayout.HORIZONTAL);
		header.setGravity(Gravity.CENTER_VERTICAL);

		TextView tvTitle = new TextView(this);
		tvTitle.setText("EQUALIZER");
		tvTitle.setTextColor(0xFF88DDFF);
		tvTitle.setTextSize(12);
		tvTitle.setTypeface(null, android.graphics.Typeface.BOLD);
		LinearLayout.LayoutParams tlp = new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f);
		header.addView(tvTitle, tlp);

		mCbEqEnable = new CheckBox(this);
		mCbEqEnable.setText("ON");
		mCbEqEnable.setTextColor(0xCCCCCCCC);
		mCbEqEnable.setTextSize(11);
		mCbEqEnable.setChecked(mEqEnabled);
		mCbEqEnable.setOnCheckedChangeListener((v, on) -> {
			mEqEnabled = on;
			if (mEqOverlay != null) mEqOverlay.refresh();
		});
		header.addView(mCbEqEnable);

		// Кнопка "+" — добавить фильтр
		Button btnAdd = new Button(this);
		btnAdd.setText("+");
		btnAdd.setTextSize(18);
		btnAdd.setTextColor(0xFF88FF88);
		btnAdd.setBackground(null);
		btnAdd.setPadding(dp(10), 0, dp(10), 0);
		btnAdd.setOnClickListener(v -> {
			new android.app.AlertDialog.Builder(this)
				.setTitle("Add filter")
				.setItems(new String[]{
					"HPF  (High Pass, −12 dB/oct)",
					"LPF  (Low Pass, −12 dB/oct)",
					"Peak (Bell ±12 dB)",
					"Low Shelf  (shelf on lows)",
					"High Shelf (shelf on highs)"
				}, (d, which) -> {
					EqBand band = new EqBand();
					band.type    = which; // HPF=0,LPF=1,PEAK=2,LSHELF=3,HSHELF=4
					band.freq    = (which == EqBand.HPF)    ? 80f
					             : (which == EqBand.LPF)    ? 8000f
					             : (which == EqBand.LSHELF) ? 120f
					             : (which == EqBand.HSHELF) ? 8000f
					             : 1000f;
					band.q       = 1.0f;
					band.gainDb  = 0f;
					band.slopeDb = 6f;
					band.enabled = true;
					synchronized (mEqLock) {
						band.computeCoeffs(AUDIO_SR);
						mEqBands.add(band);
					}
					addEqBandRow(band);
					if (mEqOverlay != null) mEqOverlay.refresh();
				})
				.show();
		});
		header.addView(btnAdd);

		// Кнопка закрытия
		Button btnClose = new Button(this);
		btnClose.setText("✕");
		btnClose.setTextSize(14);
		btnClose.setTextColor(0xFFAAAAAA);
		btnClose.setBackground(null);
		btnClose.setPadding(dp(6), 0, dp(2), 0);
		btnClose.setOnClickListener(v -> {
			mEqPanelVisible = false;
			mEqPanel.setVisibility(View.GONE);
			mBtnEq.setText("EQ");
		});
		header.addView(btnClose);
		panel.addView(header, new LinearLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

		// ── Строка Save / Load config ─────────────────────────────────────────
		LinearLayout cfgRow = new LinearLayout(this);
		cfgRow.setOrientation(LinearLayout.HORIZONTAL);
		cfgRow.setGravity(Gravity.CENTER_VERTICAL);
		cfgRow.setPadding(0, dp(3), 0, dp(3));

		Button btnSaveCfg = new Button(this);
		btnSaveCfg.setText("💾 Save config");
		btnSaveCfg.setTextSize(11);
		btnSaveCfg.setTextColor(0xFFAADDFF);
		btnSaveCfg.setBackground(null);
		btnSaveCfg.setPadding(dp(4), dp(2), dp(14), dp(2));
		btnSaveCfg.setOnClickListener(v -> saveEqConfig());
		cfgRow.addView(btnSaveCfg);

		Button btnLoadCfg = new Button(this);
		btnLoadCfg.setText("📂 Load config");
		btnLoadCfg.setTextSize(11);
		btnLoadCfg.setTextColor(0xFFAADDFF);
		btnLoadCfg.setBackground(null);
		btnLoadCfg.setPadding(dp(4), dp(2), dp(4), dp(2));
		btnLoadCfg.setOnClickListener(v -> loadEqConfig());
		cfgRow.addView(btnLoadCfg);

		panel.addView(cfgRow, new LinearLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

		// Разделитель
		View div = new View(this);
		div.setBackgroundColor(0x44FFFFFF);
		panel.addView(div, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 1));

		// ── Прокручиваемый список фильтров ────────────────────────────────────
		ScrollView sv = new ScrollView(this) {
			@Override protected void onMeasure(int wMs, int hMs) {
				// Ограничиваем высоту списка: не более 55% высоты экрана
				int maxH = (int)(getResources().getDisplayMetrics().heightPixels * 0.55f);
				super.onMeasure(wMs, MeasureSpec.makeMeasureSpec(maxH, MeasureSpec.AT_MOST));
			}
		};
		mEqListView = new LinearLayout(this);
		mEqListView.setOrientation(LinearLayout.VERTICAL);
		sv.addView(mEqListView, new LinearLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
		panel.addView(sv, new LinearLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

		return panel;
	}

	private void addEqBandRow(EqBand band) {
		final String[] typeNames = {"HPF", "LPF", "PEAK", "L.SHELF", "H.SHELF"};

		LinearLayout row = new LinearLayout(this);
		row.setOrientation(LinearLayout.VERTICAL);
		row.setBackgroundColor(0x22FFFFFF);
		row.setPadding(dp(4), dp(3), dp(4), dp(4));
		LinearLayout.LayoutParams rowLP = new LinearLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
		rowLP.topMargin = dp(4);
		row.setLayoutParams(rowLP);

		// ── Строка 1: [TYPE] [✓ ON] [F: -------- Hz] [✕] ──────────────────
		LinearLayout top = new LinearLayout(this);
		top.setOrientation(LinearLayout.HORIZONTAL);
		top.setGravity(Gravity.CENTER_VERTICAL);

		TextView tvType = new TextView(this);
		tvType.setText(typeNames[band.type]);
		tvType.setTextColor(0xFF88DDFF);
		tvType.setTextSize(11);
		tvType.setTypeface(null, android.graphics.Typeface.BOLD);
		tvType.setMinWidth(dp(44));
		top.addView(tvType);

		CheckBox cbEn = new CheckBox(this);
		cbEn.setText("ON");
		cbEn.setTextColor(0xCCCCCCCC);
		cbEn.setTextSize(11);
		cbEn.setChecked(band.enabled);
		cbEn.setOnCheckedChangeListener((v, on) -> {
			synchronized (mEqLock) { band.enabled = on; }
			if (mEqOverlay != null) mEqOverlay.refresh();
		});
		top.addView(cbEn);

		TextView tvFL = new TextView(this);
		tvFL.setText("F:");
		tvFL.setTextColor(0xCCCCCCCC);
		tvFL.setTextSize(11);
		top.addView(tvFL);

		SeekBar sbFreq = new SeekBar(this);
		sbFreq.setMax(100);
		sbFreq.setProgress(eqFreqToProgress(band.freq));
		sbFreq.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
		top.addView(sbFreq);

		final TextView tvFreq = new TextView(this);
		tvFreq.setText(eqFormatFreq(band.freq));
		tvFreq.setTextColor(0xFFDDDDDD);
		tvFreq.setTextSize(11);
		tvFreq.setMinWidth(dp(54));
		top.addView(tvFreq);

		Button btnDel = new Button(this);
		btnDel.setText("✕");
		btnDel.setTextSize(12);
		btnDel.setTextColor(0xFFFF4444);
		btnDel.setBackground(null);
		btnDel.setPadding(dp(6), 0, dp(2), 0);
		btnDel.setOnClickListener(v -> {
			synchronized (mEqLock) { mEqBands.remove(band); }
			mEqListView.removeView(row);
			if (mEqOverlay != null) mEqOverlay.refresh();
		});
		top.addView(btnDel);
		row.addView(top, new LinearLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

		sbFreq.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
			public void onProgressChanged(SeekBar s, int p, boolean u) {
				float f = eqProgressToFreq(p);
				tvFreq.setText(eqFormatFreq(f));
				synchronized (mEqLock) { band.freq = f; band.computeCoeffs(AUDIO_SR); band.resetState(); }
				if (mEqOverlay != null) mEqOverlay.refresh();
			}
			public void onStartTrackingTouch(SeekBar s) {}
			public void onStopTrackingTouch(SeekBar s) {}
		});

		// ── Peak: строки Q и Gain ─────────────────────────────────────────────
		if (band.type == EqBand.PEAK) {
			// Q row
			LinearLayout qRow = new LinearLayout(this);
			qRow.setOrientation(LinearLayout.HORIZONTAL);
			qRow.setGravity(Gravity.CENTER_VERTICAL);
			TextView tvQL = new TextView(this);
			tvQL.setText("Q:"); tvQL.setTextColor(0xCCCCCCCC); tvQL.setTextSize(11); tvQL.setMinWidth(dp(44));
			qRow.addView(tvQL);
			SeekBar sbQ = new SeekBar(this);
			sbQ.setMax(100);
			sbQ.setProgress(Math.round((band.q - 0.1f) / 3.9f * 100f));
			sbQ.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
			qRow.addView(sbQ);
			final TextView tvQ = new TextView(this);
			tvQ.setText(String.format("%.2f", band.q));
			tvQ.setTextColor(0xFFDDDDDD); tvQ.setTextSize(11); tvQ.setMinWidth(dp(54));
			qRow.addView(tvQ);
			TextView sp1 = new TextView(this); sp1.setText("  "); qRow.addView(sp1);
			row.addView(qRow, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
			sbQ.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
				public void onProgressChanged(SeekBar s, int p, boolean u) {
					float qv = 0.1f + p * 3.9f / 100f;
					tvQ.setText(String.format("%.2f", qv));
					synchronized (mEqLock) { band.q = qv; band.computeCoeffs(AUDIO_SR); band.resetState(); }
					if (mEqOverlay != null) mEqOverlay.refresh();
				}
				public void onStartTrackingTouch(SeekBar s) {}
				public void onStopTrackingTouch(SeekBar s) {}
			});

			// Gain row
			LinearLayout gRow = new LinearLayout(this);
			gRow.setOrientation(LinearLayout.HORIZONTAL);
			gRow.setGravity(Gravity.CENTER_VERTICAL);
			TextView tvGL = new TextView(this);
			tvGL.setText("dB:"); tvGL.setTextColor(0xCCCCCCCC); tvGL.setTextSize(11); tvGL.setMinWidth(dp(44));
			gRow.addView(tvGL);
			SeekBar sbGain = new SeekBar(this);
			sbGain.setMax(48);
			sbGain.setProgress(Math.round((band.gainDb + 12f) * 2f));
			sbGain.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
			gRow.addView(sbGain);
			final TextView tvGain = new TextView(this);
			tvGain.setText(String.format("%+.1f dB", band.gainDb));
			tvGain.setTextColor(0xFFDDDDDD); tvGain.setTextSize(11); tvGain.setMinWidth(dp(54));
			gRow.addView(tvGain);
			TextView sp2 = new TextView(this); sp2.setText("  "); gRow.addView(sp2);
			row.addView(gRow, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
			sbGain.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
				public void onProgressChanged(SeekBar s, int p, boolean u) {
					float gdb = -12f + p * 0.5f;
					tvGain.setText(String.format("%+.1f dB", gdb));
					synchronized (mEqLock) { band.gainDb = gdb; band.computeCoeffs(AUDIO_SR); band.resetState(); }
					if (mEqOverlay != null) mEqOverlay.refresh();
				}
				public void onStartTrackingTouch(SeekBar s) {}
				public void onStopTrackingTouch(SeekBar s) {}
			});
		}

		// ── Shelf: Gain и Slope ────────────────────────────────────────────────
		if (band.type == EqBand.LSHELF || band.type == EqBand.HSHELF) {
			// Gain row ±12 dB
			LinearLayout gRow = new LinearLayout(this);
			gRow.setOrientation(LinearLayout.HORIZONTAL);
			gRow.setGravity(Gravity.CENTER_VERTICAL);
			TextView tvGL = new TextView(this);
			tvGL.setText("dB:"); tvGL.setTextColor(0xCCCCCCCC); tvGL.setTextSize(11); tvGL.setMinWidth(dp(44));
			gRow.addView(tvGL);
			SeekBar sbGain = new SeekBar(this);
			sbGain.setMax(48);
			sbGain.setProgress(Math.round((band.gainDb + 12f) * 2f));
			sbGain.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
			gRow.addView(sbGain);
			final TextView tvGain = new TextView(this);
			tvGain.setText(String.format("%+.1f dB", band.gainDb));
			tvGain.setTextColor(0xFFDDDDDD); tvGain.setTextSize(11); tvGain.setMinWidth(dp(54));
			gRow.addView(tvGain);
			TextView spG = new TextView(this); spG.setText("  "); gRow.addView(spG);
			row.addView(gRow, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
			sbGain.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
				public void onProgressChanged(SeekBar s, int p, boolean u) {
					float gdb = -12f + p * 0.5f;
					tvGain.setText(String.format("%+.1f dB", gdb));
					synchronized (mEqLock) { band.gainDb = gdb; band.computeCoeffs(AUDIO_SR); band.resetState(); }
					if (mEqOverlay != null) mEqOverlay.refresh();
				}
				public void onStartTrackingTouch(SeekBar s) {}
				public void onStopTrackingTouch(SeekBar s) {}
			});

			// Slope row: 6..24 дБ/окт
			LinearLayout sRow = new LinearLayout(this);
			sRow.setOrientation(LinearLayout.HORIZONTAL);
			sRow.setGravity(Gravity.CENTER_VERTICAL);
			TextView tvSL = new TextView(this);
			tvSL.setText("Slp:"); tvSL.setTextColor(0xCCCCCCCC); tvSL.setTextSize(11); tvSL.setMinWidth(dp(44));
			sRow.addView(tvSL);
			SeekBar sbSlope = new SeekBar(this);
			sbSlope.setMax(18); // 6..24 шаг 1 → 18 позиций
			sbSlope.setProgress(Math.round(band.slopeDb - 6f));
			sbSlope.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
			sRow.addView(sbSlope);
			final TextView tvSlope = new TextView(this);
			tvSlope.setText(String.format("%.0f dB/oct", band.slopeDb));
			tvSlope.setTextColor(0xFFDDDDDD); tvSlope.setTextSize(11); tvSlope.setMinWidth(dp(54));
			sRow.addView(tvSlope);
			TextView spS = new TextView(this); spS.setText("  "); sRow.addView(spS);
			row.addView(sRow, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
			sbSlope.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
				public void onProgressChanged(SeekBar s, int p, boolean u) {
					float sl = 6f + p;
					tvSlope.setText(String.format("%.0f dB/oct", sl));
					synchronized (mEqLock) { band.slopeDb = sl; band.computeCoeffs(AUDIO_SR); band.resetState(); }
					if (mEqOverlay != null) mEqOverlay.refresh();
				}
				public void onStartTrackingTouch(SeekBar s) {}
				public void onStopTrackingTouch(SeekBar s) {}
			});
		}

		mEqListView.addView(row);
		if (mEqOverlay != null) mEqOverlay.refresh();
	}

	// Логарифмическая шкала частот: 20 Гц .. 18 кГц (progress 0..100)
	private static int eqFreqToProgress(float freq) {
		return (int) Math.round(100.0 * Math.log(Math.max(20f, freq) / 20.0) / Math.log(900.0));
	}
	private static float eqProgressToFreq(int p) {
		return 20f * (float) Math.pow(900.0, p / 100.0);
	}
	private static String eqFormatFreq(float hz) {
		return hz >= 1000f ? String.format("%.1f kHz", hz / 1000f) : String.format("%.0f Hz", hz);
	}

	/** Применяет цепочку biquad-фильтров к PCM-буферу (in-place). */
	private void applyEq(short[] buf, int r, int ch) {
		synchronized (mEqLock) {
			for (EqBand b : mEqBands) {
				if (!b.enabled) continue;
				for (int i = 0; i < r; i++) {
					int c = (ch > 1) ? (i & 1) : 0; // 0=L/mono, 1=R
					double x = buf[i];
					double y = b.b0 * x + b.b1 * b.x1[c] + b.b2 * b.x2[c]
					         - b.a1 * b.y1[c] - b.a2 * b.y2[c];
					b.x2[c] = b.x1[c]; b.x1[c] = x;
					b.y2[c] = b.y1[c]; b.y1[c] = y;
					float s = (float) y;
					buf[i] = (short)(s > 32767f ? 32767 : (s < -32768f ? -32768 : (int) s));
				}
			}
		}
	}

	// =========================================================================
	// EqOverlayView — Bode plot поверх спектр-анализатора
	// =========================================================================
	private class EqOverlayView extends View {
		private final android.graphics.Paint mCurvePaint = new android.graphics.Paint(android.graphics.Paint.ANTI_ALIAS_FLAG);
		private final android.graphics.Paint mGridPaint  = new android.graphics.Paint();
		private final android.graphics.Paint mLblPaint   = new android.graphics.Paint(android.graphics.Paint.ANTI_ALIAS_FLAG);
		private static final int PLOT_POINTS = 256;
		// Масштаб должен совпадать со SpectrumView:
		// X: log10(f) от log10(20) до log10(sr/2), Y: 0..h → −90..0 dB (norm 0..1)
		// Мы отображаем EQ response в диапазоне ±20 dB вокруг 0 dB:
		// центр (0 дБ) → середина высоты; −20 дБ → низ; +20 дБ → верх
		private static final float DB_RANGE = 20f; // ±20 dB

		EqOverlayView(android.content.Context ctx) {
			super(ctx);
			mCurvePaint.setColor(0xFFFFD700);
			mCurvePaint.setStrokeWidth(2.5f);
			mCurvePaint.setStyle(android.graphics.Paint.Style.STROKE);
			mCurvePaint.setStrokeJoin(android.graphics.Paint.Join.ROUND);
			mGridPaint.setColor(0x44FFD700);
			mGridPaint.setStrokeWidth(0.8f);
			mLblPaint.setColor(0xAAFFD700);
			mLblPaint.setTextSize(dp(8));
			mLblPaint.setTextAlign(android.graphics.Paint.Align.RIGHT);
		}

		void refresh() { postInvalidate(); }

		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			if (w == 0 || h == 0) return;
			if (!mEqEnabled) return;

			// Метки частот в SpectrumView занимают верхнюю полосу высотой lblH
			// воспроизводим то же смещение
			float lblH = mLblPaint.getTextSize() + 4f;
			float plotTop = lblH;
			float plotH   = h - plotTop;
			float midY    = plotTop + plotH / 2f; // 0 дБ

			// Горизонтальная линия 0 дБ
			canvas.drawLine(0, midY, w, midY, mGridPaint);
			// +10 / -10 дБ штрихи
			float y10 = midY - plotH / 2f * (10f / DB_RANGE);
			float ym10 = midY + plotH / 2f * (10f / DB_RANGE);
			canvas.drawLine(0, y10,  w, y10,  mGridPaint);
			canvas.drawLine(0, ym10, w, ym10, mGridPaint);
			canvas.drawText("+10", w - 2, y10  + mLblPaint.getTextSize() * 0.4f, mLblPaint);
			canvas.drawText("-10", w - 2, ym10 + mLblPaint.getTextSize() * 0.4f, mLblPaint);
			canvas.drawText("  0", w - 2, midY + mLblPaint.getTextSize() * 0.4f, mLblPaint);

			double logFMin = Math.log10(20.0);
			double logFMax = Math.log10(AUDIO_SR / 2.0);

			// Считаем суммарный response по всем активным полосам
			android.graphics.Path path = new android.graphics.Path();
			boolean first = true;
			for (int i = 0; i < PLOT_POINTS; i++) {
				double logF = logFMin + (double) i / (PLOT_POINTS - 1) * (logFMax - logFMin);
				double freq  = Math.pow(10.0, logF);
				// Комплексный отклик biquad при частоте freq:
				// H(z) при z = e^(j*w), w = 2π*f/sr
				double totalDb = 0.0;
				synchronized (mEqLock) {
					for (EqBand b : mEqBands) {
						if (!b.enabled) continue;
						double w0 = 2.0 * Math.PI * freq / AUDIO_SR;
						// z^-1 = e^(-jw0), оцениваем числитель и знаменатель
						double cosW = Math.cos(w0), sinW = Math.sin(w0);
						double cos2W = Math.cos(2 * w0), sin2W = Math.sin(2 * w0);
						// Числитель: b0 + b1*z^-1 + b2*z^-2
						double numRe = b.b0 + b.b1 * cosW + b.b2 * cos2W;
						double numIm =      - b.b1 * sinW - b.b2 * sin2W;
						// Знаменатель: 1 + a1*z^-1 + a2*z^-2
						double denRe = 1.0  + b.a1 * cosW + b.a2 * cos2W;
						double denIm =      - b.a1 * sinW - b.a2 * sin2W;
						double magSq = (numRe*numRe + numIm*numIm) / (denRe*denRe + denIm*denIm);
						if (magSq > 1e-20) totalDb += 10.0 * Math.log10(magSq);
					}
				}
				float x = (float)(w * (logF - logFMin) / (logFMax - logFMin));
				float db = (float) Math.max(-DB_RANGE, Math.min(DB_RANGE, totalDb));
				float y  = midY - plotH / 2f * (db / DB_RANGE);
				if (first) { path.moveTo(x, y); first = false; }
				else         path.lineTo(x, y);
			}
			canvas.drawPath(path, mCurvePaint);
		}
	}

	/** Строит колонку с барабаном фокуса (как кольцо на настоящей камере) */
	private View buildFocusColumn() {
		FrameLayout col = new FrameLayout(this);
		col.setBackgroundColor(0x33000000);
		
		mFocusDrum = new FocusDrumView(this);
		mFocusDrum.setOnFocusChangeListener(value -> {
			mFocusValue = value; // 0=∞, 1=macro
			updateFocusLabel(value);
			if (mManualFocus && mCamHandler != null)
			mCamHandler.post(MainActivity.this::buildAndSendRequest);
		});
		mFocusDrum.setOnDrumScrollListener(new FocusDrumView.OnDrumScrollListener() {
			@Override
			public void onScrollStart() {
				if (mCbFocusAssist == null || !mCbFocusAssist.isChecked()) return;
				// Отменяем отложенное восстановление (вдруг снова начали крутить)
				mFocusAssistHandler.removeCallbacksAndMessages(null);
				// Запоминаем текущий зум и форсируем максимальный (или ×3, но не меньше 4)
				mSavedZoomBeforeAssist = mZoomLevel;
				float assistZoom = Math.min(mMaxZoom, Math.max(mZoomLevel * 3f, 4f));
				mZoomLevel = assistZoom;
				if (mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest);
			}
			@Override
			public void onScrollStop() {
				if (mCbFocusAssist == null || !mCbFocusAssist.isChecked()) return;
				// Через 300 мс восстанавливаем зум
				mFocusAssistHandler.removeCallbacksAndMessages(null);
				mFocusAssistHandler.postDelayed(() -> {
					mZoomLevel = mSavedZoomBeforeAssist;
					if (mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest);
				}, 300);
			}
		});
		
		FrameLayout.LayoutParams drumLP = new FrameLayout.LayoutParams(
		ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
		col.addView(mFocusDrum, drumLP);
		
		// Метки ∞ сверху, макро снизу
		TextView tvTop = smallLabel("∞");
		FrameLayout.LayoutParams topLP = new FrameLayout.LayoutParams(
		ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
		topLP.gravity = Gravity.TOP | Gravity.CENTER_HORIZONTAL;
		topLP.topMargin = dp(4);
		col.addView(tvTop, topLP);
		
		TextView tvBot = smallLabel("▲");
		FrameLayout.LayoutParams botLP = new FrameLayout.LayoutParams(
		ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
		botLP.gravity = Gravity.BOTTOM | Gravity.CENTER_HORIZONTAL;
		botLP.bottomMargin = dp(4);
		col.addView(tvBot, botLP);
		
		mTvFocus = smallLabel("∞");
		FrameLayout.LayoutParams midLP = new FrameLayout.LayoutParams(
		ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
		midLP.gravity = Gravity.CENTER;
		col.addView(mTvFocus, midLP);
		
		return col;
	}
	
	private void updateFocusLabel(float value) {
		if (mTvFocus == null) return;
		String txt = value < 0.005f ? "∞" : String.format("%.1f", value * mMinFocusDist) + "m⁻¹";
		mTvFocus.setText(txt);
	}

	private void updateEvLabel(int ev) {
		if (mTvEv == null) return;
		runOnUiThread(() -> mTvEv.setText(ev == 0 ? "EV  0" : String.format("EV %+d", ev)));
	}
	
	// ── Helpers ───────────────────────────────────────────────────────────────
	
	private GradientDrawable makeOval(int color) {
		GradientDrawable d = new GradientDrawable();
		d.setShape(GradientDrawable.OVAL);
		d.setColor(color);
		return d;
	}
	
	private TextView smallLabel(String t) {
		TextView v = new TextView(this);
		v.setText(t);
		v.setTextColor(0xCCCCCCCC);
		v.setTextSize(11);
		v.setBackgroundColor(0x88000000);
		v.setPadding(dp(3), dp(1), dp(3), dp(1));
		return v;
	}
	
	private LinearLayout hrow(View... views) {
		LinearLayout ll = new LinearLayout(this);
		ll.setOrientation(LinearLayout.HORIZONTAL);
		ll.setGravity(Gravity.CENTER_VERTICAL);
		LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT,
		ViewGroup.LayoutParams.WRAP_CONTENT);
		lp.bottomMargin = dp(2);
		ll.setLayoutParams(lp);
		for (View v : views) {
			if (v.getLayoutParams() == null)
			v.setLayoutParams(new LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT,
			ViewGroup.LayoutParams.WRAP_CONTENT));
			ll.addView(v);
		}
		return ll;
	}
	
	private ViewGroup.LayoutParams mp_mp() {
		return new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
	}
	
	private int dp(int x) {
		return Math.round(x * getResources().getDisplayMetrics().density);
	}
	
	// =========================================================================
	// Напоминание — авиарежим
	// =========================================================================

	private void showHelp() {
		new android.app.AlertDialog.Builder(this)
			.setTitle("\u2139  CaMic — Settings Guide")
			.setMessage(
				"GAIN  Vertical slider on the left.\n" +
				"  0 dB = center. Range \u221220 to +20 dB.\n\n" +
				"SOFT CLIP  Gentle saturation limiter.\n" +
				"  Prevents digital clipping on loud transients.\n\n" +
				"AGC  System automatic gain control.\n\n" +
				"NC  System hardware noise cancellation.\n\n" +
				"CUST.NC  Software noise gate with lookahead (30 ms).\n" +
				"  Thr  — open threshold (× noise floor). Start around 2\u00d7.\n" +
				"  Hyst — hysteresis in dB. How far below Thr the gate\n" +
				"         closes. \u22126 dB = gate closes at half amplitude.\n" +
				"  Rel  — release time. How long the tail fades after gate\n" +
				"         closes. 600\u2013800 ms suits most strings.\n" +
				"  Res  — residual level (0 = silence, 100% = no gate).\n" +
				"         Acts as an expander when > 0.\n\n" +
				"PRE-BUFFER  Keeps a rolling buffer so recording\n" +
				"  starts slightly in the past (1\u20135 s).\n\n" +
				"EIS  Electronic image stabilisation (crop-based).\n" +
				"  Adds slight crop; A/V sync is compensated automatically.\n\n" +
				"WAV  Records a separate uncompressed sidecar file\n" +
				"  (pre-gate, pre-NC — raw capture).\n\n" +
				"BPS / RES  Video bitrate and resolution.\n" +
				"  Cannot be changed during recording.")
			.setPositiveButton("OK", null)
			.show();
	}

	// =========================================================================
	// NC overlay update
	// =========================================================================

	/** Обновляет постоянный оверлей «NC / CUST.NC» над спектром. */
	private void updateNcOverlay() {
		if (mTvNcOverlay == null) return;
		boolean sysNc  = mNcEnabled;
		boolean custNc = mCustomNcEnabled;
		if (!sysNc && !custNc) {
			mTvNcOverlay.setVisibility(View.GONE);
		} else {
			StringBuilder sb = new StringBuilder();
			if (sysNc)  sb.append("NC");
			if (custNc) { if (sb.length() > 0) sb.append("  "); sb.append("CUST.NC"); }
			mTvNcOverlay.setText(sb.toString());
			mTvNcOverlay.setVisibility(View.VISIBLE);
		}
	}

	// =========================================================================
	// EQ config save / load
	// =========================================================================

	/**
	 * Сохраняет текущую цепочку EQ-фильтров в JSON-файл.
	 * Показывает AlertDialog с полем ввода имени пресета.
	 * Файлы хранятся в getExternalFilesDir(null) — доступны без рут,
	 * видны при подключении USB (MTP).
	 */
	private void saveEqConfig() {
		android.widget.EditText et = new android.widget.EditText(this);
		et.setHint("Preset name");
		et.setInputType(android.text.InputType.TYPE_CLASS_TEXT);
		et.setPadding(dp(16), dp(8), dp(16), dp(8));
		new android.app.AlertDialog.Builder(this)
			.setTitle("Save EQ config")
			.setView(et)
			.setPositiveButton("Save", (d, w) -> {
				String name = et.getText().toString().trim();
				if (name.isEmpty()) name = "eq_config";
				// Убираем недопустимые символы для имени файла
				name = name.replaceAll("[^a-zA-Z0-9_\\-]", "_");
				try {
					org.json.JSONArray arr = new org.json.JSONArray();
					synchronized (mEqLock) {
						for (EqBand b : mEqBands) {
							org.json.JSONObject obj = new org.json.JSONObject();
							obj.put("type",    b.type);
							obj.put("enabled", b.enabled);
							obj.put("freq",    b.freq);
							obj.put("q",       b.q);
							obj.put("gainDb",  b.gainDb);
							obj.put("slopeDb", b.slopeDb);
							arr.put(obj);
						}
					}
					org.json.JSONObject root = new org.json.JSONObject();
					root.put("eqEnabled", mEqEnabled);
					root.put("bands", arr);
					java.io.File dir = getExternalFilesDir(null);
					if (dir == null) dir = getFilesDir();
					if (!dir.exists()) dir.mkdirs();
					java.io.File f = new java.io.File(dir, name + ".json");
					java.io.FileWriter fw = new java.io.FileWriter(f);
					fw.write(root.toString(2));
					fw.close();
					status("EQ saved: " + f.getName());
				} catch (Exception ex) {
					status("Save failed: " + ex.getMessage());
				}
			})
			.setNegativeButton("Cancel", null)
			.show();
	}

	/**
	 * Загружает цепочку EQ-фильтров из ранее сохранённого JSON-файла.
	 * Показывает список .json файлов из getExternalFilesDir(null).
	 */
	private void loadEqConfig() {
		java.io.File dir = getExternalFilesDir(null);
		if (dir == null) dir = getFilesDir();
		java.io.File[] files = dir.listFiles((d, n) -> n.endsWith(".json"));
		if (files == null || files.length == 0) {
			new android.app.AlertDialog.Builder(this)
				.setTitle("Load EQ config")
				.setMessage("No saved configs found.\nSave a config first using 💾 Save config.")
				.setPositiveButton("OK", null)
				.show();
			return;
		}
		// Сортируем по дате изменения (новейший первый)
		java.util.Arrays.sort(files, (a, b) -> Long.compare(b.lastModified(), a.lastModified()));
		String[] names = new String[files.length];
		for (int i = 0; i < files.length; i++) {
			String n = files[i].getName();
			names[i] = n.endsWith(".json") ? n.substring(0, n.length() - 5) : n;
		}
		final java.io.File[] filesRef = files;
		new android.app.AlertDialog.Builder(this)
			.setTitle("Load EQ config")
			.setItems(names, (d, which) -> {
				try {
					java.io.BufferedReader br = new java.io.BufferedReader(
						new java.io.FileReader(filesRef[which]));
					StringBuilder sb = new StringBuilder();
					String line;
					while ((line = br.readLine()) != null) sb.append(line);
					br.close();
					org.json.JSONObject root = new org.json.JSONObject(sb.toString());
					org.json.JSONArray arr = root.getJSONArray("bands");
					boolean eqOn = root.optBoolean("eqEnabled", true);

					// Мы уже на UI-потоке (setItems callback), runOnUiThread не нужен
					synchronized (mEqLock) { mEqBands.clear(); }
					if (mEqListView != null) mEqListView.removeAllViews();
					for (int i = 0; i < arr.length(); i++) {
						org.json.JSONObject obj = arr.getJSONObject(i);
						EqBand b = new EqBand();
						b.type    = obj.getInt("type");
						b.enabled = obj.getBoolean("enabled");
						b.freq    = (float) obj.getDouble("freq");
						b.q       = (float) obj.getDouble("q");
						b.gainDb  = (float) obj.getDouble("gainDb");
						b.slopeDb = (float) obj.optDouble("slopeDb", 6.0);
						synchronized (mEqLock) { b.computeCoeffs(AUDIO_SR); mEqBands.add(b); }
						addEqBandRow(b);
					}
					mEqEnabled = eqOn;
					if (mCbEqEnable != null) mCbEqEnable.setChecked(eqOn); // триггерит refresh()
					else if (mEqOverlay != null) mEqOverlay.refresh();
					status("EQ loaded: " + names[which]);
				} catch (Exception ex) {
					status("Load failed: " + ex.getMessage());
				}
			})
			.setNegativeButton("Cancel", null)
			.show();
	}

	private static final String P = "cam_prefs";

	private void savePrefs() {
		android.content.SharedPreferences.Editor e =
			getSharedPreferences(P, 0).edit();
		// ── Audio FX ─────────────────────────────────────────────────────────
		if (mCbAgc        != null) e.putBoolean("agc",         mCbAgc.isChecked());
		if (mCbNc         != null) e.putBoolean("nc",          mCbNc.isChecked());
		if (mCbCustomNc   != null) e.putBoolean("customNc",    mCbCustomNc.isChecked());
		if (mCbSoftClip   != null) e.putBoolean("softClip",    mCbSoftClip.isChecked());
		if (mCbRecordWav  != null) e.putBoolean("recordWav",   mCbRecordWav.isChecked());
		if (mCbEis        != null) e.putBoolean("eis",         mCbEis.isChecked());
		// ── Custom NC gate params ─────────────────────────────────────────────
		e.putFloat("ncThr",     mNcThreshMult);
		e.putFloat("ncHyst",    mNcHystDb);
		e.putInt  ("ncRel",     mNcReleaseMs);
		e.putFloat("ncRes",     mNcResidual);
		// ── Gain slider ───────────────────────────────────────────────────────
		if (mSeekGain != null) e.putInt("gain", mSeekGain.getProgress());
		// ── Video ─────────────────────────────────────────────────────────────
		e.putInt("videoW",  mVideoW);
		e.putInt("videoH",  mVideoH);
		e.putInt("videoBps", mVideoBps);
		// ── Pre-buffer ────────────────────────────────────────────────────────
		e.putBoolean("preBuf", mPreBufferEnabled);
		e.putInt    ("preBufSecs", mPreBufSecs);
		// ── Audio source spinner ──────────────────────────────────────────────
		if (mSpinner != null) e.putInt("audSrc", mSpinner.getSelectedItemPosition());
		// ── Visibility toggles ────────────────────────────────────────────────
		if (mCbOsc != null) e.putBoolean("showOsc", mCbOsc.isChecked());
		if (mCbSpec != null) e.putBoolean("showSpec", mCbSpec.isChecked());
		// ── EQ chain ──────────────────────────────────────────────────────────
		e.putBoolean("eqEnabled", mEqEnabled);
		try {
			org.json.JSONArray arr = new org.json.JSONArray();
			synchronized (mEqLock) {
				for (EqBand b : mEqBands) {
					org.json.JSONObject obj = new org.json.JSONObject();
					obj.put("type",    b.type);
					obj.put("enabled", b.enabled);
					obj.put("freq",    b.freq);
					obj.put("q",       b.q);
					obj.put("gainDb",  b.gainDb);
					obj.put("slopeDb", b.slopeDb);
					arr.put(obj);
				}
			}
			e.putString("eqChain", arr.toString());
		} catch (Exception ignored) {}
		e.apply();
	}

	// loadPrefs вызывается в конце onCreate, ПОСЛЕ создания всех View
	private void loadPrefs() {
		android.content.SharedPreferences p =
			getSharedPreferences(P, 0);
		if (!p.contains("gain")) return; // первый запуск — не трогаем дефолты
		// ── Audio FX ─────────────────────────────────────────────────────────
		if (mCbAgc      != null) mCbAgc.setChecked(p.getBoolean("agc",      false));
		if (mCbNc       != null) mCbNc.setChecked( p.getBoolean("nc",       false));
		if (mCbCustomNc != null) mCbCustomNc.setChecked(p.getBoolean("customNc", false));
		if (mCbSoftClip != null) mCbSoftClip.setChecked(p.getBoolean("softClip", false));
		if (mCbRecordWav!= null) mCbRecordWav.setChecked(p.getBoolean("recordWav", false));
		// EIS не восстанавливаем автоматически — требует startEisOverlay()
		// ── Custom NC ─────────────────────────────────────────────────────────
		mNcThreshMult = p.getFloat("ncThr",  2.0f);
		mNcHystDb     = p.getFloat("ncHyst", -6.0f);
		mNcReleaseMs  = p.getInt  ("ncRel",  600);
		mNcResidual   = p.getFloat("ncRes",  0.0f);
		// Восстанавливаем позиции слайдеров и подписи
		if (mSbNcThr != null) {
			int prog = Math.round((mNcThreshMult - 1.0f) / 0.09f);
			mSbNcThr.setProgress(prog);
			mTvNcThr.setText(String.format("Thr:%.1fx", mNcThreshMult));
		}
		if (mSbNcHyst != null) {
			int prog = Math.round((mNcHystDb + 12f) / 0.1f);
			mSbNcHyst.setProgress(prog);
			mTvNcHyst.setText(String.format("Hyst:%.0fdB", mNcHystDb));
		}
		if (mSbNcRel != null) {
			int prog = Math.round((mNcReleaseMs - 50) / 29.5f);
			mSbNcRel.setProgress(prog);
			mTvNcRel.setText("Rel:" + mNcReleaseMs + "ms");
		}
		if (mSbNcRes != null) {
			int prog = Math.round(mNcResidual * 100f);
			mSbNcRes.setProgress(prog);
			mTvNcRes.setText("Res:" + prog + "%");
		}
		// ── Gain ─────────────────────────────────────────────────────────────
		if (mSeekGain != null) mSeekGain.setProgress(p.getInt("gain", 400));
		// ── Video ─────────────────────────────────────────────────────────────
		mVideoW   = p.getInt("videoW",   1920);
		mVideoH   = p.getInt("videoH",   1080);
		mVideoBps = p.getInt("videoBps", mVideoBps);
		// ── Pre-buffer ────────────────────────────────────────────────────────
		mPreBufferEnabled = p.getBoolean("preBuf",     true);
		mPreBufSecs    = p.getInt    ("preBufSecs", 1);
		// ── Audio source (отложенно — список может ещё не заполниться) ────────
		int audSrcIdx = p.getInt("audSrc", 0);
		if (mSpinner != null && audSrcIdx < mSpinner.getCount())
			mSpinner.setSelection(audSrcIdx);
		// ── Visibility ────────────────────────────────────────────────────────
		if (mCbOsc  != null) mCbOsc.setChecked(p.getBoolean("showOsc",  true));
		if (mCbSpec != null) mCbSpec.setChecked(p.getBoolean("showSpec", true));
		// ── EQ chain ──────────────────────────────────────────────────────────
		mEqEnabled = p.getBoolean("eqEnabled", false);
		if (mCbEqEnable != null) mCbEqEnable.setChecked(mEqEnabled);
		try {
			String eqJson = p.getString("eqChain", "[]");
			org.json.JSONArray arr = new org.json.JSONArray(eqJson);
			synchronized (mEqLock) { mEqBands.clear(); }
			if (mEqListView != null) mEqListView.removeAllViews();
			for (int i = 0; i < arr.length(); i++) {
				org.json.JSONObject obj = arr.getJSONObject(i);
				EqBand b = new EqBand();
				b.type    = obj.getInt("type");
				b.enabled = obj.getBoolean("enabled");
				b.freq    = (float) obj.getDouble("freq");
				b.q       = (float) obj.getDouble("q");
				b.gainDb  = (float) obj.getDouble("gainDb");
				b.slopeDb = (float) obj.optDouble("slopeDb", 6.0);
				synchronized (mEqLock) { b.computeCoeffs(AUDIO_SR); mEqBands.add(b); }
				addEqBandRow(b);
			}
		} catch (Exception ignored) {}
		// Восстанавливаем оверлеи после загрузки всех настроек
		updateNcOverlay();
		if (mEqOverlay != null) mEqOverlay.refresh();
	}

	private void showAirplaneModeReminder() {
		new android.app.AlertDialog.Builder(this)
			.setTitle("\u2708  Airplane Mode recommended")
			.setMessage(
				"For distraction-free recording:\n\n" +
				"  \u2022  Turn on Airplane Mode\n\n" +
				"This prevents calls, notifications\n" +
				"and Wi-Fi interruptions during recording.\n\n" +
				"(Screen will stay on while the app is open.)")
			.setPositiveButton("Got it", null)
			.setNegativeButton("\u2753 Help", (d, w) -> showHelp())
			.setNeutralButton("Open Settings", (d, w) -> {
				try {
					startActivity(new android.content.Intent(
						android.provider.Settings.ACTION_AIRPLANE_MODE_SETTINGS));
				} catch (Exception ignored) {}
			})
			.show();
	}

	// =========================================================================
	// Разрешения
	// =========================================================================
	
	private void checkPerms() {
		List<String> need = new ArrayList<>();
		if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED)
		need.add(Manifest.permission.CAMERA);
		if (checkSelfPermission(Manifest.permission.RECORD_AUDIO) != PackageManager.PERMISSION_GRANTED)
		need.add(Manifest.permission.RECORD_AUDIO);
		if (need.isEmpty()) {
			mPermsOk = true;
			if (mSurfaceReady)
			openCamera();
		} else
		requestPermissions(need.toArray(new String[0]), REQ_PERMS);
	}
	
	@Override
	public void onRequestPermissionsResult(int req, String[] perms, int[] res) {
		for (int r : res) {
			if (r != PackageManager.PERMISSION_GRANTED) {
				status("Permissions required");
				return;
			}
		}
		mPermsOk = true;
		if (mSurfaceReady)
		openCamera();
	}
	
	// =========================================================================
	// SurfaceHolder.Callback
	// =========================================================================
	
	@Override
	public void surfaceCreated(SurfaceHolder h) {
		mSurfaceReady = true;
		if (mPermsOk)
		openCamera();
	}
	
	@Override
	public void surfaceChanged(SurfaceHolder h, int f, int w, int t) {
	}
	
	@Override
	public void surfaceDestroyed(SurfaceHolder h) {
		mSurfaceReady = false;
	}
	
	// =========================================================================
	// Camera2
	// =========================================================================
	
	@SuppressLint("MissingPermission")
	private void openCamera() {
		if (mCamThread == null || !mCamThread.isAlive()) {
			mCamThread = new HandlerThread("cam");
			mCamThread.start();
			mCamHandler = new Handler(mCamThread.getLooper());
		}
		try {
			String camId = null;
			for (String id : mCamMgr.getCameraIdList()) {
				CameraCharacteristics ch = mCamMgr.getCameraCharacteristics(id);
				Integer facing = ch.get(CameraCharacteristics.LENS_FACING);
				if (facing != null && facing == CameraCharacteristics.LENS_FACING_BACK) {
					camId = id;
					Integer so = ch.get(CameraCharacteristics.SENSOR_ORIENTATION);
					if (so != null)
					mSensorOrientation = so;
					Rect rect = ch.get(CameraCharacteristics.SENSOR_INFO_ACTIVE_ARRAY_SIZE);
					if (rect != null) mSensorRect = rect;
					Rect preCorr = ch.get(CameraCharacteristics.SENSOR_INFO_PRE_CORRECTION_ACTIVE_ARRAY_SIZE);
					mPreCorrRect = (preCorr != null) ? preCorr : mSensorRect;
					Float maxZ = ch.get(CameraCharacteristics.SCALER_AVAILABLE_MAX_DIGITAL_ZOOM);
					if (maxZ != null)
					mMaxZoom = maxZ;
					Float minFocus = ch.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE);
					if (minFocus != null) mMinFocusDist = minFocus;
					android.util.Range<Integer> evR = ch.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE);
					if (evR != null) { mEvMin = evR.getLower(); mEvMax = evR.getUpper(); }
					// ── Проверяем поддержку аппаратного EIS ──────────────────────
					int[] eisModes = ch.get(
						CameraCharacteristics.CONTROL_AVAILABLE_VIDEO_STABILIZATION_MODES);
					mEisSupported = false;
					if (eisModes != null) {
						for (int m : eisModes) {
							if (m == CameraCharacteristics.CONTROL_VIDEO_STABILIZATION_MODE_ON) {
								mEisSupported = true;
								break;
							}
						}
					}
					break;
				}
			}
			if (camId == null)
			camId = mCamMgr.getCameraIdList()[0];
			
			mCamMgr.openCamera(camId, new CameraDevice.StateCallback() {
				@Override
				public void onOpened(CameraDevice dev) {
					mCamDev = dev;
					startPreview();
					buildAudioSources();
					mCamHandler.post(mZoomRunnable);
					runOnUiThread(() -> {
						if (mSeekEv!=null){mSeekEv.setMax(mEvMax-mEvMin);mSeekEv.setProgress(-mEvMin);updateEvLabel(0);}
						// Отображаем поддержку EIS в чекбоксе
						if (mCbEis != null) {
							mCbEis.setEnabled(mEisSupported);
							if (!mEisSupported) {
								mCbEis.setChecked(false);
								mEisEnabled = false;
								mCbEis.setText("HW EIS (не поддерживается)");
							} else {
								mCbEis.setText("ImageStab");
							}
						}
					});
				}
				
				@Override
				public void onDisconnected(CameraDevice dev) {
					dev.close();
					mCamDev = null;
				}
				
				@Override
				public void onError(CameraDevice dev, int e) {
					dev.close();
					mCamDev = null;
				}
			}, mCamHandler);
			} catch (Exception e) {
			status("openCamera: " + e.getMessage());
		}
	}
	
	private void startPreview() {
		if (mCamDev == null || !mSurfaceReady) return;
		ensureEncoders();
		try {
			if (mCapSess != null) { mCapSess.close(); mCapSess = null; }

			Surface preview = mSv.getHolder().getSurface();
			List<Surface> targets = new ArrayList<>();
			targets.add(preview);
			if (mEncSurface != null && mEncSurface.isValid())
				targets.add(mEncSurface);
			// PiP питается от decoder-а, не от capture session

			mCamDev.createCaptureSession(targets, new CameraCaptureSession.StateCallback() {
				@Override
				public void onConfigured(CameraCaptureSession sess) {
					mCapSess = sess;
					buildAndSendRequest();
				}
				@Override
				public void onConfigureFailed(CameraCaptureSession sess) {
					status("Session config failed");
				}
			}, mCamHandler);
		} catch (Exception e) {
			status("startPreview: " + e.getMessage());
		}
	}
	
	private void buildAndSendRequest() {
		CameraCaptureSession sess = mCapSess;
		CameraDevice dev = mCamDev;
		if (sess == null || dev == null || !mSurfaceReady)
		return;
		try {
			// Всегда TEMPLATE_PREVIEW — шаблон не переключается при старте записи,
			// поэтому AE не пересчитывается и яркость не прыгает.
			// Encoder surface просто добавляется как дополнительный target.
			int tmpl = CameraDevice.TEMPLATE_PREVIEW;
			Surface preview = mSv.getHolder().getSurface();
			CaptureRequest.Builder rb = dev.createCaptureRequest(tmpl);
			rb.addTarget(preview);
			if (mEncSurface != null && mEncSurface.isValid())
				rb.addTarget(mEncSurface);
			
			if (mManualFocus) {
				// Ручной фокус: переводим прогресс (0=∞, 1=macro) в диоптрии
				// Верх слайдера = прогресс 100 = macro (mMinFocusDist)
				// Низ слайдера  = прогресс 0   = бесконечность (0 диоптрий)
				float diopters = mFocusValue * mMinFocusDist;
				rb.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_OFF);
				rb.set(CaptureRequest.LENS_FOCUS_DISTANCE, diopters);
				} else {
				rb.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_VIDEO);
			}
			
			rb.set(CaptureRequest.CONTROL_AE_MODE, CaptureRequest.CONTROL_AE_MODE_ON);
			rb.set(CaptureRequest.CONTROL_AE_EXPOSURE_COMPENSATION, mEvComp);
			
			// ── Аппаратный EIS ────────────────────────────────────────────────────
			// Устанавливаем в каждом запросе — Camera2 применяет per-frame.
			// При включении EIS камера буферизует несколько кадров внутри (латентность
			// ~100-500 мс), что автоматически покрывается расширенным кольцевым буфером.
			rb.set(CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE,
				(mEisEnabled && mEisSupported)
					? CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE_ON
					: CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE_OFF);
			
			if (mSensorRect != null) {
				// При EIS=ON камера интерпретирует SCALER_CROP_REGION в пространстве
				// PRE_CORRECTION_ACTIVE_ARRAY_SIZE, а не ACTIVE_ARRAY_SIZE.
				// Используем правильный базовый прямоугольник:
				Rect base = (mEisEnabled && mEisSupported && mPreCorrRect != null)
						? mPreCorrRect : mSensorRect;
				int cropW = Math.max(1, (int) (base.width()  / mZoomLevel));
				int cropH = Math.max(1, (int) (base.height() / mZoomLevel));
				int cropX = base.left + (base.width()  - cropW) / 2;
				int cropY = base.top  + (base.height() - cropH) / 2;
				rb.set(CaptureRequest.SCALER_CROP_REGION, new Rect(cropX, cropY, cropX + cropW, cropY + cropH));
			}
			sess.setRepeatingRequest(rb.build(), null, mCamHandler);
			} catch (Exception ignored) {
		}
	}
	
	// =========================================================================
	// REC / STOP
	// =========================================================================
	
	private void onPauseClick() {
		mPaused = !mPaused;
		if (mPaused) {
			// Пауза: переводим в RING, кольца очищаем
			mPauseStartNano = System.nanoTime();
			mVidWriteMode = 0;
			mAudWriteMode = 0;
			mPcmWriteMode = 0; // WAV-кольцо тоже чистим
			synchronized(mVidRingLock) { mVidRing.clear(); }
			synchronized(mAudRingLock) { mAudRing.clear(); }
			synchronized(mPcmRingLock) { mPcmRing.clear(); }
			mBtnPause.setText("▶");
			mBtnPause.setBackground(makeOval(0xFF228833));
			status("⏸ Paused");
		} else {
			// Снятие с паузы: LIVE сразу, без пре-буфера
			// mMuxBasePts сдвигаем: следующий фрейм будет записан с текущим PTS минус BasePts
			// Корректируем BasePts так, чтобы не было прыжка PTS в файле.
			// Самый простой способ: выставить mVidWriteMode=2 и mAudWriteMode=2 напрямую.
			// PTS коррекция: запоминаем момент паузы и момент возобновления,
			// сдвигаем BasePts на длину паузы.
			mPauseEndNano = System.nanoTime();
			long pauseDurUs = (mPauseEndNano - mPauseStartNano) / 1000L;
			mMuxBasePts += pauseDurUs; // вычитаем паузу из всех будущих PTS
			mVidWriteMode = 2; // LIVE
			mAudWriteMode = 2;
			if (mRecordWav) mPcmWriteMode = 2; // WAV возобновляется тоже LIVE
			mBtnPause.setText("⏸");
			mBtnPause.setBackground(mBtnBgPause);
			status("● REC (resumed)");
		}
	}

	private void onRecordClick() {
		if (mRecording) {
			mRecording = false;
			mBtn.setEnabled(false);
			status("Stopping…");
			new Thread(this::doStop).start();
		} else {
			mBtn.setEnabled(false);
			status("Starting…");
			new Thread(this::doStart).start();
		}
	}
	
	// =========================================================================
	// Запуск записи
	// =========================================================================
	

	// =========================================================================
	// Энкодеры: создание / видео-петля
	// =========================================================================

	/** Идемпотентно создаёт видео+аудио энкодеры и запускает videoPreviewLoop. */
	private synchronized void ensureEncoders() {
		// Видео-энкодер
		if (mVidEnc == null || mEncSurface == null || !mEncSurface.isValid()) {
			try {
				if (mVidEnc != null) { try{mVidEnc.stop();mVidEnc.release();}catch(Exception e){} mVidEnc=null; }
				if (mEncSurface != null) { try{mEncSurface.release();}catch(Exception e){} mEncSurface=null; }
				MediaFormat vf = MediaFormat.createVideoFormat(MediaFormat.MIMETYPE_VIDEO_AVC, mVideoW, mVideoH);
				vf.setInteger(MediaFormat.KEY_BIT_RATE, mVideoBps);
				vf.setInteger(MediaFormat.KEY_FRAME_RATE, VIDEO_FPS);
				vf.setInteger(MediaFormat.KEY_I_FRAME_INTERVAL, 1);
				vf.setInteger(MediaFormat.KEY_COLOR_FORMAT, CodecCapabilities.COLOR_FormatSurface);
				vf.setInteger(MediaFormat.KEY_PROFILE, CodecProfileLevel.AVCProfileBaseline);
				vf.setInteger(MediaFormat.KEY_LEVEL, CodecProfileLevel.AVCLevel31);
				mVidEnc = MediaCodec.createEncoderByType(MediaFormat.MIMETYPE_VIDEO_AVC);
				mVidEnc.configure(vf, null, null, MediaCodec.CONFIGURE_FLAG_ENCODE);
				mEncSurface = mVidEnc.createInputSurface();
				mVidEnc.start();
				mVidOutFmt = null;
				synchronized(mVidRingLock) { mVidRing.clear(); }
				mVidWriteMode = 0;
			} catch (Exception e) { status("VidEnc err: " + e.getMessage()); return; }
		}
		// Видео-петля
		if (!mVidLoopRunning) {
			Thread t = new Thread(this::videoPreviewLoop, "vid-preview");
			t.setDaemon(true); t.start();
		}
	}

	/**
	 * Непрерывно дренирует видео-энкодер.
	 * Переключение RING→FLUSH→LIVE происходит ЗДЕСЬ, в этом же потоке —
	 * никаких гонок, никаких пропущенных фреймов между кольцом и файлом.
	 */
	private void videoPreviewLoop() {
		mVidLoopRunning = true;
		MediaCodec.BufferInfo info = new MediaCodec.BufferInfo();
		while (mVidLoopRunning) {
			MediaCodec enc = mVidEnc;
			if (enc == null) { try{Thread.sleep(20);}catch(Exception e){} continue; }
			int out;
			try { out = enc.dequeueOutputBuffer(info, 40_000); }
			catch (Exception e) { break; }

			if (out == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED) {
				MediaFormat fmt = enc.getOutputFormat();
				synchronized(mVidRingLock) { mVidOutFmt = fmt; }
				if (mEisEnabled && mEisSupported) ensurePipDecoder(fmt);
				continue;
			}
			if (out < 0) continue;

			try {
				boolean cfg = (info.flags & MediaCodec.BUFFER_FLAG_CODEC_CONFIG) != 0;
				if (cfg || info.size <= 0) continue;
				ByteBuffer data = enc.getOutputBuffer(out);
				int mode = mVidWriteMode;
				// PiP: ответвляем фрейм в декодер ДО releaseOutputBuffer
				feedToPipDecoder(data, info);

				if (mode == 0) {
					// ── RING: добавляем в кольцо, обрезаем по mPreBufSecs ──
					// При активном EIS добавляем EIS_LATENCY_US: стабилизатор буферизует
					// кадры внутри камеры, и реальная глубина пре-записи должна быть
					// шире на эту задержку, чтобы пре-буфер не потерял начало.
					EncodedFrame f = new EncodedFrame(data, info);
					synchronized(mVidRingLock) {
						mVidRing.addLast(f);
						long eisExtra = (mEisEnabled && mEisSupported) ? EIS_LATENCY_US : 0L;
						while (mVidRing.size() > 1) {
							long span = mVidRing.peekLast().pts - mVidRing.peekFirst().pts;
							if (span <= (long) mPreBufSecs * 1_200_000L + eisExtra) break;
							mVidRing.removeFirst();
						}
					}
				} else if (mode == 1) {
					// ── FLUSH: сбрасываем кольцо в мюксер, затем текущий кадр ──
					// Всё делаем здесь — атомарно, в одном потоке.
					synchronized(mVidRingLock) {
						// Пропускаем до первого I-frame
						boolean foundKey = false;
						for (EncodedFrame rf : mVidRing) {
							if (!foundKey && !rf.isKey()) continue;
							foundKey = true;
							ByteBuffer rb = ByteBuffer.wrap(rf.data);
							MediaCodec.BufferInfo bi = new MediaCodec.BufferInfo();
							bi.set(0, rf.data.length, rf.pts - mMuxBasePts, rf.flags);
							synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mVidTrack, rb, bi); }
						}
						mVidRing.clear();
					}
					// Текущий кадр — первый живой
					MediaCodec.BufferInfo n = new MediaCodec.BufferInfo();
					n.set(info.offset, info.size, info.presentationTimeUs - mMuxBasePts, info.flags);
					synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mVidTrack, data, n); }
					mVidWriteMode = 2; // LIVE
				} else {
					// ── LIVE: прямо в мюксер ──
					MediaCodec.BufferInfo n = new MediaCodec.BufferInfo();
					n.set(info.offset, info.size, info.presentationTimeUs - mMuxBasePts, info.flags);
					synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mVidTrack, data, n); }
				}
			} finally { enc.releaseOutputBuffer(out, false); }
		}
		mVidLoopRunning = false;
	}

	// =========================================================================
	// Аудио-пайплайн
	// =========================================================================

	@SuppressLint("MissingPermission")
	private void startMonitor() {
		if (mAudRunning || !mPermsOk) return;
		int pos = mSpinner.getSelectedItemPosition();
		AudioSrcItem src2 = (pos >= 0 && pos < mSrcList.size()) ? mSrcList.get(pos) : null;
		int audioSrc = src2 != null ? src2.audioSource : MediaRecorder.AudioSource.MIC;

		int chanCfg = AudioFormat.CHANNEL_IN_STEREO; int channels = 2;
		int minBuf = AudioRecord.getMinBufferSize(AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT);
		if (minBuf <= 0) { chanCfg = AudioFormat.CHANNEL_IN_MONO; channels = 1;
			minBuf = AudioRecord.getMinBufferSize(AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT); }
		int bufSize = Math.max(minBuf, AUDIO_SR * channels * 2 / 5);
		AudioRecord rec = new AudioRecord(audioSrc, AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT, bufSize);
		if (rec.getState() != AudioRecord.STATE_INITIALIZED && channels == 2) {
			rec.release(); chanCfg = AudioFormat.CHANNEL_IN_MONO; channels = 1;
			minBuf = AudioRecord.getMinBufferSize(AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT);
			bufSize = Math.max(minBuf, AUDIO_SR * 2 / 5);
			rec = new AudioRecord(audioSrc, AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT, bufSize);
		}
		if (rec.getState() != AudioRecord.STATE_INITIALIZED) { rec.release(); return; }
		if (Build.VERSION.SDK_INT >= 23 && src2 != null && src2.device != null)
			rec.setPreferredDevice(src2.device);
		// UNPROCESSED source аппаратно обходит весь DSP (AGC/NC/AEC) —
		// вызов configureAudioEffects излишен и может активировать эффекты
		// через параллельный путь. Применяем эффекты только для «обработанных» источников.
		if (audioSrc != MediaRecorder.AudioSource.UNPROCESSED) {
			configureAudioEffects(rec.getAudioSessionId());
		}
		mAudRec = rec; mAudChannels = channels;

		// Создаём аудио-энкодер
		try {
			MediaFormat af = MediaFormat.createAudioFormat(MediaFormat.MIMETYPE_AUDIO_AAC, AUDIO_SR, channels);
			af.setInteger(MediaFormat.KEY_BIT_RATE, channels == 1 ? 192_000 : 320_000);
			af.setInteger(MediaFormat.KEY_AAC_PROFILE, CodecProfileLevel.AACObjectLC);
			mAudEnc = MediaCodec.createEncoderByType(MediaFormat.MIMETYPE_AUDIO_AAC);
			mAudEnc.configure(af, null, null, MediaCodec.CONFIGURE_FLAG_ENCODE);
			mAudEnc.start();
			mAudOutFmt = null;
			synchronized(mAudRingLock) { mAudRing.clear(); }
			mAudWriteMode = 0;
		} catch (Exception e) { status("AudEnc err: " + e.getMessage()); mAudEnc = null; }

		mAudRunning = true;
		mAudThread = new Thread(this::audioMainLoop, "aud-main");
		mAudThread.setDaemon(true); mAudThread.start();
	}

	private void stopAudio() {
		mAudRunning = false;
		if (mAudRec != null) try { mAudRec.stop(); } catch (Exception ignored) {}
		if (mAudThread != null) { try { mAudThread.join(600); } catch (Exception ignored) {} mAudThread = null; }
		if (mAudRec != null) { try { mAudRec.release(); } catch (Exception ignored) {} mAudRec = null; }
		if (mAudEnc != null) { try { mAudEnc.stop(); mAudEnc.release(); } catch (Exception ignored) {} mAudEnc = null; }
		mAudOutFmt = null;
		synchronized(mAudRingLock) { mAudRing.clear(); }
	}

	/**
	 * Применяет текущие настройки AGC/NC/AEC к сессии по её ID.
	 * Вызывается из startMonitor() после создания AudioRecord,
	 * а также из UI при изменении чекбоксов/слайдера.
	 */
	private void configureAudioEffects(int sid) {
		// AGC
		try {
			if (AutomaticGainControl.isAvailable()) {
				AutomaticGainControl agc = AutomaticGainControl.create(sid);
				if (agc != null) { agc.setEnabled(mAgcEnabled); agc.release(); }
			}
		} catch (Exception ignored) {}

		// NC
		try {
			if (NoiseSuppressor.isAvailable()) {
				NoiseSuppressor ns = NoiseSuppressor.create(sid);
				if (ns != null) {
					ns.setEnabled(mNcEnabled);
					if (mNcEnabled) {
						// NoiseSuppressor.setParameter(int,int) наследуется от AudioEffect,
						// но помечен @hide в публичном SDK — вызываем через рефлексию.
						// На устройствах, где вендор не реализовал этот параметр, silently ignored.
						try {
							java.lang.reflect.Method m = ns.getClass()
								.getMethod("setParameter", int.class, int.class);
							m.invoke(ns, 0, mNcLevel);
						} catch (Exception ignored2) {}
					}
					ns.release();
				}
			}
		} catch (Exception ignored) {}

		// AEC — для съёмочной камеры всегда выкл
		try {
			if (AcousticEchoCanceler.isAvailable()) {
				AcousticEchoCanceler aec = AcousticEchoCanceler.create(sid);
				if (aec != null) { aec.setEnabled(false); aec.release(); }
			}
		} catch (Exception ignored) {}
	}

	/**
	 * Обновляет метку слайдера агрессивности в зависимости от того,
	 * какой NC активен: системный, кастомный или оба.
	 */
	private void updateNcLevelLabel() {
		// Метки обновляются каждым слайдером индивидуально; здесь ничего не нужно.
	}

	/**
	 * Кастомное DSP-шумоподавление: адаптивный шумовой гейт с оценкой
	 * шумового пола методом скользящего RMS-минимума.
	 *
	 * Алгоритм:
	 *   1. Считаем RMS текущего 20-мс фрейма.
	 *   2. Обновляем оценку шумового пола (быстро снижаем, медленно растём).
	 *   3. Вычисляем SNR = frameRms / noiseFloor.
	 *   4. При SNR < threshold — плавно подавляем сигнал (soft knee gate).
	 *
	 * @param buf    PCM-буфер (16-bit signed, interleaved channels)
	 * @param r      число сэмплов (не байт)
	 */
	private void applyCustomNc(short[] buf, int r) {
		//
		// Noise gate с гистерезисом и экспоненциальными атакой/риливом.
		//
		// Параметры, выводимые из слайдера aggression 0..100:
		//   0  → почти прозрачно: очень мягкий порог, очень долгий рилив
		//   100 → агрессивно: высокий порог, быстрый рилив
		//
		// Гистерезис: open_thresh > close_thresh — предотвращает дребезг
		// на экспоненциальных хвостах струнных нот.
		//
		// ── Lookahead: задерживаем сигнал на NC_LOOKAHEAD_MS мс ─────────────────
		// Копируем текущий сырой буфер в очередь задержки
		short[] rawCopy = java.util.Arrays.copyOf(buf, r);
		mNcDelayQ.add(rawCopy);
		mNcDelayedSamples += r;

		// ── Параметры гейта ───────────────────────────────────────────────────
		final float openMult  = mNcThreshMult;
		// Гистерезис в дБ: closeThresh = openThresh × 10^(dB/20)
		final float hystLinear = (float) Math.pow(10.0, mNcHystDb / 20.0); // <1
		final float closeMult = openMult * hystLinear;
		// Атака: сигмоида smoothstep 3t²-2t³ за ATK_SAMPLES сэмплов.
		// Нулевая производная на обоих концах → нет излома → нет щелчка.
		// Длина ~4ms при 48 кГц; lookahead 30ms покрывает с запасом.
		final int   ATK_SAMPLES = (int)(AUDIO_SR * 0.004f); // 4 мс
		final float ATK_STEP    = 1f / ATK_SAMPLES;
		// Release: per-sample коэффициент (аналогично атаке)
		// tau = releaseMs/1000 с, dt = 1/AUDIO_SR с → alpha = exp(-dt/tau)
		final float REL_PER_SAMPLE = (float) Math.exp(-1000.0 / ((double) AUDIO_SR * mNcReleaseMs));

		// ── Сглаживание RMS (tau ≈ 5 мс) ────────────────────────────────────────
		long sumSq = 0;
		for (int i = 0; i < r; i++) sumSq += (long) buf[i] * buf[i];
		float frameRms = (float) Math.sqrt((double) sumSq / r);

		// alphaRms ≈ 1 - exp(-20/5) → быстрое сглаживание
		final float alphaRms = 0.98f;
		mNcRmsEst = mNcRmsEst * (1f - alphaRms) + frameRms * alphaRms;

		// ── Оценка шумового пола — медленный tracker минимума ────────────────────
		if (mNcFloorEst < 1f) {
			mNcFloorEst = frameRms;             // первая инициализация
		} else if (frameRms < mNcFloorEst) {
			mNcFloorEst = mNcFloorEst * 0.90f + frameRms * 0.10f; // быстро вниз
		} else {
			mNcFloorEst = mNcFloorEst * 0.998f + frameRms * 0.002f; // медленно вверх
		}
		if (mNcFloorEst < 1f) mNcFloorEst = 1f;

		// ── Гистерезис: переключение состояния гейта ─────────────────────────────
		float openThresh  = mNcFloorEst * openMult;
		float closeThresh = mNcFloorEst * closeMult;

		if (!mNcGateOpen && mNcRmsEst >= openThresh) {
			mNcGateOpen = true;
			mNcAttackPhase = 0f; // запускаем сигмоиду с нуля
		} else if (mNcGateOpen && mNcRmsEst < closeThresh) {
			mNcGateOpen = false;
		}

		// ── Применяем gain к буферу с плавной атакой/риливом ─────────────────────
		// ── Применяем gain к ЗАДЕРЖАННОМУ сигналу (lookahead) ───────────────────
		// Достаточно ли накоплено?
		int lookaheadSamples = NC_LOOKAHEAD_MS * AUDIO_SR / 1000;
		short[] outBuf;
		if (mNcDelayedSamples >= lookaheadSamples + r) {
			// Извлекаем самый старый фрейм
			outBuf = mNcDelayQ.poll();
			mNcDelayedSamples -= (outBuf != null ? outBuf.length : r);
		} else {
			// Буфер ещё не заполнен — тишина
			java.util.Arrays.fill(buf, 0, r, (short) 0);
			return;
		}
		if (outBuf == null) outBuf = new short[r];

		// Применяем gain с логарифмически-плавной атакой (per-sample)
		final float residual = mNcResidual;
		int outLen = Math.min(r, outBuf.length);
		for (int i = 0; i < outLen; i++) {
			if (mNcGateOpen) {
				// Атака: smoothstep(t) = 3t²-2t³  (сигмоида Ken Perlin)
				// Производная = 0 при t=0 и t=1 → абсолютно гладкий старт и конец
				if (mNcAttackPhase < 1f) {
					mNcAttackPhase = Math.min(1f, mNcAttackPhase + ATK_STEP);
					float t = mNcAttackPhase;
					mNcGateGain = residual + (1f - residual) * t * t * (3f - 2f * t);
				} else {
					mNcGateGain = 1f;
				}
			} else {
				// Рилив: экспоненциальное затухание к residual (per-sample, tau=releaseMs)
				mNcGateGain = residual + (mNcGateGain - residual) * REL_PER_SAMPLE;
				if (mNcGateGain < residual) mNcGateGain = residual;
			}
			float s = outBuf[i] * mNcGateGain;
			buf[i] = (short)(s > 32767f ? 32767f : (s < -32768f ? -32768f : s));
		}
	}
	/** Применяет текущие настройки к активной AudioRecord сессии (вызов из UI). */
	private void applyAudioEffects() {
		AudioRecord rec = mAudRec;
		if (rec == null) return;
		configureAudioEffects(rec.getAudioSessionId());
	}

	/**
	 * Аудио-петля: читает PCM, кодирует AAC, дренирует в кольцо или мюксер.
	 * Переключение RING→FLUSH→LIVE — в этом же потоке, атомарно.
	 */
	private void audioMainLoop() {
		final AudioRecord rec = mAudRec;
		final int ch = mAudChannels;
		final int chunkSamples = AUDIO_SR * ch / 50; // 20 мс
		short[] buf = new short[chunkSamples];
		// Абсолютный старт в мкс — тот же CLOCK_MONOTONIC, что у видео-сенсора
		// startUs синхронизируется с mRecStartUs при первом write (см. ниже)
		long startUs = System.nanoTime() / 1000L;
		long totalFrames = 0L;
		boolean startUsSynced = false;

		rec.startRecording();
		while (mAudRunning) {
			int r = rec.read(buf, 0, chunkSamples);
			if (r <= 0) continue;

			// ── gain / soft-clip ──────────────────────────────────────────────
			final float g = mGain; final boolean sc = mSoftClip;
			long sumSq = 0;
			for (int i = 0; i < r; i++) {
				float s = buf[i] * g;
				if (sc) {
					final float T = 32768f * 0.7f, knee = 32768f - T;
					float ab = Math.abs(s);
					if (ab > T) s = Math.signum(s) * (T + knee * (float)Math.tanh((ab-T)/knee));
				}
				if (s > 32767f) s = 32767f; else if (s < -32768f) s = -32768f;
				buf[i] = (short) s; sumSq += (long) buf[i] * buf[i];
			}

			// ── Custom NC: DSP-шумоподавление по оценке шумового пола ────────
			// ── WAV sidecar: пишем сырой PCM (до EQ и NC) ───────────────────
			if (mRecordWav) {
				handlePcmForWav(buf, r, startUs + totalFrames * 1_000_000L / AUDIO_SR);
			}

			// ── EQ: бiquad-цепочка (после WAV, до NC) ────────────────────────
			if (mEqEnabled) applyEq(buf, r, ch);

			// ── Custom NC (модифицирует buf in-place) ────────────────────────
			if (mCustomNcEnabled) applyCustomNc(buf, r);

			float peakAmp = 0f;
			for (int i = 0; i < r; i++) { float a = Math.abs(buf[i]) / 32768f; if (a > peakAmp) peakAmp = a; }
			mVu.setPeak(peakAmp);
			long sumSqPost = 0;
			for (int _i = 0; _i < r; _i++) sumSqPost += (long) buf[_i] * buf[_i];
			mVu.setLevel((float) Math.sqrt((double) sumSqPost / r) / 32768f);
			if (mOscilloscope != null) mOscilloscope.pushSamples(buf, r, ch);
			if (mEnvelope     != null) mEnvelope.pushSamples(buf, r, ch);
			if (mSpectrum     != null) mSpectrum.pushSamples(buf, r, ch);

			// ── кодируем PCM→AAC ──────────────────────────────────────────────
			MediaCodec enc = mAudEnc;
			if (enc == null) continue;
			// PTS: абсолютный System.nanoTime (мкс) — тот же домен, что у видео
			// Синхронизируем временну́ю базу аудио с видео при первом write
			if (!startUsSynced && mRecStartUs != 0L && mAudWriteMode != 0) {
				// Пересчитываем startUs так, чтобы PTS текущего фрейма
				// совпал с видео-базой. totalFrames уже накоплены — компенсируем.
				startUs = mRecStartUs - totalFrames * 1_000_000L / AUDIO_SR;
				startUsSynced = true;
			}
			long pts = startUs + totalFrames * 1_000_000L / AUDIO_SR
					- (mCustomNcEnabled ? (long) NC_LOOKAHEAD_MS * 1000L : 0L);
			totalFrames += r / ch;
			int idx = enc.dequeueInputBuffer(5_000);
			if (idx >= 0) {
				ByteBuffer bb = enc.getInputBuffer(idx);
				bb.clear();
				for (int i = 0; i < r; i++) { bb.put((byte)(buf[i]&0xFF)); bb.put((byte)(buf[i]>>8&0xFF)); }
				enc.queueInputBuffer(idx, 0, r * 2, pts, 0);
			}
			drainAudioEncoder(enc);
		}
		mVu.setLevel(0f);
		try { rec.stop(); } catch (Exception ignored) {}
	}

	/**
	 * Дренирует аудио-энкодер. Переключение RING→FLUSH→LIVE — здесь, атомарно.
	 */
	private void drainAudioEncoder(MediaCodec enc) {
		MediaCodec.BufferInfo info = new MediaCodec.BufferInfo();
		while (true) {
			int out = enc.dequeueOutputBuffer(info, 0);
			if (out == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED) {
				synchronized(mAudRingLock) { mAudOutFmt = enc.getOutputFormat(); }
				continue;
			}
			if (out < 0) break;
			try {
				boolean cfg = (info.flags & MediaCodec.BUFFER_FLAG_CODEC_CONFIG) != 0;
				if (cfg || info.size <= 0) continue;
				ByteBuffer data = enc.getOutputBuffer(out);
				int mode = mAudWriteMode;

				if (mode == 0) {
					// RING
					EncodedFrame f = new EncodedFrame(data, info);
					synchronized(mAudRingLock) {
						mAudRing.addLast(f);
						while (mAudRing.size() > 1) {
							long span = mAudRing.peekLast().pts - mAudRing.peekFirst().pts;
							if (span <= (long) mPreBufSecs * 1_200_000L) break;
							mAudRing.removeFirst();
						}
					}
				} else if (mode == 1) {
					// FLUSH: сбрасываем кольцо начиная с первого аудио-фрейма >= mMuxBasePts
					synchronized(mAudRingLock) {
						boolean started = false;
						for (EncodedFrame rf : mAudRing) {
							if (!started && rf.pts < mMuxBasePts) continue;
							started = true;
							ByteBuffer rb = ByteBuffer.wrap(rf.data);
							MediaCodec.BufferInfo bi = new MediaCodec.BufferInfo();
							bi.set(0, rf.data.length, rf.pts - mMuxBasePts, rf.flags);
							synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mAudTrack, rb, bi); }
						}
						mAudRing.clear();
					}
					// Текущий аудио-пакет
					MediaCodec.BufferInfo n = new MediaCodec.BufferInfo();
					n.set(info.offset, info.size, info.presentationTimeUs - mMuxBasePts, info.flags);
					synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mAudTrack, data, n); }
					mAudWriteMode = 2; // LIVE
				} else {
					// LIVE
					MediaCodec.BufferInfo n = new MediaCodec.BufferInfo();
					n.set(info.offset, info.size, info.presentationTimeUs - mMuxBasePts, info.flags);
					synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mAudTrack, data, n); }
				}
			} finally { enc.releaseOutputBuffer(out, false); }
			if ((info.flags & MediaCodec.BUFFER_FLAG_END_OF_STREAM) != 0) break;
		}
	}

	// =========================================================================
	// REC: doStart / doStop / finalizeMuxer
	// =========================================================================

	/**
	 * doStart():
	 *  1. Вычисляем mMuxBasePts = PTS первого I-frame в видео-кольце.
	 *     Аудио-кольцо совпадает по clock → синхронизировано автоматически.
	 *  2. Создаём мюксер и добавляем треки.
	 *  3. Устанавливаем mVidWriteMode=FLUSH, mAudWriteMode=FLUSH.
	 *  4. Каждый поток сам (атомарно!) сбрасывает кольцо и продолжает LIVE.
	 *  Нет снимков, нет гонок, нет разрывов.
	 */
	@SuppressLint("MissingPermission")
	private void doStart() {
		try {
			// Ждём форматов от энкодеров (максимум 2 с)
			for (int wait = 0; wait < 40 && (mVidOutFmt == null || mAudOutFmt == null); wait++) {
				Thread.sleep(50);
			}
			if (mVidOutFmt == null || mAudOutFmt == null) {
				runOnUiThread(() -> { mBtn.setEnabled(true); status("Encoder not ready — retry"); });
				return;
			}

			// ── Единая база времени — фиксируем ДО старта потоков ──────────────
			// mRecStartUs — общий нулевой момент для аудио и видео.
			// При пре-буфере: берём PTS первого I-frame в кольце (он на этом же clock).
			// Без пре-буфера: System.nanoTime()/1000 прямо сейчас.
			// В обоих случаях mMuxBasePts = mRecStartUs, и аудио использует его же.
			long basePts;
			synchronized(mVidRingLock) {
				if (mPreBufferEnabled) {
					basePts = Long.MAX_VALUE;
					for (EncodedFrame f : mVidRing) {
						if (f.isKey()) { basePts = f.pts; break; }
					}
					if (basePts == Long.MAX_VALUE) basePts = System.nanoTime() / 1000L;
				} else {
					basePts = System.nanoTime() / 1000L;
				}
			}
			mRecStartUs = basePts;
			mMuxBasePts = basePts;

			// ── Создаём MediaStore-запись ──────────────────────────────────────
			String displayPath;
			// Общий таймстамп для mp4 и wav — файлы получат одинаковое имя с разным расширением
			String recTag = "VID_" + System.currentTimeMillis();
			if (Build.VERSION.SDK_INT >= 29) {
				ContentValues cv = new ContentValues();
				cv.put(MediaStore.Video.Media.DISPLAY_NAME, recTag + ".mp4");
				cv.put(MediaStore.Video.Media.MIME_TYPE, "video/mp4");
				cv.put(MediaStore.Video.Media.RELATIVE_PATH, "DCIM/CaMic");
				cv.put(MediaStore.Video.Media.IS_PENDING, 1);
				mPendingUri = getContentResolver().insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, cv);
				mPfd = getContentResolver().openFileDescriptor(mPendingUri, "rw");
				mMuxer = new MediaMuxer(mPfd.getFileDescriptor(), MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4);
				displayPath = "DCIM/CaMic";
			} else {
				@SuppressWarnings("deprecation")
				File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DCIM), "CaMic");
				dir.mkdirs();
				File f = new File(dir, recTag + ".mp4");
				mMuxer = new MediaMuxer(f.getAbsolutePath(), MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4);
				displayPath = f.getAbsolutePath();
			}
			@SuppressWarnings("deprecation")
			int rot = getWindowManager().getDefaultDisplay().getRotation() * 90;
			mMuxer.setOrientationHint((mSensorOrientation - rot + 360) % 360);

			// ── Добавляем треки, стартуем мюксер ──────────────────────────────
			synchronized(mMuxLock) {
				mVidTrack = mMuxer.addTrack(mVidOutFmt);
				mAudTrack = mMuxer.addTrack(mAudOutFmt);
				mMuxer.start();
				mMuxReady = true;
			}

			// ── WAV sidecar: создаём файл ДО переключения режимов ─────────────
			// Файл должен быть открыт раньше, чем mPcmWriteMode переключится в FLUSH,
			// иначе аудио-поток может вызвать writePcmToWav с null-каналом.
			if (mRecordWav) {
				try {
					startWavFile(recTag + ".wav", "Music/CaMic");
				} catch (Exception wavEx) {
					// WAV ошибка не должна прерывать видеозапись — только предупреждаем
					status("WAV: " + wavEx.getMessage());
				}
			}

			// ── Переводим потоки в режим FLUSH → они сами сбросят кольца ──────
			mRecording = true;
			if (mPreBufferEnabled) {
				mVidWriteMode = 1; // FLUSH
				mAudWriteMode = 1; // FLUSH
				if (mRecordWav) mPcmWriteMode = 1; // FLUSH PCM-кольцо в WAV
			} else {
				mVidWriteMode = 2; // LIVE сразу
				mAudWriteMode = 2;
				if (mRecordWav) mPcmWriteMode = 2; // LIVE сразу
			}

			final String fp = displayPath;
			runOnUiThread(() -> {
				mBtn.setText("⏹ STOP"); mBtn.setBackground(mBtnBgRec); mBtn.setEnabled(true);
				mBtnPause.setVisibility(View.VISIBLE);
				mBtnPause.setText("⏸"); mBtnPause.setBackground(mBtnBgPause);
				mPaused = false;
				// Блокируем EIS — нельзя менять стабилизатор во время записи
				if (mCbEis != null) mCbEis.setEnabled(false);
				status("● REC  →  " + fp);
			});
		} catch (Exception e) {
			mRecording = false; mVidWriteMode = 0; mAudWriteMode = 0; mPcmWriteMode = 0;
			finalizeMuxer();
			finalizeWavFile();
			runOnUiThread(() -> {
				mBtn.setText("⏺ REC"); mBtn.setBackground(mBtnBgIdle); mBtn.setEnabled(true);
				mBtnPause.setVisibility(View.GONE);
				if (mCbEis != null) mCbEis.setEnabled(mEisSupported);
				status("Error: " + e.getMessage());
			});
		}
	}

	private void doStop() {
		// Даём энкодерам 200 мс выдать буферизованные пакеты
		try { Thread.sleep(200); } catch (Exception ignored) {}
		mVidWriteMode = 0; mAudWriteMode = 0; mPcmWriteMode = 0; // обратно в RING
		finalizeMuxer();
		finalizeWavFile(); // закрывает WAV (если был открыт)
	}

	private void finalizeMuxer() {
		synchronized(mMuxLock) {
			try { if (mMuxer != null) { if (mMuxReady) mMuxer.stop(); mMuxer.release(); } }
			catch (Exception ignored) {}
			mMuxer = null; mMuxReady = false; mVidTrack = -1; mAudTrack = -1;
		}
		try { if (mPfd != null) { mPfd.close(); mPfd = null; } } catch (Exception ignored) {}
		if (Build.VERSION.SDK_INT >= 29 && mPendingUri != null) {
			ContentValues cv = new ContentValues();
			cv.put(MediaStore.Video.Media.IS_PENDING, 0);
			getContentResolver().update(mPendingUri, cv, null, null);
			mPendingUri = null;
		}
		runOnUiThread(() -> {
			mBtn.setText("⏺ REC"); mBtn.setBackground(mBtnBgIdle); mBtn.setEnabled(true);
			mBtnPause.setVisibility(View.GONE);
			mPaused = false;
			// Разблокируем EIS после окончания записи
			if (mCbEis != null) mCbEis.setEnabled(mEisSupported);
			status("Saved");
		});
	}


	private void status(String s) {
		runOnUiThread(() -> mTvStatus.setText(s));
	}
	
	// =========================================================================
	// Аудио-источники
	// =========================================================================
	
	/**
	 * Пробует создать AudioRecord с заданным audioSource.
	 * Возвращает true, если источник инициализировался успешно.
	 * Метод вызывается из фонового потока.
	 */
	@SuppressLint("MissingPermission")
	private boolean probeAudioSource(int src) {
		try {
			int minBuf = AudioRecord.getMinBufferSize(
				AUDIO_SR, AudioFormat.CHANNEL_IN_MONO, AudioFormat.ENCODING_PCM_16BIT);
			if (minBuf <= 0) return false;
			AudioRecord ar = new AudioRecord(
				src, AUDIO_SR, AudioFormat.CHANNEL_IN_MONO,
				AudioFormat.ENCODING_PCM_16BIT, minBuf);
			boolean ok = ar.getState() == AudioRecord.STATE_INITIALIZED;
			ar.release();
			return ok;
		} catch (Exception e) {
			return false;
		}
	}

	/**
	 * Зондирует AudioSource с явным device routing.
	 * Нужен для внешних микрофонов: обычный probeAudioSource без setPreferredDevice
	 * маршрутизирует на встроенный микрофон и возвращает true даже если внешний
	 * с этим источником несовместим.
	 */
	@SuppressLint("MissingPermission")
	private boolean probeAudioSourceWithDevice(int src, AudioDeviceInfo device) {
		if (Build.VERSION.SDK_INT < 23) return probeAudioSource(src);
		try {
			int minBuf = AudioRecord.getMinBufferSize(
				AUDIO_SR, AudioFormat.CHANNEL_IN_MONO, AudioFormat.ENCODING_PCM_16BIT);
			if (minBuf <= 0) return false;
			AudioRecord ar = new AudioRecord(
				src, AUDIO_SR, AudioFormat.CHANNEL_IN_MONO,
				AudioFormat.ENCODING_PCM_16BIT, minBuf);
			if (ar.getState() != AudioRecord.STATE_INITIALIZED) { ar.release(); return false; }
			if (device != null) ar.setPreferredDevice(device);
			// STATE не меняется от setPreferredDevice — но AudioRecord создался успешно,
			// значит source поддерживается системой; реальный routing будет при start().
			ar.release();
			return true;
		} catch (Exception e) {
			return false;
		}
	}

	private void buildAudioSources() {
		// Зондирование запускаем в фоновом потоке — каждое AudioRecord.create занимает время
		new Thread(() -> {
			List<AudioSrcItem> list = new ArrayList<>();

			if (Build.VERSION.SDK_INT >= 23) {
				AudioManager am = (AudioManager) getSystemService(AUDIO_SERVICE);
				AudioDeviceInfo[] devs = am.getDevices(AudioManager.GET_DEVICES_INPUTS);
				boolean hasBuiltin = false;

				for (AudioDeviceInfo d : devs) {
					int t = d.getType();
					if (t == AudioDeviceInfo.TYPE_BUILTIN_MIC) {
						if (hasBuiltin) continue;
						hasBuiltin = true;

						// Форсированно пробуем все стандартные источники на встроенном микрофоне.
						// В спиннере показываем только те, которые реально инициализировались.
						int[][] candidates = {
							{MediaRecorder.AudioSource.MIC,                   0},
							{MediaRecorder.AudioSource.CAMCORDER,             0},
							{MediaRecorder.AudioSource.VOICE_RECOGNITION,     0},
							{MediaRecorder.AudioSource.VOICE_COMMUNICATION,   0},
						};
						String[] candidateNames = {
							"Built-in mic",
							"Camcorder",
							"Voice recognition",
							"Voice comm.",
						};
						for (int i = 0; i < candidates.length; i++) {
							if (probeAudioSource(candidates[i][0]))
								list.add(new AudioSrcItem(candidateNames[i], candidates[i][0], d));
						}
						// UNPROCESSED для встроенного mic — device=d (built-in mic device).
						// Для каждого внешнего устройства ниже создаётся свой UNPROCESSED item.
						if (Build.VERSION.SDK_INT >= 24 &&
								probeAudioSource(MediaRecorder.AudioSource.UNPROCESSED))
							list.add(new AudioSrcItem("Built-in (raw)",
								MediaRecorder.AudioSource.UNPROCESSED, d));

					} else if (t == AudioDeviceInfo.TYPE_USB_DEVICE ||
								t == AudioDeviceInfo.TYPE_USB_HEADSET) {
						CharSequence pn = d.getProductName();
						String usbLabel = "USB: " + (pn != null && pn.length() > 0 ? pn : "audio");
						// MIC source с маршрутизацией на USB-устройство
						list.add(new AudioSrcItem(usbLabel,
							MediaRecorder.AudioSource.MIC, d));
						// UNPROCESSED + device=d: обходит весь DSP аппаратно.
						// setPreferredDevice в startMonitor() направит поток
						// именно на это USB-устройство, а не на built-in mic.
						if (Build.VERSION.SDK_INT >= 24 &&
								probeAudioSourceWithDevice(MediaRecorder.AudioSource.UNPROCESSED, d))
							list.add(new AudioSrcItem(usbLabel + " (raw)",
								MediaRecorder.AudioSource.UNPROCESSED, d));
					} else if (t == AudioDeviceInfo.TYPE_WIRED_HEADSET) {
						// Проводной микрофон (TRRS/TRS)
						list.add(new AudioSrcItem("Wired mic",
							MediaRecorder.AudioSource.MIC, d));
						// UNPROCESSED + device routing на внешний микрофон:
						// единственный способ получить сырой звук без AGC/NC/AEC.
						// device=d гарантирует, что setPreferredDevice направит поток
						// на wired mic, а audioSource=UNPROCESSED убирает DSP.
						if (Build.VERSION.SDK_INT >= 24 &&
								probeAudioSourceWithDevice(MediaRecorder.AudioSource.UNPROCESSED, d))
							list.add(new AudioSrcItem("Wired mic (raw)",
								MediaRecorder.AudioSource.UNPROCESSED, d));
					} else if (t == AudioDeviceInfo.TYPE_BLUETOOTH_SCO) {
						list.add(new AudioSrcItem("Bluetooth mic",
							MediaRecorder.AudioSource.MIC, d));
						// BT SCO не поддерживает UNPROCESSED — ограничение SCO-кодека
					}
				}
			}

			// Фолбэк: если ни одного источника не обнаружено — пробуем все подряд без device
			if (list.isEmpty()) {
				int[] fallbackSrc  = {
					MediaRecorder.AudioSource.MIC,
					MediaRecorder.AudioSource.CAMCORDER,
					MediaRecorder.AudioSource.VOICE_RECOGNITION,
					MediaRecorder.AudioSource.VOICE_COMMUNICATION,
				};
				String[] fallbackNames = {
					"Microphone", "Camcorder", "Voice recognition", "Voice comm."
				};
				for (int i = 0; i < fallbackSrc.length; i++) {
					if (probeAudioSource(fallbackSrc[i]))
						list.add(new AudioSrcItem(fallbackNames[i], fallbackSrc[i], null));
				}
				if (Build.VERSION.SDK_INT >= 24 &&
						probeAudioSource(MediaRecorder.AudioSource.UNPROCESSED))
					list.add(new AudioSrcItem("Unprocessed (raw)",
						MediaRecorder.AudioSource.UNPROCESSED, null));
				// Абсолютный фолбэк — хоть что-то
				if (list.isEmpty())
					list.add(new AudioSrcItem("Default",
						MediaRecorder.AudioSource.DEFAULT, null));
			}

			final List<AudioSrcItem> finalList = list;
			runOnUiThread(() -> {
				mSrcList.clear();
				mSrcList.addAll(finalList);
				List<String> names = new ArrayList<>();
				for (AudioSrcItem item : mSrcList) names.add(item.name);
				@SuppressWarnings("unchecked")
				ArrayAdapter<String> ad2 = (ArrayAdapter<String>) mSpinner.getAdapter();
				ad2.clear();
				ad2.addAll(names);
				ad2.notifyDataSetChanged();

				// Выбор источника по умолчанию:
				// Приоритет: внешний (raw) → внешний MIC → встроенный (raw) → первый
				int defaultIdx = 0;
				// 1. Ищем внешний UNPROCESSED (USB или wired с device routing)
				if (Build.VERSION.SDK_INT >= 23) {
					for (int i = 0; i < mSrcList.size(); i++) {
						AudioSrcItem item = mSrcList.get(i);
						if (item.audioSource == MediaRecorder.AudioSource.UNPROCESSED
								&& item.device != null) {
							int t = item.device.getType();
							if (t == AudioDeviceInfo.TYPE_USB_DEVICE
									|| t == AudioDeviceInfo.TYPE_USB_HEADSET
									|| t == AudioDeviceInfo.TYPE_WIRED_HEADSET) {
								defaultIdx = i;
								break;
							}
						}
					}
				}
				// 2. Нет внешнего (raw) — ищем любой внешний MIC
				if (defaultIdx == 0 && Build.VERSION.SDK_INT >= 23) {
					for (int i = 0; i < mSrcList.size(); i++) {
						AudioSrcItem item = mSrcList.get(i);
						if (item.device != null) {
							int t = item.device.getType();
							if (t == AudioDeviceInfo.TYPE_USB_DEVICE
									|| t == AudioDeviceInfo.TYPE_USB_HEADSET
									|| t == AudioDeviceInfo.TYPE_WIRED_HEADSET) {
								defaultIdx = i;
								break;
							}
						}
					}
				}
				// 3. Нет внешних — ищем встроенный UNPROCESSED
				if (defaultIdx == 0) {
					for (int i = 0; i < mSrcList.size(); i++) {
						if (mSrcList.get(i).audioSource == MediaRecorder.AudioSource.UNPROCESSED) {
							defaultIdx = i;
							break;
						}
					}
				}
				mSpinner.setSelection(defaultIdx);
				if (!mRecording) {
					stopAudio();
					startMonitor();
				}
			});
		}, "audio-probe").start();
	}
	
	// =========================================================================
	// Вспомогательные классы
	// =========================================================================

	// ─── WAV sidecar: контейнер PCM-чанка с временной меткой ────────────────
	private static class PcmChunk {
		final short[] data;
		final int len;
		final long pts; // мкс, тот же CLOCK_MONOTONIC что у видео/AAC

		PcmChunk(short[] src, int l, long p) {
			data = java.util.Arrays.copyOfRange(src, 0, l);
			len  = l;
			pts  = p;
		}
	}

	// ─── WAV sidecar: аудио-поток → кольцо / сброс / файл ───────────────────

	/**
	 * Вызывается из audioMainLoop ПОСЛЕ обработки gain/softclip.
	 * Зеркалит логику drainAudioEncoder: RING→FLUSH→LIVE.
	 * Переключение RING→FLUSH→LIVE происходит здесь — в аудио-потоке,
	 * атомарно, без пропущенных сэмплов.
	 */
	private void handlePcmForWav(short[] buf, int len, long pts) {
		int mode = mPcmWriteMode;
		if (mode == 0) {
			// ── RING: накапливаем, обрезаем по mPreBufSecs + запас ──────────
			PcmChunk chunk = new PcmChunk(buf, len, pts);
			synchronized (mPcmRingLock) {
				mPcmRing.addLast(chunk);
				long keepUs = (long)(mPreBufSecs + 1) * 1_200_000L;
				while (mPcmRing.size() > 1 &&
						mPcmRing.peekLast().pts - mPcmRing.peekFirst().pts > keepUs) {
					mPcmRing.removeFirst();
				}
			}
		} else if (mode == 1) {
			// ── FLUSH: сбрасываем кольцо начиная с mMuxBasePts, затем текущий чанк ──
			// mMuxBasePts — PTS первого I-frame видео; аудио и PCM синхронизированы
			// через общий CLOCK_MONOTONIC → буфер начнётся точно с нужного момента.
			synchronized (mPcmRingLock) {
				for (PcmChunk c : mPcmRing) {
					if (c.pts < mMuxBasePts) continue; // пропускаем до точки старта
					writePcmToWav(c.data, c.len);
				}
				mPcmRing.clear();
			}
			writePcmToWav(buf, len); // первый «живой» чанк
			mPcmWriteMode = 2; // LIVE
		} else { // mode == 2
			// ── LIVE: напрямую в файл ───────────────────────────────────────
			writePcmToWav(buf, len);
		}
	}

	/** Пишет len сэмплов из short[] в WAV-канал (16-bit LE). Потокобезопасно. */
	private void writePcmToWav(short[] buf, int len) {
		synchronized (mWavLock) {
			java.nio.channels.FileChannel ch = mWavChannel;
			if (ch == null) return;
			try {
				java.nio.ByteBuffer bb = java.nio.ByteBuffer.allocate(len * 2);
				bb.order(java.nio.ByteOrder.LITTLE_ENDIAN);
				for (int i = 0; i < len; i++) bb.putShort(buf[i]);
				bb.flip();
				ch.write(bb);
				mWavDataBytes += len * 2L;
			} catch (Exception ignored) {}
		}
	}

	/**
	 * Создаёт WAV-файл рядом с MP4, пишет 44-байтный placeholder-заголовок.
	 * @param wavName  отображаемое имя файла (напр. "VID_1234.wav")
	 * @param relPath  путь в MediaStore (напр. "DCIM/CaMic"), используется только
	 *                 на Android 10+; на старых версиях файл кладётся в DCIM/CaMic.
	 */
	private void startWavFile(String wavName, String relPath) throws Exception {
		mWavDataBytes = 0;
		if (Build.VERSION.SDK_INT >= 29) {
			ContentValues cv = new ContentValues();
			cv.put(MediaStore.Audio.Media.DISPLAY_NAME, wavName);
			cv.put(MediaStore.Audio.Media.MIME_TYPE, "audio/wav");
			cv.put(MediaStore.Audio.Media.RELATIVE_PATH, relPath);
			cv.put(MediaStore.Audio.Media.IS_PENDING, 1);
			mWavPendingUri = getContentResolver().insert(
					MediaStore.Audio.Media.EXTERNAL_CONTENT_URI, cv);
			mWavPfd = getContentResolver().openFileDescriptor(mWavPendingUri, "rw");
			// FileOutputStream + getChannel() поддерживает position() — нужно для обновления заголовка
			java.io.FileOutputStream fos =
					new java.io.FileOutputStream(mWavPfd.getFileDescriptor());
			mWavChannel = fos.getChannel();
		} else {
			@SuppressWarnings("deprecation")
			File dir = new File(
					Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DCIM),
					"CaMic");
			dir.mkdirs();
			// RandomAccessFile нужен для seek при финализации заголовка
			mWavChannel = new java.io.RandomAccessFile(new File(dir, wavName), "rw").getChannel();
		}
		// Записываем placeholder-заголовок (размеры = 0, обновятся в finalizeWavFile)
		synchronized (mWavLock) {
			java.nio.ByteBuffer hdr = buildWavHeader(0L);
			mWavChannel.position(0);
			mWavChannel.write(hdr);
		}
	}

	/** Строит 44-байтный WAV-заголовок (PCM, 16-bit LE). */
	private java.nio.ByteBuffer buildWavHeader(long dataBytes) {
		int ch = (mAudChannels >= 1 && mAudChannels <= 2) ? mAudChannels : 1;
		java.nio.ByteBuffer bb = java.nio.ByteBuffer.allocate(44);
		bb.order(java.nio.ByteOrder.LITTLE_ENDIAN);
		// RIFF chunk
		bb.put(new byte[]{'R','I','F','F'});
		bb.putInt((int)(36L + dataBytes));   // размер без первых 8 байт
		bb.put(new byte[]{'W','A','V','E'});
		// fmt chunk
		bb.put(new byte[]{'f','m','t',' '});
		bb.putInt(16);                        // размер fmt = 16 (PCM)
		bb.putShort((short) 1);               // AudioFormat: PCM
		bb.putShort((short) ch);
		bb.putInt(AUDIO_SR);
		bb.putInt(AUDIO_SR * ch * 2);         // ByteRate
		bb.putShort((short)(ch * 2));         // BlockAlign
		bb.putShort((short) 16);              // BitsPerSample
		// data chunk
		bb.put(new byte[]{'d','a','t','a'});
		bb.putInt((int) dataBytes);
		bb.flip();
		return bb;
	}

	/**
	 * Финализирует WAV: перезаписывает заголовок с правильными размерами,
	 * закрывает файл, снимает IS_PENDING в MediaStore.
	 * Безопасно вызывать даже если WAV не запускался (mWavChannel == null).
	 */
	private void finalizeWavFile() {
		java.nio.channels.FileChannel ch;
		synchronized (mWavLock) {
			ch = mWavChannel;
			mWavChannel = null; // аудио-поток больше не пишет
		}
		mPcmWriteMode = 0;
		synchronized (mPcmRingLock) { mPcmRing.clear(); }
		if (ch == null) return;
		try {
			// Обновляем заголовок с реальными размерами
			java.nio.ByteBuffer hdr = buildWavHeader(mWavDataBytes);
			ch.position(0);
			ch.write(hdr);
			ch.close();
		} catch (Exception ignored) {}
		try { if (mWavPfd != null) { mWavPfd.close(); mWavPfd = null; } } catch (Exception ignored) {}
		if (Build.VERSION.SDK_INT >= 29 && mWavPendingUri != null) {
			ContentValues cv = new ContentValues();
			cv.put(MediaStore.Audio.Media.IS_PENDING, 0);
			getContentResolver().update(mWavPendingUri, cv, null, null);
			mWavPendingUri = null;
		}
		mWavDataBytes = 0;
	}

	private static class AudioSrcItem {
		final String name;
		final int audioSource;
		final AudioDeviceInfo device;
		
		AudioSrcItem(String n, int s, AudioDeviceInfo d) {
			name = n;
			audioSource = s;
			device = d;
		}
	}
	
	static class VerticalSeekBar extends View {
		private int mMax = 100;
		private int mProgress = 0;
		
		private final Paint mTrackPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mFillPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mThumbPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mRidgePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		
		private SeekBar.OnSeekBarChangeListener mListener;
		
		VerticalSeekBar(Context c) {
			super(c);
			mTrackPaint.setColor(0x44FFFFFF);
			mFillPaint.setColor(0xFFDDCC00);
			mThumbPaint.setColor(0xFFEEEEEE);
			mRidgePaint.setColor(0xFF888866);
			mRidgePaint.setStyle(Paint.Style.STROKE);
			mRidgePaint.setStrokeWidth(1.2f * c.getResources().getDisplayMetrics().density);
			setClickable(true);
		}
		
		void setMax(int max) { mMax = max; invalidate(); }
		void setProgress(int p) { mProgress = Math.max(0, Math.min(mMax, p)); invalidate(); }
		int getMax() { return mMax; }
		int getProgress() { return mProgress; }
		void setOnSeekBarChangeListener(SeekBar.OnSeekBarChangeListener l) { mListener = l; }

		// Высота ручки микшера в px
		private float faderH(float w) { return Math.round(w * 0.7f) + dp(20); }

		private int dp(int x) {
			return Math.round(x * getResources().getDisplayMetrics().density);
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			final float trackW = w * 0.3f;
			final float cx = w / 2f;
			final float trkX1 = cx - trackW / 2f;
			final float trkX2 = cx + trackW / 2f;
			final float halfFader = faderH(w) / 2f;
			final float padV = halfFader + 2f;
			final float trkT = padV;
			final float trkB = h - padV;
			final float trkH = trkB - trkT;

			float frac = mMax > 0 ? (float) mProgress / mMax : 0f;
			float thumbY = trkB - frac * trkH;

			// Трек
			canvas.drawRoundRect(new RectF(trkX1, trkT, trkX2, trkB),
				trackW / 2f, trackW / 2f, mTrackPaint);
			// Заполненная часть
			canvas.drawRoundRect(new RectF(trkX1, thumbY, trkX2, trkB),
				trackW / 2f, trackW / 2f, mFillPaint);
			// Метка 0 dB
			Paint z = new Paint(Paint.ANTI_ALIAS_FLAG);
			z.setColor(0x88FFFFFF); z.setStrokeWidth(1.5f);
			canvas.drawLine(trkX1 - 3f, trkB - 0.5f * trkH, trkX2 + 3f, trkB - 0.5f * trkH, z);

			// ── Ручка (fader cap) — широкий прямоугольник во всю ширину ──────
			float fH = faderH(w);
			float fW = w - 2f;
			RectF fader = new RectF(1f, thumbY - fH/2f, 1f + fW, thumbY + fH/2f);
			// Тень
			Paint shadow = new Paint(Paint.ANTI_ALIAS_FLAG);
			shadow.setColor(0x66000000);
			shadow.setStyle(Paint.Style.FILL);
			canvas.drawRoundRect(new RectF(fader.left+2, fader.top+3, fader.right+2, fader.bottom+3),
				dp(4), dp(4), shadow);
			// Тело ручки
			canvas.drawRoundRect(fader, dp(4), dp(4), mThumbPaint);
			// Горизонтальные риски (3 штуки по центру)
			float rInset = fW * 0.18f;
			for (int ri = -1; ri <= 1; ri++) {
				float ry = thumbY + ri * dp(4);
				canvas.drawLine(1f + rInset, ry, 1f + fW - rInset, ry, mRidgePaint);
			}
			// Центральная риска чуть длиннее и ярче
			Paint cLine = new Paint(Paint.ANTI_ALIAS_FLAG);
			cLine.setColor(0xFFDDCC00); cLine.setStrokeWidth(1.5f);
			canvas.drawLine(1f + rInset * 0.6f, thumbY, 1f + fW - rInset * 0.6f, thumbY, cLine);
		}
		
		@Override
		public boolean onTouchEvent(MotionEvent e) {
			if (!isEnabled()) return false;
			final float h = getHeight(), w = getWidth();
			final float halfFader = faderH(w) / 2f;
			final float padV = halfFader + 2f;
			final float trkT = padV;
			final float trkB = h - padV;
			final float trkH = trkB - trkT;
			
			switch (e.getAction()) {
				case MotionEvent.ACTION_DOWN:
				if (mListener != null) mListener.onStartTrackingTouch(null);
				// fall through
				case MotionEvent.ACTION_MOVE: {
					float frac = 1f - (e.getY() - trkT) / trkH;
					int p = Math.max(0, Math.min(mMax, Math.round(frac * mMax)));
					mProgress = p;
					invalidate();
					if (mListener != null) mListener.onProgressChanged(null, p, true);
					return true;
				}
				case MotionEvent.ACTION_UP:
				case MotionEvent.ACTION_CANCEL:
				if (mListener != null) mListener.onStopTrackingTouch(null);
				return true;
			}
			return false;
		}
	}
	
	// ─── Вертикальный VU-метр dBFS ───────────────────────────────────────────
	// Сегменты снизу вверх. Пик-маркер — горизонтальная черта с hold 1.8s.

	static class VuMeterView extends View {
		private static final int N = 30;
		private static final float MIN_DB = -60f;
		private static final long PEAK_HOLD_MS = 1800;

		private final Paint mSegPaint   = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mPeakPaint  = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mDbLblPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final RectF mRect       = new RectF();
		private float mLevelDb  = MIN_DB;
		private float mPeakDb   = MIN_DB;
		private long  mPeakHoldUntil = 0;

		VuMeterView(Context c) {
			super(c);
			mPeakPaint.setColor(0xFFFFFFFF);
			float vuDensity = c.getResources().getDisplayMetrics().density;
			mPeakPaint.setStrokeWidth(4f * vuDensity);
			mPeakPaint.setStyle(Paint.Style.STROKE);
			float density = c.getResources().getDisplayMetrics().density;
			mDbLblPaint.setTextSize(5.5f * density);
			mDbLblPaint.setTextAlign(Paint.Align.RIGHT);
			mDbLblPaint.setAntiAlias(true);
		}

		void setLevel(float rms) {
			mLevelDb = rms > 1e-6f ? Math.max(MIN_DB, (float)(20.0 * Math.log10(rms))) : MIN_DB;
			postInvalidate();
		}

		void setPeak(float peak) {
			float db = peak > 1e-6f ? Math.max(MIN_DB, (float)(20.0 * Math.log10(peak))) : MIN_DB;
			if (db >= mPeakDb || System.currentTimeMillis() > mPeakHoldUntil) {
				mPeakDb = db;
				mPeakHoldUntil = System.currentTimeMillis() + PEAK_HOLD_MS;
			}
		}

		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			final float segH = (h - N - 1f) / N;
			final float segW = w - 2f;

			for (int i = 0; i < N; i++) {
				float segDb = MIN_DB + (float) i / N * (-MIN_DB);
				boolean lit = mLevelDb >= segDb;
				int color;
				if (!lit)             color = 0xFF181818;
				else if (segDb < -12f) color = 0xFF00CC55;
				else if (segDb <  -6f) color = 0xFFFFBB00;
				else                   color = 0xFFFF2200;
				mSegPaint.setColor(color);
				float y = h - 1f - i * (segH + 1f) - segH;
				mRect.set(1f, y, 1f + segW, y + segH);
				canvas.drawRoundRect(mRect, 2f, 2f, mSegPaint);
			}

			// Пик-маркер
			if (mPeakDb > MIN_DB) {
				float frac = (mPeakDb - MIN_DB) / (-MIN_DB);
				float py = h - 1f - frac * (h - 2f);
				long now = System.currentTimeMillis();
				int peakColor;
				if      (mPeakDb >= -3f)  peakColor = 0xFFFF2200;
				else if (mPeakDb >= -12f) peakColor = 0xFFFFBB00;
				else                      peakColor = 0xFF00FF88;
				boolean fading = now > mPeakHoldUntil - 400;
				if (!fading || (now / 150) % 2 == 0) {
					mPeakPaint.setColor(peakColor);
					canvas.drawLine(0, py, w, py, mPeakPaint);
				}
			}

			// ── dB-метки поверх индикатора ────────────────────────────────────
			float[] dbMarks  = { 0f, -6f, -12f, -24f, -48f, -60f };
			String[] dbStrs  = { "0", "-6", "-12", "-24", "-48", "-60" };
			float lblAscent = -mDbLblPaint.ascent();
			for (int di = 0; di < dbMarks.length; di++) {
				float frac = (dbMarks[di] - MIN_DB) / (-MIN_DB);
				float ly   = h - 1f - frac * (h - 2f);
				// цвет совпадает с цветом сегмента
				if      (dbMarks[di] >= -6f)  mDbLblPaint.setColor(0xFFFF6644);
				else if (dbMarks[di] >= -12f) mDbLblPaint.setColor(0xFFFFDD44);
				else                          mDbLblPaint.setColor(0xCCBBFFCC);
				mDbLblPaint.setAlpha(200);
				// рисуем справа, сдвинув вверх на половину высоты шрифта
				canvas.drawText(dbStrs[di], w - 1f, ly + lblAscent * 0.5f, mDbLblPaint);
			}
		}
	}
	
	// ─── Рычаг зума ──────────────────────────────────────────────────────────
	
	static class ZoomLeverView extends View {
		interface Listener {
			void onLever(float pos);
		}
		
		private Listener mListener;
		private volatile float mPos = 0f;
		private boolean mTracking = false;
		private float trkT, trkB, trkH, trkW, mid, cx;
		
		private final Paint mTrackPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mThumbPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mMarkPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mTextPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		
		ZoomLeverView(Context c) {
			super(c);
			mTrackPaint.setColor(0x55FFFFFF);
			mThumbPaint.setColor(0xFFFFFFFF);
			mMarkPaint.setColor(0xAAFFFFFF);
			mMarkPaint.setStyle(Paint.Style.STROKE);
			mMarkPaint.setStrokeWidth(1.5f * c.getResources().getDisplayMetrics().density);
			mTextPaint.setColor(0xCCFFFFFF);
			mTextPaint.setTextAlign(Paint.Align.CENTER);
			mTextPaint.setTextSize(11 * c.getResources().getDisplayMetrics().density);
			setBackgroundColor(0x44000000);
		}
		
		void setListener(Listener l) {
			mListener = l;
		}
		
		private void recalc() {
			float w = getWidth(), h = getHeight();
			float lblH = mTextPaint.getTextSize() + dp(4);
			trkT = lblH;
			trkB = h - lblH;
			trkH = trkB - trkT;
			trkW = dp(16);
			mid = (trkT + trkB) / 2f;
			cx = w / 2f;
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			recalc();
			float h = getHeight();
			RectF track = new RectF(cx - trkW / 2f, trkT, cx + trkW / 2f, trkB);
			canvas.drawRoundRect(track, dp(5), dp(5), mTrackPaint);
			canvas.drawLine(cx - trkW / 2f - dp(6), mid, cx + trkW / 2f + dp(6), mid, mMarkPaint);
			float thumbCY = mid - mPos * trkH / 2f;
			float thumbH = dp(28), thumbW = trkW + dp(12);
			mThumbPaint.setAlpha((int) (160 + 90 * Math.abs(mPos)));
			canvas.drawRoundRect(
			new RectF(cx - thumbW / 2f, thumbCY - thumbH / 2f, cx + thumbW / 2f, thumbCY + thumbH / 2f), dp(6),
			dp(6), mThumbPaint);
			Paint.FontMetrics fm = mTextPaint.getFontMetrics();
			float pad = mTextPaint.getTextSize() + dp(2);
			canvas.drawText("T+", cx, pad / 2f - (fm.ascent + fm.descent) / 2f, mTextPaint);
			canvas.drawText("W−", cx, h - pad / 2f - fm.ascent, mTextPaint);
		}
		
		@Override
		public boolean onTouchEvent(MotionEvent e) {
			recalc();
			switch (e.getAction()) {
				case MotionEvent.ACTION_DOWN:
				case MotionEvent.ACTION_MOVE:
				removeCallbacks(mSpring);
				mTracking = true;
				mPos = Math.max(-1f, Math.min(1f, (mid - e.getY()) / (trkH / 2f)));
				if (mListener != null)
				mListener.onLever(mPos);
				invalidate();
				return true;
				case MotionEvent.ACTION_UP:
				case MotionEvent.ACTION_CANCEL:
				mTracking = false;
				post(mSpring);
				return true;
			}
			return super.onTouchEvent(e);
		}
		
		private final Runnable mSpring = new Runnable() {
			@Override
			public void run() {
				if (mTracking)
				return;
				mPos *= 0.75f;
				if (mListener != null)
				mListener.onLever(mPos);
				invalidate();
				if (Math.abs(mPos) > 0.01f)
				postDelayed(this, 16);
				else {
					mPos = 0f;
					if (mListener != null)
					mListener.onLever(0f);
					invalidate();
				}
			}
		};
		
		private int dp(int x) {
			return Math.round(x * getResources().getDisplayMetrics().density);
		}
	}
	
	// ─── Focus Assist — зумированное окно в центре экрана ───────────────────
	// Захватывает центральную область превью через PixelCopy и рисует её
	// с увеличением x4. Обновляется каждые ~100 мс.
	// Поверх — сетка Петцваля и рамка.
	
	class FocusAssistView extends View implements Runnable {
		private Bitmap mBmp;
		private final Paint mBmpPaint = new Paint(Paint.ANTI_ALIAS_FLAG | Paint.FILTER_BITMAP_FLAG);
		private final Paint mBorderPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mGridPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mLabelPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private static final int ZOOM = 4;
		private static final int SAMPLE_SIZE = 120; // px стороны захватываемого квадрата
		private volatile boolean mRunning;
		
		FocusAssistView(Context c) {
			super(c);
			mBorderPaint.setColor(0xFFDDCC00);
			mBorderPaint.setStyle(Paint.Style.STROKE);
			mBorderPaint.setStrokeWidth(2f);
			mGridPaint.setColor(0x55FFFFFF);
			mGridPaint.setStyle(Paint.Style.STROKE);
			mGridPaint.setStrokeWidth(0.8f);
			mLabelPaint.setColor(0xFFDDCC00);
			mLabelPaint.setTextAlign(Paint.Align.CENTER);
			mLabelPaint.setTextSize(10 * getResources().getDisplayMetrics().density);
			mLabelPaint.setAntiAlias(true);
			setBackgroundColor(0x00000000);
		}
		
		@Override
		protected void onAttachedToWindow() {
			super.onAttachedToWindow();
			mRunning = true;
			postDelayed(this, 100);
		}
		
		@Override
		protected void onDetachedFromWindow() {
			super.onDetachedFromWindow();
			mRunning = false;
			removeCallbacks(this);
		}
		
		@Override
		public void run() {
			if (!mRunning || getVisibility() != View.VISIBLE) {
				if (mRunning) postDelayed(this, 200);
				return;
			}
			capture();
			postDelayed(this, 100);
		}
		
		private void capture() {
			if (mSv == null || !mSurfaceReady) return;
			if (android.os.Build.VERSION.SDK_INT < 26) {
				// PixelCopy недоступен — рисуем заглушку
				invalidate();
				return;
			}
			try {
				int svW = mSv.getWidth(), svH = mSv.getHeight();
				if (svW <= 0 || svH <= 0) return;
				
				// Центральная область SAMPLE_SIZE × SAMPLE_SIZE
				int cx = svW / 2, cy = svH / 2, half = SAMPLE_SIZE / 2;
				int l = Math.max(0, cx - half), t = Math.max(0, cy - half);
				int r = Math.min(svW, l + SAMPLE_SIZE), b = Math.min(svH, t + SAMPLE_SIZE);
				android.graphics.Rect src = new android.graphics.Rect(l, t, r, b);
				
				Bitmap dst = Bitmap.createBitmap(r - l, b - t, Bitmap.Config.ARGB_8888);
				android.view.PixelCopy.request(mSv, src, dst, result -> {
					if (result == android.view.PixelCopy.SUCCESS) {
						mBmp = dst;
						postInvalidate();
					}
				}, new Handler(android.os.Looper.getMainLooper()));
			} catch (Exception ignored) {}
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			
			// Фон — чёрный полупрозрачный
			canvas.drawARGB(200, 0, 0, 0);
			
			if (mBmp != null && !mBmp.isRecycled()) {
				// Рисуем захваченный фрагмент, растянутый на весь квадрат
				android.graphics.RectF dst = new android.graphics.RectF(0, 0, w, h);
				canvas.drawBitmap(mBmp, null, dst, mBmpPaint);
				} else {
				// Заглушка когда PixelCopy ещё не отработал
				Paint p = new Paint();
				p.setColor(0xFF333333);
				canvas.drawRect(0, 0, w, h, p);
			}
			
			// Сетка — тонкая перекрёстная линия (центральная)
			canvas.drawLine(w / 2f, 0, w / 2f, h, mGridPaint);
			canvas.drawLine(0, h / 2f, w, h / 2f, mGridPaint);
			// Третьи (по правило третей)
			canvas.drawLine(w / 3f, 0, w / 3f, h, mGridPaint);
			canvas.drawLine(2 * w / 3f, 0, 2 * w / 3f, h, mGridPaint);
			canvas.drawLine(0, h / 3f, w, h / 3f, mGridPaint);
			canvas.drawLine(0, 2 * h / 3f, w, 2 * h / 3f, mGridPaint);
			
			// Рамка
			canvas.drawRect(1f, 1f, w - 1f, h - 1f, mBorderPaint);
			
			// Уголки (более жирные акценты)
			float corner = w * 0.12f;
			mBorderPaint.setStrokeWidth(3f);
			canvas.drawLine(1f, 1f, corner, 1f, mBorderPaint);
			canvas.drawLine(1f, 1f, 1f, corner, mBorderPaint);
			canvas.drawLine(w - corner, 1f, w - 1f, 1f, mBorderPaint);
			canvas.drawLine(w - 1f, 1f, w - 1f, corner, mBorderPaint);
			canvas.drawLine(1f, h - corner, 1f, h - 1f, mBorderPaint);
			canvas.drawLine(1f, h - 1f, corner, h - 1f, mBorderPaint);
			canvas.drawLine(w - 1f, h - corner, w - 1f, h - 1f, mBorderPaint);
			canvas.drawLine(w - corner, h - 1f, w - 1f, h - 1f, mBorderPaint);
			mBorderPaint.setStrokeWidth(2f);
			
			// Подпись
			canvas.drawText("FOCUS ×" + ZOOM, w / 2f, h - 4f, mLabelPaint);
		}
	}
	
	// ─── Барабан фокуса (как кольцо на настоящей камере) ────────────────────
	// Свайп вниз = фокус вдаль (∞), свайп вверх = макро.
	// Визуально: риски на цилиндре с перспективным сжатием.
	
	static class FocusDrumView extends View {
		interface OnFocusChangeListener {
			void onFocusChanged(float value); // 0=∞, 1=macro
		}
		
		/** Коллбэк начала/остановки прокрутки барабана */
		interface OnDrumScrollListener {
			void onScrollStart();
			void onScrollStop();
		}
		
		private OnFocusChangeListener mListener;
		private OnDrumScrollListener mScrollListener;
		private float mValue = 0f; // 0..1
		private float mLastY;
		private boolean mDragging;
		
		// Визуальный «угол» барабана — непрерывный для анимации рисок
		private float mAngle = 0f;
		private static final float FULL_RANGE_PX_PER_UNIT = 4000f; // 5× плавнее оригинала
		
		private final Paint mDrumPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mRiskPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mShadowPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mCenterLinePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		
		FocusDrumView(Context c) {
			super(c);
			float density = c.getResources().getDisplayMetrics().density;
			mDrumPaint.setColor(0xFF2A2A2A);
			mRiskPaint.setStrokeWidth(1.5f * density);
			mRiskPaint.setStyle(Paint.Style.STROKE);
			mShadowPaint.setStyle(Paint.Style.FILL);
			mCenterLinePaint.setColor(0xFFDDCC00);
			mCenterLinePaint.setStrokeWidth(2f * density);
			mCenterLinePaint.setStyle(Paint.Style.STROKE);
		}
		
		void setOnFocusChangeListener(OnFocusChangeListener l) {
			mListener = l;
		}
		
		void setOnDrumScrollListener(OnDrumScrollListener l) {
			mScrollListener = l;
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			final float cx = w / 2f;
			final float drumW = w * 0.72f;
			final float drumLeft = cx - drumW / 2f;
			final float drumRight = cx + drumW / 2f;
			
			// Фон барабана
			RectF drumRect = new RectF(drumLeft, 0, drumRight, h);
			mDrumPaint.setColor(0xFF222222);
			canvas.drawRoundRect(drumRect, drumW * 0.12f, drumW * 0.12f, mDrumPaint);
			
			// Риски барабана с перспективным сжатием
			final float riskStep = h * 0.07f;
			float offset = mAngle % riskStep;
			if (offset < 0) offset += riskStep;
			
			final int totalRisks = (int) (h / riskStep) + 2;
			for (int i = -1; i <= totalRisks; i++) {
				float ry = offset + i * riskStep;
				if (ry < 0 || ry > h) continue;
				
				float distFromCenter = Math.abs(ry - h / 2f) / (h / 2f);
				float squeeze = 1f - 0.55f * distFromCenter * distFromCenter;
				float riskLen = drumW * 0.8f * squeeze;
				int alpha = (int) (200 * (1f - distFromCenter * 0.7f));
				
				boolean isMajor = (Math.abs(Math.round((ry - offset) / riskStep)) % 5 == 0);
				if (isMajor) { riskLen *= 1.25f; alpha = Math.min(255, alpha + 40); }
				
				mRiskPaint.setColor(0xFFFFFFFF);
				mRiskPaint.setAlpha(alpha);
				mRiskPaint.setStrokeWidth(isMajor ? 2f : 1.2f);
				canvas.drawLine(cx - riskLen / 2f, ry, cx + riskLen / 2f, ry, mRiskPaint);
			}
			
			// Градиентные тени сверху/снизу (имитация цилиндра)
			int[] colorsTop = { 0xCC000000, 0x00000000 };
			int[] colorsBot = { 0x00000000, 0xCC000000 };
			android.graphics.LinearGradient shadTop = new android.graphics.LinearGradient(
			0, 0, 0, h * 0.28f, colorsTop, null, android.graphics.Shader.TileMode.CLAMP);
			android.graphics.LinearGradient shadBot = new android.graphics.LinearGradient(
			0, h * 0.72f, 0, h, colorsBot, null, android.graphics.Shader.TileMode.CLAMP);
			mShadowPaint.setShader(shadTop);
			canvas.drawRoundRect(drumRect, drumW * 0.12f, drumW * 0.12f, mShadowPaint);
			mShadowPaint.setShader(shadBot);
			canvas.drawRoundRect(drumRect, drumW * 0.12f, drumW * 0.12f, mShadowPaint);
			mShadowPaint.setShader(null);
			
			// Центральная риска-указатель (жёлтая)
			canvas.drawLine(drumLeft - 4f, h / 2f, drumRight + 4f, h / 2f, mCenterLinePaint);
		}
		
		@Override
		public boolean onTouchEvent(MotionEvent e) {
			switch (e.getAction()) {
				case MotionEvent.ACTION_DOWN:
				mLastY = e.getY();
				mDragging = true;
				if (mScrollListener != null) mScrollListener.onScrollStart();
				return true;
				case MotionEvent.ACTION_MOVE: {
					if (!mDragging) return true;
					float dy = e.getY() - mLastY;
					mLastY = e.getY();
					// Свайп вниз → фокус на ∞ (value уменьшается)
					// Свайп вверх → макро (value увеличивается)
					mAngle += dy;
					float newVal = mValue - dy / FULL_RANGE_PX_PER_UNIT;
					newVal = Math.max(0f, Math.min(1f, newVal));
					// Фиксируем барабан у упора
					if (newVal == 0f && mValue == 0f) mAngle = Math.min(mAngle, 0f);
					if (newVal == 1f && mValue == 1f) mAngle = Math.max(mAngle, 0f);
					if (newVal != mValue) {
						mValue = newVal;
						if (mListener != null) mListener.onFocusChanged(mValue);
					}
					invalidate();
					return true;
				}
				case MotionEvent.ACTION_UP:
				case MotionEvent.ACTION_CANCEL:
				mDragging = false;
				if (mScrollListener != null) mScrollListener.onScrollStop();
				return true;
			}
			return false;
		}
	}

	// ─── Осциллограф с триггером ─────────────────────────────────────────────
	// Прозрачный фон, наложен поверх изображения камеры.
	// Триггер: фронт нарастания (rising edge) при пересечении порога.
	// Окно отображения — 2048 выборок (~46 мс при 44100 Гц).
	
	static class OscilloscopeView extends View {
		private static final int DISP_SAMPLES = 2048;
		private static final int BUF_SIZE = DISP_SAMPLES * 4; // кольцевой буфер
		
		private final float[] mRingBuf = new float[BUF_SIZE];
		private int mWritePos = 0;
		private final float[] mFrame = new float[DISP_SAMPLES];
		private volatile boolean mNewFrame = false;
		private final Object mLock = new Object();
		
		// Триггер
		private static final float TRIG_LEVEL = 0.05f; // нормализованный уровень
		private static final int TRIG_HYSTERESIS = 64; // выборок предыстории
		
		private final Paint mWavePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mGridPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mLabelPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		/** Цвет по амплитуде 0..1 — как сегменты VU-метра */
		static int levelColor(float amp) {
			if (amp >= 0.7f) return 0xFFFF2200;
			if (amp >= 0.3f) return 0xFFFFBB00;
			return 0xFF00CC55;
		}

		OscilloscopeView(Context c) {
			super(c);
			setBackgroundColor(0x00000000); // прозрачный
			mWavePaint.setStrokeWidth(1.8f * c.getResources().getDisplayMetrics().density);
			mWavePaint.setStyle(Paint.Style.STROKE);
			mWavePaint.setStrokeCap(Paint.Cap.ROUND);
			mGridPaint.setColor(0x33FFFFFF);
			mGridPaint.setStrokeWidth(0.8f);
			mGridPaint.setStyle(Paint.Style.STROKE);
			mLabelPaint.setColor(0xAAFFFFFF);
			mLabelPaint.setTextSize(9 * c.getResources().getDisplayMetrics().density);
			mLabelPaint.setAntiAlias(true);
		}
		
		/** Принимает буфер PCM-16, конвертирует в mono float и кладёт в кольцевой буфер */
		void pushSamples(short[] buf, int len, int channels) {
			synchronized (mLock) {
				for (int i = 0; i < len; i += channels) {
					float mono = buf[i] / 32768f;
					if (channels == 2 && i + 1 < len)
						mono = (mono + buf[i + 1] / 32768f) * 0.5f;
					mRingBuf[mWritePos] = mono;
					mWritePos = (mWritePos + 1) % BUF_SIZE;
				}
				// Поиск триггера: восходящий фронт >= TRIG_LEVEL
				// Ищем в последних BUF_SIZE выборках
				int trigPos = -1;
				int searchStart = (mWritePos - BUF_SIZE + BUF_SIZE) % BUF_SIZE;
				for (int k = TRIG_HYSTERESIS; k < BUF_SIZE - DISP_SAMPLES; k++) {
					int p = (searchStart + k) % BUF_SIZE;
					int pp = (p - 1 + BUF_SIZE) % BUF_SIZE;
					if (mRingBuf[pp] < TRIG_LEVEL && mRingBuf[p] >= TRIG_LEVEL) {
						trigPos = p;
						break;
					}
				}
				if (trigPos < 0) {
					// Триггер не найден — показываем последние DISP_SAMPLES
					trigPos = (mWritePos - DISP_SAMPLES + BUF_SIZE) % BUF_SIZE;
				}
				for (int k = 0; k < DISP_SAMPLES; k++) {
					mFrame[k] = mRingBuf[(trigPos + k) % BUF_SIZE];
				}
				mNewFrame = true;
			}
			postInvalidate();
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			if (w == 0 || h == 0) return;

			// Полностью прозрачный фон — не рисуем ничего
			// canvas.drawARGB(90, 0, 0, 0);
			
			// Сетка
			for (int gx = 1; gx < 4; gx++)
				canvas.drawLine(w * gx / 4f, 0, w * gx / 4f, h, mGridPaint);
			for (int gy = 1; gy < 4; gy++)
				canvas.drawLine(0, h * gy / 4f, w, h * gy / 4f, mGridPaint);
			// Ось Y = 0
			Paint zeroPaint = new Paint(mGridPaint);
			zeroPaint.setColor(0x55FFFFFF);
			zeroPaint.setStrokeWidth(1.4f);
			canvas.drawLine(0, h / 2f, w, h / 2f, zeroPaint);
			
			// Линия уровня триггера
			Paint trigPaint = new Paint();
			trigPaint.setColor(0x88FFFF00);
			trigPaint.setStrokeWidth(1f);
			trigPaint.setStyle(Paint.Style.STROKE);
			trigPaint.setPathEffect(new android.graphics.DashPathEffect(new float[]{6f, 4f}, 0));
			float trigY = h / 2f - TRIG_LEVEL * h / 2f;
			canvas.drawLine(0, trigY, w, trigY, trigPaint);
			
			// Волна — цветные сегменты (зелёный→оранжевый→красный)
			float[] frame;
			synchronized (mLock) {
				frame = mFrame.clone();
			}
			for (int i = 0; i < DISP_SAMPLES - 1; i++) {
				float x0 = i       * w / (DISP_SAMPLES - 1f);
				float x1 = (i + 1) * w / (DISP_SAMPLES - 1f);
				float y0 = h / 2f - frame[i]     * h / 2f * 0.92f;
				float y1 = h / 2f - frame[i + 1] * h / 2f * 0.92f;
				mWavePaint.setColor(levelColor(Math.abs(frame[i])));
				canvas.drawLine(x0, y0, x1, y1, mWavePaint);
			}
			
			// Подпись
			canvas.drawText("OSC  T↑", 4, h - 3f, mLabelPaint);
		}
	}
	

	// ─── Огибающая: бегущий 10-секундный осциллограф ────────────────────────────
	// Хранит пиковые значения с шагом ~10 мс (CHUNK выборок).
	// Показывается когда осциллограф выключен; вертикальный масштаб совпадает.

	static class EnvelopeView extends View {
		private static final int HIST  = 1000; // 10 с × 100 точек/с
		private static final int CHUNK = 441;  // ~10 мс при 44100 Гц

		private final float[] mEnv    = new float[HIST];
		private int   mWritePos = 0;
		private int   mFilled   = 0;
		private float mAccPeak  = 0f;
		private int   mAccCount = 0;
		private final Object mLock = new Object();

		private final Paint mSegPaint   = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mGridPaint  = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mLabelPaint = new Paint(Paint.ANTI_ALIAS_FLAG);

		EnvelopeView(Context c) {
			super(c);
			setBackgroundColor(0x00000000);
			float d = c.getResources().getDisplayMetrics().density;
			mSegPaint.setStyle(Paint.Style.STROKE);
			mSegPaint.setStrokeWidth(1.6f * d);
			mSegPaint.setStrokeCap(Paint.Cap.ROUND);
			mGridPaint.setColor(0x33FFFFFF);
			mGridPaint.setStrokeWidth(0.8f);
			mGridPaint.setStyle(Paint.Style.STROKE);
			mLabelPaint.setColor(0xAAFFFFFF);
			mLabelPaint.setTextSize(9 * d);
			mLabelPaint.setAntiAlias(true);
		}

		void pushSamples(short[] buf, int len, int channels) {
			synchronized (mLock) {
				for (int i = 0; i < len; i += channels) {
					float s = Math.abs(buf[i] / 32768f);
					if (channels == 2 && i + 1 < len)
						s = Math.max(s, Math.abs(buf[i + 1] / 32768f));
					if (s > mAccPeak) mAccPeak = s;
					mAccCount++;
					if (mAccCount >= CHUNK) {
						mEnv[mWritePos] = mAccPeak;
						mWritePos = (mWritePos + 1) % HIST;
						if (mFilled < HIST) mFilled++;
						mAccPeak  = 0f;
						mAccCount = 0;
					}
				}
			}
			postInvalidate();
		}

		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			if (w == 0 || h == 0) return;

			// Сетка (как у осциллографа)
			for (int gx = 1; gx < 4; gx++)
				canvas.drawLine(w * gx / 4f, 0, w * gx / 4f, h, mGridPaint);
			for (int gy = 1; gy < 4; gy++)
				canvas.drawLine(0, h * gy / 4f, w, h * gy / 4f, mGridPaint);
			Paint zeroPaint = new Paint(mGridPaint);
			zeroPaint.setColor(0x55FFFFFF);
			zeroPaint.setStrokeWidth(1.4f);
			canvas.drawLine(0, h / 2f, w, h / 2f, zeroPaint);

			float[] snap;
			int filled, writePos;
			synchronized (mLock) {
				snap     = mEnv.clone();
				filled   = mFilled;
				writePos = mWritePos;
			}
			if (filled < 2) {
				mLabelPaint.setColor(0xAAFFFFFF);
				canvas.drawText("ENV  10s", 4, h - 3f, mLabelPaint);
				return;
			}

			int count = Math.min(filled, HIST);
			int start = (filled < HIST) ? 0 : writePos;

			// Рисуем симметричную огибающую цветными сегментами
			for (int i = 0; i < count - 1; i++) {
				float a0 = snap[(start + i)     % HIST];
				float a1 = snap[(start + i + 1) % HIST];
				float x0 = i       * w / (count - 1f);
				float x1 = (i + 1) * w / (count - 1f);
				float yT0 = h / 2f - a0 * h / 2f * 0.92f;
				float yT1 = h / 2f - a1 * h / 2f * 0.92f;
				float yB0 = h / 2f + a0 * h / 2f * 0.92f;
				float yB1 = h / 2f + a1 * h / 2f * 0.92f;
				mSegPaint.setColor(OscilloscopeView.levelColor((a0 + a1) * 0.5f));
				canvas.drawLine(x0, yT0, x1, yT1, mSegPaint);
				canvas.drawLine(x0, yB0, x1, yB1, mSegPaint);
			}

			// Вертикальная черта «сейчас» (правый край)
			Paint curPaint = new Paint();
			curPaint.setColor(0x66FFFFFF);
			curPaint.setStrokeWidth(1f);
			canvas.drawLine(w - 1f, 0, w - 1f, h, curPaint);

			mLabelPaint.setColor(0xAAFFFFFF);
			canvas.drawText("ENV  10s", 4, h - 3f, mLabelPaint);
		}
	}

	// ─── Спектр-анализатор: FFT 2048 точек ───────────────────────────────────
	// Компактный вид в нижней панели. Логарифмическая шкала частот.
	// Накопительный буфер: когда накоплено >= FFT_SIZE выборок — считаем FFT.
	
	static class SpectrumView extends View {
		private static final int FFT_SIZE = 2048;
		private static final int HALF = FFT_SIZE / 2;
		
		private final float[] mAccBuf = new float[FFT_SIZE];
		private int mAccPos = 0;
		
		private final float[] mMagnitude = new float[HALF]; // последний спектр
		private final float[] mSmooth = new float[HALF];    // сглаженный
		private final float[] mPeaks = new float[HALF];     // пик-холд для спектра
		private final Object mLock = new Object();
		
		// FFT рабочие массивы (переиспользуются)
		private final float[] mFftRe = new float[FFT_SIZE];
		private final float[] mFftIm = new float[FFT_SIZE];
		// Окно Ханна
		private final float[] mWindow = new float[FFT_SIZE];
		
		private final Paint mBarPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mPeakPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mLblPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
		private final Paint mBgPaint = new Paint();
		
		private static final int DISPLAY_BINS = 60; // уменьшено вдвое
		private static final float SAMPLE_RATE = 48000f;
		private static final float DECAY = 0.82f;    // коэффициент спада сглаженного
		private static final float PEAK_DECAY = 0.996f;
		
		SpectrumView(Context c) {
			super(c);
			// Окно Ханна
			for (int i = 0; i < FFT_SIZE; i++)
				mWindow[i] = 0.5f * (1f - (float) Math.cos(2.0 * Math.PI * i / (FFT_SIZE - 1)));
			mBarPaint.setStyle(Paint.Style.FILL);
			mPeakPaint.setStyle(Paint.Style.STROKE);
			mPeakPaint.setColor(0xFFFFFFFF);
			mPeakPaint.setStrokeWidth(1.5f);
			mLblPaint.setColor(0xCCFFFFFF);
			mLblPaint.setTextSize(7.5f * c.getResources().getDisplayMetrics().density);
			mLblPaint.setAntiAlias(true);
			mBgPaint.setColor(0x00000000); // полностью прозрачный фон
		}
		
		/** Получает новый блок PCM-16, микширует в моно, накапливает до FFT_SIZE */
		void pushSamples(short[] buf, int len, int channels) {
			for (int i = 0; i < len; i += channels) {
				float mono = buf[i] / 32768f;
				if (channels == 2 && i + 1 < len)
					mono = (mono + buf[i + 1] / 32768f) * 0.5f;
				mAccBuf[mAccPos++] = mono;
				if (mAccPos >= FFT_SIZE) {
					computeFFT();
					// Перекрытие 50% — сдвигаем буфер
					System.arraycopy(mAccBuf, FFT_SIZE / 2, mAccBuf, 0, FFT_SIZE / 2);
					mAccPos = FFT_SIZE / 2;
				}
			}
		}
		
		private void computeFFT() {
			// Применяем окно Ханна
			for (int i = 0; i < FFT_SIZE; i++) {
				mFftRe[i] = mAccBuf[i] * mWindow[i];
				mFftIm[i] = 0f;
			}
			// Cooley-Tukey in-place radix-2 DIT FFT
			int n = FFT_SIZE;
			for (int i = 1, j = 0; i < n; i++) {
				int bit = n >> 1;
				for (; (j & bit) != 0; bit >>= 1) j ^= bit;
				j ^= bit;
				if (i < j) {
					float tr = mFftRe[i]; mFftRe[i] = mFftRe[j]; mFftRe[j] = tr;
					float ti = mFftIm[i]; mFftIm[i] = mFftIm[j]; mFftIm[j] = ti;
				}
			}
			for (int len = 2; len <= n; len <<= 1) {
				double ang = -2.0 * Math.PI / len;
				float wRe = (float) Math.cos(ang), wIm = (float) Math.sin(ang);
				for (int i = 0; i < n; i += len) {
					float curRe = 1f, curIm = 0f;
					for (int k = 0; k < len / 2; k++) {
						float uRe = mFftRe[i + k], uIm = mFftIm[i + k];
						float vRe = mFftRe[i + k + len/2] * curRe - mFftIm[i + k + len/2] * curIm;
						float vIm = mFftRe[i + k + len/2] * curIm + mFftIm[i + k + len/2] * curRe;
						mFftRe[i + k]         = uRe + vRe;
						mFftIm[i + k]         = uIm + vIm;
						mFftRe[i + k + len/2] = uRe - vRe;
						mFftIm[i + k + len/2] = uIm - vIm;
						float nRe = curRe * wRe - curIm * wIm;
						curIm = curRe * wIm + curIm * wRe;
						curRe = nRe;
					}
				}
			}
			// Вычисляем амплитуду в дБ
			synchronized (mLock) {
				for (int i = 0; i < HALF; i++) {
					float mag = (float) Math.sqrt(mFftRe[i]*mFftRe[i] + mFftIm[i]*mFftIm[i]) / (FFT_SIZE / 2f);
					float db = mag > 1e-9f ? Math.max(-90f, (float)(20.0 * Math.log10(mag))) : -90f;
					// Нормализуем 0..1 (от -90dB до 0dB)
					float norm = (db + 90f) / 90f;
					mMagnitude[i] = norm;
					mSmooth[i] = Math.max(norm, mSmooth[i] * DECAY);
					mPeaks[i] = Math.max(mSmooth[i], mPeaks[i] * PEAK_DECAY);
				}
			}
			postInvalidate();
		}
		
		@Override
		protected void onDraw(Canvas canvas) {
			final float w = getWidth(), h = getHeight();
			if (w == 0 || h == 0) return;

			// Фон полностью прозрачный — не рисуем ничего
			// canvas.drawRect(0, 0, w, h, mBgPaint);

			final float lblH = mLblPaint.getTextSize() + 4f;
			final float barTop   = lblH;            // верхняя полоса зарезервирована под метки
			final float barAreaH = h - barTop;      // высота зоны баров

			float[] freqMarks  = {50, 100, 200, 500, 1000, 2000, 5000, 10000, 20000};
			String[] freqLabels = {"50", "100", "200", "500", "1k", "2k", "5k", "10k", "20k"};
			float fMin = (float) Math.log10(20.0);
			float fMax = (float) Math.log10(SAMPLE_RATE / 2f);

			// Сетка только в зоне баров (ниже полосы меток)
			Paint gridPaint = new Paint();
			gridPaint.setColor(0x44FFFFFF);
			gridPaint.setStrokeWidth(0.8f);
			for (int fi = 0; fi < freqMarks.length; fi++) {
				if (freqMarks[fi] > SAMPLE_RATE / 2f) break;
				float xf = ((float) Math.log10(freqMarks[fi]) - fMin) / (fMax - fMin) * w;
				canvas.drawLine(xf, barTop, xf, h, gridPaint);
			}

			// Полосы спектра
			float[] smooth, peaks;
			synchronized (mLock) {
				smooth = mSmooth.clone();
				peaks  = mPeaks.clone();
			}

			float logFMin  = (float) Math.log10(Math.max(1f, 20f));
			float logFMaxV = (float) Math.log10(SAMPLE_RATE / 2f);

			for (int b = 0; b < DISPLAY_BINS; b++) {
				float logF0 = logFMin + (float) b       / DISPLAY_BINS * (logFMaxV - logFMin);
				float logF1 = logFMin + (float)(b + 1)  / DISPLAY_BINS * (logFMaxV - logFMin);
				float f0 = (float) Math.pow(10.0, logF0);
				float f1 = (float) Math.pow(10.0, logF1);

				int bin0 = Math.max(0,        Math.round(f0 / SAMPLE_RATE * FFT_SIZE));
				int bin1 = Math.min(HALF - 1, Math.round(f1 / SAMPLE_RATE * FFT_SIZE));

				float val = 0f, pk = 0f;
				for (int i = bin0; i <= bin1; i++) {
					if (smooth[i] > val) val = smooth[i];
					if (peaks[i]  > pk)  pk  = peaks[i];
				}

				float x0 = (float) b       / DISPLAY_BINS * w;
				float x1 = (float)(b + 1)  / DISPLAY_BINS * w - 1f;
				if (x1 < x0 + 0.5f) x1 = x0 + 0.5f;

				int red   = Math.min(255, (int)(val * 510f));
				int green = Math.min(255, (int)((1f - val) * 510f));
				mBarPaint.setColor(0xDD000000 | (red << 16) | (green << 8) | 0x22);
				float barH = val * barAreaH;
				canvas.drawRect(x0, h - barH, x1, h, mBarPaint);

				if (pk > 0.02f) {
					float peakY = h - pk * barAreaH;
					canvas.drawLine(x0, peakY, x1, peakY, mPeakPaint);
				}
			}

			// ── Метки частот в верхней полосе (всегда видны) ───────────────
			float labelY = lblH - 4f;
			float prevLblRight = -1f;
			mLblPaint.setTextAlign(Paint.Align.CENTER);
			for (int fi = 0; fi < freqMarks.length; fi++) {
				if (freqMarks[fi] > SAMPLE_RATE / 2f) break;
				float xf = ((float) Math.log10(freqMarks[fi]) - fMin) / (fMax - fMin) * w;
				float lblW = mLblPaint.measureText(freqLabels[fi]);
				float lblX = xf - lblW / 2f;
				if (lblX > prevLblRight && lblX + lblW < w - 2f) {
					canvas.drawText(freqLabels[fi], xf, labelY, mLblPaint);
					prevLblRight = lblX + lblW + 3f;
				}
			}
		}
	}

	// =========================================================================
	// =========================================================================
	// PiP decoder: encoder output → MediaCodec AVC decoder → SurfaceView
	// =========================================================================

	private synchronized void ensurePipDecoder(MediaFormat fmt) {
		if (mPipDecSurface == null) return;
		stopPipDecoder();
		try {
			mPipDec = MediaCodec.createDecoderByType(MediaFormat.MIMETYPE_VIDEO_AVC);
			mPipDec.configure(fmt, mPipDecSurface, null, 0);
			mPipDec.start();
			mPipDecReady = true;
			mPipDecThread = new Thread(this::pipDecodeLoop, "pip-dec");
			mPipDecThread.setDaemon(true);
			mPipDecThread.start();
		} catch (Exception e) {
			mPipDecReady = false;
			if (mPipDec != null) { try { mPipDec.release(); } catch (Exception ignored) {} mPipDec = null; }
		}
	}

	private synchronized void stopPipDecoder() {
		mPipDecReady = false;
		if (mPipDecThread != null) {
			mPipDecThread.interrupt();
			try { mPipDecThread.join(400); } catch (Exception ignored) {}
			mPipDecThread = null;
		}
		if (mPipDec != null) {
			try { mPipDec.stop(); mPipDec.release(); } catch (Exception ignored) {}
			mPipDec = null;
		}
	}

	/** Неблокирующая подача фрейма в PiP-декодер. Вызов из videoPreviewLoop. */
	private void feedToPipDecoder(ByteBuffer data, MediaCodec.BufferInfo info) {
		if (!mPipDecReady || !mEisEnabled) return;
		MediaCodec dec = mPipDec;
		if (dec == null) return;
		try {
			int idx = dec.dequeueInputBuffer(0);
			if (idx < 0) return; // занят — пропускаем кадр
			ByteBuffer inBuf = dec.getInputBuffer(idx);
			inBuf.clear();
			byte[] tmp = new byte[info.size];
			data.position(info.offset);
			data.get(tmp, 0, info.size);
			inBuf.put(tmp, 0, info.size);
			dec.queueInputBuffer(idx, 0, info.size, info.presentationTimeUs, info.flags);
		} catch (Exception ignored) {}
	}

	private void pipDecodeLoop() {
		MediaCodec.BufferInfo info = new MediaCodec.BufferInfo();
		while (!Thread.interrupted() && mPipDecReady) {
			MediaCodec dec = mPipDec;
			if (dec == null) break;
			try {
				int out = dec.dequeueOutputBuffer(info, 20_000);
				if (out >= 0) dec.releaseOutputBuffer(out, true);
			} catch (Exception e) { break; }
		}
	}

	private void startEisOverlay() {
		runOnUiThread(() -> {
			if (mPipView != null) mPipView.setVisibility(View.VISIBLE);
		});
		// Декодер стартует из SurfaceHolder.Callback.surfaceCreated когда surface готов.
		// Если surface уже существует (видимость менялась раньше) — стартуем сразу.
		if (mPipDecSurface != null) {
			MediaFormat fmt;
			synchronized (mVidRingLock) { fmt = mVidOutFmt; }
			if (fmt != null) ensurePipDecoder(fmt);
		}
		if (mCamHandler != null) mCamHandler.post(this::startPreview);
	}

	private void stopEisOverlay() {
		stopPipDecoder();
		runOnUiThread(() -> {
			if (mPipView != null) mPipView.setVisibility(View.GONE);
		});
		if (mCamHandler != null) mCamHandler.post(this::startPreview);
	}

}
