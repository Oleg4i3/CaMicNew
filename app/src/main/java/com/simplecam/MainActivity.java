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

import java.io.File;
import java.nio.ByteBuffer;
import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.LinkedBlockingQueue;
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

	// ─── EIS PiP: маленький SurfaceView, декодирует выход энкодера ──────────────
	// Архитектура: videoPreviewLoop копирует каждый кадр в mPipQueue
	// (не трогая mVidRing и не беря synchronized(this)).
	// Отдельный поток pip-dec читает из очереди, кормит MediaCodec decoder,
	// тот рендерит в маленький SurfaceView. Задержка ≈ 1-3 кадра (encoder lag).
	private SurfaceView    mPipSv;
	private volatile boolean mPipSvReady   = false;
	private Thread         mPipDecThread;
	private volatile boolean mPipDecRunning = false;
	// Очередь: ограничена 90 кадрами (~3 с при 30 fps).
	// Если pip-dec не успевает — offer() возвращает false, старый кадр не теряется,
	// просто новый не добавляется; это нормально для мониторинга.
	private final LinkedBlockingQueue<EncodedFrame> mPipQueue =
		new LinkedBlockingQueue<>(90);
	// Формат от энкодера (содержит CSD: SPS+PPS) — нужен для configure() декодера
	private volatile MediaFormat mPipEncFmt = null;
	
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
	private final java.util.ArrayDeque<EncodedFrame> mVidRing = new java.util.ArrayDeque<>();
	private final java.util.ArrayDeque<EncodedFrame> mAudRing = new java.util.ArrayDeque<>();
	private final Object mVidRingLock = new Object();
	private final Object mAudRingLock = new Object();
	// 0=RING 1=FLUSH 2=LIVE
	private volatile int mVidWriteMode = 0;
	private volatile int mAudWriteMode = 0;
	private volatile long mMuxBasePts  = 0L;
	private volatile MediaFormat mVidOutFmt = null;
	private volatile MediaFormat mAudOutFmt = null;
	private volatile boolean mVidLoopRunning = false;

	// ─── Настройки ───────────────────────────────────────────────────────────
	private volatile int  mVideoBps = VIDEO_BPS_DEFAULT;
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
		showAirplaneModeReminder();
		checkPerms();
	}
	
	private volatile boolean mDestroyed = false;

	@Override
	protected void onResume() {
		super.onResume();
		if (mEisEnabled && mEisSupported) startPipDecoder();
	}

	@Override
	protected void onPause() {
		super.onPause();
		if (mRecording) mRecording = false;
		stopPipDecoder();
	}
	
	@Override
	protected void onDestroy() {
		super.onDestroy();
		mDestroyed = true;
		stopPipDecoder(); // до закрытия энкодера — иначе pip-dec читает мёртвый формат
		if (mCamHandler != null)
			mCamHandler.removeCallbacks(mZoomRunnable);
		mVidLoopRunning = false;
		stopAudio();
		finalizeMuxer();
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
		// Размер буфера SurfaceView = размеру энкодера, ДО surfaceCreated.
		// Если ставить setFixedSize в surfaceCreated — вызывает surfaceDestroyed
		// → surfaceCreated повторно → openCamera() дважды → краш при старте.
		// При одинаковом размере превью и энкодера HAL строит единый EIS-пайплайн
		// и кроп симметрично центрирован. Визуально SurfaceView масштабирует
		// буфер до размеров экрана аппаратно — качество не страдает.
		mSv.getHolder().setFixedSize(VIDEO_W, VIDEO_H);
		mSv.getHolder().addCallback(this);
		FrameLayout.LayoutParams svLP = new FrameLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT);
		svLP.gravity = Gravity.CENTER;
		root.addView(mSv, svLP);

		// ── EIS PiP: маленький SurfaceView, показывает реальный выход стабилизатора
		mPipSv = new SurfaceView(this);
		mPipSv.setVisibility(View.GONE);
		mPipSv.getHolder().addCallback(new SurfaceHolder.Callback() {
			@Override public void surfaceCreated(SurfaceHolder h)               { mPipSvReady = true; }
			@Override public void surfaceChanged(SurfaceHolder h,int f,int w,int t) {}
			@Override public void surfaceDestroyed(SurfaceHolder h)             { mPipSvReady = false; }
		});
		// Рамка: жёлтая = "это то, что пишется в файл"
		GradientDrawable pipBorder = new GradientDrawable();
		pipBorder.setStroke(dp(2), 0xFFFFCC00);
		pipBorder.setColor(0xFF000000);
		mPipSv.setBackground(pipBorder);
		FrameLayout.LayoutParams pipLP = new FrameLayout.LayoutParams(dp(200), dp(113)); // 16:9
		pipLP.gravity    = Gravity.TOP | Gravity.RIGHT;
		pipLP.topMargin  = dp(6);
		pipLP.rightMargin = dp(60); // не перекрывать зум-рычаг
		root.addView(mPipSv, pipLP);

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
		
		mTvStatus = new TextView(this);
		mTvStatus.setTextColor(0xFFAAAAAA);
		mTvStatus.setTextSize(11);
		mTvStatus.setText("Ready");
		mTvStatus.setSingleLine(false);
		mTvStatus.setMaxLines(2);
		mTvStatus.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
		// Шестерёнка слева, статус справа (weight=1)
		panel.addView(hrow(mSrcToggleBtn, mTvStatus));
		
		// Схлопываемая панель: спиннер + soft clip + manual focus
		// Центрируем по экрану — слайдер Gain слева не перекрывает
		mAudioSrcPanel = new LinearLayout(this);
		mAudioSrcPanel.setOrientation(LinearLayout.VERTICAL);
		mAudioSrcPanel.setVisibility(View.GONE);
		mAudioSrcPanel.setPadding(dp(8), dp(4), dp(8), dp(4));
		
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
		mAudioSrcPanel.addView(srcRow);
		
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
		mAudioSrcPanel.addView(cbRow);

		// ── Hardware EIS ─────────────────────────────────────────────────────
		// Чекбокс EIS: блокируется во время записи, чтобы не сбросить стабилизатор
		// и не нарушить синхронизацию кольцевого буфера.
		mCbEis = new CheckBox(this);
		mCbEis.setText("HW EIS");
		mCbEis.setTextColor(0xCCCCCCCC);
		mCbEis.setTextSize(12);
		mCbEis.setEnabled(false); // разблокируется после openCamera, если устройство поддерживает
		mCbEis.setOnCheckedChangeListener((cb, checked) -> {
			if (mRecording) {
				cb.setChecked(!checked);
				status("EIS нельзя изменить во время записи");
				return;
			}
			mEisEnabled = checked;
			if (checked) startPipDecoder();
			else          stopPipDecoder();
			if (mCamHandler != null)
				mCamHandler.post(MainActivity.this::buildAndSendRequest);
		});
		cbRow.addView(mCbEis);

		// Чекбоксы видимости анализаторов
		CheckBox mCbOsc = new CheckBox(this);
		mCbOsc.setText("Oscilloscope");
		mCbOsc.setTextColor(0xCCCCCCCC);
		mCbOsc.setTextSize(12);
		mCbOsc.setChecked(false);
		mCbOsc.setOnCheckedChangeListener((cb, checked) -> {
			if (mOscilloscope != null) mOscilloscope.setVisibility(checked ? View.VISIBLE : View.GONE);
			if (mEnvelope != null) mEnvelope.setVisibility(checked ? View.GONE : View.VISIBLE);
		});

		CheckBox mCbSpec = new CheckBox(this);
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
		mAudioSrcPanel.addView(cbRow2);
		
		// Focus Assist
		mCbFocusAssist = new CheckBox(this);
		mCbFocusAssist.setText("Focus assist (zoom while focusing)");
		mCbFocusAssist.setTextColor(0xCCCCCCCC);
		mCbFocusAssist.setTextSize(12);
		mCbFocusAssist.setVisibility(View.GONE);
		mAudioSrcPanel.addView(mCbFocusAssist);

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
		mAudioSrcPanel.addView(evRow);

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
		mAudioSrcPanel.addView(pbRow);

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
		bpsRow.addView(smallLabel("Bps: ")); bpsRow.addView(spBps);
		mAudioSrcPanel.addView(bpsRow);

		panel.addView(mAudioSrcPanel);

		// ── Строка: спектр-анализатор (слева, weight=1) + кнопка REC (справа) ──
		// REC справа, с отступом rightMargin=58dp чтобы не перекрыть рычаг зума (54dp)
		// Спектр — только анализатор, занимает всю ширину нижней панели
		mSpectrum = new SpectrumView(this);
		LinearLayout.LayoutParams specLP = new LinearLayout.LayoutParams(
			ViewGroup.LayoutParams.MATCH_PARENT, dp(72));
		specLP.rightMargin = dp(120); // не заходить под кнопки REC+PAUSE
		panel.addView(mSpectrum, specLP);

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

		return root;
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
		if (mPermsOk) openCamera();
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
					if (rect != null)
					mSensorRect = rect;
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
								mCbEis.setText("HW EIS");
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
			// ImageReader убран: PiP декодирует из выхода энкодера, а не из camera session

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
			// TEMPLATE_PREVIEW  — по умолчанию: AE не пересчитывается, нет прыжка яркости.
			// TEMPLATE_RECORD   — когда включён EIS: ISP строит EIS-пайплайн
			//   относительно видео-поверхности (encoder surface), а не превью.
			//   Без этого стабилизатор отображает кроп в координатах SurfaceView
			//   и encoder surface получает неправильно смещённый кадр — обрезание
			//   ~30% справа и сверху. TEMPLATE_RECORD устраняет это: камера знает,
			//   что главный выход — видео, и правильно масштабирует EIS-окно.
			//   Прыжка яркости нет, т.к. сессия уже прогрета и AE сходится.
			int tmpl = (mEisEnabled && mEisSupported)
					? CameraDevice.TEMPLATE_RECORD
					: CameraDevice.TEMPLATE_PREVIEW;
			Surface preview = mSv.getHolder().getSurface();
			CaptureRequest.Builder rb = dev.createCaptureRequest(tmpl);
			rb.addTarget(preview);
			if (mEncSurface != null && mEncSurface.isValid())
				rb.addTarget(mEncSurface);
			// ImageReader убран из сессии — PiP читает из энкодера

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
			
			// ── Зум через SCALER_CROP_REGION ──────────────────────────────────────
			// КРИТИЧНО для EIS: при zoom=1.0 НЕ устанавливаем SCALER_CROP_REGION.
			// На многих HAL явная установка full-sensor rect + VIDEO_STABILIZATION_MODE_ON
			// смещает якорь стабилизатора в corner (0,0) вместо центра сенсора.
			// Результат: EIS crop несимметрично обрезает кадр (30-40% справа и сверху).
			// Без явного SCALER_CROP_REGION HAL использует центрированный default.
			// При zoom>1.0 задаём crop явно — стабилизатор работает внутри него.
			if (mSensorRect != null && mZoomLevel > 1.0f) {
				int cropW = Math.max(1, (int)(mSensorRect.width()  / mZoomLevel));
				int cropH = Math.max(1, (int)(mSensorRect.height() / mZoomLevel));
				int cropX = mSensorRect.left + (mSensorRect.width()  - cropW) / 2;
				int cropY = mSensorRect.top  + (mSensorRect.height() - cropH) / 2;
				rb.set(CaptureRequest.SCALER_CROP_REGION,
					new Rect(cropX, cropY, cropX + cropW, cropY + cropH));
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
			synchronized(mVidRingLock) { mVidRing.clear(); }
			synchronized(mAudRingLock) { mAudRing.clear(); }
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
				MediaFormat vf = MediaFormat.createVideoFormat(MediaFormat.MIMETYPE_VIDEO_AVC, VIDEO_W, VIDEO_H);
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
				mPipEncFmt = fmt; // для configure() PiP декодера
				continue;
			}
			if (out < 0) continue;

			try {
				boolean cfg = (info.flags & MediaCodec.BUFFER_FLAG_CODEC_CONFIG) != 0;
				if (cfg || info.size <= 0) continue;
				ByteBuffer data = enc.getOutputBuffer(out);

				int mode = mVidWriteMode;

				if (mode == 0) {
					// ── RING: добавляем в кольцо, обрезаем по mPreBufSecs ──
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
					// Отправляем копию в PiP — offer() не блокирует; если очередь
					// полна (pip-dec отстаёт) — просто пропускаем кадр.
					if (mPipDecRunning) mPipQueue.offer(f);
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
					if (mPipDecRunning) mPipQueue.offer(new EncodedFrame(data, info));
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
		disableAudioEffects(rec.getAudioSessionId());
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

	private void disableAudioEffects(int sid) {
		try { if (AutomaticGainControl.isAvailable()) { AutomaticGainControl a = AutomaticGainControl.create(sid); if (a!=null){a.setEnabled(false);a.release();} } } catch (Exception ignored) {}
		try { if (NoiseSuppressor.isAvailable()) { NoiseSuppressor n = NoiseSuppressor.create(sid); if (n!=null){n.setEnabled(false);n.release();} } } catch (Exception ignored) {}
		try { if (AcousticEchoCanceler.isAvailable()) { AcousticEchoCanceler e = AcousticEchoCanceler.create(sid); if (e!=null){e.setEnabled(false);e.release();} } } catch (Exception ignored) {}
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
		final long startUs = System.nanoTime() / 1000L;
		long totalFrames = 0L;

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
			float peakAmp = 0f;
			for (int i = 0; i < r; i++) { float a = Math.abs(buf[i]) / 32768f; if (a > peakAmp) peakAmp = a; }
			mVu.setPeak(peakAmp);
			mVu.setLevel((float) Math.sqrt((double) sumSq / r) / 32768f);
			if (mOscilloscope != null) mOscilloscope.pushSamples(buf, r, ch);
			if (mEnvelope     != null) mEnvelope.pushSamples(buf, r, ch);
			if (mSpectrum     != null) mSpectrum.pushSamples(buf, r, ch);

			// ── кодируем PCM→AAC ──────────────────────────────────────────────
			MediaCodec enc = mAudEnc;
			if (enc == null) continue;
			// PTS: абсолютный System.nanoTime (мкс) — тот же домен, что у видео
			long pts = startUs + totalFrames * 1_000_000L / AUDIO_SR;
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

			// ── Вычисляем mMuxBasePts по первому I-frame в видео-кольце ───────
			long basePts;
			synchronized(mVidRingLock) {
				if (mPreBufferEnabled) {
					basePts = Long.MAX_VALUE;
					for (EncodedFrame f : mVidRing) {
						if (f.isKey()) { basePts = f.pts; break; }
					}
					if (basePts == Long.MAX_VALUE) basePts = 0;
				} else {
					// Без пре-буфера: берём PTS следующего I-frame (придёт через ≤1 с)
					// Пока ждём его — просто ставим текущее время
					basePts = System.nanoTime() / 1000L;
				}
			}
			mMuxBasePts = basePts;

			// ── Создаём MediaStore-запись ──────────────────────────────────────
			String displayPath;
			if (Build.VERSION.SDK_INT >= 29) {
				ContentValues cv = new ContentValues();
				cv.put(MediaStore.Video.Media.DISPLAY_NAME, "VID_" + System.currentTimeMillis() + ".mp4");
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
				File f = new File(dir, "VID_" + System.currentTimeMillis() + ".mp4");
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

			// ── Переводим потоки в режим FLUSH → они сами сбросят кольца ──────
			mRecording = true;
			if (mPreBufferEnabled) {
				mVidWriteMode = 1; // FLUSH
				mAudWriteMode = 1; // FLUSH
			} else {
				mVidWriteMode = 2; // LIVE сразу
				mAudWriteMode = 2;
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
			mRecording = false; mVidWriteMode = 0; mAudWriteMode = 0;
			finalizeMuxer();
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
		mVidWriteMode = 0; mAudWriteMode = 0; // обратно в RING
		finalizeMuxer();
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
	
	private void buildAudioSources() {
		List<AudioSrcItem> list = new ArrayList<>();
		if (Build.VERSION.SDK_INT >= 23) {
			AudioManager am = (AudioManager) getSystemService(AUDIO_SERVICE);
			AudioDeviceInfo[] devs = am.getDevices(AudioManager.GET_DEVICES_INPUTS);
			boolean hasBuiltin = false;
			for (AudioDeviceInfo d : devs) {
				int t = d.getType();
				if (t == AudioDeviceInfo.TYPE_BUILTIN_MIC) {
					if (hasBuiltin)
					continue;
					hasBuiltin = true;
					list.add(new AudioSrcItem("Built-in mic", MediaRecorder.AudioSource.MIC, d));
					if (Build.VERSION.SDK_INT >= 24)
					list.add(new AudioSrcItem("Built-in mic (raw)", MediaRecorder.AudioSource.UNPROCESSED, d));
					} else if (t == AudioDeviceInfo.TYPE_USB_DEVICE || t == AudioDeviceInfo.TYPE_USB_HEADSET) {
					CharSequence pn = d.getProductName();
					list.add(new AudioSrcItem("USB: " + (pn != null && pn.length() > 0 ? pn : "audio"),
					MediaRecorder.AudioSource.MIC, d));
					} else if (t == AudioDeviceInfo.TYPE_WIRED_HEADSET) {
					list.add(new AudioSrcItem("Wired headset", MediaRecorder.AudioSource.MIC, d));
					} else if (t == AudioDeviceInfo.TYPE_BLUETOOTH_SCO) {
					list.add(new AudioSrcItem("Bluetooth mic", MediaRecorder.AudioSource.MIC, d));
				}
			}
		}
		if (list.isEmpty()) {
			list.add(new AudioSrcItem("Default", MediaRecorder.AudioSource.DEFAULT, null));
			list.add(new AudioSrcItem("Microphone", MediaRecorder.AudioSource.MIC, null));
			list.add(new AudioSrcItem("Camcorder", MediaRecorder.AudioSource.CAMCORDER, null));
			list.add(new AudioSrcItem("Communication", MediaRecorder.AudioSource.VOICE_COMMUNICATION, null));
			if (Build.VERSION.SDK_INT >= 24)
			list.add(new AudioSrcItem("Unprocessed (raw)", MediaRecorder.AudioSource.UNPROCESSED, null));
		}
		runOnUiThread(() -> {
			mSrcList.clear();
			mSrcList.addAll(list);
			List<String> names = new ArrayList<>();
			for (AudioSrcItem item : mSrcList)
			names.add(item.name);
			@SuppressWarnings("unchecked")
			ArrayAdapter<String> ad2 = (ArrayAdapter<String>) mSpinner.getAdapter();
			ad2.clear();
			ad2.addAll(names);
			ad2.notifyDataSetChanged();
			
			int defaultIdx = 0;
			for (int i = 0; i < mSrcList.size(); i++) {
				AudioSrcItem item = mSrcList.get(i);
				if (item.device != null && Build.VERSION.SDK_INT >= 23) {
					int t = item.device.getType();
					if (t == AudioDeviceInfo.TYPE_USB_DEVICE || t == AudioDeviceInfo.TYPE_USB_HEADSET) {
						defaultIdx = i;
						break;
					}
				}
			}
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
	}
	
	// =========================================================================
	// Вспомогательные классы
	// =========================================================================
	
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
		private static final float FULL_RANGE_PX_PER_UNIT = 800f;
		
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
		private static final float SAMPLE_RATE = 44100f;
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
	// EIS PiP — декодер из выхода энкодера
	// =========================================================================

	/**
	 * Запускает pip-dec поток и показывает мини-превью.
	 * Безопасно вызывать несколько раз подряд — idempotent.
	 */
	private void startPipDecoder() {
		if (mPipDecRunning) return;
		mPipQueue.clear();
		mPipDecRunning = true;
		runOnUiThread(() -> { if (mPipSv != null) mPipSv.setVisibility(View.VISIBLE); });
		mPipDecThread = new Thread(this::pipDecLoop, "pip-dec");
		mPipDecThread.setDaemon(true);
		mPipDecThread.start();
	}

	/**
	 * Останавливает pip-dec поток и скрывает мини-превью.
	 * Безопасно вызывать несколько раз и из любого потока.
	 */
	private void stopPipDecoder() {
		if (!mPipDecRunning) return;
		mPipDecRunning = false;
		// Будим поток, если он висит в poll()
		mPipQueue.offer(new EncodedFrame(ByteBuffer.allocate(0),
			new MediaCodec.BufferInfo())); // пустой sentinel
		if (mPipDecThread != null) {
			try { mPipDecThread.join(500); } catch (InterruptedException ignored) {}
			mPipDecThread = null;
		}
		mPipQueue.clear();
		runOnUiThread(() -> { if (mPipSv != null) mPipSv.setVisibility(View.GONE); });
	}

	/**
	 * Главный цикл pip-dec потока.
	 *
	 * Алгоритм:
	 *  1. Ждём пока SurfaceHolder и mPipEncFmt будут готовы.
	 *  2. Конфигурируем MediaCodec-декодер с поверхностью PiP SurfaceView.
	 *  3. В цикле: берём кадр из очереди → queueInputBuffer → dequeueOutputBuffer
	 *     с render=true → декодер сам рисует на поверхность.
	 *  4. При остановке (mPipDecRunning=false) — нормальное завершение.
	 *
	 * Нет shared locks с основным пайплайном. EncodedFrame — immutable byte[].
	 */
	private void pipDecLoop() {
		// Шаг 1: ждём формат и Surface (максимум 5 с)
		MediaFormat fmt = null;
		for (int i = 0; i < 100 && mPipDecRunning; i++) {
			fmt = mPipEncFmt;
			if (fmt != null && mPipSvReady) break;
			try { Thread.sleep(50); } catch (InterruptedException e) { return; }
		}
		if (fmt == null || !mPipSvReady || !mPipDecRunning) return;

		MediaCodec dec = null;
		try {
			Surface outSurface = mPipSv.getHolder().getSurface();
			dec = MediaCodec.createDecoderByType(MediaFormat.MIMETYPE_VIDEO_AVC);
			dec.configure(fmt, outSurface, null, 0);
			dec.start();

			MediaCodec.BufferInfo outInfo = new MediaCodec.BufferInfo();
			boolean inputDone = false;

			while (mPipDecRunning) {
				// ── Input: берём кадр из очереди ─────────────────────────────
				if (!inputDone) {
					EncodedFrame frame = mPipQueue.poll(30, TimeUnit.MILLISECONDS);
					if (frame != null && frame.data.length > 0) {
						int idx = dec.dequeueInputBuffer(0);
						if (idx >= 0) {
							ByteBuffer inBuf = dec.getInputBuffer(idx);
							if (inBuf != null) {
								inBuf.clear();
								inBuf.put(frame.data);
								dec.queueInputBuffer(idx, 0, frame.data.length,
									frame.pts, frame.flags & ~MediaCodec.BUFFER_FLAG_CODEC_CONFIG);
							} else {
								dec.releaseInputBuffer(idx);
							}
						}
						// Если idx < 0 — декодер занят, кадр теряем (нормально для PiP)
					}
				}

				// ── Output: рендерим готовые кадры ────────────────────────────
				int outIdx = dec.dequeueOutputBuffer(outInfo, 0);
				while (outIdx >= 0) {
					dec.releaseOutputBuffer(outIdx, /*render=*/true);
					outIdx = dec.dequeueOutputBuffer(outInfo, 0);
				}
				// INFO_OUTPUT_FORMAT_CHANGED / INFO_TRY_AGAIN_LATER — игнорируем
			}
		} catch (Exception e) {
			// Тихо завершаем — это некритичный монитор
		} finally {
			if (dec != null) {
				try { dec.stop(); }    catch (Exception ignored) {}
				try { dec.release(); } catch (Exception ignored) {}
			}
		}
	}

}
