package com.simplecam;

import android.Manifest;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.content.Context;
import android.content.pm.PackageManager;
import android.graphics.*;
import android.graphics.drawable.GradientDrawable;
import android.hardware.camera2.*;
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

public class MainActivity extends Activity implements SurfaceHolder.Callback {

private static final int VIDEO_W = 1280;
private static final int VIDEO_H = 720;
private static final int VIDEO_BPS_DEFAULT = 6_000_000;
private static final int VIDEO_FPS = 30;
private static final int AUDIO_SR = 48000;
private static final int REQ_PERMS = 1;
private static final float MAX_ZOOM_SPEED = 0.08f;
private static final long EIS_LATENCY_US = 500_000L;

private SurfaceView mSv;
private Spinner mSpinner;
private VerticalSeekBar mSeekGain;
private FocusDrumView mFocusDrum;
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
private View mFocusColumn;

private volatile float mSavedZoomBeforeAssist = 1f;
private Handler mFocusAssistHandler;

private GradientDrawable mBtnBgIdle, mBtnBgRec;

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

private volatile boolean mManualFocus = false;
private volatile float mFocusValue = 0f;
private float mMinFocusDist = 0f;

private volatile boolean mEisEnabled  = false;
private volatile boolean mEisSupported = false;

private SurfaceView mMonitorView;
private SurfaceHolder mMonitorHolder;
private MediaCodec mPreviewDecoder;
private volatile boolean mPreviewDecoderReady = false;

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

private Uri mPendingUri;
private ParcelFileDescriptor mPfd;

private final List<AudioSrcItem> mSrcList = new ArrayList<>();

private volatile boolean mAudRunning;

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
private volatile int mVidWriteMode = 0;
private volatile int mAudWriteMode = 0;
private volatile long mMuxBasePts  = 0L;
private volatile MediaFormat mVidOutFmt = null;
private volatile MediaFormat mAudOutFmt = null;
private volatile boolean mVidLoopRunning = false;

private volatile int  mVideoBps = VIDEO_BPS_DEFAULT;
private volatile int  mPreBufSecs = 1;
private volatile boolean mPreBufferEnabled = true;
private volatile int  mEvComp = 0;
private int mEvMin = -6, mEvMax = 6;
private SeekBar mSeekEv;
private TextView mTvEv;

private final Runnable mZoomRunnable = new Runnable() {
@Override
public void run() {
float lever = mZoomLeverPos;
if (Math.abs(lever) > 0.02f) {
float abs = Math.abs(lever);
float speed = (float) ((Math.exp(abs * 3.0) - 1.0) / (Math.exp(3.0) - 1.0)) * MAX_ZOOM_SPEED * Math.signum(lever);
mZoomLevel = Math.max(1f, Math.min(mMaxZoom, mZoomLevel + speed));
buildAndSendRequest();
}
if (mCamHandler != null) mCamHandler.postDelayed(this, 33);
}
};

@Override
protected void onCreate(Bundle saved) {
super.onCreate(saved);
getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON | WindowManager.LayoutParams.FLAG_FULLSCREEN);
mFocusAssistHandler = new Handler(Looper.getMainLooper());
setContentView(buildLayout());
mCamMgr = (CameraManager) getSystemService(CAMERA_SERVICE);
showAirplaneModeReminder();
checkPerms();
}

@Override protected void onResume() { super.onResume(); }
@Override protected void onPause() { super.onPause(); if (mRecording) mRecording = false; }
@Override protected void onDestroy() {
super.onDestroy();
if (mCamHandler != null) mCamHandler.removeCallbacks(mZoomRunnable);
mVidLoopRunning = false;
stopAudio();
finalizeMuxer();
if (mVidEnc!=null){try{mVidEnc.stop();mVidEnc.release();}catch(Exception e){} mVidEnc=null;}
if (mEncSurface!=null){try{mEncSurface.release();}catch(Exception e){} mEncSurface=null;}
try { if (mCapSess != null) mCapSess.close(); } catch (Exception ignored) {}
try { if (mCamDev != null) mCamDev.close(); } catch (Exception ignored) {}
if (mCamThread != null) mCamThread.quitSafely();
}

private View buildLayout() {
FrameLayout root = new FrameLayout(this);
root.setBackgroundColor(Color.BLACK);

mSv = new SurfaceView(this) {
@Override
protected void onMeasure(int wMs, int hMs) {
int w = MeasureSpec.getSize(wMs);
int h = MeasureSpec.getSize(hMs);
int targetH = w * 9 / 16;
if (targetH > h) {
int targetW = h * 16 / 9;
super.onMeasure(MeasureSpec.makeMeasureSpec(targetW, MeasureSpec.EXACTLY), MeasureSpec.makeMeasureSpec(h, MeasureSpec.EXACTLY));
} else {
super.onMeasure(MeasureSpec.makeMeasureSpec(w, MeasureSpec.EXACTLY), MeasureSpec.makeMeasureSpec(targetH, MeasureSpec.EXACTLY));
}
}
};
mSv.getHolder().addCallback(this);
root.addView(mSv, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT, Gravity.CENTER));

mMonitorView = new SurfaceView(this);
mMonitorView.setZOrderMediaOverlay(true);
FrameLayout.LayoutParams monLP = new FrameLayout.LayoutParams(dp(110), dp(80));
monLP.gravity = Gravity.TOP | Gravity.RIGHT;
monLP.topMargin = dp(10); monLP.rightMargin = dp(10);
root.addView(mMonitorView, monLP);
mMonitorHolder = mMonitorView.getHolder();
mMonitorHolder.addCallback(new SurfaceHolder.Callback() {
@Override public void surfaceCreated(SurfaceHolder holder) {
if (mRecording && !mPreviewDecoderReady) startPreviewDecoderIfNeeded();
}
@Override public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {}
@Override public void surfaceDestroyed(SurfaceHolder holder) {
if (mPreviewDecoder != null) {
try { mPreviewDecoder.stop(); mPreviewDecoder.release(); } catch (Exception e) {}
mPreviewDecoder = null;
}
mPreviewDecoderReady = false;
}
});
mMonitorView.setVisibility(View.GONE);

mOscilloscope = new OscilloscopeView(this);
FrameLayout.LayoutParams oscLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(130));
oscLP.gravity = Gravity.TOP | Gravity.LEFT;
oscLP.leftMargin = dp(50); oscLP.rightMargin = dp(60); oscLP.topMargin = dp(6);
root.addView(mOscilloscope, oscLP);
mOscilloscope.setVisibility(View.GONE);

mEnvelope = new EnvelopeView(this);
FrameLayout.LayoutParams envLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(130));
envLP.gravity = Gravity.TOP | Gravity.LEFT;
envLP.leftMargin = dp(50); envLP.rightMargin = dp(60); envLP.topMargin = dp(6);
root.addView(mEnvelope, envLP);

mBtnBgIdle = makeOval(0xFFDDCC00);
mBtnBgRec = makeOval(0xFFCC1100);
mBtnBgPause = makeOval(0xFF1155CC);

LinearLayout outer = new LinearLayout(this);
outer.setOrientation(LinearLayout.VERTICAL);
root.addView(outer, mp_mp());

FrameLayout content = new FrameLayout(this);
outer.addView(content, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f));

mSeekGain = new VerticalSeekBar(this);
mSeekGain.setMax(800);
mSeekGain.setProgress(400);
mSeekGain.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
public void onProgressChanged(SeekBar s, int p, boolean u) {
float db = -20f + p * 40f / 800f;
mGain = (float) Math.pow(10.0, db / 20.0);
if (mTvGain != null) mTvGain.setText(String.format("%+.1f", db) + "dB");
}
public void onStartTrackingTouch(SeekBar s) {}
public void onStopTrackingTouch(SeekBar s) {}
});
root.addView(mSeekGain, new FrameLayout.LayoutParams(dp(44), ViewGroup.LayoutParams.MATCH_PARENT, Gravity.LEFT));

TextView tvGainLbl = smallLabel("GAIN");
FrameLayout.LayoutParams gainLblLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
gainLblLP.gravity = Gravity.LEFT | Gravity.TOP; gainLblLP.leftMargin = dp(6); gainLblLP.topMargin = dp(4);
root.addView(tvGainLbl, gainLblLP);

mTvGain = smallLabel("+0.0dB");
FrameLayout.LayoutParams gainValLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
gainValLP.gravity = Gravity.LEFT | Gravity.BOTTOM; gainValLP.leftMargin = dp(3); gainValLP.bottomMargin = dp(169);
root.addView(mTvGain, gainValLP);

mVu = new VuMeterView(this);
FrameLayout.LayoutParams vuVertLP = new FrameLayout.LayoutParams(dp(14), ViewGroup.LayoutParams.MATCH_PARENT);
vuVertLP.gravity = Gravity.LEFT; vuVertLP.leftMargin = dp(44);
root.addView(mVu, vuVertLP);

LinearLayout rightCol = new LinearLayout(this);
rightCol.setOrientation(LinearLayout.HORIZONTAL);
FrameLayout.LayoutParams rightColLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.MATCH_PARENT);
rightColLP.gravity = Gravity.RIGHT;
root.addView(rightCol, rightColLP);

mFocusColumn = buildFocusColumn();
mFocusColumn.setVisibility(View.GONE);
rightCol.addView(mFocusColumn, new LinearLayout.LayoutParams(dp(44), ViewGroup.LayoutParams.MATCH_PARENT));

mZoomLever = new ZoomLeverView(this);
mZoomLever.setListener(pos -> mZoomLeverPos = pos);
rightCol.addView(mZoomLever, new LinearLayout.LayoutParams(dp(54), ViewGroup.LayoutParams.MATCH_PARENT));

LinearLayout panel = new LinearLayout(this);
panel.setOrientation(LinearLayout.VERTICAL);
panel.setBackgroundColor(0x00000000);
panel.setPadding(dp(62), dp(2), dp(8), dp(3));
outer.addView(panel, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));

mSrcToggleBtn = new Button(this);
mSrcToggleBtn.setText("⚙"); mSrcToggleBtn.setAllCaps(false); mSrcToggleBtn.setTextSize(28);
mSrcToggleBtn.setTextColor(0xFFBBBBBB); mSrcToggleBtn.setBackground(null);
mSrcToggleBtn.setPadding(0, 0, dp(8), 0);
mSrcToggleBtn.setOnClickListener(v -> {
mAudioSrcExpanded = !mAudioSrcExpanded;
mAudioSrcPanel.setVisibility(mAudioSrcExpanded ? View.VISIBLE : View.GONE);
mSrcToggleBtn.setText(mAudioSrcExpanded ? "⚙ ▴" : "⚙");
});

mTvStatus = new TextView(this);
mTvStatus.setTextColor(0xFFAAAAAA); mTvStatus.setTextSize(11);
mTvStatus.setText("Ready"); mTvStatus.setSingleLine(false); mTvStatus.setMaxLines(2);
mTvStatus.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f));
panel.addView(hrow(mSrcToggleBtn, mTvStatus));

mAudioSrcPanel = new LinearLayout(this);
mAudioSrcPanel.setOrientation(LinearLayout.VERTICAL);
mAudioSrcPanel.setVisibility(View.GONE);
mAudioSrcPanel.setPadding(dp(8), dp(4), dp(8), dp(4));

mSpinner = new Spinner(this);
ArrayAdapter<String> ad = new ArrayAdapter<>(this, android.R.layout.simple_spinner_item, new ArrayList<String>());
ad.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item);
mSpinner.setAdapter(ad);
mSpinner.setLayoutParams(new LinearLayout.LayoutParams(dp(200), ViewGroup.LayoutParams.WRAP_CONTENT));
mSpinner.setOnItemSelectedListener(new AdapterView.OnItemSelectedListener() {
@Override public void onItemSelected(AdapterView<?> p, View v, int pos, long id) { if (!mRecording) { stopAudio(); startMonitor(); } }
@Override public void onNothingSelected(AdapterView<?> p) {}
});

LinearLayout srcRow = new LinearLayout(this);
srcRow.setOrientation(LinearLayout.HORIZONTAL); srcRow.setGravity(Gravity.CENTER_VERTICAL);
srcRow.addView(smallLabel("Src: ")); srcRow.addView(mSpinner);
mAudioSrcPanel.addView(srcRow);

mCbSoftClip = new CheckBox(this);
mCbSoftClip.setText("Soft clip"); mCbSoftClip.setTextColor(0xCCCCCCCC); mCbSoftClip.setTextSize(12);
mCbSoftClip.setChecked(true); mSoftClip = true;
mCbSoftClip.setOnCheckedChangeListener((cb, checked) -> mSoftClip = checked);

mCbManualFocus = new CheckBox(this);
mCbManualFocus.setText("Manual focus"); mCbManualFocus.setTextColor(0xCCCCCCCC); mCbManualFocus.setTextSize(12);
mCbManualFocus.setOnCheckedChangeListener((cb, checked) -> {
mManualFocus = checked;
mFocusColumn.setVisibility(checked ? View.VISIBLE : View.GONE);
if (mCbFocusAssist != null) mCbFocusAssist.setVisibility(checked ? View.VISIBLE : View.GONE);
if (!checked) { if (mFocusAssistHandler != null) mFocusAssistHandler.removeCallbacksAndMessages(null); }
if (mCamHandler != null) mCamHandler.post(this::buildAndSendRequest);
});

LinearLayout cbRow = new LinearLayout(this);
cbRow.setOrientation(LinearLayout.HORIZONTAL); cbRow.setGravity(Gravity.CENTER_VERTICAL);
cbRow.addView(mCbSoftClip); cbRow.addView(mCbManualFocus);
mAudioSrcPanel.addView(cbRow);

mCbEis = new CheckBox(this);
mCbEis.setText("HW EIS"); mCbEis.setTextColor(0xCCCCCCCC); mCbEis.setTextSize(12);
mCbEis.setEnabled(false);
mCbEis.setOnCheckedChangeListener((cb, checked) -> {
if (mRecording) { cb.setChecked(!checked); status("EIS нельзя изменить во время записи"); return; }
mEisEnabled = checked;
if (mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest);
});
cbRow.addView(mCbEis);

CheckBox mCbOsc = new CheckBox(this);
mCbOsc.setText("Oscilloscope"); mCbOsc.setTextColor(0xCCCCCCCC); mCbOsc.setTextSize(12); mCbOsc.setChecked(false);
mCbOsc.setOnCheckedChangeListener((cb, checked) -> {
if (mOscilloscope != null) mOscilloscope.setVisibility(checked ? View.VISIBLE : View.GONE);
if (mEnvelope != null) mEnvelope.setVisibility(checked ? View.GONE : View.VISIBLE);
});

CheckBox mCbSpec = new CheckBox(this);
mCbSpec.setText("Spectrum analyzer"); mCbSpec.setTextColor(0xCCCCCCCC); mCbSpec.setTextSize(12); mCbSpec.setChecked(true);
mCbSpec.setOnCheckedChangeListener((cb, checked) -> { if (mSpectrum != null) mSpectrum.setVisibility(checked ? View.VISIBLE : View.GONE); });

LinearLayout cbRow2 = new LinearLayout(this);
cbRow2.setOrientation(LinearLayout.HORIZONTAL); cbRow2.setGravity(Gravity.CENTER_VERTICAL);
cbRow2.addView(mCbOsc); cbRow2.addView(mCbSpec);
mAudioSrcPanel.addView(cbRow2);

mCbFocusAssist = new CheckBox(this);
mCbFocusAssist.setText("Focus assist (zoom while focusing)"); mCbFocusAssist.setTextColor(0xCCCCCCCC); mCbFocusAssist.setTextSize(12);
mCbFocusAssist.setVisibility(View.GONE);
mAudioSrcPanel.addView(mCbFocusAssist);

mTvEv = smallLabel("EV  0");
mSeekEv = new SeekBar(this);
mSeekEv.setMax(mEvMax - mEvMin); mSeekEv.setProgress(-mEvMin);
mSeekEv.setLayoutParams(new LinearLayout.LayoutParams(dp(160), ViewGroup.LayoutParams.WRAP_CONTENT));
mSeekEv.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
public void onProgressChanged(SeekBar s, int p, boolean u) { mEvComp = mEvMin + p; updateEvLabel(mEvComp); if (mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest); }
public void onStartTrackingTouch(SeekBar s) {}
public void onStopTrackingTouch(SeekBar s) {}
});
LinearLayout evRow = new LinearLayout(this);
evRow.setOrientation(LinearLayout.HORIZONTAL); evRow.setGravity(Gravity.CENTER_VERTICAL);
evRow.addView(mTvEv); evRow.addView(mSeekEv);
mAudioSrcPanel.addView(evRow);

CheckBox cbPB = new CheckBox(this);
cbPB.setText("Pre-buffer"); cbPB.setTextColor(0xCCCCCCCC); cbPB.setTextSize(12); cbPB.setChecked(true);
cbPB.setOnCheckedChangeListener((cb, on) -> mPreBufferEnabled = on);
final TextView tvPBLen = smallLabel("1 s");
SeekBar sbPB = new SeekBar(this);
sbPB.setMax(4); sbPB.setProgress(0);
sbPB.setLayoutParams(new LinearLayout.LayoutParams(dp(110), ViewGroup.LayoutParams.WRAP_CONTENT));
sbPB.setOnSeekBarChangeListener(new SeekBar.OnSeekBarChangeListener() {
public void onProgressChanged(SeekBar s, int p, boolean u) { mPreBufSecs = p + 1; tvPBLen.setText(mPreBufSecs + " s"); }
public void onStartTrackingTouch(SeekBar s) {}
public void onStopTrackingTouch(SeekBar s) {}
});
LinearLayout pbRow = new LinearLayout(this);
pbRow.setOrientation(LinearLayout.HORIZONTAL); pbRow.setGravity(Gravity.CENTER_VERTICAL);
pbRow.addView(cbPB); pbRow.addView(sbPB); pbRow.addView(tvPBLen);
mAudioSrcPanel.addView(pbRow);

String[] bpsL={"500 kbps","1 Mbps","2 Mbps","3 Mbps","4 Mbps","6 Mbps (def)","8 Mbps","12 Mbps"};
int[] bpsV={500_000,1_000_000,2_000_000,3_000_000,4_000_000,6_000_000,8_000_000,12_000_000};
Spinner spBps = new Spinner(this);
ArrayAdapter<String> bpsAd = new ArrayAdapter<>(this, android.R.layout.simple_spinner_item, bpsL);
bpsAd.setDropDownViewResource(android.R.layout.simple_spinner_dropdown_item);
spBps.setAdapter(bpsAd); spBps.setSelection(5);
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

mSpectrum = new SpectrumView(this);
LinearLayout.LayoutParams specLP = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dp(72));
specLP.rightMargin = dp(120);
panel.addView(mSpectrum, specLP);

int recSize = dp(68), recRight = dp(62), recBottom = dp(8);

mBtn = new Button(this);
mBtn.setText("REC"); mBtn.setTextColor(Color.WHITE); mBtn.setTextSize(13);
mBtn.setBackground(mBtnBgIdle);
mBtn.setOnClickListener(v -> onRecordClick());
FrameLayout.LayoutParams recLP = new FrameLayout.LayoutParams(recSize, recSize);
recLP.gravity = Gravity.BOTTOM | Gravity.RIGHT; recLP.rightMargin = recRight; recLP.bottomMargin = recBottom;
root.addView(mBtn, recLP);

mBtnPause = new Button(this);
mBtnPause.setText("⏸"); mBtnPause.setTextColor(Color.WHITE); mBtnPause.setTextSize(16);
mBtnPause.setBackground(mBtnBgPause); mBtnPause.setVisibility(View.GONE);
mBtnPause.setOnClickListener(v -> onPauseClick());
FrameLayout.LayoutParams pauseLP = new FrameLayout.LayoutParams(dp(44), dp(44));
pauseLP.gravity = Gravity.BOTTOM | Gravity.RIGHT;
pauseLP.rightMargin = recRight + (recSize - dp(44)) / 2;
pauseLP.bottomMargin = recBottom + recSize + dp(6);
root.addView(mBtnPause, pauseLP);

return root;
}

private View buildFocusColumn() {
FrameLayout col = new FrameLayout(this); col.setBackgroundColor(0x33000000);
mFocusDrum = new FocusDrumView(this);
mFocusDrum.setOnFocusChangeListener(value -> { mFocusValue = value; updateFocusLabel(value); if (mManualFocus && mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest); });
mFocusDrum.setOnDrumScrollListener(new FocusDrumView.OnDrumScrollListener() {
@Override public void onScrollStart() { if (mCbFocusAssist == null || !mCbFocusAssist.isChecked()) return; mFocusAssistHandler.removeCallbacksAndMessages(null); mSavedZoomBeforeAssist = mZoomLevel; float assistZoom = Math.min(mMaxZoom, Math.max(mZoomLevel * 3f, 4f)); mZoomLevel = assistZoom; if (mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest); }
@Override public void onScrollStop() { if (mCbFocusAssist == null || !mCbFocusAssist.isChecked()) return; mFocusAssistHandler.removeCallbacksAndMessages(null); mFocusAssistHandler.postDelayed(() -> { mZoomLevel = mSavedZoomBeforeAssist; if (mCamHandler != null) mCamHandler.post(MainActivity.this::buildAndSendRequest); }, 300); }
});
FrameLayout.LayoutParams drumLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT); col.addView(mFocusDrum, drumLP);
TextView tvTop = smallLabel("∞"); FrameLayout.LayoutParams topLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT); topLP.gravity = Gravity.TOP | Gravity.CENTER_HORIZONTAL; topLP.topMargin = dp(4); col.addView(tvTop, topLP);
TextView tvBot = smallLabel("▲"); FrameLayout.LayoutParams botLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT); botLP.gravity = Gravity.BOTTOM | Gravity.CENTER_HORIZONTAL; botLP.bottomMargin = dp(4); col.addView(tvBot, botLP);
mTvFocus = smallLabel("∞"); FrameLayout.LayoutParams midLP = new FrameLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT); midLP.gravity = Gravity.CENTER; col.addView(mTvFocus, midLP);
return col;
}

private void updateFocusLabel(float value) { if (mTvFocus == null) return; String txt = value < 0.005f ? "∞" : String.format("%.1f", value * mMinFocusDist) + "m⁻¹"; mTvFocus.setText(txt); }
private void updateEvLabel(int ev) { if (mTvEv == null) return; runOnUiThread(() -> mTvEv.setText(ev == 0 ? "EV  0" : String.format("EV %+d", ev))); }
private GradientDrawable makeOval(int color) { GradientDrawable d = new GradientDrawable(); d.setShape(GradientDrawable.OVAL); d.setColor(color); return d; }
private TextView smallLabel(String t) { TextView v = new TextView(this); v.setText(t); v.setTextColor(0xCCCCCCCC); v.setTextSize(11); v.setBackgroundColor(0x88000000); v.setPadding(dp(3), dp(1), dp(3), dp(1)); return v; }
private LinearLayout hrow(View... views) { LinearLayout ll = new LinearLayout(this); ll.setOrientation(LinearLayout.HORIZONTAL); ll.setGravity(Gravity.CENTER_VERTICAL); LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT); lp.bottomMargin = dp(2); ll.setLayoutParams(lp); for (View v : views) { if (v.getLayoutParams() == null) v.setLayoutParams(new LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT)); ll.addView(v); } return ll; }
private ViewGroup.LayoutParams mp_mp() { return new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT); }
private int dp(int x) { return Math.round(x * getResources().getDisplayMetrics().density); }

private void showAirplaneModeReminder() {
new android.app.AlertDialog.Builder(this)
.setTitle("\u2708  Airplane Mode recommended")
.setMessage("For distraction-free recording:\n\n\u2022  Turn on Airplane Mode\n\nThis prevents calls, notifications and Wi-Fi interruptions during recording.\n\n(Screen will stay on while the app is open.)")
.setPositiveButton("Got it", null)
.setNeutralButton("Open Settings", (d, w) -> { try { startActivity(new android.content.Intent(android.provider.Settings.ACTION_AIRPLANE_MODE_SETTINGS)); } catch (Exception ignored) {} })
.show();
}

private void checkPerms() {
List<String> need = new ArrayList<>();
if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) need.add(Manifest.permission.CAMERA);
if (checkSelfPermission(Manifest.permission.RECORD_AUDIO) != PackageManager.PERMISSION_GRANTED) need.add(Manifest.permission.RECORD_AUDIO);
if (need.isEmpty()) { mPermsOk = true; if (mSurfaceReady) openCamera(); }
else requestPermissions(need.toArray(new String[0]), REQ_PERMS);
}

@Override
public void onRequestPermissionsResult(int req, String[] perms, int[] res) {
for (int r : res) { if (r != PackageManager.PERMISSION_GRANTED) { status("Permissions required"); return; } }
mPermsOk = true; if (mSurfaceReady) openCamera();
}

@Override public void surfaceCreated(SurfaceHolder h) { mSurfaceReady = true; if (mPermsOk) openCamera(); }
@Override public void surfaceChanged(SurfaceHolder h, int f, int w, int t) {}
@Override public void surfaceDestroyed(SurfaceHolder h) { mSurfaceReady = false; }

@SuppressLint("MissingPermission")
private void openCamera() {
if (mCamThread == null || !mCamThread.isAlive()) { mCamThread = new HandlerThread("cam"); mCamThread.start(); mCamHandler = new Handler(mCamThread.getLooper()); }
try {
String camId = null;
for (String id : mCamMgr.getCameraIdList()) {
CameraCharacteristics ch = mCamMgr.getCameraCharacteristics(id);
Integer facing = ch.get(CameraCharacteristics.LENS_FACING);
if (facing != null && facing == CameraCharacteristics.LENS_FACING_BACK) {
camId = id;
Integer so = ch.get(CameraCharacteristics.SENSOR_ORIENTATION); if (so != null) mSensorOrientation = so;
Rect rect = ch.get(CameraCharacteristics.SENSOR_INFO_ACTIVE_ARRAY_SIZE); if (rect != null) mSensorRect = rect;
Float maxZ = ch.get(CameraCharacteristics.SCALER_AVAILABLE_MAX_DIGITAL_ZOOM); if (maxZ != null) mMaxZoom = maxZ;
Float minFocus = ch.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE); if (minFocus != null) mMinFocusDist = minFocus;
android.util.Range<Integer> evR = ch.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE); if (evR != null) { mEvMin = evR.getLower(); mEvMax = evR.getUpper(); }
int[] eisModes = ch.get(CameraCharacteristics.CONTROL_AVAILABLE_VIDEO_STABILIZATION_MODES);
mEisSupported = false;
if (eisModes != null) { for (int m : eisModes) { if (m == CameraCharacteristics.CONTROL_VIDEO_STABILIZATION_MODE_ON) { mEisSupported = true; break; } } }
break;
}
}
if (camId == null) camId = mCamMgr.getCameraIdList()[0];

mCamMgr.openCamera(camId, new CameraDevice.StateCallback() {
@Override public void onOpened(CameraDevice dev) {
mCamDev = dev; startPreview(); buildAudioSources(); mCamHandler.post(mZoomRunnable);
runOnUiThread(() -> {
if (mSeekEv!=null){mSeekEv.setMax(mEvMax-mEvMin);mSeekEv.setProgress(-mEvMin);updateEvLabel(0);}
if (mCbEis != null) {
mCbEis.setEnabled(mEisSupported);
if (!mEisSupported) { mCbEis.setChecked(false); mEisEnabled = false; mCbEis.setText("HW EIS (не поддерживается)"); }
else { mCbEis.setText("HW EIS"); }
}
});
}
@Override public void onDisconnected(CameraDevice dev) { dev.close(); mCamDev = null; }
@Override public void onError(CameraDevice dev, int e) { dev.close(); mCamDev = null; }
}, mCamHandler);
} catch (Exception e) { status("openCamera: " + e.getMessage()); }
}

private void startPreview() {
if (mCamDev == null || !mSurfaceReady) return;
ensureEncoders();
try {
if (mCapSess != null) { mCapSess.close(); mCapSess = null; }
Surface preview = mSv.getHolder().getSurface();
List<Surface> targets = new ArrayList<>(); targets.add(preview);
if (mEncSurface != null && mEncSurface.isValid()) targets.add(mEncSurface);
mCamDev.createCaptureSession(targets, new CameraCaptureSession.StateCallback() {
@Override public void onConfigured(CameraCaptureSession sess) { mCapSess = sess; buildAndSendRequest(); }
@Override public void onConfigureFailed(CameraCaptureSession sess) { status("Session config failed"); }
}, mCamHandler);
} catch (Exception e) { status("startPreview: " + e.getMessage()); }
}

private void buildAndSendRequest() {
CameraCaptureSession sess = mCapSess; CameraDevice dev = mCamDev;
if (sess == null || dev == null || !mSurfaceReady) return;
try {
CaptureRequest.Builder rb = dev.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW);
rb.addTarget(mSv.getHolder().getSurface());
if (mEncSurface != null && mEncSurface.isValid()) rb.addTarget(mEncSurface);
if (mManualFocus) { rb.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_OFF); rb.set(CaptureRequest.LENS_FOCUS_DISTANCE, mFocusValue * mMinFocusDist); }
else { rb.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_VIDEO); }
rb.set(CaptureRequest.CONTROL_AE_MODE, CaptureRequest.CONTROL_AE_MODE_ON);
rb.set(CaptureRequest.CONTROL_AE_EXPOSURE_COMPENSATION, mEvComp);
rb.set(CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE, (mEisEnabled && mEisSupported) ? CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE_ON : CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE_OFF);
if (mSensorRect != null) {
int cropW = Math.max(1, (int)(mSensorRect.width()/mZoomLevel)); int cropH = Math.max(1, (int)(mSensorRect.height()/mZoomLevel));
int cropX = mSensorRect.left + (mSensorRect.width()-cropW)/2; int cropY = mSensorRect.top + (mSensorRect.height()-cropH)/2;
rb.set(CaptureRequest.SCALER_CROP_REGION, new Rect(cropX, cropY, cropX+cropW, cropY+cropH));
}
sess.setRepeatingRequest(rb.build(), null, mCamHandler);
} catch (Exception ignored) {}
}

private void onPauseClick() {
mPaused = !mPaused;
if (mPaused) {
mPauseStartNano = System.nanoTime();
mVidWriteMode = 0; mAudWriteMode = 0;
synchronized(mVidRingLock) { mVidRing.clear(); } synchronized(mAudRingLock) { mAudRing.clear(); }
mBtnPause.setText("▶"); mBtnPause.setBackground(makeOval(0xFF228833));
status("⏸ Paused");
} else {
mPauseEndNano = System.nanoTime();
long pauseDurUs = (mPauseEndNano - mPauseStartNano) / 1000L;
mMuxBasePts += pauseDurUs;
mVidWriteMode = 2; mAudWriteMode = 2;
mBtnPause.setText("⏸"); mBtnPause.setBackground(mBtnBgPause);
status("● REC (resumed)");
}
}

private void onRecordClick() {
if (mRecording) { mRecording = false; mBtn.setEnabled(false); status("Stopping…"); new Thread(this::doStop).start(); }
else { mBtn.setEnabled(false); status("Starting…"); new Thread(this::doStart).start(); }
}

private synchronized void ensureEncoders() {
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
if (!mVidLoopRunning) { Thread t = new Thread(this::videoPreviewLoop, "vid-preview"); t.setDaemon(true); t.start(); }
}

private void videoPreviewLoop() {
mVidLoopRunning = true;
MediaCodec.BufferInfo info = new MediaCodec.BufferInfo();
while (mVidLoopRunning) {
MediaCodec enc = mVidEnc; if (enc == null) { try{Thread.sleep(20);}catch(Exception e){} continue; }
int out; try { out = enc.dequeueOutputBuffer(info, 40_000); } catch (Exception e) { break; }
if (out == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED) { synchronized(mVidRingLock) { mVidOutFmt = enc.getOutputFormat(); } continue; }
if (out < 0) continue;
try {
boolean cfg = (info.flags & MediaCodec.BUFFER_FLAG_CODEC_CONFIG) != 0;
if (cfg || info.size <= 0) {
if (cfg && mRecording && mPreviewDecoderReady && mPreviewDecoder != null) {
ByteBuffer data = enc.getOutputBuffer(out); if (data != null) { byte[] bytes = new byte[info.size]; data.position(info.offset); data.get(bytes, 0, info.size); sendToPreviewDecoder(ByteBuffer.wrap(bytes), info); }
}
continue;
}
ByteBuffer data = enc.getOutputBuffer(out); if (data == null) continue;
int mode = mVidWriteMode;
if (mode == 0) {
EncodedFrame f = new EncodedFrame(data, info);
synchronized(mVidRingLock) {
mVidRing.addLast(f);
long eisExtra = (mEisEnabled && mEisSupported) ? EIS_LATENCY_US : 0L;
while (mVidRing.size() > 1) { long span = mVidRing.peekLast().pts - mVidRing.peekFirst().pts; if (span <= (long)mPreBufSecs*1_200_000L + eisExtra) break; mVidRing.removeFirst(); }
}
} else if (mode == 1) {
synchronized(mVidRingLock) {
boolean foundKey = false;
for (EncodedFrame rf : mVidRing) { if (!foundKey && !rf.isKey()) continue; foundKey = true; ByteBuffer rb = ByteBuffer.wrap(rf.data); MediaCodec.BufferInfo bi = new MediaCodec.BufferInfo(); bi.set(0, rf.data.length, rf.pts - mMuxBasePts, rf.flags); synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mVidTrack, rb, bi); } if (mPreviewDecoderReady && mPreviewDecoder != null) sendToPreviewDecoder(rb, bi); }
mVidRing.clear();
}
MediaCodec.BufferInfo n = new MediaCodec.BufferInfo(); n.set(info.offset, info.size, info.presentationTimeUs - mMuxBasePts, info.flags);
synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mVidTrack, data, n); }
if (mPreviewDecoderReady && mPreviewDecoder != null) sendToPreviewDecoder(data, n);
mVidWriteMode = 2;
} else {
MediaCodec.BufferInfo n = new MediaCodec.BufferInfo(); n.set(info.offset, info.size, info.presentationTimeUs - mMuxBasePts, info.flags);
synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mVidTrack, data, n); }
if (mPreviewDecoderReady && mPreviewDecoder != null) sendToPreviewDecoder(data, n);
}
} finally { enc.releaseOutputBuffer(out, false); }
}
mVidLoopRunning = false;
}

private void sendToPreviewDecoder(ByteBuffer src, MediaCodec.BufferInfo info) {
MediaCodec dec = mPreviewDecoder; if (dec == null || !mPreviewDecoderReady) return;
int idx = dec.dequeueInputBuffer(10_000);
if (idx >= 0) {
ByteBuffer decIn = dec.getInputBuffer(idx); if (decIn != null) {
decIn.clear(); int pos = src.position(); int lim = src.limit();
src.position(info.offset); src.limit(info.offset + info.size); decIn.put(src);
src.limit(lim); src.position(pos);
dec.queueInputBuffer(idx, 0, info.size, info.presentationTimeUs, info.flags);
}
}
drainPreviewDecoder(dec);
}

private void drainPreviewDecoder(MediaCodec dec) {
MediaCodec.BufferInfo info = new MediaCodec.BufferInfo();
while (true) { int out = dec.dequeueOutputBuffer(info, 0); if (out < 0) break; dec.releaseOutputBuffer(out, true); }
}

@SuppressLint("MissingPermission")
private void startMonitor() {
if (mAudRunning || !mPermsOk) return;
int pos = mSpinner.getSelectedItemPosition();
AudioSrcItem src2 = (pos >= 0 && pos < mSrcList.size()) ? mSrcList.get(pos) : null;
int audioSrc = src2 != null ? src2.audioSource : MediaRecorder.AudioSource.MIC;

int chanCfg = AudioFormat.CHANNEL_IN_STEREO; int channels = 2;
int minBuf = AudioRecord.getMinBufferSize(AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT);
if (minBuf <= 0) { chanCfg = AudioFormat.CHANNEL_IN_MONO; channels = 1; minBuf = AudioRecord.getMinBufferSize(AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT); }
int bufSize = Math.max(minBuf, AUDIO_SR * channels * 2 / 5);
AudioRecord rec = new AudioRecord(audioSrc, AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT, bufSize);
if (rec.getState() != AudioRecord.STATE_INITIALIZED && channels == 2) {
rec.release(); chanCfg = AudioFormat.CHANNEL_IN_MONO; channels = 1;
minBuf = AudioRecord.getMinBufferSize(AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT);
bufSize = Math.max(minBuf, AUDIO_SR * 2 / 5);
rec = new AudioRecord(audioSrc, AUDIO_SR, chanCfg, AudioFormat.ENCODING_PCM_16BIT, bufSize);
}
if (rec.getState() != AudioRecord.STATE_INITIALIZED) { rec.release(); return; }
if (Build.VERSION.SDK_INT >= 23 && src2 != null && src2.device != null) rec.setPreferredDevice(src2.device);
disableAudioEffects(rec.getAudioSessionId());
mAudRec = rec; mAudChannels = channels;

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
mAudThread = new Thread(this::audioMainLoop, "aud-main"); mAudThread.setDaemon(true); mAudThread.start();
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

private void audioMainLoop() {
final AudioRecord rec = mAudRec; final int ch = mAudChannels; final int chunkSamples = AUDIO_SR * ch / 50;
short[] buf = new short[chunkSamples];
final long startUs = System.nanoTime() / 1000L; long totalFrames = 0L;
rec.startRecording();
while (mAudRunning) {
int r = rec.read(buf, 0, chunkSamples); if (r <= 0) continue;
final float g = mGain; final boolean sc = mSoftClip; long sumSq = 0;
for (int i = 0; i < r; i++) {
float s = buf[i] * g;
if (sc) { final float T = 32768f * 0.7f, knee = 32768f - T; float ab = Math.abs(s); if (ab > T) s = Math.signum(s) * (T + knee * (float)Math.tanh((ab-T)/knee)); }
if (s > 32767f) s = 32767f; else if (s < -32768f) s = -32768f;
buf[i] = (short) s; sumSq += (long) buf[i] * buf[i];
}
float peakAmp = 0f; for (int i = 0; i < r; i++) { float a = Math.abs(buf[i]) / 32768f; if (a > peakAmp) peakAmp = a; }
mVu.setPeak(peakAmp); mVu.setLevel((float)Math.sqrt((double)sumSq/r)/32768f);
if (mOscilloscope != null) mOscilloscope.pushSamples(buf, r, ch);
if (mEnvelope != null) mEnvelope.pushSamples(buf, r, ch);
if (mSpectrum != null) mSpectrum.pushSamples(buf, r, ch);
MediaCodec enc = mAudEnc; if (enc == null) continue;
long pts = startUs + totalFrames * 1_000_000L / AUDIO_SR; totalFrames += r / ch;
int idx = enc.dequeueInputBuffer(5_000);
if (idx >= 0) { ByteBuffer bb = enc.getInputBuffer(idx); bb.clear(); for (int i = 0; i < r; i++) { bb.put((byte)(buf[i]&0xFF)); bb.put((byte)(buf[i]>>8&0xFF)); } enc.queueInputBuffer(idx, 0, r*2, pts, 0); }
drainAudioEncoder(enc);
}
mVu.setLevel(0f); try { rec.stop(); } catch (Exception ignored) {}
}

private void drainAudioEncoder(MediaCodec enc) {
MediaCodec.BufferInfo info = new MediaCodec.BufferInfo();
while (true) {
int out = enc.dequeueOutputBuffer(info, 0);
if (out == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED) { synchronized(mAudRingLock) { mAudOutFmt = enc.getOutputFormat(); } continue; }
if (out < 0) break;
try {
boolean cfg = (info.flags & MediaCodec.BUFFER_FLAG_CODEC_CONFIG) != 0; if (cfg || info.size <= 0) continue;
ByteBuffer data = enc.getOutputBuffer(out); int mode = mAudWriteMode;
if (mode == 0) {
EncodedFrame f = new EncodedFrame(data, info);
synchronized(mAudRingLock) { mAudRing.addLast(f); while (mAudRing.size() > 1) { long span = mAudRing.peekLast().pts - mAudRing.peekFirst().pts; if (span <= (long)mPreBufSecs*1_200_000L) break; mAudRing.removeFirst(); } }
} else if (mode == 1) {
synchronized(mAudRingLock) { boolean started = false; for (EncodedFrame rf : mAudRing) { if (!started && rf.pts < mMuxBasePts) continue; started = true; ByteBuffer rb = ByteBuffer.wrap(rf.data); MediaCodec.BufferInfo bi = new MediaCodec.BufferInfo(); bi.set(0, rf.data.length, rf.pts - mMuxBasePts, rf.flags); synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mAudTrack, rb, bi); } } mAudRing.clear(); }
MediaCodec.BufferInfo n = new MediaCodec.BufferInfo(); n.set(info.offset, info.size, info.presentationTimeUs - mMuxBasePts, info.flags);
synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mAudTrack, data, n); }
mAudWriteMode = 2;
} else {
MediaCodec.BufferInfo n = new MediaCodec.BufferInfo(); n.set(info.offset, info.size, info.presentationTimeUs - mMuxBasePts, info.flags);
synchronized(mMuxLock) { if (mMuxReady) mMuxer.writeSampleData(mAudTrack, data, n); }
}
} finally { enc.releaseOutputBuffer(out, false); }
if ((info.flags & MediaCodec.BUFFER_FLAG_END_OF_STREAM) != 0) break;
}
}

private void startPreviewDecoderIfNeeded() {
if (mPreviewDecoder != null || mMonitorHolder == null || mMonitorHolder.getSurface() == null || !mRecording) return;
try {
MediaFormat decoderFormat = MediaFormat.createVideoFormat(MediaFormat.MIMETYPE_VIDEO_AVC, VIDEO_W, VIDEO_H);
mPreviewDecoder = MediaCodec.createDecoderByType(MediaFormat.MIMETYPE_VIDEO_AVC);
mPreviewDecoder.configure(decoderFormat, mMonitorHolder.getSurface(), null, 0);
mPreviewDecoder.start();
mPreviewDecoderReady = true;
} catch (Exception e) { status("Preview decoder err: " + e.getMessage()); mPreviewDecoder = null; }
}

@SuppressLint("MissingPermission")
private void doStart() {
try {
for (int wait = 0; wait < 40 && (mVidOutFmt == null || mAudOutFmt == null); wait++) { Thread.sleep(50); }
if (mVidOutFmt == null || mAudOutFmt == null) { runOnUiThread(() -> { mBtn.setEnabled(true); status("Encoder not ready — retry"); }); return; }
long basePts;
synchronized(mVidRingLock) { if (mPreBufferEnabled) { basePts = Long.MAX_VALUE; for (EncodedFrame f : mVidRing) { if (f.isKey()) { basePts = f.pts; break; } } if (basePts == Long.MAX_VALUE) basePts = 0; } else { basePts = System.nanoTime() / 1000L; } }
mMuxBasePts = basePts;
String displayPath;
if (Build.VERSION.SDK_INT >= 29) {
ContentValues cv = new ContentValues(); cv.put(MediaStore.Video.Media.DISPLAY_NAME, "VID_" + System.currentTimeMillis() + ".mp4"); cv.put(MediaStore.Video.Media.MIME_TYPE, "video/mp4"); cv.put(MediaStore.Video.Media.RELATIVE_PATH, "DCIM/CaMic"); cv.put(MediaStore.Video.Media.IS_PENDING, 1);
mPendingUri = getContentResolver().insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, cv);
mPfd = getContentResolver().openFileDescriptor(mPendingUri, "rw");
mMuxer = new MediaMuxer(mPfd.getFileDescriptor(), MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4);
displayPath = "DCIM/CaMic";
} else {
@SuppressWarnings("deprecation") File dir = new File(Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_DCIM), "CaMic"); dir.mkdirs();
File f = new File(dir, "VID_" + System.currentTimeMillis() + ".mp4");
mMuxer = new MediaMuxer(f.getAbsolutePath(), MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4);
displayPath = f.getAbsolutePath();
}
@SuppressWarnings("deprecation") int rot = getWindowManager().getDefaultDisplay().getRotation() * 90;
mMuxer.setOrientationHint((mSensorOrientation - rot + 360) % 360);
synchronized(mMuxLock) { mVidTrack = mMuxer.addTrack(mVidOutFmt); mAudTrack = mMuxer.addTrack(mAudOutFmt); mMuxer.start(); mMuxReady = true; }
mRecording = true;
if (mPreBufferEnabled) { mVidWriteMode = 1; mAudWriteMode = 1; } else { mVidWriteMode = 2; mAudWriteMode = 2; }
final String fp = displayPath;
runOnUiThread(() -> {
mBtn.setText("⏹ STOP"); mBtn.setBackground(mBtnBgRec); mBtn.setEnabled(true);
mBtnPause.setVisibility(View.VISIBLE); mBtnPause.setText("⏸"); mBtnPause.setBackground(mBtnBgPause);
mPaused = false;
if (mCbEis != null) mCbEis.setEnabled(false);
if (mMonitorView != null) { mMonitorView.setVisibility(View.VISIBLE); if (mMonitorHolder.getSurface() != null && mMonitorHolder.getSurface().isValid()) startPreviewDecoderIfNeeded(); }
status("● REC  →  " + fp);
});
} catch (Exception e) { mRecording = false; mVidWriteMode = 0; mAudWriteMode = 0; finalizeMuxer(); runOnUiThread(() -> { mBtn.setText("⏺ REC"); mBtn.setBackground(mBtnBgIdle); mBtn.setEnabled(true); mBtnPause.setVisibility(View.GONE); if (mCbEis != null) mCbEis.setEnabled(mEisSupported); if (mMonitorView != null) mMonitorView.setVisibility(View.GONE); status("Error: " + e.getMessage()); }); }
}

private void doStop() { try { Thread.sleep(200); } catch (Exception ignored) {} mVidWriteMode = 0; mAudWriteMode = 0; finalizeMuxer(); }

private void finalizeMuxer() {
synchronized(mMuxLock) { try { if (mMuxer != null) { if (mMuxReady) mMuxer.stop(); mMuxer.release(); } } catch (Exception ignored) {} mMuxer = null; mMuxReady = false; mVidTrack = -1; mAudTrack = -1; }
try { if (mPfd != null) { mPfd.close(); mPfd = null; } } catch (Exception ignored) {}
if (Build.VERSION.SDK_INT >= 29 && mPendingUri != null) { ContentValues cv = new ContentValues(); cv.put(MediaStore.Video.Media.IS_PENDING, 0); getContentResolver().update(mPendingUri, cv, null, null); mPendingUri = null; }
if (mPreviewDecoder != null) { try { mPreviewDecoder.stop(); mPreviewDecoder.release(); } catch (Exception ignored) {} mPreviewDecoder = null; }
mPreviewDecoderReady = false;
runOnUiThread(() -> {
mBtn.setText("⏺ REC"); mBtn.setBackground(mBtnBgIdle); mBtn.setEnabled(true); mBtnPause.setVisibility(View.GONE);
mPaused = false; if (mCbEis != null) mCbEis.setEnabled(mEisSupported); if (mMonitorView != null) mMonitorView.setVisibility(View.GONE);
status("Saved");
});
}

private void status(String s) { runOnUiThread(() -> mTvStatus.setText(s)); }

private void buildAudioSources() {
List<AudioSrcItem> list = new ArrayList<>();
if (Build.VERSION.SDK_INT >= 23) {
AudioManager am = (AudioManager) getSystemService(AUDIO_SERVICE);
AudioDeviceInfo[] devs = am.getDevices(AudioManager.GET_DEVICES_INPUTS);
boolean hasBuiltin = false;
for (AudioDeviceInfo d : devs) {
int t = d.getType();
if (t == AudioDeviceInfo.TYPE_BUILTIN_MIC) { if (hasBuiltin) continue; hasBuiltin = true; list.add(new AudioSrcItem("Built-in mic", MediaRecorder.AudioSource.MIC, d)); if (Build.VERSION.SDK_INT >= 24) list.add(new AudioSrcItem("Built-in mic (raw)", MediaRecorder.AudioSource.UNPROCESSED, d)); }
else if (t == AudioDeviceInfo.TYPE_USB_DEVICE || t == AudioDeviceInfo.TYPE_USB_HEADSET) { CharSequence pn = d.getProductName(); list.add(new AudioSrcItem("USB: " + (pn != null && pn.length() > 0 ? pn : "audio"), MediaRecorder.AudioSource.MIC, d)); }
else if (t == AudioDeviceInfo.TYPE_WIRED_HEADSET) { list.add(new AudioSrcItem("Wired headset", MediaRecorder.AudioSource.MIC, d)); }
else if (t == AudioDeviceInfo.TYPE_BLUETOOTH_SCO) { list.add(new AudioSrcItem("Bluetooth mic", MediaRecorder.AudioSource.MIC, d)); }
}
}
if (list.isEmpty()) { list.add(new AudioSrcItem("Default", MediaRecorder.AudioSource.DEFAULT, null)); list.add(new AudioSrcItem("Microphone", MediaRecorder.AudioSource.MIC, null)); list.add(new AudioSrcItem("Camcorder", MediaRecorder.AudioSource.CAMCORDER, null)); list.add(new AudioSrcItem("Communication", MediaRecorder.AudioSource.VOICE_COMMUNICATION, null)); if (Build.VERSION.SDK_INT >= 24) list.add(new AudioSrcItem("Unprocessed (raw)", MediaRecorder.AudioSource.UNPROCESSED, null)); }
runOnUiThread(() -> {
mSrcList.clear(); mSrcList.addAll(list);
List<String> names = new ArrayList<>(); for (AudioSrcItem item : mSrcList) names.add(item.name);
@SuppressWarnings("unchecked") ArrayAdapter<String> ad2 = (ArrayAdapter<String>) mSpinner.getAdapter(); ad2.clear(); ad2.addAll(names); ad2.notifyDataSetChanged();
int defaultIdx = 0;
for (int i = 0; i < mSrcList.size(); i++) { AudioSrcItem item = mSrcList.get(i); if (item.device != null && Build.VERSION.SDK_INT >= 23) { int t = item.device.getType(); if (t == AudioDeviceInfo.TYPE_USB_DEVICE || t == AudioDeviceInfo.TYPE_USB_HEADSET) { defaultIdx = i; break; } } }
if (defaultIdx == 0) { for (int i = 0; i < mSrcList.size(); i++) { if (mSrcList.get(i).audioSource == MediaRecorder.AudioSource.UNPROCESSED) { defaultIdx = i; break; } } }
mSpinner.setSelection(defaultIdx);
if (!mRecording) { stopAudio(); startMonitor(); }
});
}

private static class AudioSrcItem {
final String name; final int audioSource; final AudioDeviceInfo device;
AudioSrcItem(String n, int s, AudioDeviceInfo d) { name = n; audioSource = s; device = d; }
}
// Продолжение MainActivity.java – кастомные View

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

    private float faderH(float w) { return Math.round(w * 0.7f) + dp(20); }
    private int dp(int x) { return Math.round(x * getResources().getDisplayMetrics().density); }

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

        canvas.drawRoundRect(new RectF(trkX1, trkT, trkX2, trkB), trackW / 2f, trackW / 2f, mTrackPaint);
        canvas.drawRoundRect(new RectF(trkX1, thumbY, trkX2, trkB), trackW / 2f, trackW / 2f, mFillPaint);
        Paint z = new Paint(Paint.ANTI_ALIAS_FLAG); z.setColor(0x88FFFFFF); z.setStrokeWidth(1.5f);
        canvas.drawLine(trkX1 - 3f, trkB - 0.5f * trkH, trkX2 + 3f, trkB - 0.5f * trkH, z);

        float fH = faderH(w), fW = w - 2f;
        RectF fader = new RectF(1f, thumbY - fH/2f, 1f + fW, thumbY + fH/2f);
        Paint shadow = new Paint(Paint.ANTI_ALIAS_FLAG); shadow.setColor(0x66000000); shadow.setStyle(Paint.Style.FILL);
        canvas.drawRoundRect(new RectF(fader.left+2, fader.top+3, fader.right+2, fader.bottom+3), dp(4), dp(4), shadow);
        canvas.drawRoundRect(fader, dp(4), dp(4), mThumbPaint);
        float rInset = fW * 0.18f;
        for (int ri = -1; ri <= 1; ri++) { float ry = thumbY + ri * dp(4); canvas.drawLine(1f + rInset, ry, 1f + fW - rInset, ry, mRidgePaint); }
        Paint cLine = new Paint(Paint.ANTI_ALIAS_FLAG); cLine.setColor(0xFFDDCC00); cLine.setStrokeWidth(1.5f);
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
            case MotionEvent.ACTION_DOWN: if (mListener != null) mListener.onStartTrackingTouch(null);
            case MotionEvent.ACTION_MOVE: {
                float frac = 1f - (e.getY() - trkT) / trkH;
                int p = Math.max(0, Math.min(mMax, Math.round(frac * mMax)));
                mProgress = p; invalidate();
                if (mListener != null) mListener.onProgressChanged(null, p, true);
                return true;
            }
            case MotionEvent.ACTION_UP:
            case MotionEvent.ACTION_CANCEL: if (mListener != null) mListener.onStopTrackingTouch(null); return true;
        }
        return false;
    }
}

static class VuMeterView extends View {
    private static final int N = 30;
    private static final float MIN_DB = -60f;
    private static final long PEAK_HOLD_MS = 1800;
    private final Paint mSegPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint mPeakPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint mDbLblPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final RectF mRect = new RectF();
    private float mLevelDb = MIN_DB;
    private float mPeakDb = MIN_DB;
    private long mPeakHoldUntil = 0;

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

    void setLevel(float rms) { mLevelDb = rms > 1e-6f ? Math.max(MIN_DB, (float)(20.0 * Math.log10(rms))) : MIN_DB; postInvalidate(); }
    void setPeak(float peak) { float db = peak > 1e-6f ? Math.max(MIN_DB, (float)(20.0 * Math.log10(peak))) : MIN_DB; if (db >= mPeakDb || System.currentTimeMillis() > mPeakHoldUntil) { mPeakDb = db; mPeakHoldUntil = System.currentTimeMillis() + PEAK_HOLD_MS; } }

    @Override
    protected void onDraw(Canvas canvas) {
        final float w = getWidth(), h = getHeight();
        final float segH = (h - N - 1f) / N;
        final float segW = w - 2f;
        for (int i = 0; i < N; i++) {
            float segDb = MIN_DB + (float) i / N * (-MIN_DB);
            boolean lit = mLevelDb >= segDb;
            int color;
            if (!lit) color = 0xFF181818;
            else if (segDb < -12f) color = 0xFF00CC55;
            else if (segDb < -6f) color = 0xFFFFBB00;
            else color = 0xFFFF2200;
            mSegPaint.setColor(color);
            float y = h - 1f - i * (segH + 1f) - segH;
            mRect.set(1f, y, 1f + segW, y + segH);
            canvas.drawRoundRect(mRect, 2f, 2f, mSegPaint);
        }
        if (mPeakDb > MIN_DB) {
            float frac = (mPeakDb - MIN_DB) / (-MIN_DB);
            float py = h - 1f - frac * (h - 2f);
            long now = System.currentTimeMillis();
            int peakColor;
            if (mPeakDb >= -3f) peakColor = 0xFFFF2200;
            else if (mPeakDb >= -12f) peakColor = 0xFFFFBB00;
            else peakColor = 0xFF00FF88;
            boolean fading = now > mPeakHoldUntil - 400;
            if (!fading || (now / 150) % 2 == 0) { mPeakPaint.setColor(peakColor); canvas.drawLine(0, py, w, py, mPeakPaint); }
        }
        float[] dbMarks = {0f, -6f, -12f, -24f, -48f, -60f};
        String[] dbStrs = {"0", "-6", "-12", "-24", "-48", "-60"};
        float lblAscent = -mDbLblPaint.ascent();
        for (int di = 0; di < dbMarks.length; di++) {
            float frac = (dbMarks[di] - MIN_DB) / (-MIN_DB);
            float ly = h - 1f - frac * (h - 2f);
            if (dbMarks[di] >= -6f) mDbLblPaint.setColor(0xFFFF6644);
            else if (dbMarks[di] >= -12f) mDbLblPaint.setColor(0xFFFFDD44);
            else mDbLblPaint.setColor(0xCCBBFFCC);
            mDbLblPaint.setAlpha(200);
            canvas.drawText(dbStrs[di], w - 1f, ly + lblAscent * 0.5f, mDbLblPaint);
        }
    }
}

static class ZoomLeverView extends View {
    interface Listener { void onLever(float pos); }
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
        mTrackPaint.setColor(0x55FFFFFF); mThumbPaint.setColor(0xFFFFFFFF);
        mMarkPaint.setColor(0xAAFFFFFF); mMarkPaint.setStyle(Paint.Style.STROKE);
        mMarkPaint.setStrokeWidth(1.5f * c.getResources().getDisplayMetrics().density);
        mTextPaint.setColor(0xCCFFFFFF); mTextPaint.setTextAlign(Paint.Align.CENTER);
        mTextPaint.setTextSize(11 * c.getResources().getDisplayMetrics().density);
        setBackgroundColor(0x44000000);
    }

    void setListener(Listener l) { mListener = l; }

    private void recalc() {
        float w = getWidth(), h = getHeight();
        float lblH = mTextPaint.getTextSize() + dp(4);
        trkT = lblH; trkB = h - lblH; trkH = trkB - trkT;
        trkW = dp(16); mid = (trkT + trkB) / 2f; cx = w / 2f;
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
        mThumbPaint.setAlpha((int)(160 + 90 * Math.abs(mPos)));
        canvas.drawRoundRect(new RectF(cx - thumbW / 2f, thumbCY - thumbH / 2f, cx + thumbW / 2f, thumbCY + thumbH / 2f), dp(6), dp(6), mThumbPaint);
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
                removeCallbacks(mSpring); mTracking = true;
                mPos = Math.max(-1f, Math.min(1f, (mid - e.getY()) / (trkH / 2f)));
                if (mListener != null) mListener.onLever(mPos);
                invalidate(); return true;
            case MotionEvent.ACTION_UP:
            case MotionEvent.ACTION_CANCEL:
                mTracking = false; post(mSpring); return true;
        }
        return super.onTouchEvent(e);
    }

    private final Runnable mSpring = new Runnable() {
        @Override
        public void run() {
            if (mTracking) return;
            mPos *= 0.75f; if (mListener != null) mListener.onLever(mPos); invalidate();
            if (Math.abs(mPos) > 0.01f) postDelayed(this, 16);
            else { mPos = 0f; if (mListener != null) mListener.onLever(0f); invalidate(); }
        }
    };

    private int dp(int x) { return Math.round(x * getResources().getDisplayMetrics().density); }
}

class FocusAssistView extends View implements Runnable {
    private Bitmap mBmp;
    private final Paint mBmpPaint = new Paint(Paint.ANTI_ALIAS_FLAG | Paint.FILTER_BITMAP_FLAG);
    private final Paint mBorderPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint mGridPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint mLabelPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private static final int ZOOM = 4;
    private static final int SAMPLE_SIZE = 120;
    private volatile boolean mRunning;

    FocusAssistView(Context c) {
        super(c);
        mBorderPaint.setColor(0xFFDDCC00); mBorderPaint.setStyle(Paint.Style.STROKE); mBorderPaint.setStrokeWidth(2f);
        mGridPaint.setColor(0x55FFFFFF); mGridPaint.setStyle(Paint.Style.STROKE); mGridPaint.setStrokeWidth(0.8f);
        mLabelPaint.setColor(0xFFDDCC00); mLabelPaint.setTextAlign(Paint.Align.CENTER);
        mLabelPaint.setTextSize(10 * getResources().getDisplayMetrics().density); mLabelPaint.setAntiAlias(true);
        setBackgroundColor(0x00000000);
    }

    @Override
    protected void onAttachedToWindow() { super.onAttachedToWindow(); mRunning = true; postDelayed(this, 100); }
    @Override
    protected void onDetachedFromWindow() { super.onDetachedFromWindow(); mRunning = false; removeCallbacks(this); }

    @Override
    public void run() {
        if (!mRunning || getVisibility() != View.VISIBLE) { if (mRunning) postDelayed(this, 200); return; }
        capture(); postDelayed(this, 100);
    }

    private void capture() {
        if (mSv == null || !mSurfaceReady) return;
        if (android.os.Build.VERSION.SDK_INT < 26) { invalidate(); return; }
        try {
            int svW = mSv.getWidth(), svH = mSv.getHeight();
            if (svW <= 0 || svH <= 0) return;
            int cx = svW / 2, cy = svH / 2, half = SAMPLE_SIZE / 2;
            int l = Math.max(0, cx - half), t = Math.max(0, cy - half);
            int r = Math.min(svW, l + SAMPLE_SIZE), b = Math.min(svH, t + SAMPLE_SIZE);
            android.graphics.Rect src = new android.graphics.Rect(l, t, r, b);
            Bitmap dst = Bitmap.createBitmap(r - l, b - t, Bitmap.Config.ARGB_8888);
            android.view.PixelCopy.request(mSv, src, dst, result -> {
                if (result == android.view.PixelCopy.SUCCESS) { mBmp = dst; postInvalidate(); }
            }, new Handler(android.os.Looper.getMainLooper()));
        } catch (Exception ignored) {}
    }

    @Override
    protected void onDraw(Canvas canvas) {
        final float w = getWidth(), h = getHeight();
        canvas.drawARGB(200, 0, 0, 0);
        if (mBmp != null && !mBmp.isRecycled()) { canvas.drawBitmap(mBmp, null, new RectF(0, 0, w, h), mBmpPaint); }
        else { Paint p = new Paint(); p.setColor(0xFF333333); canvas.drawRect(0, 0, w, h, p); }
        canvas.drawLine(w/2f, 0, w/2f, h, mGridPaint); canvas.drawLine(0, h/2f, w, h/2f, mGridPaint);
        canvas.drawLine(w/3f, 0, w/3f, h, mGridPaint); canvas.drawLine(2*w/3f, 0, 2*w/3f, h, mGridPaint);
        canvas.drawLine(0, h/3f, w, h/3f, mGridPaint); canvas.drawLine(0, 2*h/3f, w, 2*h/3f, mGridPaint);
        canvas.drawRect(1f, 1f, w-1f, h-1f, mBorderPaint);
        float corner = w*0.12f; mBorderPaint.setStrokeWidth(3f);
        canvas.drawLine(1f,1f,corner,1f,mBorderPaint); canvas.drawLine(1f,1f,1f,corner,mBorderPaint);
        canvas.drawLine(w-corner,1f,w-1f,1f,mBorderPaint); canvas.drawLine(w-1f,1f,w-1f,corner,mBorderPaint);
        canvas.drawLine(1f,h-corner,1f,h-1f,mBorderPaint); canvas.drawLine(1f,h-1f,corner,h-1f,mBorderPaint);
        canvas.drawLine(w-1f,h-corner,w-1f,h-1f,mBorderPaint); canvas.drawLine(w-corner,h-1f,w-1f,h-1f,mBorderPaint);
        mBorderPaint.setStrokeWidth(2f);
        canvas.drawText("FOCUS ×" + ZOOM, w/2f, h-4f, mLabelPaint);
    }
}

static class FocusDrumView extends View {
    interface OnFocusChangeListener { void onFocusChanged(float value); }
    interface OnDrumScrollListener { void onScrollStart(); void onScrollStop(); }
    private OnFocusChangeListener mListener;
    private OnDrumScrollListener mScrollListener;
    private float mValue = 0f;
    private float mLastY;
    private boolean mDragging;
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
        mRiskPaint.setStrokeWidth(1.5f * density); mRiskPaint.setStyle(Paint.Style.STROKE);
        mShadowPaint.setStyle(Paint.Style.FILL);
        mCenterLinePaint.setColor(0xFFDDCC00); mCenterLinePaint.setStrokeWidth(2f * density); mCenterLinePaint.setStyle(Paint.Style.STROKE);
    }

    void setOnFocusChangeListener(OnFocusChangeListener l) { mListener = l; }
    void setOnDrumScrollListener(OnDrumScrollListener l) { mScrollListener = l; }

    @Override
    protected void onDraw(Canvas canvas) {
        final float w = getWidth(), h = getHeight();
        final float cx = w/2f, drumW = w*0.72f, drumLeft = cx - drumW/2f, drumRight = cx + drumW/2f;
        RectF drumRect = new RectF(drumLeft, 0, drumRight, h);
        mDrumPaint.setColor(0xFF222222);
        canvas.drawRoundRect(drumRect, drumW*0.12f, drumW*0.12f, mDrumPaint);
        final float riskStep = h*0.07f;
        float offset = mAngle % riskStep; if (offset < 0) offset += riskStep;
        final int totalRisks = (int)(h/riskStep)+2;
        for (int i=-1; i<=totalRisks; i++) {
            float ry = offset + i*riskStep; if (ry < 0 || ry > h) continue;
            float distFromCenter = Math.abs(ry - h/2f)/(h/2f);
            float squeeze = 1f - 0.55f*distFromCenter*distFromCenter;
            float riskLen = drumW*0.8f*squeeze;
            int alpha = (int)(200*(1f - distFromCenter*0.7f));
            boolean isMajor = (Math.abs(Math.round((ry-offset)/riskStep))%5==0);
            if (isMajor) { riskLen *= 1.25f; alpha = Math.min(255, alpha+40); }
            mRiskPaint.setColor(0xFFFFFFFF); mRiskPaint.setAlpha(alpha);
            mRiskPaint.setStrokeWidth(isMajor ? 2f : 1.2f);
            canvas.drawLine(cx - riskLen/2f, ry, cx + riskLen/2f, ry, mRiskPaint);
        }
        int[] colorsTop = {0xCC000000, 0x00000000}, colorsBot = {0x00000000, 0xCC000000};
        android.graphics.LinearGradient shadTop = new android.graphics.LinearGradient(0,0,0,h*0.28f,colorsTop,null,android.graphics.Shader.TileMode.CLAMP);
        android.graphics.LinearGradient shadBot = new android.graphics.LinearGradient(0,h*0.72f,0,h,colorsBot,null,android.graphics.Shader.TileMode.CLAMP);
        mShadowPaint.setShader(shadTop); canvas.drawRoundRect(drumRect, drumW*0.12f, drumW*0.12f, mShadowPaint);
        mShadowPaint.setShader(shadBot); canvas.drawRoundRect(drumRect, drumW*0.12f, drumW*0.12f, mShadowPaint);
        mShadowPaint.setShader(null);
        canvas.drawLine(drumLeft-4f, h/2f, drumRight+4f, h/2f, mCenterLinePaint);
    }

    @Override
    public boolean onTouchEvent(MotionEvent e) {
        switch (e.getAction()) {
            case MotionEvent.ACTION_DOWN: mLastY = e.getY(); mDragging = true; if (mScrollListener != null) mScrollListener.onScrollStart(); return true;
            case MotionEvent.ACTION_MOVE: {
                if (!mDragging) return true;
                float dy = e.getY() - mLastY; mLastY = e.getY(); mAngle += dy;
                float newVal = mValue - dy/FULL_RANGE_PX_PER_UNIT;
                newVal = Math.max(0f, Math.min(1f, newVal));
                if (newVal == 0f && mValue == 0f) mAngle = Math.min(mAngle, 0f);
                if (newVal == 1f && mValue == 1f) mAngle = Math.max(mAngle, 0f);
                if (newVal != mValue) { mValue = newVal; if (mListener != null) mListener.onFocusChanged(mValue); }
                invalidate(); return true;
            }
            case MotionEvent.ACTION_UP:
            case MotionEvent.ACTION_CANCEL: mDragging = false; if (mScrollListener != null) mScrollListener.onScrollStop(); return true;
        }
        return false;
    }
}

static class OscilloscopeView extends View {
    private static final int DISP_SAMPLES = 2048, BUF_SIZE = DISP_SAMPLES*4;
    private final float[] mRingBuf = new float[BUF_SIZE]; private int mWritePos = 0;
    private final float[] mFrame = new float[DISP_SAMPLES];
    private volatile boolean mNewFrame = false; private final Object mLock = new Object();
    private static final float TRIG_LEVEL = 0.05f; private static final int TRIG_HYSTERESIS = 64;
    private final Paint mWavePaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint mGridPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    private final Paint mLabelPaint = new Paint(Paint.ANTI_ALIAS_FLAG);
    static int levelColor(float amp) { if (amp >= 0.7f) return 0xFFFF2200; if (amp >= 0.3f) return 0xFFFFBB00; return 0xFF00CC55; }

    OscilloscopeView(Context c) {
        super(c); setBackgroundColor(0x00000000);
        mWavePaint.setStrokeWidth(1.8f*c.getResources().getDisplayMetrics().density); mWavePaint.setStyle(Paint.Style.STROKE); mWavePaint.setStrokeCap(Paint.Cap.ROUND);
        mGridPaint.setColor(0x33FFFFFF); mGridPaint.setStrokeWidth(0.8f); mGridPaint.setStyle(Paint.Style.STROKE);
        mLabelPaint.setColor(0xAAFFFFFF); mLabelPaint.setTextSize(9*c.getResources().getDisplayMetrics().density); mLabelPaint.setAntiAlias(true);
    }

    void pushSamples(short[] buf, int len, int channels) {
        synchronized (mLock) {
            for (int i=0; i<len; i+=channels) {
                float mono = buf[i]/32768f; if (channels==2 && i+1<len) mono = (mono + buf[i+1]/32768f)*0.5f;
                mRingBuf[mWritePos] = mono; mWritePos = (mWritePos+1)%BUF_SIZE;
            }
            int trigPos = -1, searchStart = (mWritePos - BUF_SIZE + BUF_SIZE)%BUF_SIZE;
            for (int k=TRIG_HYSTERESIS; k<BUF_SIZE-DISP_SAMPLES; k++) { int p=(searchStart+k)%BUF_SIZE; if (mRingBuf[(p-1+BUF_SIZE)%BUF_SIZE]<TRIG_LEVEL && mRingBuf[p]>=TRIG_LEVEL) { trigPos=p; break; } }
            if (trigPos<0) trigPos = (mWritePos - DISP_SAMPLES + BUF_SIZE)%BUF_SIZE;
            for (int k=0; k<DISP_SAMPLES; k++) mFrame[k] = mRingBuf[(trigPos+k)%BUF_SIZE];
            mNewFrame = true;
        }
        postInvalidate();
    }

    @Override
    protected void onDraw(Canvas canvas) {
        final float w = getWidth(), h = getHeight(); if (w==0||h==0) return;
        for (int gx=1; gx<4; gx++) canvas.drawLine(w*gx/4f,0,w*gx/4f,h,mGridPaint);
        for (int gy=1; gy<4; gy++) canvas.drawLine(0,h*gy/4f,w,h*gy/4f,mGridPaint);
        Paint zeroPaint = new Paint(mGridPaint); zeroPaint.setColor(0x55FFFFFF); zeroPaint.setStrokeWidth(1.4f); canvas.drawLine(0,h/2f,w,h/2f,zeroPaint);
        Paint trigPaint = new Paint(); trigPaint.setColor(0x88FFFF00); trigPaint.setStrokeWidth(1f); trigPaint.setStyle(Paint.Style.STROKE); trigPaint.setPathEffect(new DashPathEffect(new float[]{6f,4f},0)); canvas.drawLine(0,h/2f-TRIG_LEVEL*h/2f,w,h/2f-TRIG_LEVEL*h/2f,trigPaint);
        float[] frame; synchronized (mLock) { frame = mFrame.clone(); }
        for (int i=0; i<DISP_SAMPLES-1; i++) { float x0=i*w/(DISP_SAMPLES-1f), x1=(i+1)*w/(DISP_SAMPLES-1f); canvas.drawLine(x0, h/2f-frame[i]*h/2f*0.92f, x1, h/2f-frame[i+1]*h/2f*0.92f, mWavePaint); }
        canvas.drawText("OSC  T↑", 4, h-3f, mLabelPaint);
    }
}

static class EnvelopeView extends View {
    private static final int HIST=1000, CHUNK=441;
    private final float[] mEnv = new float[HIST]; private int mWritePos=0, mFilled=0; private float mAccPeak=0f; private int mAccCount=0; private final Object mLock=new Object();
    private final Paint mSegPaint=new Paint(Paint.ANTI_ALIAS_FLAG), mGridPaint=new Paint(Paint.ANTI_ALIAS_FLAG), mLabelPaint=new Paint(Paint.ANTI_ALIAS_FLAG);
    EnvelopeView(Context c) { super(c); setBackgroundColor(0x00000000); float d=c.getResources().getDisplayMetrics().density; mSegPaint.setStyle(Paint.Style.STROKE); mSegPaint.setStrokeWidth(1.6f*d); mSegPaint.setStrokeCap(Paint.Cap.ROUND); mGridPaint.setColor(0x33FFFFFF); mGridPaint.setStrokeWidth(0.8f); mGridPaint.setStyle(Paint.Style.STROKE); mLabelPaint.setColor(0xAAFFFFFF); mLabelPaint.setTextSize(9*d); mLabelPaint.setAntiAlias(true); }
    void pushSamples(short[] buf, int len, int channels) { synchronized(mLock) { for (int i=0; i<len; i+=channels) { float s=Math.abs(buf[i]/32768f); if (channels==2&&i+1<len) s=Math.max(s,Math.abs(buf[i+1]/32768f)); if (s>mAccPeak) mAccPeak=s; mAccCount++; if (mAccCount>=CHUNK) { mEnv[mWritePos]=mAccPeak; mWritePos=(mWritePos+1)%HIST; if (mFilled<HIST) mFilled++; mAccPeak=0f; mAccCount=0; } } } postInvalidate(); }
    @Override protected void onDraw(Canvas canvas) { final float w=getWidth(), h=getHeight(); if (w==0||h==0) return; for (int gx=1; gx<4; gx++) canvas.drawLine(w*gx/4f,0,w*gx/4f,h,mGridPaint); for (int gy=1; gy<4; gy++) canvas.drawLine(0,h*gy/4f,w,h*gy/4f,mGridPaint); Paint zeroPaint=new Paint(mGridPaint); zeroPaint.setColor(0x55FFFFFF); zeroPaint.setStrokeWidth(1.4f); canvas.drawLine(0,h/2f,w,h/2f,zeroPaint); float[] snap; int filled, writePos; synchronized(mLock) { snap=mEnv.clone(); filled=mFilled; writePos=mWritePos; } if (filled<2) { mLabelPaint.setColor(0xAAFFFFFF); canvas.drawText("ENV  10s",4,h-3f,mLabelPaint); return; } int count=Math.min(filled,HIST), start=(filled<HIST)?0:writePos; for (int i=0; i<count-1; i++) { float a0=snap[(start+i)%HIST], a1=snap[(start+i+1)%HIST]; float x0=i*w/(count-1f), x1=(i+1)*w/(count-1f); float yT0=h/2f-a0*h/2f*0.92f, yT1=h/2f-a1*h/2f*0.92f, yB0=h/2f+a0*h/2f*0.92f, yB1=h/2f+a1*h/2f*0.92f; mSegPaint.setColor(OscilloscopeView.levelColor((a0+a1)*0.5f)); canvas.drawLine(x0,yT0,x1,yT1,mSegPaint); canvas.drawLine(x0,yB0,x1,yB1,mSegPaint); } Paint curPaint=new Paint(); curPaint.setColor(0x66FFFFFF); curPaint.setStrokeWidth(1f); canvas.drawLine(w-1f,0,w-1f,h,curPaint); mLabelPaint.setColor(0xAAFFFFFF); canvas.drawText("ENV  10s",4,h-3f,mLabelPaint); }
}

static class SpectrumView extends View {
    private static final int FFT_SIZE=2048, HALF=FFT_SIZE/2;
    private final float[] mAccBuf=new float[FFT_SIZE]; private int mAccPos=0;
    private final float[] mMagnitude=new float[HALF], mSmooth=new float[HALF], mPeaks=new float[HALF]; private final Object mLock=new Object();
    private final float[] mFftRe=new float[FFT_SIZE], mFftIm=new float[FFT_SIZE], mWindow=new float[FFT_SIZE];
    private final Paint mBarPaint=new Paint(Paint.ANTI_ALIAS_FLAG), mPeakPaint=new Paint(Paint.ANTI_ALIAS_FLAG), mLblPaint=new Paint(Paint.ANTI_ALIAS_FLAG), mBgPaint=new Paint();
    private static final int DISPLAY_BINS=60; private static final float SAMPLE_RATE=44100f, DECAY=0.82f, PEAK_DECAY=0.996f;
    SpectrumView(Context c) { super(c); for (int i=0; i<FFT_SIZE; i++) mWindow[i]=0.5f*(1f-(float)Math.cos(2.0*Math.PI*i/(FFT_SIZE-1))); mBarPaint.setStyle(Paint.Style.FILL); mPeakPaint.setStyle(Paint.Style.STROKE); mPeakPaint.setColor(0xFFFFFFFF); mPeakPaint.setStrokeWidth(1.5f); mLblPaint.setColor(0xCCFFFFFF); mLblPaint.setTextSize(7.5f*c.getResources().getDisplayMetrics().density); mLblPaint.setAntiAlias(true); mBgPaint.setColor(0x00000000); }
    void pushSamples(short[] buf, int len, int channels) { for (int i=0; i<len; i+=channels) { float mono=buf[i]/32768f; if (channels==2&&i+1<len) mono=(mono+buf[i+1]/32768f)*0.5f; mAccBuf[mAccPos++]=mono; if (mAccPos>=FFT_SIZE) { computeFFT(); System.arraycopy(mAccBuf,FFT_SIZE/2,mAccBuf,0,FFT_SIZE/2); mAccPos=FFT_SIZE/2; } } }
    private void computeFFT() { for (int i=0; i<FFT_SIZE; i++) { mFftRe[i]=mAccBuf[i]*mWindow[i]; mFftIm[i]=0f; } int n=FFT_SIZE; for (int i=1,j=0; i<n; i++) { int bit=n>>1; for (; (j&bit)!=0; bit>>=1) j^=bit; j^=bit; if (i<j) { float tr=mFftRe[i]; mFftRe[i]=mFftRe[j]; mFftRe[j]=tr; float ti=mFftIm[i]; mFftIm[i]=mFftIm[j]; mFftIm[j]=ti; } } for (int len=2; len<=n; len<<=1) { double ang=-2.0*Math.PI/len; float wRe=(float)Math.cos(ang), wIm=(float)Math.sin(ang); for (int i=0; i<n; i+=len) { float curRe=1f, curIm=0f; for (int k=0; k<len/2; k++) { float uRe=mFftRe[i+k], uIm=mFftIm[i+k]; float vRe=mFftRe[i+k+len/2]*curRe - mFftIm[i+k+len/2]*curIm; float vIm=mFftRe[i+k+len/2]*curIm + mFftIm[i+k+len/2]*curRe; mFftRe[i+k]=uRe+vRe; mFftIm[i+k]=uIm+vIm; mFftRe[i+k+len/2]=uRe-vRe; mFftIm[i+k+len/2]=uIm-vIm; float nRe=curRe*wRe - curIm*wIm; curIm=curRe*wIm + curIm*wRe; curRe=nRe; } } } synchronized (mLock) { for (int i=0; i<HALF; i++) { float mag=(float)Math.sqrt(mFftRe[i]*mFftRe[i]+mFftIm[i]*mFftIm[i])/(FFT_SIZE/2f); float db=mag>1e-9f?Math.max(-90f,(float)(20.0*Math.log10(mag))):-90f; float norm=(db+90f)/90f; mMagnitude[i]=norm; mSmooth[i]=Math.max(norm, mSmooth[i]*DECAY); mPeaks[i]=Math.max(mSmooth[i], mPeaks[i]*PEAK_DECAY); } } postInvalidate(); }
    @Override protected void onDraw(Canvas canvas) { final float w=getWidth(), h=getHeight(); if (w==0||h==0) return; final float lblH=mLblPaint.getTextSize()+4f, barTop=lblH, barAreaH=h-barTop; float[] freqMarks={50,100,200,500,1000,2000,5000,10000,20000}; String[] freqLabels={"50","100","200","500","1k","2k","5k","10k","20k"}; float fMin=(float)Math.log10(20.0), fMax=(float)Math.log10(SAMPLE_RATE/2f); Paint gridPaint=new Paint(); gridPaint.setColor(0x44FFFFFF); gridPaint.setStrokeWidth(0.8f); for (int fi=0; fi<freqMarks.length; fi++) { if (freqMarks[fi]>SAMPLE_RATE/2f) break; float xf=((float)Math.log10(freqMarks[fi])-fMin)/(fMax-fMin)*w; canvas.drawLine(xf, barTop, xf, h, gridPaint); } float[] smooth, peaks; synchronized (mLock) { smooth=mSmooth.clone(); peaks=mPeaks.clone(); } float logFMin=(float)Math.log10(Math.max(1f,20f)), logFMaxV=(float)Math.log10(SAMPLE_RATE/2f); for (int b=0; b<DISPLAY_BINS; b++) { float logF0=logFMin + (float)b/DISPLAY_BINS*(logFMaxV-logFMin), logF1=logFMin + (float)(b+1)/DISPLAY_BINS*(logFMaxV-logFMin); float f0=(float)Math.pow(10.0, logF0), f1=(float)Math.pow(10.0, logF1); int bin0=Math.max(0, Math.round(f0/SAMPLE_RATE*FFT_SIZE)), bin1=Math.min(HALF-1, Math.round(f1/SAMPLE_RATE*FFT_SIZE)); float val=0f, pk=0f; for (int i=bin0; i<=bin1; i++) { if (smooth[i]>val) val=smooth[i]; if (peaks[i]>pk) pk=peaks[i]; } float x0=(float)b/DISPLAY_BINS*w, x1=(float)(b+1)/DISPLAY_BINS*w-1f; if (x1<x0+0.5f) x1=x0+0.5f; int red=Math.min(255,(int)(val*510f)), green=Math.min(255,(int)((1f-val)*510f)); mBarPaint.setColor(0xDD000000|(red<<16)|(green<<8)|0x22); float barH=val*barAreaH; canvas.drawRect(x0, h-barH, x1, h, mBarPaint); if (pk>0.02f) { float peakY=h-pk*barAreaH; canvas.drawLine(x0, peakY, x1, peakY, mPeakPaint); } } float labelY=lblH-4f, prevLblRight=-1f; mLblPaint.setTextAlign(Paint.Align.CENTER); for (int fi=0; fi<freqMarks.length; fi++) { if (freqMarks[fi]>SAMPLE_RATE/2f) break; float xf=((float)Math.log10(freqMarks[fi])-fMin)/(fMax-fMin)*w; float lblW=mLblPaint.measureText(freqLabels[fi]), lblX=xf-lblW/2f; if (lblX>prevLblRight && lblX+lblW<w-2f) { canvas.drawText(freqLabels[fi], xf, labelY, mLblPaint); prevLblRight=lblX+lblW+3f; } } }
}

// Закрывающая скобка класса MainActivity
}