// Form1.cs - 修复搜索框输入法问题 - 使用独立输入窗口方案

using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing.Drawing2D;
using System.Drawing.Imaging;
using System.Linq;
using System;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Threading;
using System.Windows.Forms;
using System.IO;
using System.Media;
using WMPLib;
using NAudio.Wave;
using NAudio.Dsp;

namespace DynamicIsland
{
    public class ContentItem
    {
        public string Text { get; set; }
        public string SubText { get; set; }
        public Font Font { get; set; }
        public Font SubFont { get; set; }
        public Color Color { get; set; }
        public Color SubColor { get; set; }
        public float TargetScale { get; set; } = 1.0f;
        public float CurrentScale { get; set; } = 0.0f;
        public float CurrentAlpha { get; set; } = 0.0f;
        public bool IsActive { get; set; } = false;
        public DateTime ShowTime { get; set; }
        public TimeSpan Duration { get; set; }
        public bool IsClickable { get; set; } = false;
        public Action OnConfirm { get; set; }
        public Action OnCancel { get; set; }

        public float ScaleVelocity { get; set; } = 0.0f;
        public float AlphaVelocity { get; set; } = 0.0f;
        public const float SpringStrength = 0.15f;
        public const float Damping = 0.75f;

        public void UpdateAnimation(float deltaMs)
        {
            float dt = Math.Min(deltaMs / 1000f, 0.05f) * 60;

            float scaleDisplacement = TargetScale - CurrentScale;
            float scaleForce = scaleDisplacement * SpringStrength;
            ScaleVelocity += scaleForce * dt;
            ScaleVelocity *= Damping;
            CurrentScale += ScaleVelocity * dt;

            float targetAlpha = IsActive ? 255f : 0f;
            float alphaDisplacement = targetAlpha - CurrentAlpha;
            float alphaForce = alphaDisplacement * SpringStrength;
            AlphaVelocity += alphaForce * dt;
            AlphaVelocity *= Damping;
            CurrentAlpha += AlphaVelocity * dt;

            if (Math.Abs(scaleDisplacement) < 0.01f && Math.Abs(ScaleVelocity) < 0.01f)
            {
                CurrentScale = TargetScale;
                ScaleVelocity = 0;
            }
            if (Math.Abs(alphaDisplacement) < 1f && Math.Abs(AlphaVelocity) < 1f)
            {
                CurrentAlpha = targetAlpha;
                AlphaVelocity = 0;
            }
        }

        public bool ShouldRemove => !IsActive && CurrentAlpha <= 1f;
    }

    public class Form1 : Form
    {
        private const string MUTEX_NAME = "DynamicIsland_SingleInstance_Mutex_v1";
        private const string WM_SHOWINSTANCE = "WM_DynamicIsland_ShowInstance_v2";
        private static Mutex _mutex;
        private static uint WM_SHOWINSTANCE_MESSAGE = 0;

        private const int WM_CLIPBOARDUPDATE = 0x031D;
        private string _lastClipboardText = "";
        private DateTime _lastClipboardCheck = DateTime.MinValue;
        private readonly TimeSpan _clipboardDebounce = TimeSpan.FromSeconds(2);

        private bool _isMusicMode = false;
        private bool _isMusicModeExpanded = true;
        private string _musicModeState = "waiting";
        private bool _isPlaying = false;
        private string _currentFileName = "";
        private TimeSpan _currentPosition = TimeSpan.Zero;
        private TimeSpan _totalDuration = TimeSpan.FromMinutes(3);
        private System.Windows.Forms.Timer _musicProgressTimer;
        private RectangleF _playPauseButtonRect;
        private RectangleF _progressBarRect;
        private Font _largeTimeFont;
        private Font _hintFont;
        private Font _musicFileFont;
        private Font _musicTimeFont;
        private DateTime _musicModeStartTime;
        private bool _altKeyPressed = false;

        // 搜索模式 - 使用自定义绘制而非真实 TextBox
        private bool _isSearchMode = false;
        private string _searchText = "";
        private RectangleF _searchBoxRect;
        private RectangleF _searchIconRect;
        private DateTime _lastSearchTime = DateTime.MinValue;
        private readonly TimeSpan _searchDebounce = TimeSpan.FromMilliseconds(300);
        private System.Windows.Forms.Timer _cursorTimer;
        private bool _cursorVisible = true;
        private int _cursorPosition = 0;

        // IMM (输入法管理器) 相关
        private IntPtr _imcHandle = IntPtr.Zero;
        private bool _immEnabled = false;

        private WindowsMediaPlayer _mediaPlayer;
        private string _currentAudioFilePath = "";

        private WasapiLoopbackCapture _audioCapture;
        private float[] _audioBars = new float[8] { 0.15f, 0.15f, 0.15f, 0.15f, 0.15f, 0.15f, 0.15f, 0.15f };
        private float[] _audioBarTargets = new float[8] { 0.15f, 0.15f, 0.15f, 0.15f, 0.15f, 0.15f, 0.15f, 0.15f };
        private System.Windows.Forms.Timer _audioVisualizerTimer;
        private readonly object _audioDataLock = new object();
        private bool _isCapturingAudio = false;
        private DateTime _lastAudioDataTime = DateTime.MinValue;

        private const int FFT_SIZE = 4096;
        private float[] _fftBuffer;
        private Complex[] _fftComplex;
        private float[] _window;
        private readonly Queue<float> _sampleQueue = new Queue<float>();

        private readonly float[] _freqBands = new float[9] { 20, 60, 150, 400, 1000, 2500, 6000, 15000, 20000 };

        private float _timeAnimationProgress = 0f;

        // 窗口位置固定，不受第三方软件影响
        private Point _fixedWindowPosition;

        // IMM API 声明
        [DllImport("imm32.dll")]
        private static extern IntPtr ImmGetContext(IntPtr hWnd);

        [DllImport("imm32.dll")]
        private static extern bool ImmReleaseContext(IntPtr hWnd, IntPtr hIMC);

        [DllImport("imm32.dll")]
        private static extern bool ImmSetCompositionWindow(IntPtr hIMC, ref COMPOSITIONFORM lpCompForm);

        [DllImport("imm32.dll")]
        private static extern bool ImmSetCandidateWindow(IntPtr hIMC, ref CANDIDATEFORM lpCandidate);

        [DllImport("imm32.dll")]
        private static extern bool ImmAssociateContext(IntPtr hWnd, IntPtr hIMC);

        [DllImport("imm32.dll")]
        private static extern IntPtr ImmCreateContext();

        [DllImport("imm32.dll")]
        private static extern bool ImmDestroyContext(IntPtr hIMC);

        [DllImport("imm32.dll")]
        private static extern bool ImmSetOpenStatus(IntPtr hIMC, bool fOpen);

        [StructLayout(LayoutKind.Sequential)]
        private struct COMPOSITIONFORM
        {
            public uint dwStyle;
            public int x;
            public int y;
            public int dxWidth;
            public int dyHeight;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct CANDIDATEFORM
        {
            public uint dwIndex;
            public uint dwStyle;
            public int x;
            public int y;
            public int dxWidth;
            public int dyHeight;
        }

        [DllImport("shcore.dll")]
        private static extern int SetProcessDpiAwareness(int awareness);

        [DllImport("user32.dll")]
        private static extern bool SetProcessDPIAware();

        static Form1()
        {
            try
            {
                SetProcessDpiAwareness(2);
            }
            catch
            {
                try
                {
                    SetProcessDPIAware();
                }
                catch { }
            }
        }

        [DllImport("user32.dll", ExactSpelling = true, SetLastError = true)]
        private static extern bool UpdateLayeredWindow(IntPtr hwnd, IntPtr hdcDst,
            ref Win32Point pptDst, ref Size psize, IntPtr hdcSrc, ref Win32Point pptSrc,
            uint crKey, ref BLENDFUNCTION pblend, uint dwFlags);

        [DllImport("user32.dll", ExactSpelling = true, SetLastError = true)]
        private static extern IntPtr GetDC(IntPtr hWnd);

        [DllImport("user32.dll", ExactSpelling = true)]
        private static extern int ReleaseDC(IntPtr hWnd, IntPtr hDC);

        [DllImport("gdi32.dll", ExactSpelling = true, SetLastError = true)]
        private static extern IntPtr CreateCompatibleDC(IntPtr hDC);

        [DllImport("gdi32.dll", ExactSpelling = true, SetLastError = true)]
        private static extern bool DeleteDC(IntPtr hdc);

        [DllImport("gdi32.dll", ExactSpelling = true, SetLastError = true)]
        private static extern IntPtr SelectObject(IntPtr hDC, IntPtr hObject);

        [DllImport("gdi32.dll", ExactSpelling = true, SetLastError = true)]
        private static extern bool DeleteObject(IntPtr hObject);

        [DllImport("user32.dll", SetLastError = true)]
        private static extern int SetWindowLong(IntPtr hWnd, int nIndex, int dwNewLong);

        [DllImport("user32.dll", SetLastError = true)]
        private static extern int GetWindowLong(IntPtr hWnd, int nIndex);

        [DllImport("user32.dll")]
        private static extern bool SetWindowPos(IntPtr hWnd, IntPtr hWndInsertAfter,
            int X, int Y, int cx, int cy, uint uFlags);

        [DllImport("user32.dll")]
        private static extern bool GetCursorPos(out POINT lpPoint);

        [DllImport("user32.dll")]
        private static extern bool ScreenToClient(IntPtr hWnd, ref POINT lpPoint);

        [DllImport("user32.dll")]
        private static extern bool TrackMouseEvent(ref TRACKMOUSEEVENT lpEventTrack);

        [DllImport("user32.dll")]
        private static extern int GetDpiForWindow(IntPtr hwnd);

        [DllImport("user32.dll")]
        private static extern IntPtr MonitorFromWindow(IntPtr hwnd, uint dwFlags);

        [DllImport("shcore.dll")]
        private static extern int GetDpiForMonitor(IntPtr hmonitor, int dpiType, out uint dpiX, out uint dpiY);

        [DllImport("user32.dll")]
        private static extern bool BringWindowToTop(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern bool ShowWindow(IntPtr hWnd, int nCmdShow);

        [DllImport("user32.dll")]
        private static extern bool IsWindow(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern bool SetWindowPos(IntPtr hWnd, int hWndInsertAfter, int X, int Y, int cx, int cy, uint uFlags);

        [DllImport("user32.dll", CharSet = CharSet.Auto)]
        private static extern IntPtr FindWindow(string lpClassName, string lpWindowName);

        [DllImport("user32.dll")]
        private static extern bool PostMessage(IntPtr hWnd, uint Msg, IntPtr wParam, IntPtr lParam);

        [DllImport("user32.dll")]
        private static extern IntPtr SendMessage(IntPtr hWnd, uint Msg, IntPtr wParam, IntPtr lParam);

        [DllImport("user32.dll", CharSet = CharSet.Unicode)]
        private static extern uint RegisterWindowMessage(string lpString);

        [DllImport("user32.dll")]
        private static extern bool IsWindowVisible(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern bool SetForegroundWindow(IntPtr hWnd);

        [DllImport("user32.dll", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        private static extern bool AddClipboardFormatListener(IntPtr hwnd);

        [DllImport("user32.dll", SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        private static extern bool RemoveClipboardFormatListener(IntPtr hwnd);

        [DllImport("user32.dll")]
        private static extern short GetAsyncKeyState(int vKey);

        [DllImport("user32.dll")]
        private static extern IntPtr SetFocus(IntPtr hWnd);

        [DllImport("user32.dll")]
        private static extern IntPtr GetFocus();

        private const int VK_MENU = 0x12;
        private const int VK_CONTROL = 0x11;

        private static readonly IntPtr HWND_TOPMOST = new IntPtr(-1);
        private const int SW_SHOWNOACTIVATE = 4;
        private const uint SWP_NOSIZE = 0x0001;
        private const uint SWP_NOMOVE = 0x0002;
        private const uint SWP_NOACTIVATE = 0x0010;
        private const uint SWP_SHOWWINDOW = 0x0040;
        private const uint SWP_FRAMECHANGED = 0x0020;
        private const uint SWP_NOSENDCHANGING = 0x0400;
        private const uint TOPMOST_FLAGS = SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_SHOWWINDOW;

        private const uint MONITOR_DEFAULTTONEAREST = 2;
        private const uint TME_LEAVE = 0x00000002;
        private const int GWL_EXSTYLE = -20;
        private const int WS_EX_LAYERED = 0x80000;
        private const int WS_EX_TOOLWINDOW = 0x80;
        private const int WS_EX_TRANSPARENT = 0x20;
        private const int WS_EX_NOACTIVATE = 0x08000000;
        private const uint ULW_ALPHA = 0x02;
        private const byte AC_SRC_OVER = 0x00;
        private const byte AC_SRC_ALPHA = 0x01;

        [StructLayout(LayoutKind.Sequential)]
        private struct POINT
        {
            public int X;
            public int Y;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct TRACKMOUSEEVENT
        {
            public uint cbSize;
            public uint dwFlags;
            public IntPtr hwndTrack;
            public uint dwHoverTime;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct BLENDFUNCTION
        {
            public byte BlendOp;
            public byte BlendFlags;
            public byte SourceConstantAlpha;
            public byte AlphaFormat;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct Win32Point
        {
            public int x, y;
            public Win32Point(int x, int y) { this.x = x; this.y = y; }
        }

        private const int BaseWindowWidth = 400;
        private const int BaseWindowHeight = 140;
        private const int BaseIslandWidth = 150;
        private const int BaseIslandHeight = 40;
        private const int BaseExpandedWidth = 320;
        private const int BaseExpandedHeight = 70;
        private const float BaseIslandTopY = 20f;

        private int WindowWidth;
        private int WindowHeight;
        private int IslandWidth;
        private int IslandHeight;
        private int ExpandedWidth;
        private int ExpandedHeight;
        private float IslandTopY;
        private float _dpiScale = 1.0f;

        private float _currentWidth;
        private float _currentHeight;
        private float _targetWidth;
        private float _targetHeight;
        private bool _isExpanded = false;

        private System.Threading.Timer _renderTimer;
        private System.Threading.Timer _topmostTimer;
        private readonly object _renderLock = new object();
        private long _lastTickTime;
        private bool _isAnimating = false;

        private float _velocityX = 0f;
        private float _velocityY = 0f;
        private const float SpringStrength = 0.12f;
        private const float Damping = 0.82f;

        private bool _mouseTracking = false;
        private bool _mouseInside = false;
        private System.Windows.Forms.Timer _mousePollingTimer;

        private Font _timeFont;
        private Font _dateFont;
        private Font _notificationFont;
        private Font _linkFont;
        private Font _buttonFont;
        private Font _promptFont;
        private StringFormat _stringFormat;

        private Bitmap _bufferBitmap;
        private Graphics _bufferGraphics;

        private Bitmap _shadowBitmap;
        private float _lastShadowWidth = -1;
        private float _lastShadowHeight = -1;
        private float shadowOpacity = 0.35f;

        private NotifyIcon _notifyIcon;
        private ContextMenuStrip _contextMenu;
        private bool _isExiting = false;

        private ContentItem _currentContent;
        private ContentItem _nextContent;
        private System.Windows.Forms.Timer _autoPopupTimer;
        private bool _isAutoPopupActive = false;

        private System.Threading.Timer _hardwareMonitorTimer;
        private bool _wasOnline = false;
        private string _lastSSID = null;
        private HashSet<string> _lastBluetoothDevices = new HashSet<string>();
        private readonly object _hardwareLock = new object();

        private bool _isLinkDialogActive = false;
        private string _pendingLink = null;
        private RectangleF _confirmButtonRect;
        private bool _isClickableMode = false;

        public static bool IsAlreadyRunning()
        {
            bool createdNew;
            _mutex = new Mutex(true, MUTEX_NAME, out createdNew);
            return !createdNew;
        }

        public static void ActivateExistingInstance()
        {
            try
            {
                uint msg = RegisterWindowMessage(WM_SHOWINSTANCE);
                IntPtr hWnd = IntPtr.Zero;
                hWnd = FindWindow(null, "Dynamic Island");

                if (hWnd == IntPtr.Zero)
                {
                    Process currentProcess = Process.GetCurrentProcess();
                    Process[] processes = Process.GetProcessesByName(currentProcess.ProcessName);
                    foreach (Process process in processes)
                    {
                        if (process.Id != currentProcess.Id && process.MainWindowHandle != IntPtr.Zero)
                        {
                            hWnd = process.MainWindowHandle;
                            break;
                        }
                    }
                }

                if (hWnd != IntPtr.Zero)
                {
                    if (!IsWindowVisible(hWnd))
                    {
                        ShowWindow(hWnd, 4);
                    }
                    IntPtr result = SendMessage(hWnd, msg, new IntPtr(1), IntPtr.Zero);
                    SetForegroundWindow(hWnd);
                    BringWindowToTop(hWnd);
                }
            }
            catch (Exception ex)
            {
                Debug.WriteLine($"ActivateExistingInstance error: {ex.Message}");
            }
        }

        public Form1()
        {
            CalculateScaledSizes();
            _currentWidth = IslandWidth;
            _currentHeight = IslandHeight;
            _targetWidth = IslandWidth;
            _targetHeight = IslandHeight;
            InitializeComponent();

            _fftBuffer = new float[FFT_SIZE];
            _fftComplex = new Complex[FFT_SIZE];
            _window = new float[FFT_SIZE];

            for (int i = 0; i < FFT_SIZE; i++)
            {
                _window[i] = 0.5f * (1 - (float)Math.Cos(2 * Math.PI * i / (FFT_SIZE - 1)));
            }

            WM_SHOWINSTANCE_MESSAGE = RegisterWindowMessage(WM_SHOWINSTANCE);
        }

        private float GetDpiScale()
        {
            try { using (Graphics g = Graphics.FromHwnd(IntPtr.Zero)) return g.DpiX / 96f; }
            catch { return 1.0f; }
        }

        private void CalculateScaledSizes()
        {
            _dpiScale = GetDpiScale();
            WindowWidth = (int)(BaseWindowWidth * _dpiScale);
            WindowHeight = (int)(BaseWindowHeight * _dpiScale);
            IslandWidth = (int)(BaseIslandWidth * _dpiScale);
            IslandHeight = (int)(BaseIslandHeight * _dpiScale);
            ExpandedWidth = (int)(BaseExpandedWidth * _dpiScale);
            ExpandedHeight = (int)(BaseExpandedHeight * _dpiScale);
            IslandTopY = BaseIslandTopY * _dpiScale;
        }

        private void InitializeComponent()
        {
            this.Text = "Dynamic Island";
            this.Size = new Size(WindowWidth, WindowHeight);
            this.StartPosition = FormStartPosition.Manual;

            // 使用 Bounds 替代 WorkingArea，避免受第三方软件影响
            var screen = Screen.PrimaryScreen.Bounds;
            _fixedWindowPosition = new Point((screen.Width - WindowWidth) / 2, 0);
            this.Location = _fixedWindowPosition;

            this.FormBorderStyle = FormBorderStyle.None;
            this.ShowInTaskbar = false;
            this.AllowDrop = true;
            this.Load += Form1_Load;

            float timeFontSize = 17f * _dpiScale;
            float dateFontSize = 11f * _dpiScale;
            float notificationFontSize = 22f * _dpiScale;
            float linkFontSize = 12f * _dpiScale;
            float buttonFontSize = 13f * _dpiScale;
            float promptFontSize = 15f * _dpiScale;
            float largeTimeFontSize = 24f * _dpiScale;
            float hintFontSize = 10f * _dpiScale;
            float musicFileFontSize = 12f * _dpiScale;
            float musicTimeFontSize = 11f * _dpiScale;

            _timeFont = new Font("Microsoft YaHei", timeFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _dateFont = new Font("Microsoft YaHei", dateFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _notificationFont = new Font("Microsoft YaHei", notificationFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _linkFont = new Font("Microsoft YaHei", linkFontSize, FontStyle.Regular, GraphicsUnit.Pixel);
            _buttonFont = new Font("Microsoft YaHei", buttonFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _promptFont = new Font("Microsoft YaHei", promptFontSize, FontStyle.Bold, GraphicsUnit.Pixel);

            _largeTimeFont = new Font("Microsoft YaHei", largeTimeFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _hintFont = new Font("Microsoft YaHei", hintFontSize, FontStyle.Regular, GraphicsUnit.Pixel);
            _musicFileFont = new Font("Microsoft YaHei", musicFileFontSize, FontStyle.Regular, GraphicsUnit.Pixel);
            _musicTimeFont = new Font("Microsoft YaHei", musicTimeFontSize, FontStyle.Regular, GraphicsUnit.Pixel);

            _stringFormat = new StringFormat
            {
                Alignment = StringAlignment.Center,
                LineAlignment = StringAlignment.Center
            };

            this.MouseMove += Form1_MouseMove;
            this.MouseLeave += Form1_MouseLeave;
            this.MouseDown += Form1_MouseDown;
            this.MouseUp += Form1_MouseUp;
            this.DragEnter += Form1_DragEnter;
            this.DragDrop += Form1_DragDrop;
            this.KeyDown += Form1_KeyDown;
            this.KeyPress += Form1_KeyPress;
            this.KeyPreview = true;

            _cursorTimer = new System.Windows.Forms.Timer { Interval = 530 };
            _cursorTimer.Tick += (s, e) =>
            {
                if (_isSearchMode)
                {
                    _cursorVisible = !_cursorVisible;
                    RequestRender();
                }
            };
        }

        private void InitializeTrayIcon()
        {
            _contextMenu = new ContextMenuStrip();
            ToolStripMenuItem exitMenuItem = new ToolStripMenuItem("退出");
            exitMenuItem.Click += ExitMenuItem_Click;
            _contextMenu.Items.Add(exitMenuItem);

            _notifyIcon = new NotifyIcon
            {
                Text = "Csharp Island",
                Visible = true,
                ContextMenuStrip = _contextMenu
            };

            try { _notifyIcon.Icon = SystemIcons.Application; }
            catch
            {
                using (Bitmap bmp = new Bitmap(16, 16))
                {
                    using (Graphics g = Graphics.FromImage(bmp)) g.Clear(Color.Black);
                    _notifyIcon.Icon = Icon.FromHandle(bmp.GetHicon());
                }
            }
        }

        private void ExitMenuItem_Click(object sender, EventArgs e)
        {
            if (_isExiting) return;
            _isExiting = true;

            try
            {
                if (_notifyIcon != null)
                {
                    _notifyIcon.Visible = false;
                }
            }
            catch { }

            this.BeginInvoke(new Action(() =>
            {
                try
                {
                    CleanupResources();
                }
                catch (Exception ex)
                {
                    Debug.WriteLine($"Exit error: {ex.Message}");
                }
                finally
                {
                    Environment.Exit(0);
                }
            }));
        }

        private void CleanupResources()
        {
            if (this.IsHandleCreated)
            {
                try
                {
                    RemoveClipboardFormatListener(this.Handle);
                }
                catch { }
            }

            StopAudioCapture();

            _renderTimer?.Dispose();
            _topmostTimer?.Dispose();
            _mousePollingTimer?.Stop();
            _mousePollingTimer?.Dispose();
            _autoPopupTimer?.Stop();
            _autoPopupTimer?.Dispose();
            _hardwareMonitorTimer?.Dispose();
            _musicProgressTimer?.Stop();
            _musicProgressTimer?.Dispose();
            _audioVisualizerTimer?.Stop();
            _audioVisualizerTimer?.Dispose();

            _cursorTimer?.Stop();
            _cursorTimer?.Dispose();

            // 清理 IMM 上下文
            if (_imcHandle != IntPtr.Zero)
            {
                try
                {
                    ImmDestroyContext(_imcHandle);
                }
                catch { }
                _imcHandle = IntPtr.Zero;
            }

            if (_mediaPlayer != null)
            {
                try
                {
                    _mediaPlayer.controls.stop();
                    _mediaPlayer.close();
                }
                catch { }
                _mediaPlayer = null;
            }

            _currentContent = null;
            _nextContent = null;

            _timeFont?.Dispose();
            _dateFont?.Dispose();
            _notificationFont?.Dispose();
            _linkFont?.Dispose();
            _buttonFont?.Dispose();
            _promptFont?.Dispose();
            _largeTimeFont?.Dispose();
            _hintFont?.Dispose();
            _musicFileFont?.Dispose();
            _musicTimeFont?.Dispose();
            _stringFormat?.Dispose();
            _bufferGraphics?.Dispose();
            _bufferBitmap?.Dispose();
            _shadowBitmap?.Dispose();

            if (_notifyIcon != null)
            {
                try
                {
                    _notifyIcon.Dispose();
                }
                catch { }
                _notifyIcon = null;
            }
            _contextMenu?.Dispose();
        }
        private bool IsValidUrl(string text)
        {
            if (string.IsNullOrWhiteSpace(text) || text.Length > 2000)
                return false;

            string[] schemes = { "http://", "https://", "ftp://", "file://" };
            bool hasScheme = schemes.Any(s => text.StartsWith(s, StringComparison.OrdinalIgnoreCase));

            if (!hasScheme)
            {
                if (!text.Contains(".") || text.Contains(" "))
                    return false;

                string[] nonUrlPatterns = { "\n", "\r", "\\", ";", "|", "<", ">", "\"", "'" };
                if (nonUrlPatterns.Any(p => text.Contains(p)))
                    return false;

                var domainRegex = new Regex(@"^[a-zA-Z0-9]([a-zA-Z0-9\-]{0,61}[a-zA-Z0-9])?(\.[a-zA-Z0-9]([a-zA-Z0-9\-]{0,61}[a-zA-Z0-9])?)*$", RegexOptions.IgnoreCase);
                string domainPart = text.Split('/')[0].Split(':')[0];
                if (!domainRegex.IsMatch(domainPart))
                    return false;

                return true;
            }

            try
            {
                Uri uri = new Uri(text);
                return uri.Scheme == Uri.UriSchemeHttp ||
                       uri.Scheme == Uri.UriSchemeHttps ||
                       uri.Scheme == Uri.UriSchemeFtp ||
                       uri.Scheme == Uri.UriSchemeFile;
            }
            catch
            {
                return false;
            }
        }

        private string FormatLinkForDisplay(string link, int maxLength = 40)
        {
            if (string.IsNullOrEmpty(link))
                return "";

            string display = link;
            if (display.StartsWith("https://", StringComparison.OrdinalIgnoreCase))
                display = display.Substring(8);
            else if (display.StartsWith("http://", StringComparison.OrdinalIgnoreCase))
                display = display.Substring(7);
            else if (display.StartsWith("ftp://", StringComparison.OrdinalIgnoreCase))
                display = display.Substring(6);

            if (display.Length > maxLength)
                display = display.Substring(0, maxLength - 3) + "...";

            return display;
        }

        private void ProcessClipboardLink(string link)
        {
            if (_isLinkDialogActive || _isMusicMode || _isSearchMode)
                return;

            if (link == _lastClipboardText &&
                (DateTime.Now - _lastClipboardCheck) < _clipboardDebounce)
                return;

            _lastClipboardText = link;
            _lastClipboardCheck = DateTime.Now;
            _pendingLink = link;

            this.BeginInvoke(new Action(() =>
            {
                ShowLinkConfirmationDialog(link);
            }));
        }

        private void ShowLinkConfirmationDialog(string link)
        {
            _isLinkDialogActive = true;
            _isAutoPopupActive = true;

            SetClickableMode(true);

            SetExpanded(true);
            _targetWidth = ExpandedWidth;
            _targetHeight = ExpandedHeight;

            var linkItem = new ContentItem
            {
                Text = "检测到链接，是否打开？",
                SubText = FormatLinkForDisplay(link),
                Font = _promptFont,
                SubFont = _linkFont,
                Color = Color.White,
                SubColor = Color.FromArgb(200, 200, 200),
                TargetScale = 1.0f,
                CurrentScale = 0.5f,
                CurrentAlpha = 0f,
                IsActive = true,
                Duration = TimeSpan.FromSeconds(5),
                IsClickable = true,
                OnConfirm = () =>
                {
                    OpenLink(link);
                    CloseLinkDialog();
                }
            };

            TransitionToContent(linkItem);

            _autoPopupTimer?.Stop();
            _autoPopupTimer?.Dispose();
            _autoPopupTimer = new System.Windows.Forms.Timer { Interval = 5000 };
            _autoPopupTimer.Tick += (s, e) =>
            {
                if (!_mouseInside)
                {
                    CloseLinkDialog();
                }
            };
            _autoPopupTimer.Start();
        }

        private void OpenLink(string link)
        {
            try
            {
                string url = link;
                if (!url.StartsWith("http://", StringComparison.OrdinalIgnoreCase) &&
                    !url.StartsWith("https://", StringComparison.OrdinalIgnoreCase) &&
                    !url.StartsWith("ftp://", StringComparison.OrdinalIgnoreCase) &&
                    !url.StartsWith("file://", StringComparison.OrdinalIgnoreCase))
                {
                    url = "https://" + url;
                }

                Process.Start(new ProcessStartInfo
                {
                    FileName = url,
                    UseShellExecute = true
                });
            }
            catch (Exception ex)
            {
                ShowNotification($"无法打开链接: {ex.Message}", TimeSpan.FromSeconds(3));
            }
        }

        private void CloseLinkDialog()
        {
            if (!_isLinkDialogActive)
                return;

            _isLinkDialogActive = false;
            _pendingLink = null;

            _autoPopupTimer?.Stop();
            _autoPopupTimer?.Dispose();
            _autoPopupTimer = null;

            SetClickableMode(false);

            SetExpanded(false);

            var timeItem = new ContentItem
            {
                Text = DateTime.Now.ToString("HH:mm:ss"),
                Font = _timeFont,
                Color = Color.White,
                TargetScale = 1.0f,
                CurrentScale = 0.8f,
                CurrentAlpha = 0f,
                IsActive = true,
                Duration = TimeSpan.Zero
            };

            TransitionToContent(timeItem);
            _isAutoPopupActive = false;
        }

        private void SetClickableMode(bool clickable)
        {
            if (_isClickableMode == clickable)
                return;

            _isClickableMode = clickable;

            if (this.IsDisposed || !this.IsHandleCreated)
                return;

            int exStyle = GetWindowLong(this.Handle, GWL_EXSTYLE);

            if (clickable)
            {
                exStyle &= ~WS_EX_TRANSPARENT;
            }
            else
            {
                exStyle |= WS_EX_TRANSPARENT;
            }

            SetWindowLong(this.Handle, GWL_EXSTYLE, exStyle);
            SetWindowPos(this.Handle, HWND_TOPMOST, 0, 0, 0, 0,
                SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_FRAMECHANGED);
        }

        private void ToggleMusicMode()
        {
            if (_isMusicMode)
            {
                ExitMusicMode();
            }
            else
            {
                EnterMusicMode();
            }
        }

        private void EnterMusicMode()
        {
            _isMusicMode = true;
            _isMusicModeExpanded = true;
            _musicModeState = "waiting";
            _musicModeStartTime = DateTime.Now;
            _currentFileName = "";
            _currentPosition = TimeSpan.Zero;
            _isPlaying = false;

            for (int i = 0; i < 8; i++)
            {
                _audioBars[i] = 0.15f;
                _audioBarTargets[i] = 0.15f;
            }

            SetClickableMode(true);
            SetExpanded(true);

            if (_musicProgressTimer == null)
            {
                _musicProgressTimer = new System.Windows.Forms.Timer { Interval = 1000 };
                _musicProgressTimer.Tick += MusicProgressTimer_Tick;
            }
            _musicProgressTimer.Start();

            if (_audioVisualizerTimer == null)
            {
                _audioVisualizerTimer = new System.Windows.Forms.Timer { Interval = 16 };
                _audioVisualizerTimer.Tick += AudioVisualizerTimer_Tick;
            }
            _audioVisualizerTimer.Start();

            RequestRender();
        }

        private void ExitMusicMode()
        {
            StopAudioCapture();

            if (_mediaPlayer != null)
            {
                try
                {
                    _mediaPlayer.controls.stop();
                    _mediaPlayer.close();
                }
                catch { }
                _mediaPlayer = null;
            }

            _isMusicMode = false;
            _isMusicModeExpanded = true;
            _musicModeState = "waiting";
            _isPlaying = false;
            _currentAudioFilePath = "";
            _musicProgressTimer?.Stop();
            _audioVisualizerTimer?.Stop();
            SetClickableMode(false);
            SetExpanded(false);

            var timeItem = new ContentItem
            {
                Text = DateTime.Now.ToString("HH:mm:ss"),
                Font = _timeFont,
                Color = Color.White,
                TargetScale = 1.0f,
                CurrentScale = 0.8f,
                CurrentAlpha = 0f,
                IsActive = true,
                Duration = TimeSpan.Zero
            };
            TransitionToContent(timeItem);
        }

        private void MinimizeMusicMode()
        {
            _isMusicModeExpanded = false;
            SetExpanded(false);
            RequestRender();
        }

        private void ExpandMusicMode()
        {
            _isMusicModeExpanded = true;
            SetExpanded(true);
            RequestRender();
        }

        private void StartAudioCapture()
        {
            if (_isCapturingAudio) return;

            try
            {
                lock (_sampleQueue)
                {
                    _sampleQueue.Clear();
                }

                _audioCapture = new WasapiLoopbackCapture();
                _audioCapture.DataAvailable += AudioCapture_DataAvailable;
                _audioCapture.RecordingStopped += (sender, e) => { _isCapturingAudio = false; };

                _audioCapture.StartRecording();
                _isCapturingAudio = true;
                _lastAudioDataTime = DateTime.Now;
            }
            catch
            {
                _isCapturingAudio = false;
            }
        }

        private void AudioCapture_DataAvailable(object sender, WaveInEventArgs e)
        {
            try
            {
                _lastAudioDataTime = DateTime.Now;

                if (e.BytesRecorded <= 0) return;

                int bytesPerSample = 4;

                for (int i = 0; i < e.BytesRecorded; i += bytesPerSample * 2)
                {
                    if (i + bytesPerSample * 2 <= e.BytesRecorded)
                    {
                        float left = BitConverter.ToSingle(e.Buffer, i);
                        float right = BitConverter.ToSingle(e.Buffer, i + bytesPerSample);
                        float sample = (left + right) * 0.5f;

                        lock (_sampleQueue)
                        {
                            _sampleQueue.Enqueue(sample);
                            if (_sampleQueue.Count > FFT_SIZE * 4)
                            {
                                while (_sampleQueue.Count > FFT_SIZE)
                                    _sampleQueue.Dequeue();
                            }
                        }
                    }
                }
            }
            catch { }
        }

        private void StopAudioCapture()
        {
            if (!_isCapturingAudio) return;

            try
            {
                _audioCapture?.StopRecording();
                _audioCapture?.Dispose();
                _audioCapture = null;
                _isCapturingAudio = false;

                lock (_audioDataLock)
                {
                    for (int i = 0; i < 8; i++)
                    {
                        _audioBarTargets[i] = 0.15f;
                    }
                }

                lock (_sampleQueue)
                {
                    _sampleQueue.Clear();
                }
            }
            catch { }
        }

        private void MusicProgressTimer_Tick(object sender, EventArgs e)
        {
            if (_isPlaying && _musicModeState == "playing" && _mediaPlayer != null)
            {
                try
                {
                    _currentPosition = TimeSpan.FromSeconds(_mediaPlayer.controls.currentPosition);
                    double totalSeconds = _mediaPlayer.currentMedia.duration;

                    if (_currentPosition.TotalSeconds >= totalSeconds - 0.5 && totalSeconds > 0)
                    {
                        _mediaPlayer.controls.currentPosition = 0;
                        _currentPosition = TimeSpan.Zero;
                        _mediaPlayer.controls.play();
                    }

                    RequestRender();
                }
                catch
                {
                }
            }
        }

        private void AudioVisualizerTimer_Tick(object sender, EventArgs e)
        {
            if (!_isMusicMode) return;

            float[] samples = null;
            lock (_sampleQueue)
            {
                if (_sampleQueue.Count >= FFT_SIZE)
                {
                    samples = new float[FFT_SIZE];
                    for (int i = 0; i < FFT_SIZE; i++)
                    {
                        samples[i] = _sampleQueue.Dequeue();
                    }
                }
            }

            if (samples != null)
            {
                float[] bandEnergies = PerformFFTAndGetBandEnergies(samples);

                lock (_audioDataLock)
                {
                    for (int i = 0; i < 8; i++)
                    {
                        _audioBarTargets[i] = bandEnergies[i];
                    }
                }
            }
            else
            {
                lock (_audioDataLock)
                {
                    for (int i = 0; i < 8; i++)
                    {
                        _audioBarTargets[i] = 0.15f;
                    }
                }
            }

            for (int i = 0; i < 8; i++)
            {
                float diff = _audioBarTargets[i] - _audioBars[i];
                float smoothing = 0.35f;
                _audioBars[i] += diff * smoothing;
                _audioBars[i] = Math.Max(0.15f, Math.Min(1.0f, _audioBars[i]));
            }

            RequestRender();
        }

        private float[] PerformFFTAndGetBandEnergies(float[] samples)
        {
            float[] bandEnergies = new float[8];

            try
            {
                for (int i = 0; i < FFT_SIZE; i++)
                {
                    _fftComplex[i].X = samples[i] * _window[i];
                    _fftComplex[i].Y = 0;
                }

                int log2n = (int)Math.Log(FFT_SIZE, 2);
                FastFourierTransform.FFT(true, log2n, _fftComplex);

                float sampleRate = 44100f;
                float freqResolution = sampleRate / FFT_SIZE;

                int[] bandBinStart = new int[8];
                int[] bandBinEnd = new int[8];

                for (int band = 0; band < 8; band++)
                {
                    bandBinStart[band] = Math.Max(2, (int)(_freqBands[band] / freqResolution));
                    bandBinEnd[band] = Math.Min(FFT_SIZE / 2, (int)(_freqBands[band + 1] / freqResolution));
                    if (bandBinEnd[band] <= bandBinStart[band])
                        bandBinEnd[band] = bandBinStart[band] + 1;
                }

                for (int band = 0; band < 8; band++)
                {
                    float maxMagnitude = 0;
                    float sumMagnitude = 0;
                    int count = 0;

                    for (int i = bandBinStart[band]; i < bandBinEnd[band] && i < FFT_SIZE / 2; i++)
                    {
                        float real = _fftComplex[i].X;
                        float imag = _fftComplex[i].Y;
                        float magnitude = (float)Math.Sqrt(real * real + imag * imag);

                        if (magnitude > maxMagnitude)
                            maxMagnitude = magnitude;

                        sumMagnitude += magnitude;
                        count++;
                    }

                    float avgMagnitude = count > 0 ? sumMagnitude / count : 0;
                    float combinedMagnitude = maxMagnitude * 0.7f + avgMagnitude * 0.3f;

                    float[] dbRanges = { -50, -45, -40, -35, -35, -40, -45, -50 };

                    float db = 20 * (float)Math.Log10(combinedMagnitude + 1e-10f);
                    float normalized = (db - dbRanges[band]) / (0 - dbRanges[band]);

                    normalized = (float)Math.Pow(normalized, 0.7);
                    normalized = Math.Max(0.15f, Math.Min(1.0f, normalized));

                    bandEnergies[band] = normalized;
                }
            }
            catch
            {
                for (int i = 0; i < 8; i++)
                    bandEnergies[i] = 0.15f;
            }

            return bandEnergies;
        }

        private void TogglePlayPause()
        {
            if (_musicModeState == "waiting" || _mediaPlayer == null) return;

            if (_isPlaying)
            {
                _mediaPlayer.controls.pause();
                _isPlaying = false;
                _musicModeState = "paused";
                StopAudioCapture();
            }
            else
            {
                _mediaPlayer.controls.play();
                _isPlaying = true;
                _musicModeState = "playing";
                StartAudioCapture();
            }
            RequestRender();
        }

        private void Form1_DragEnter(object sender, DragEventArgs e)
        {
            if (!_isMusicMode) return;

            if (e.Data.GetDataPresent(DataFormats.FileDrop))
            {
                string[] files = (string[])e.Data.GetData(DataFormats.FileDrop);
                string[] audioExtensions = { ".mp3", ".wav", ".wma", ".m4a", ".flac", ".aac", ".ogg" };

                if (files.Any(f => audioExtensions.Contains(Path.GetExtension(f).ToLower())))
                {
                    e.Effect = DragDropEffects.Copy;
                }
            }
        }

        private void Form1_DragDrop(object sender, DragEventArgs e)
        {
            if (!_isMusicMode) return;

            string[] files = (string[])e.Data.GetData(DataFormats.FileDrop);
            string[] audioExtensions = { ".mp3", ".wav", ".wma", ".m4a", ".flac", ".aac", ".ogg" };

            var audioFile = files.FirstOrDefault(f => audioExtensions.Contains(Path.GetExtension(f).ToLower()));
            if (audioFile != null)
            {
                LoadAudioFile(audioFile);
            }
        }

        private void LoadAudioFile(string filePath)
        {
            try
            {
                if (_mediaPlayer != null)
                {
                    try
                    {
                        _mediaPlayer.controls.stop();
                        _mediaPlayer.close();
                    }
                    catch { }
                }

                StopAudioCapture();

                _mediaPlayer = new WindowsMediaPlayer();
                _mediaPlayer.URL = filePath;
                _mediaPlayer.settings.autoStart = false;

                _currentFileName = Path.GetFileNameWithoutExtension(filePath);
                _currentAudioFilePath = filePath;

                RequestRender();

                _mediaPlayer.OpenStateChange += (state) =>
                {
                    if (state == 13)
                    {
                        this.BeginInvoke(new Action(() =>
                        {
                            try
                            {
                                if (_mediaPlayer != null && _mediaPlayer.currentMedia != null)
                                {
                                    double duration = _mediaPlayer.currentMedia.duration;
                                    if (duration > 0)
                                    {
                                        _totalDuration = TimeSpan.FromSeconds(duration);
                                    }
                                    else
                                    {
                                        _totalDuration = TimeSpan.FromMinutes(3);
                                    }
                                    _currentPosition = TimeSpan.Zero;
                                    _musicModeState = "playing";
                                    _isPlaying = true;
                                    _mediaPlayer.controls.play();

                                    StartAudioCapture();

                                    RequestRender();
                                }
                            }
                            catch { }
                        }));
                    }
                };

                _mediaPlayer.MediaError += (item) =>
                {
                    this.BeginInvoke(new Action(() =>
                    {
                        ShowNotification("音频文件加载失败", TimeSpan.FromSeconds(3));
                        _musicModeState = "waiting";
                        _isPlaying = false;
                        RequestRender();
                    }));
                };
            }
            catch (Exception ex)
            {
                ShowNotification($"加载音频失败: {ex.Message}", TimeSpan.FromSeconds(3));
                _musicModeState = "waiting";
                _isPlaying = false;
            }
        }

        private string TruncateFileName(string fileName, int maxLength)
        {
            if (fileName.Length <= maxLength) return fileName;
            return fileName.Substring(0, maxLength - 3) + "...";
        }

        private bool CheckInternetConnection()
        {
            try
            {
                using (var client = new TcpClient())
                {
                    client.Connect("8.8.8.8", 53);
                    return true;
                }
            }
            catch
            {
                return false;
            }
        }

        private string GetWifiSSID()
        {
            try
            {
                var process = new Process
                {
                    StartInfo = new ProcessStartInfo
                    {
                        FileName = "netsh",
                        Arguments = "wlan show interfaces",
                        RedirectStandardOutput = true,
                        UseShellExecute = false,
                        CreateNoWindow = true,
                        StandardOutputEncoding = System.Text.Encoding.UTF8
                    }
                };
                process.Start();
                string output = process.StandardOutput.ReadToEnd();
                process.WaitForExit();

                var match = Regex.Match(output, @"SSID\s*:\s*(.+?)\r?\n");
                if (match.Success)
                {
                    return match.Groups[1].Value.Trim();
                }
                return null;
            }
            catch
            {
                return null;
            }
        }

        private HashSet<string> GetBluetoothDevices()
        {
            var devices = new HashSet<string>();
            try
            {
                var psProcess = new Process
                {
                    StartInfo = new ProcessStartInfo
                    {
                        FileName = "powershell",
                        Arguments = "-Command \"Get-PnpDevice -Class Bluetooth | Where-Object {$_.Status -eq 'OK' -and $_.FriendlyName -notmatch 'Enumerator|Adapter|Radio'} | Select-Object -ExpandProperty FriendlyName\"",
                        RedirectStandardOutput = true,
                        UseShellExecute = false,
                        CreateNoWindow = true,
                        StandardOutputEncoding = System.Text.Encoding.UTF8
                    }
                };
                psProcess.Start();
                string output = psProcess.StandardOutput.ReadToEnd();
                psProcess.WaitForExit();

                var lines = output.Split(new[] { '\r', '\n' }, StringSplitOptions.RemoveEmptyEntries);
                foreach (var line in lines)
                {
                    string name = line.Trim();
                    if (!string.IsNullOrEmpty(name))
                    {
                        devices.Add(name);
                    }
                }
            }
            catch { }
            return devices;
        }

        private void HardwareMonitorLoop(object state)
        {
            try
            {
                bool isOnline = CheckInternetConnection();
                string currentSSID = GetWifiSSID();

                lock (_hardwareLock)
                {
                    if (isOnline)
                    {
                        if (!_wasOnline)
                        {
                            string msg = !string.IsNullOrEmpty(currentSSID) ? $"{currentSSID}" : "网络已连接";
                            ShowNotification(msg, TimeSpan.FromSeconds(3));
                        }
                        else if (!string.IsNullOrEmpty(currentSSID) && currentSSID != _lastSSID)
                        {
                            ShowNotification($"{currentSSID}", TimeSpan.FromSeconds(3));
                        }
                    }

                    _wasOnline = isOnline;
                    _lastSSID = currentSSID;

                    var currentBTDevices = GetBluetoothDevices();
                    var newDevices = currentBTDevices.Except(_lastBluetoothDevices).ToList();

                    foreach (var device in newDevices)
                    {
                        ShowNotification($"蓝牙[{device}]已连接", TimeSpan.FromSeconds(3));
                    }

                    _lastBluetoothDevices = currentBTDevices;
                }
            }
            catch { }
        }

        private void Form1_Load(object sender, EventArgs e)
        {
            InitializeTrayIcon();

            int exStyle = GetWindowLong(this.Handle, GWL_EXSTYLE);
            SetWindowLong(this.Handle, GWL_EXSTYLE, exStyle | WS_EX_LAYERED | WS_EX_TOOLWINDOW | WS_EX_TRANSPARENT | WS_EX_NOACTIVATE);

            ForceSuperTopMost();

            _bufferBitmap = new Bitmap(WindowWidth, WindowHeight, PixelFormat.Format32bppPArgb);
            _bufferGraphics = Graphics.FromImage(_bufferBitmap);
            _bufferGraphics.SmoothingMode = SmoothingMode.AntiAlias;
            _bufferGraphics.TextRenderingHint = System.Drawing.Text.TextRenderingHint.AntiAliasGridFit;
            _bufferGraphics.CompositingQuality = CompositingQuality.HighQuality;
            _bufferGraphics.InterpolationMode = InterpolationMode.HighQualityBicubic;
            _bufferGraphics.PixelOffsetMode = PixelOffsetMode.HighQuality;

            _currentContent = new ContentItem
            {
                Text = DateTime.Now.ToString("HH:mm:ss"),
                Font = _timeFont,
                Color = Color.White,
                TargetScale = 1.0f,
                CurrentScale = 1.0f,
                CurrentAlpha = 255f,
                IsActive = true,
                Duration = TimeSpan.Zero
            };

            _mousePollingTimer = new System.Windows.Forms.Timer { Interval = 8 };
            _mousePollingTimer.Tick += MousePollingTimer_Tick;
            _mousePollingTimer.Start();

            _lastTickTime = DateTime.UtcNow.Ticks;
            _renderTimer = new System.Threading.Timer(state => RenderTick(state), null, 0, 8);

            _topmostTimer = new System.Threading.Timer(EnsureSuperTopMost, null, 0, 100);

            _wasOnline = CheckInternetConnection();
            _lastSSID = GetWifiSSID();
            _lastBluetoothDevices = GetBluetoothDevices();

            _hardwareMonitorTimer = new System.Threading.Timer(HardwareMonitorLoop, null, TimeSpan.FromSeconds(2), TimeSpan.FromSeconds(4));

            AddClipboardFormatListener(this.Handle);
            try
            {
                if (Clipboard.ContainsText())
                {
                    _lastClipboardText = Clipboard.GetText();
                }
            }
            catch { }

            ShowStartupNotification();
            RequestRender();
        }

        private void ForceSuperTopMost()
        {
            if (this.IsDisposed || !this.IsHandleCreated) return;

            SetWindowPos(this.Handle, HWND_TOPMOST, 0, 0, 0, 0, TOPMOST_FLAGS);
            BringWindowToTop(this.Handle);
            SetWindowPos(this.Handle, -1, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_SHOWWINDOW);
            ShowWindow(this.Handle, SW_SHOWNOACTIVATE);
        }

        private void EnsureSuperTopMost(object state)
        {
            if (this.IsDisposed || !this.IsHandleCreated || _isExiting) return;

            try
            {
                this.BeginInvoke(new Action(() =>
                {
                    if (this.IsDisposed || !this.IsHandleCreated) return;

                    SetWindowPos(this.Handle, -1, 0, 0, 0, 0,
                        SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_NOSENDCHANGING);
                }));
            }
            catch { }
        }

        private void ShowStartupNotification()
        {
            _isAutoPopupActive = true;
            SetExpanded(true);

            var startupItem = new ContentItem
            {
                Text = "C#灵动岛已启动",
                Font = _notificationFont,
                Color = Color.FromArgb(180, 229, 162),
                TargetScale = 1.0f,
                CurrentScale = 0.5f,
                CurrentAlpha = 0f,
                IsActive = true,
                Duration = TimeSpan.FromSeconds(2)
            };

            TransitionToContent(startupItem);

            _autoPopupTimer = new System.Windows.Forms.Timer { Interval = 2000 };
            _autoPopupTimer.Tick += (s, e) =>
            {
                _autoPopupTimer.Stop();
                _autoPopupTimer.Dispose();
                _autoPopupTimer = null;

                var timeItem = new ContentItem
                {
                    Text = DateTime.Now.ToString("HH:mm:ss"),
                    Font = _timeFont,
                    Color = Color.White,
                    TargetScale = 1.0f,
                    CurrentScale = 0.8f,
                    CurrentAlpha = 0f,
                    IsActive = true,
                    Duration = TimeSpan.Zero
                };

                TransitionToContent(timeItem);
                SetExpanded(false);
                _isAutoPopupActive = false;
            };
            _autoPopupTimer.Start();
        }

        public void ShowNotification(string text, TimeSpan duration, Font customFont = null, Color? customColor = null)
        {
            if (InvokeRequired)
            {
                Invoke(new Action<string, TimeSpan, Font, Color?>(ShowNotification), text, duration, customFont, customColor);
                return;
            }

            if (_isMusicMode || _isSearchMode) return;

            _isAutoPopupActive = true;
            SetExpanded(true);

            var notification = new ContentItem
            {
                Text = text,
                Font = customFont ?? _notificationFont,
                Color = customColor ?? Color.White,
                TargetScale = 1.0f,
                CurrentScale = 0.5f,
                CurrentAlpha = 0f,
                IsActive = true,
                Duration = duration
            };

            TransitionToContent(notification);

            if (duration > TimeSpan.Zero)
            {
                _autoPopupTimer?.Stop();
                _autoPopupTimer?.Dispose();
                _autoPopupTimer = new System.Windows.Forms.Timer { Interval = (int)duration.TotalMilliseconds };
                _autoPopupTimer.Tick += (s, e) =>
                {
                    _autoPopupTimer.Stop();
                    _autoPopupTimer.Dispose();
                    _autoPopupTimer = null;

                    var timeItem = new ContentItem
                    {
                        Text = DateTime.Now.ToString("HH:mm:ss"),
                        Font = _timeFont,
                        Color = Color.White,
                        TargetScale = 1.0f,
                        CurrentScale = 0.8f,
                        CurrentAlpha = 0f,
                        IsActive = true,
                        Duration = TimeSpan.Zero
                    };

                    TransitionToContent(timeItem);
                    SetExpanded(false);
                    _isAutoPopupActive = false;
                };
                _autoPopupTimer.Start();
            }
        }

        private void TransitionToContent(ContentItem newContent)
        {
            if (_currentContent != null)
            {
                _currentContent.IsActive = false;
                _nextContent = newContent;
            }
            else
            {
                _currentContent = newContent;
            }
            _isAnimating = true;
        }

        private void MousePollingTimer_Tick(object sender, EventArgs e)
        {
            bool altPressed = (GetAsyncKeyState(VK_MENU) & 0x8000) != 0;
            bool ctrlPressed = (GetAsyncKeyState(VK_CONTROL) & 0x8000) != 0;

            if (_isSearchMode)
            {
                if (ctrlPressed && !_altKeyPressed)
                {
                    ExitSearchMode();
                    _altKeyPressed = true;
                    return;
                }

                _altKeyPressed = ctrlPressed;
                return;
            }

            if (_isMusicMode)
            {
                if (GetCursorPos(out POINT pt))
                {
                    var islandScreenRect = GetIslandScreenRect();
                    float hitPadding = 8 * _dpiScale;
                    var hitRect = new RectangleF(islandScreenRect.X - hitPadding, islandScreenRect.Y - hitPadding,
                        islandScreenRect.Width + hitPadding * 2, islandScreenRect.Height + hitPadding * 2);
                    bool inside = hitRect.Contains(pt.X, pt.Y);

                    if (inside && !_isMusicModeExpanded && !_mouseInside)
                    {
                        ExpandMusicMode();
                    }
                    else if (!inside && _isMusicModeExpanded && _mouseInside)
                    {
                        MinimizeMusicMode();
                    }

                    _mouseInside = inside;
                }

                if (altPressed && !_altKeyPressed && _mouseInside)
                {
                    _altKeyPressed = true;
                    ExitMusicMode();
                    return;
                }
                else if (!altPressed)
                {
                    _altKeyPressed = false;
                }
                return;
            }

            if (_isLinkDialogActive)
            {
                if (GetCursorPos(out POINT pt))
                {
                    var islandScreenRect = GetIslandScreenRect();
                    float hitPadding = 8 * _dpiScale;
                    var hitRect = new RectangleF(islandScreenRect.X - hitPadding, islandScreenRect.Y - hitPadding,
                        islandScreenRect.Width + hitPadding * 2, islandScreenRect.Height + hitPadding * 2);
                    bool inside = hitRect.Contains(pt.X, pt.Y);

                    if (!inside && _mouseInside)
                    {
                        CloseLinkDialog();
                        return;
                    }
                    _mouseInside = inside;
                }
                return;
            }

            if (altPressed && !_altKeyPressed && _isExpanded && !_isMusicMode && !_isLinkDialogActive && !_isAutoPopupActive)
            {
                _altKeyPressed = true;
                ToggleMusicMode();
                return;
            }

            if (ctrlPressed && !_altKeyPressed && _isExpanded && !_isMusicMode && !_isLinkDialogActive && !_isAutoPopupActive && !_isSearchMode)
            {
                _altKeyPressed = true;
                EnterSearchMode();
                return;
            }

            if (!altPressed && !ctrlPressed)
            {
                _altKeyPressed = false;
            }

            if (_isAutoPopupActive) return;

            if (GetCursorPos(out POINT pt2))
            {
                var islandScreenRect = GetIslandScreenRect();
                float hitPadding = 8 * _dpiScale;
                var hitRect = new RectangleF(islandScreenRect.X - hitPadding, islandScreenRect.Y - hitPadding,
                    islandScreenRect.Width + hitPadding * 2, islandScreenRect.Height + hitPadding * 2);
                bool inside = hitRect.Contains(pt2.X, pt2.Y);
                if (inside != _mouseInside)
                {
                    _mouseInside = inside;
                    SetExpanded(inside);
                }
            }
        }

        private void EnterSearchMode()
        {
            _isSearchMode = true;
            _searchText = "";
            _cursorPosition = 0;
            _cursorVisible = true;

            // 修改窗口样式以允许输入
            if (this.IsHandleCreated && !this.IsDisposed)
            {
                int exStyle = GetWindowLong(this.Handle, GWL_EXSTYLE);
                // 移除 NOACTIVATE 和 TRANSPARENT，保留 LAYERED
                int newStyle = (exStyle & ~WS_EX_NOACTIVATE & ~WS_EX_TRANSPARENT) | WS_EX_LAYERED;
                SetWindowLong(this.Handle, GWL_EXSTYLE, newStyle);
                SetWindowPos(this.Handle, HWND_TOPMOST, 0, 0, 0, 0,
                    SWP_NOMOVE | SWP_NOSIZE | SWP_FRAMECHANGED | SWP_SHOWWINDOW);
            }

            // 激活窗口并设置输入法
            this.BeginInvoke(new Action(() =>
            {
                SetForegroundWindow(this.Handle);
                this.Focus();
                this.Activate();

                // 创建并关联输入法上下文
                try
                {
                    _imcHandle = ImmCreateContext();
                    if (_imcHandle != IntPtr.Zero)
                    {
                        ImmAssociateContext(this.Handle, _imcHandle);
                        ImmSetOpenStatus(_imcHandle, true);
                        _immEnabled = true;
                    }
                }
                catch (Exception ex)
                {
                    Debug.WriteLine($"IMM init error: {ex.Message}");
                }

                // 设置输入法候选框位置
                UpdateImmPosition();
            }));

            _cursorTimer?.Start();
            SetClickableMode(true);
            SetExpanded(true);
            RequestRender();
        }

        private void UpdateImmPosition()
        {
            if (!_immEnabled || _imcHandle == IntPtr.Zero) return;

            try
            {
                // 计算搜索框位置
                float margin = 20 * _dpiScale;
                float searchBoxHeight = 32 * _dpiScale;
                float searchBoxY = IslandTopY + (ExpandedHeight - searchBoxHeight) / 2;
                float searchBoxWidth = ExpandedWidth - margin * 2;
                float searchBoxX = (WindowWidth - ExpandedWidth) / 2 + margin;

                // 设置输入法合成窗口位置
                var compForm = new COMPOSITIONFORM
                {
                    dwStyle = 2, // CFS_POINT
                    x = this.Left + (int)searchBoxX + 10,
                    y = this.Top + (int)searchBoxY + (int)searchBoxHeight
                };
                ImmSetCompositionWindow(_imcHandle, ref compForm);

                // 设置候选窗口位置
                var candForm = new CANDIDATEFORM
                {
                    dwIndex = 0,
                    dwStyle = 2, // CFS_CANDIDATEPOS
                    x = this.Left + (int)searchBoxX + 10,
                    y = this.Top + (int)searchBoxY + (int)searchBoxHeight
                };
                ImmSetCandidateWindow(_imcHandle, ref candForm);
            }
            catch { }
        }

        private void ExitSearchMode()
        {
            _isSearchMode = false;
            _searchText = "";
            _cursorPosition = 0;

            _cursorTimer?.Stop();

            // 关闭输入法
            if (_immEnabled && _imcHandle != IntPtr.Zero)
            {
                try
                {
                    ImmSetOpenStatus(_imcHandle, false);
                    ImmAssociateContext(this.Handle, IntPtr.Zero);
                    ImmDestroyContext(_imcHandle);
                }
                catch { }
                _imcHandle = IntPtr.Zero;
                _immEnabled = false;
            }

            // 恢复窗口样式
            if (this.IsHandleCreated && !this.IsDisposed)
            {
                int exStyle = GetWindowLong(this.Handle, GWL_EXSTYLE);
                int newStyle = exStyle | WS_EX_NOACTIVATE | WS_EX_TRANSPARENT;
                SetWindowLong(this.Handle, GWL_EXSTYLE, newStyle);
                SetWindowPos(this.Handle, HWND_TOPMOST, 0, 0, 0, 0,
                    SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_FRAMECHANGED | SWP_SHOWWINDOW);
            }

            SetClickableMode(false);
            SetExpanded(false);
            RequestRender();
        }

        private void PerformSearch()
        {
            if (string.IsNullOrWhiteSpace(_searchText))
            {
                ExitSearchMode();
                return;
            }

            string searchUrl = "https://cn.bing.com/search?q=" + Uri.EscapeDataString(_searchText);
            try
            {
                Process.Start(new ProcessStartInfo
                {
                    FileName = searchUrl,
                    UseShellExecute = true
                });
            }
            catch (Exception ex)
            {
                ShowNotification($"搜索失败: {ex.Message}", TimeSpan.FromSeconds(3));
            }
            ExitSearchMode();
        }

        private Rectangle GetIslandScreenRect()
        {
            float x = (WindowWidth - _currentWidth) / 2;
            return new Rectangle(this.Left + (int)x, this.Top + (int)IslandTopY, (int)_currentWidth, (int)_currentHeight);
        }

        private void Form1_MouseMove(object sender, MouseEventArgs e)
        {
            if (!_mouseTracking)
            {
                TRACKMOUSEEVENT tme = new TRACKMOUSEEVENT
                {
                    cbSize = (uint)Marshal.SizeOf(typeof(TRACKMOUSEEVENT)),
                    dwFlags = TME_LEAVE,
                    hwndTrack = this.Handle,
                    dwHoverTime = 0
                };
                TrackMouseEvent(ref tme);
                _mouseTracking = true;
            }

            if (_isLinkDialogActive || _isMusicMode || _isSearchMode)
            {
                RequestRender();
            }
        }

        private void Form1_MouseLeave(object sender, EventArgs e)
        {
            _mouseTracking = false;
            _mouseInside = false;

            if (_isMusicMode && _isMusicModeExpanded)
            {
                MinimizeMusicMode();
                return;
            }

            if (_isSearchMode)
            {
                ExitSearchMode();
                return;
            }

            if (_isLinkDialogActive)
            {
                CloseLinkDialog();
            }
            else
            {
                SetExpanded(false);
            }
        }

        private void Form1_MouseDown(object sender, MouseEventArgs e)
        {
            if (e.Button != MouseButtons.Left) return;

            Point clientPoint = this.PointToClient(Cursor.Position);

            if (_isSearchMode)
            {
                // 检查是否点击搜索图标
                if (_searchIconRect.Contains(clientPoint.X, clientPoint.Y))
                {
                    DateTime now = DateTime.Now;
                    if (now - _lastSearchTime < _searchDebounce)
                    {
                        return;
                    }
                    _lastSearchTime = now;
                    PerformSearch();
                    return;
                }

                // 点击搜索框区域
                if (_searchBoxRect.Contains(clientPoint.X, clientPoint.Y))
                {
                    // 更新输入法位置
                    UpdateImmPosition();
                    return;
                }
                return;
            }

            if (_isMusicMode)
            {
                if (!_isMusicModeExpanded)
                {
                    ExpandMusicMode();
                    return;
                }

                if (_playPauseButtonRect.Contains(clientPoint.X, clientPoint.Y))
                {
                    if (_musicModeState != "waiting")
                    {
                        TogglePlayPause();
                    }
                    return;
                }

                if (_progressBarRect.Contains(clientPoint.X, clientPoint.Y))
                {
                    float percent = (clientPoint.X - _progressBarRect.X) / _progressBarRect.Width;
                    _currentPosition = TimeSpan.FromTicks((long)(_totalDuration.Ticks * percent));
                    if (_mediaPlayer != null)
                    {
                        _mediaPlayer.controls.currentPosition = percent * _totalDuration.TotalSeconds;
                    }
                    RequestRender();
                    return;
                }

                return;
            }

            if (_isLinkDialogActive && _confirmButtonRect.Contains(clientPoint.X, clientPoint.Y))
            {
                _currentContent?.OnConfirm?.Invoke();
            }
        }
        private void Form1_KeyDown(object sender, KeyEventArgs e)
        {
            if (!_isSearchMode)
            {
                // 非搜索模式下的原有逻辑
                if (e.Alt && _isMusicMode)
                {
                    ExitMusicMode();
                }
                return;
            }

            // 搜索模式下的按键处理
            switch (e.KeyCode)
            {
                case Keys.Escape:
                    e.Handled = true;
                    e.SuppressKeyPress = true;
                    ExitSearchMode();
                    break;

                case Keys.Enter:
                    e.Handled = true;
                    e.SuppressKeyPress = true;
                    DateTime now = DateTime.Now;
                    if (now - _lastSearchTime < _searchDebounce)
                    {
                        return;
                    }
                    _lastSearchTime = now;
                    PerformSearch();
                    break;

                case Keys.Left:
                    e.Handled = true;
                    e.SuppressKeyPress = true;
                    if (_cursorPosition > 0)
                    {
                        _cursorPosition--;
                        RequestRender();
                    }
                    break;

                case Keys.Right:
                    e.Handled = true;
                    e.SuppressKeyPress = true;
                    if (_cursorPosition < _searchText.Length)
                    {
                        _cursorPosition++;
                        RequestRender();
                    }
                    break;

                case Keys.Home:
                    e.Handled = true;
                    e.SuppressKeyPress = true;
                    _cursorPosition = 0;
                    RequestRender();
                    break;

                case Keys.End:
                    e.Handled = true;
                    e.SuppressKeyPress = true;
                    _cursorPosition = _searchText.Length;
                    RequestRender();
                    break;

                case Keys.Delete:
                    e.Handled = true;
                    e.SuppressKeyPress = true;
                    if (_cursorPosition < _searchText.Length)
                    {
                        _searchText = _searchText.Remove(_cursorPosition, 1);
                        RequestRender();
                    }
                    break;
            }
        }

        private void Form1_KeyPress(object sender, KeyPressEventArgs e)
        {
            if (!_isSearchMode) return;

            // 处理字符输入（包括输入法输入的字符）
            if (char.IsControl(e.KeyChar))
            {
                // 控制字符在 KeyDown 中处理
                if (e.KeyChar == (char)Keys.Back)
                {
                    e.Handled = true;
                    if (_searchText.Length > 0 && _cursorPosition > 0)
                    {
                        _searchText = _searchText.Remove(_cursorPosition - 1, 1);
                        _cursorPosition--;
                        RequestRender();
                    }
                }
                else if (e.KeyChar == (char)Keys.Enter || e.KeyChar == (char)Keys.Escape)
                {
                    e.Handled = true;
                    // 由 KeyDown 处理
                }
            }
            else
            {
                // 普通字符输入（包括输入法输入的字符）
                e.Handled = true;
                if (_searchText.Length < 100)
                {
                    _searchText = _searchText.Insert(_cursorPosition, e.KeyChar.ToString());
                    _cursorPosition++;
                    RequestRender();
                }
            }
        }

        private void Form1_MouseUp(object sender, MouseEventArgs e)
        {
        }

        private void SetExpanded(bool expanded)
        {
            if (_isExpanded == expanded) return;
            _isExpanded = expanded;
            _targetWidth = expanded ? ExpandedWidth : IslandWidth;
            _targetHeight = expanded ? ExpandedHeight : IslandHeight;
            _isAnimating = true;

            // 更新输入法位置
            if (_isSearchMode && expanded)
            {
                UpdateImmPosition();
            }
        }

        private void UpdateSpringAnimation(float deltaMs)
        {
            float dt = Math.Min(deltaMs / 1000f, 0.05f);
            float displacementX = _targetWidth - _currentWidth;
            float displacementY = _targetHeight - _currentHeight;
            float forceX = displacementX * SpringStrength;
            float forceY = displacementY * SpringStrength;
            _velocityX += forceX * dt * 60;
            _velocityY += forceY * dt * 60;
            _velocityX *= Damping;
            _velocityY *= Damping;
            _currentWidth += _velocityX * dt * 60;
            _currentHeight += _velocityY * dt * 60;
            float threshold = 0.3f * _dpiScale;
            if (Math.Abs(displacementX) < threshold && Math.Abs(_velocityX) < threshold &&
                Math.Abs(displacementY) < threshold && Math.Abs(_velocityY) < threshold)
            {
                _currentWidth = _targetWidth;
                _currentHeight = _targetHeight;
                if (!IsContentAnimating()) _isAnimating = false;
                _velocityX = 0f;
                _velocityY = 0f;
            }
        }

        private bool IsContentAnimating()
        {
            if (_currentContent != null && (_currentContent.CurrentAlpha > 1f || _currentContent.CurrentAlpha < 254f ||
                Math.Abs(_currentContent.CurrentScale - _currentContent.TargetScale) > 0.01f))
                return true;
            if (_nextContent != null && (_nextContent.CurrentAlpha > 1f || _nextContent.CurrentAlpha < 254f ||
                Math.Abs(_nextContent.CurrentScale - _nextContent.TargetScale) > 0.01f))
                return true;
            return false;
        }

        private void RenderTick(object state)
        {
            long now = DateTime.UtcNow.Ticks;
            float deltaMs = (now - _lastTickTime) / 10000f;
            _lastTickTime = now;

            bool needsRender = false;
            lock (_renderLock)
            {
                if (_isExpanded || Math.Abs(_currentWidth - _targetWidth) > 0.1f)
                {
                    UpdateSpringAnimation(deltaMs);
                    needsRender = true;

                    if (!_isMusicMode && !_isLinkDialogActive && !_isAutoPopupActive && !_isSearchMode)
                    {
                        float targetProgress = _isExpanded ? 1f : 0f;
                        float diff = targetProgress - _timeAnimationProgress;
                        if (Math.Abs(diff) > 0.005f)
                        {
                            _timeAnimationProgress += diff * 0.15f;
                            needsRender = true;
                        }
                        else
                        {
                            _timeAnimationProgress = targetProgress;
                        }
                    }
                }
                else
                {
                    if (!_isMusicMode && !_isLinkDialogActive && !_isAutoPopupActive && !_isSearchMode && _timeAnimationProgress > 0.005f)
                    {
                        _timeAnimationProgress += (0f - _timeAnimationProgress) * 0.2f;
                        if (_timeAnimationProgress < 0.005f) _timeAnimationProgress = 0f;
                        needsRender = true;
                    }
                }

                if (_currentContent != null)
                {
                    _currentContent.UpdateAnimation(deltaMs);
                    if (_currentContent.ShouldRemove)
                    {
                        _currentContent = null;
                    }
                    needsRender = true;
                }

                if (_nextContent != null)
                {
                    _nextContent.UpdateAnimation(deltaMs);
                    if (_nextContent.CurrentAlpha > 200 && _currentContent != null && _currentContent.CurrentAlpha < 50)
                    {
                        _currentContent = _nextContent;
                        _nextContent = null;
                    }
                    needsRender = true;
                }

                if (_currentContent != null && _currentContent.Duration == TimeSpan.Zero &&
                    _currentContent.Font == _timeFont && !_isAutoPopupActive && !_isMusicMode)
                {
                    string newTime = DateTime.Now.ToString("HH:mm:ss");
                    if (newTime != _currentContent.Text)
                    {
                        _currentContent.Text = newTime;
                        needsRender = true;
                    }
                }

                if (_isMusicMode && _isPlaying)
                {
                    needsRender = true;
                }

                if (_isSearchMode)
                {
                    needsRender = true;
                }
            }

            if (needsRender)
            {
                try { this.BeginInvoke(new Action(RequestRender)); }
                catch { }
            }
        }

        private void RequestRender()
        {
            if (this.IsDisposed || !this.IsHandleCreated) return;
            lock (_renderLock)
            {
                DrawToBuffer();
                UpdateLayeredWindowInternal();
            }
        }

        private RectangleF GetIslandRect()
        {
            float x = (WindowWidth - _currentWidth) / 2;
            return new RectangleF(x, IslandTopY, _currentWidth, _currentHeight);
        }

        private float GetCurrentRadius()
        {
            float ratio = (_currentHeight - IslandHeight) / (float)(ExpandedHeight - IslandHeight);
            ratio = Math.Max(0, Math.Min(1, ratio));
            return (20 + ratio * 15) * _dpiScale;
        }

        private void DrawToBuffer()
        {
            var g = _bufferGraphics;
            var islandRect = GetIslandRect();
            float radius = GetCurrentRadius();

            g.Clear(Color.Transparent);
            DrawShadow(g, islandRect, radius, shadowOpacity);

            float expandProgress = (_currentWidth - IslandWidth) / (float)(ExpandedWidth - IslandWidth);
            expandProgress = Math.Max(0, Math.Min(1, expandProgress));

            int bodyAlpha = expandProgress > 0.9f ? 255 : (int)(155 + expandProgress * 100);

            if (_isMusicMode && expandProgress > 0.5f)
            {
                using (var gradientBrush = new LinearGradientBrush(
                    new PointF(islandRect.X, islandRect.Y),
                    new PointF(islandRect.Right, islandRect.Y),
                    Color.FromArgb(255, 0xFF, 0x95, 0x55),
                    Color.FromArgb(255, 0xFE, 0x83, 0xA2)))
                using (var path = GetRoundedRect(islandRect, radius))
                {
                    g.FillPath(gradientBrush, path);
                }
            }
            else
            {
                using (var brush = new SolidBrush(Color.FromArgb(bodyAlpha, 0, 0, 0)))
                using (var path = GetRoundedRect(islandRect, radius))
                {
                    g.FillPath(brush, path);
                }
            }

            int highlightAlpha = (int)(30 + expandProgress * 30);
            using (var pen = new Pen(Color.FromArgb(highlightAlpha, 255, 255, 255), 2f * _dpiScale))
            {
                float offset = 0.5f * _dpiScale;
                var highlightRect = new RectangleF(islandRect.X + offset, islandRect.Y + offset,
                    islandRect.Width - offset * 2, islandRect.Height - offset * 2);
                using (var path = GetRoundedRect(highlightRect, radius - offset))
                    g.DrawPath(pen, path);
            }

            DrawContent(g, islandRect);

            if ((_isExpanded || _isAnimating) && !_isAutoPopupActive && expandProgress > 0.3f && !_isLinkDialogActive && !_isMusicMode && !_isSearchMode)
            {
                int dateAlpha = (int)(255 * Math.Min(1f, (expandProgress - 0.3f) / 0.7f));
                string dateStr = DateTime.Now.ToString("MM/dd");
                using (var brush = new SolidBrush(Color.FromArgb(dateAlpha, 200, 200, 200)))
                {
                    float dateWidth = 70 * _dpiScale;
                    float dateHeight = 24 * _dpiScale;
                    var dateRect = new RectangleF(islandRect.Right - dateWidth - 5 * _dpiScale,
                        islandRect.Y + (islandRect.Height - dateHeight) / 2, dateWidth, dateHeight);
                    g.DrawString(dateStr, _dateFont, brush, dateRect, _stringFormat);
                }
            }
        }

        private void DrawContent(Graphics g, RectangleF islandRect)
        {
            if (_isSearchMode)
            {
                DrawSearchModeContent(g, islandRect);
                return;
            }

            if (_isMusicMode)
            {
                DrawMusicModeContent(g, islandRect);
                return;
            }

            if ((_isExpanded || _timeAnimationProgress > 0.01f) && !_isLinkDialogActive && !_isAutoPopupActive
                && _currentContent != null && _currentContent.Font == _timeFont)
            {
                DrawAnimatedTimeContent(g, islandRect);
                return;
            }

            if (_currentContent != null && _currentContent.CurrentAlpha > 0)
            {
                DrawContentItem(g, islandRect, _currentContent);
            }

            if (_nextContent != null && _nextContent.CurrentAlpha > 0)
            {
                DrawContentItem(g, islandRect, _nextContent);
            }
        }

        private void DrawSearchModeContent(Graphics g, RectangleF islandRect)
        {
            var state = g.Save();
            g.SmoothingMode = SmoothingMode.AntiAlias;
            g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.AntiAliasGridFit;

            float margin = 20 * _dpiScale;
            float searchBoxHeight = 32 * _dpiScale;
            float searchBoxY = islandRect.Y + (islandRect.Height - searchBoxHeight) / 2;

            _searchBoxRect = new RectangleF(islandRect.X + margin, searchBoxY,
                islandRect.Width - margin * 2, searchBoxHeight);

            // 搜索框背景
            using (var bgBrush = new SolidBrush(Color.FromArgb(20, 255, 255, 255)))
            using (var bgPath = GetRoundedRect(_searchBoxRect, 16 * _dpiScale))
            {
                g.FillPath(bgBrush, bgPath);
            }

            using (var borderPen = new Pen(Color.FromArgb(120, 255, 255, 255), 1.5f * _dpiScale))
            using (var borderPath = GetRoundedRect(_searchBoxRect, 16 * _dpiScale))
            {
                g.DrawPath(borderPen, borderPath);
            }

            // 定义搜索图标区域
            float iconSize = 16 * _dpiScale;
            float iconMargin = 10 * _dpiScale;
            _searchIconRect = new RectangleF(
                _searchBoxRect.Right - iconSize - iconMargin,
                _searchBoxRect.Y + (_searchBoxRect.Height - iconSize) / 2,
                iconSize, iconSize);

            float textX = _searchBoxRect.X + 12 * _dpiScale;
            float textWidth = _searchIconRect.Left - textX - 8 * _dpiScale;
            var textRect = new RectangleF(textX, _searchBoxRect.Y,
                textWidth, _searchBoxRect.Height);

            var leftFormat = new StringFormat
            {
                Alignment = StringAlignment.Near,
                LineAlignment = StringAlignment.Center
            };

            if (string.IsNullOrEmpty(_searchText))
            {
                // 绘制占位符文本
                using (var brush = new SolidBrush(Color.FromArgb(150, 255, 255, 255)))
                using (var font = new Font("Microsoft YaHei", 14 * _dpiScale, FontStyle.Regular, GraphicsUnit.Pixel))
                {
                    g.DrawString("输入搜索内容...", font, brush, textRect, leftFormat);
                }
            }
            else
            {
                // 绘制实际输入的文本
                using (var brush = new SolidBrush(Color.White))
                using (var font = new Font("Microsoft YaHei", 14 * _dpiScale, FontStyle.Regular, GraphicsUnit.Pixel))
                {
                    g.DrawString(_searchText, font, brush, textRect, leftFormat);
                }
            }

            // 绘制光标
            if (!string.IsNullOrEmpty(_searchText) && _cursorVisible && _isSearchMode)
            {
                using (var font = new Font("Microsoft YaHei", 14 * _dpiScale, FontStyle.Regular, GraphicsUnit.Pixel))
                {
                    string textBeforeCursor = _searchText.Substring(0, Math.Min(_cursorPosition, _searchText.Length));
                    SizeF textSize = g.MeasureString(textBeforeCursor, font, int.MaxValue, leftFormat);
                    float cursorX = textX + textSize.Width;

                    if (cursorX < _searchIconRect.Left - 4 * _dpiScale)
                    {
                        using (var cursorBrush = new SolidBrush(Color.White))
                        {
                            float cursorHeight = 16 * _dpiScale;
                            float cursorY = _searchBoxRect.Y + (_searchBoxRect.Height - cursorHeight) / 2;
                            g.FillRectangle(cursorBrush, cursorX, cursorY, 1.5f * _dpiScale, cursorHeight);
                        }
                    }
                }
            }

            // 绘制搜索图标
            using (var iconBrush = new SolidBrush(Color.FromArgb(200, 255, 255, 255)))
            {
                float circleRadius = 5 * _dpiScale;
                float circleX = _searchIconRect.X + iconSize / 2 - circleRadius / 2;
                float circleY = _searchIconRect.Y + iconSize / 2 - circleRadius / 2 - 4 * _dpiScale;

                using (var circlePath = new GraphicsPath())
                {
                    circlePath.AddEllipse(circleX, circleY, circleRadius * 2, circleRadius * 2);
                    using (var pen = new Pen(iconBrush, 2 * _dpiScale))
                    {
                        g.DrawPath(pen, circlePath);
                    }
                }

                float handleStartX = circleX + circleRadius * 1.5f;
                float handleStartY = circleY + circleRadius * 1.5f;
                float handleEndX = handleStartX + 4 * _dpiScale;
                float handleEndY = handleStartY + 4 * _dpiScale;

                using (var pen = new Pen(iconBrush, 2 * _dpiScale))
                {
                    pen.StartCap = System.Drawing.Drawing2D.LineCap.Round;
                    pen.EndCap = System.Drawing.Drawing2D.LineCap.Round;
                    g.DrawLine(pen, handleStartX, handleStartY, handleEndX, handleEndY);
                }
            }

            g.Restore(state);
        }

        private void DrawAnimatedTimeContent(Graphics g, RectangleF islandRect)
        {
            var state = g.Save();
            g.SmoothingMode = SmoothingMode.AntiAlias;
            g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.AntiAliasGridFit;

            string timeText = DateTime.Now.ToString("HH:mm:ss");

            float smallSize = _timeFont.Size;
            float largeSize = _largeTimeFont.Size;
            float currentSize = smallSize + (largeSize - smallSize) * _timeAnimationProgress;

            using (var timeFont = new Font("Microsoft YaHei", currentSize, FontStyle.Bold, GraphicsUnit.Pixel))
            using (var brush = new SolidBrush(Color.White))
            {
                float centerY = islandRect.Y + islandRect.Height / 2 - currentSize / 2;
                float expandedY = islandRect.Y + 18 * _dpiScale;
                float currentY = centerY + (expandedY - centerY) * _timeAnimationProgress;

                var timeRect = new RectangleF(islandRect.X, currentY, islandRect.Width, currentSize * 1.2f);
                g.DrawString(timeText, timeFont, brush, timeRect, _stringFormat);
            }

            if (_timeAnimationProgress > 0.05f)
            {
                int hintAlpha = (int)(255 * _timeAnimationProgress);
                using (var brush = new SolidBrush(Color.FromArgb(hintAlpha, 180, 180, 180)))
                {
                    float hintBaseY = islandRect.Y + islandRect.Height / 2 + 8 * _dpiScale;
                    float hintTargetY = islandRect.Y + 45 * _dpiScale;
                    float currentHintY = hintBaseY + (hintTargetY - hintBaseY) * _timeAnimationProgress;

                    var hintRect = new RectangleF(islandRect.X, currentHintY, islandRect.Width, 20 * _dpiScale);
                    g.DrawString("Alt 音乐 | Ctrl 搜索", _hintFont, brush, hintRect, _stringFormat);
                }
            }

            g.Restore(state);
        }

        private void DrawMusicModeContent(Graphics g, RectangleF islandRect)
        {
            var state = g.Save();
            g.SmoothingMode = SmoothingMode.AntiAlias;
            g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.AntiAliasGridFit;

            if (!_isMusicModeExpanded)
            {
                using (var brush = new SolidBrush(Color.White))
                {
                    string timeText = DateTime.Now.ToString("HH:mm:ss");
                    var timeRect = new RectangleF(islandRect.X, islandRect.Y + (islandRect.Height - _timeFont.Size) / 2,
                        islandRect.Width, _timeFont.Size * 1.2f);
                    g.DrawString(timeText, _timeFont, brush, timeRect, _stringFormat);
                }
                g.Restore(state);
                return;
            }

            float margin = 15 * _dpiScale;
            float topMargin = 10 * _dpiScale;

            if (_musicModeState == "waiting")
            {
                using (var brush = new SolidBrush(Color.White))
                {
                    float waitingFontSize = 16f * _dpiScale;
                    using (var waitingFont = new Font("Microsoft YaHei", waitingFontSize, FontStyle.Bold, GraphicsUnit.Pixel))
                    {
                        var hintRect = new RectangleF(islandRect.X, islandRect.Y + (islandRect.Height - 24 * _dpiScale) / 2,
                            islandRect.Width, 24 * _dpiScale);
                        g.DrawString("请拖入音频文件", waitingFont, brush, hintRect, _stringFormat);
                    }
                }
                g.Restore(state);
                return;
            }

            float controlY = islandRect.Y + (islandRect.Height - 24 * _dpiScale) / 2;

            float playButtonSize = 28 * _dpiScale;
            _playPauseButtonRect = new RectangleF(islandRect.X + margin, controlY - 2 * _dpiScale, playButtonSize, playButtonSize);

            using (var buttonBrush = new SolidBrush(Color.FromArgb(220, 255, 255, 255)))
            using (var buttonPath = new GraphicsPath())
            {
                buttonPath.AddEllipse(_playPauseButtonRect);
                g.FillPath(buttonBrush, buttonPath);
            }

            using (var iconBrush = new SolidBrush(Color.FromArgb(255, 0xFF, 0x95, 0x55)))
            {
                if (_isPlaying)
                {
                    float barWidth = 3 * _dpiScale;
                    float barHeight = 10 * _dpiScale;
                    float centerX = _playPauseButtonRect.X + _playPauseButtonRect.Width / 2;
                    float centerY = _playPauseButtonRect.Y + _playPauseButtonRect.Height / 2;
                    g.FillRectangle(iconBrush, centerX - barWidth - 1, centerY - barHeight / 2, barWidth, barHeight);
                    g.FillRectangle(iconBrush, centerX + 1, centerY - barHeight / 2, barWidth, barHeight);
                }
                else
                {
                    float triangleSize = 10 * _dpiScale;
                    float centerX = _playPauseButtonRect.X + _playPauseButtonRect.Width / 2 - 1;
                    float centerY = _playPauseButtonRect.Y + _playPauseButtonRect.Height / 2;
                    float triangleWidth = triangleSize * 0.8f;
                    var triangle = new PointF[]
                    {
                        new PointF(centerX - triangleWidth / 3, centerY - triangleSize / 2),
                        new PointF(centerX - triangleWidth / 3, centerY + triangleSize / 2),
                        new PointF(centerX + triangleWidth / 1.5f, centerY)
                    };
                    g.FillPolygon(iconBrush, triangle);
                }
            }

            string displayFileName = TruncateFileName(_currentFileName, 22);
            float textStartX = _playPauseButtonRect.Right + 10 * _dpiScale;
            float textWidth = islandRect.Width - textStartX - margin * 2 - 45 * _dpiScale;

            using (var brush = new SolidBrush(Color.White))
            {
                var fileNameRect = new RectangleF(textStartX, islandRect.Y + 18 * _dpiScale,
                    textWidth, 18 * _dpiScale);
                var leftFormat = new StringFormat { Alignment = StringAlignment.Near, LineAlignment = StringAlignment.Center };
                g.DrawString(displayFileName, _musicFileFont, brush, fileNameRect, leftFormat);
            }

            string progressText = $"{_currentPosition:mm\\:ss}/{_totalDuration:mm\\:ss}";
            using (var brush = new SolidBrush(Color.FromArgb(200, 255, 255, 255)))
            {
                var timeRect = new RectangleF(textStartX, islandRect.Y + 36 * _dpiScale,
                    textWidth, 16 * _dpiScale);
                var leftFormat = new StringFormat { Alignment = StringAlignment.Near, LineAlignment = StringAlignment.Center };
                g.DrawString(progressText, _musicTimeFont, brush, timeRect, leftFormat);
            }

            float progressBarY = islandRect.Y + islandRect.Height - 12 * _dpiScale;
            float progressBarHeight = 4 * _dpiScale;
            float progressBarMargin = margin * 1.5f;
            float progressBarWidth = islandRect.Width - progressBarMargin * 2;
            float progressBarX = islandRect.X + progressBarMargin;
            _progressBarRect = new RectangleF(progressBarX, progressBarY, progressBarWidth, progressBarHeight);

            using (var bgBrush = new SolidBrush(Color.FromArgb(100, 255, 255, 255)))
            using (var bgPath = GetRoundedRect(_progressBarRect, progressBarHeight / 2))
            {
                g.FillPath(bgBrush, bgPath);
            }

            float progressPercent = _totalDuration.TotalSeconds > 0 ?
                (float)(_currentPosition.TotalSeconds / _totalDuration.TotalSeconds) : 0;
            float fillWidth = _progressBarRect.Width * progressPercent;
            if (fillWidth > 0)
            {
                var fillRect = new RectangleF(_progressBarRect.X, _progressBarRect.Y, fillWidth, _progressBarRect.Height);
                using (var fillBrush = new SolidBrush(Color.White))
                using (var fillPath = GetRoundedRect(fillRect, progressBarHeight / 2))
                {
                    g.FillPath(fillBrush, fillPath);
                }
            }

            DrawAudioVisualizerBars(g, islandRect);

            g.Restore(state);
        }

        private void DrawAudioVisualizerBars(Graphics g, RectangleF islandRect)
        {
            int barCount = 8;
            float barWidth = 3.5f * _dpiScale;
            float barSpacing = 2.5f * _dpiScale;
            float maxBarHeight = 22 * _dpiScale;

            float totalBarsWidth = barCount * barWidth + (barCount - 1) * barSpacing;

            float rightMargin = 18 * _dpiScale;
            float visualizerX = islandRect.Right - totalBarsWidth - rightMargin;
            float visualizerY = islandRect.Y + 24 * _dpiScale;

            for (int i = 0; i < barCount; i++)
            {
                float barValue = _audioBars[i];

                float barHeight = maxBarHeight * barValue;
                float minDisplayHeight = 4 * _dpiScale;
                if (barHeight < minDisplayHeight) barHeight = minDisplayHeight;

                if (barHeight > maxBarHeight) barHeight = maxBarHeight;

                float x = visualizerX + i * (barWidth + barSpacing);
                float y = visualizerY + (maxBarHeight - barHeight);

                var barRect = new RectangleF(x, y, barWidth, barHeight);

                float intensity = barValue;
                int alpha = 160 + (int)(95 * intensity);
                if (alpha > 255) alpha = 255;

                Color barColor = Color.FromArgb(alpha, 255, 255, 255);

                using (var barBrush = new SolidBrush(barColor))
                using (var barPath = GetRoundedRect(barRect, barWidth / 2))
                {
                    g.FillPath(barBrush, barPath);
                }
            }
        }

        private void DrawContentItem(Graphics g, RectangleF islandRect, ContentItem item)
        {
            if (item.CurrentAlpha <= 0) return;

            int alpha = Math.Max(0, Math.Min(255, (int)item.CurrentAlpha));
            var color = Color.FromArgb(alpha, item.Color.R, item.Color.G, item.Color.B);

            float scale = item.CurrentScale;
            float centerX = islandRect.X + islandRect.Width / 2;
            float centerY = islandRect.Y + islandRect.Height / 2;

            var state = g.Save();
            g.SmoothingMode = SmoothingMode.AntiAlias;
            g.TextRenderingHint = System.Drawing.Text.TextRenderingHint.AntiAliasGridFit;

            var matrix = new Matrix();
            matrix.Translate(centerX, centerY);
            matrix.Scale(scale, scale);
            matrix.Translate(-centerX, -centerY);
            g.Transform = matrix;

            if (_isLinkDialogActive && item.IsClickable)
            {
                DrawLinkDialogContent(g, islandRect, item, alpha);
            }
            else
            {
                using (var brush = new SolidBrush(color))
                {
                    g.DrawString(item.Text, item.Font, brush,
                        new RectangleF(islandRect.X, islandRect.Y + 2 * _dpiScale, islandRect.Width, islandRect.Height),
                        _stringFormat);
                }
            }

            g.Restore(state);
        }

        private void DrawLinkDialogContent(Graphics g, RectangleF islandRect, ContentItem item, int alpha)
        {
            // 整体向下偏移3px
            float offsetY = 3 * _dpiScale;

            var whiteColor = Color.FromArgb(alpha, 255, 255, 255);
            var linkColor = Color.FromArgb(alpha, item.SubColor.R, item.SubColor.G, item.SubColor.B);
            var buttonColor = Color.FromArgb(alpha, 76, 175, 80);

            using (var brush = new SolidBrush(whiteColor))
            {
                var leftFormat = new StringFormat
                {
                    Alignment = StringAlignment.Near,
                    LineAlignment = StringAlignment.Center
                };
                float leftMargin = 15 * _dpiScale;
                var promptRect = new RectangleF(islandRect.X + leftMargin, islandRect.Y + 10 * _dpiScale + offsetY,
                    islandRect.Width - leftMargin * 2, 22 * _dpiScale);
                g.DrawString(item.Text, item.Font, brush, promptRect, leftFormat);
            }

            float row2Y = islandRect.Y + 32 * _dpiScale + offsetY;
            float buttonWidth = 50 * _dpiScale;
            float buttonHeight = 22 * _dpiScale;
            float spacing = 18 * _dpiScale;

            string linkText = item.SubText;
            SizeF linkSize = g.MeasureString(linkText, item.SubFont ?? _linkFont);
            float availableWidth = islandRect.Width - buttonWidth - spacing * 3;

            if (linkSize.Width > availableWidth)
            {
                int maxChars = linkText.Length;
                while (maxChars > 0 && g.MeasureString(linkText.Substring(0, maxChars) + "...", item.SubFont ?? _linkFont).Width > availableWidth)
                {
                    maxChars--;
                }
                if (maxChars > 0)
                    linkText = linkText.Substring(0, maxChars) + "...";
            }

            float linkX = islandRect.X + spacing;
            float linkWidth = Math.Min(linkSize.Width, availableWidth);

            using (var brush = new SolidBrush(Color.FromArgb(alpha, 200, 200, 200)))
            {
                var format = new StringFormat
                {
                    Alignment = StringAlignment.Near,
                    LineAlignment = StringAlignment.Center
                };
                var linkRect = new RectangleF(linkX, row2Y, linkWidth, buttonHeight);
                g.DrawString(linkText, item.SubFont ?? _linkFont, brush, linkRect, format);
            }

            float buttonX = islandRect.Right - buttonWidth - spacing;
            _confirmButtonRect = new RectangleF(buttonX, row2Y, buttonWidth, buttonHeight);
            DrawButton(g, _confirmButtonRect, "打开", buttonColor, whiteColor, alpha);
        }

        private void DrawButton(Graphics g, RectangleF rect, string text, Color bgColor, Color textColor, int alpha)
        {
            Point mousePos = this.PointToClient(Cursor.Position);
            bool isHovered = rect.Contains(mousePos.X, mousePos.Y);

            if (isHovered)
            {
                bgColor = Color.FromArgb(alpha,
                    Math.Min(255, bgColor.R + 30),
                    Math.Min(255, bgColor.G + 30),
                    Math.Min(255, bgColor.B + 30));
            }

            using (var brush = new SolidBrush(bgColor))
            using (var path = GetRoundedRect(rect, 12 * _dpiScale))
            {
                g.FillPath(brush, path);
            }

            using (var brush = new SolidBrush(textColor))
            {
                var format = new StringFormat
                {
                    Alignment = StringAlignment.Center,
                    LineAlignment = StringAlignment.Center
                };
                var textRect = new RectangleF(rect.X, rect.Y + 3 * _dpiScale, rect.Width, rect.Height);
                g.DrawString(text, _buttonFont, brush, textRect, format);
            }
        }

        private void DrawShadow(Graphics g, RectangleF islandRect, float radius, float shadowOpacity)
        {
            bool needRegenerate = _shadowBitmap == null ||
                Math.Abs(_lastShadowWidth - islandRect.Width) > 2 ||
                Math.Abs(_lastShadowHeight - islandRect.Height) > 2;

            if (needRegenerate)
            {
                _shadowBitmap?.Dispose();
                _shadowBitmap = GenerateShadowBitmap(islandRect.Width, islandRect.Height, radius);
                _lastShadowWidth = islandRect.Width;
                _lastShadowHeight = islandRect.Height;
            }

            if (_shadowBitmap != null)
            {
                float shadowPadding = 15f * _dpiScale;
                float offsetY = 4f * _dpiScale;
                float[][] matrixItems = new float[][] {
                    new float[] { 1, 0, 0, 0, 0 },
                    new float[] { 0, 1, 0, 0, 0 },
                    new float[] { 0, 0, 1, 0, 0 },
                    new float[] { 0, 0, 0, shadowOpacity, 0 },
                    new float[] { 0, 0, 0, 0, 1 }
                };
                ColorMatrix colorMatrix = new ColorMatrix(matrixItems);
                using (var imageAttributes = new ImageAttributes())
                {
                    imageAttributes.SetColorMatrix(colorMatrix, ColorMatrixFlag.Default, ColorAdjustType.Bitmap);
                    g.DrawImage(_shadowBitmap,
                        new Rectangle((int)(islandRect.X - shadowPadding), (int)(islandRect.Y - shadowPadding + offsetY),
                            _shadowBitmap.Width, _shadowBitmap.Height),
                        0, 0, _shadowBitmap.Width, _shadowBitmap.Height, GraphicsUnit.Pixel, imageAttributes);
                }
            }
        }

        private Bitmap GenerateShadowBitmap(float width, float height, float radius)
        {
            float padding = 15f * _dpiScale;
            int bmpWidth = (int)(width + padding * 2);
            int bmpHeight = (int)(height + padding * 2);
            var bitmap = new Bitmap(bmpWidth, bmpHeight, PixelFormat.Format32bppPArgb);
            using (var g = Graphics.FromImage(bitmap))
            {
                g.SmoothingMode = SmoothingMode.AntiAlias;
                g.Clear(Color.Transparent);
                for (int i = 8; i >= 0; i--)
                {
                    float expand = i * 1.2f * _dpiScale;
                    int alpha = (int)(10 * (1f - (float)i / 8));
                    var shadowRect = new RectangleF(padding - expand, padding - expand, width + expand * 2, height + expand * 2);
                    using (var brush = new SolidBrush(Color.FromArgb(alpha, 0, 0, 0)))
                    using (var path = GetRoundedRect(shadowRect, radius + expand))
                        g.FillPath(brush, path);
                }
            }
            return bitmap;
        }

        private GraphicsPath GetRoundedRect(RectangleF rect, float radius)
        {
            var path = new GraphicsPath();
            float diameter = radius * 2;
            if (diameter > rect.Width) diameter = rect.Width;
            if (diameter > rect.Height) diameter = rect.Height;
            radius = diameter / 2;
            path.AddArc(rect.X, rect.Y, diameter, diameter, 180, 90);
            path.AddArc(rect.Right - diameter, rect.Y, diameter, diameter, 270, 90);
            path.AddArc(rect.Right - diameter, rect.Bottom - diameter, diameter, diameter, 0, 90);
            path.AddArc(rect.X, rect.Bottom - diameter, diameter, diameter, 90, 90);
            path.CloseFigure();
            return path;
        }

        private void UpdateLayeredWindowInternal()
        {
            IntPtr screenDc = IntPtr.Zero;
            IntPtr memDc = IntPtr.Zero;
            IntPtr oldBitmap = IntPtr.Zero;
            IntPtr hBitmap = IntPtr.Zero;
            try
            {
                screenDc = GetDC(IntPtr.Zero);
                memDc = CreateCompatibleDC(screenDc);
                hBitmap = _bufferBitmap.GetHbitmap(Color.FromArgb(0));
                oldBitmap = SelectObject(memDc, hBitmap);
                Win32Point pptDst = new Win32Point(this.Left, this.Top);
                Size psize = new Size(this.Width, this.Height);
                Win32Point pptSrc = new Win32Point(0, 0);
                BLENDFUNCTION blend = new BLENDFUNCTION
                {
                    BlendOp = AC_SRC_OVER,
                    BlendFlags = 0,
                    SourceConstantAlpha = 255,
                    AlphaFormat = AC_SRC_ALPHA
                };
                UpdateLayeredWindow(this.Handle, screenDc, ref pptDst, ref psize, memDc, ref pptSrc, 0, ref blend, ULW_ALPHA);
            }
            finally
            {
                if (oldBitmap != IntPtr.Zero) SelectObject(memDc, oldBitmap);
                if (hBitmap != IntPtr.Zero) DeleteObject(hBitmap);
                if (memDc != IntPtr.Zero) DeleteDC(memDc);
                if (screenDc != IntPtr.Zero) ReleaseDC(IntPtr.Zero, screenDc);
            }
        }

        protected override void WndProc(ref Message m)
        {
            if (m.Msg == WM_SHOWINSTANCE_MESSAGE && WM_SHOWINSTANCE_MESSAGE != 0)
            {
                this.BeginInvoke(new Action(() =>
                {
                    try
                    {
                        ShowNotification("程序重复启动", TimeSpan.FromSeconds(2), customColor: Color.FromArgb(180, 229, 162));
                    }
                    catch (Exception ex)
                    {
                        Debug.WriteLine($"ShowNotification error: {ex.Message}");
                    }
                }));

                m.Result = new IntPtr(1);
                return;
            }

            if (m.Msg == WM_CLIPBOARDUPDATE)
            {
                try
                {
                    if (Clipboard.ContainsText())
                    {
                        string text = Clipboard.GetText();
                        if (IsValidUrl(text))
                        {
                            ProcessClipboardLink(text);
                        }
                    }
                }
                catch { }
                m.Result = IntPtr.Zero;
                return;
            }

            // 处理输入法相关消息
            if (_isSearchMode && _immEnabled)
            {
                const int WM_IME_STARTCOMPOSITION = 0x010D;
                const int WM_IME_ENDCOMPOSITION = 0x010E;
                const int WM_IME_COMPOSITION = 0x010F;
                const int WM_IME_CHAR = 0x0286;

                if (m.Msg == WM_IME_CHAR)
                {
                    // 输入法字符输入
                    char c = (char)m.WParam;
                    if (_searchText.Length < 100)
                    {
                        _searchText = _searchText.Insert(_cursorPosition, c.ToString());
                        _cursorPosition++;
                        RequestRender();
                    }
                    m.Result = IntPtr.Zero;
                    return;
                }
            }

            base.WndProc(ref m);
        }

        protected override void OnFormClosing(FormClosingEventArgs e)
        {
            if (!_isExiting)
            {
                e.Cancel = true;
                this.Hide();
                return;
            }

            CleanupResources();
            base.OnFormClosing(e);
        }

        protected override void OnPaint(PaintEventArgs e) { }
        protected override void OnPaintBackground(PaintEventArgs e) { }
    }
}