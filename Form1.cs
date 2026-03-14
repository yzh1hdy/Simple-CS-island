// Form1.cs
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing.Drawing2D;
using System.Drawing.Imaging;
using System.Linq;
using System;
using System.Management;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;

namespace DynamicIsland
{
    public class ContentItem
    {
        public string Text { get; set; }
        public Font Font { get; set; }
        public Color Color { get; set; }
        public float TargetScale { get; set; } = 1.0f;
        public float CurrentScale { get; set; } = 0.0f;
        public float CurrentAlpha { get; set; } = 0.0f;
        public bool IsActive { get; set; } = false;
        public DateTime ShowTime { get; set; }
        public TimeSpan Duration { get; set; }

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
        // DPI 感知 API
        [DllImport("shcore.dll")]
        private static extern int SetProcessDpiAwareness(int awareness);

        [DllImport("user32.dll")]
        private static extern bool SetProcessDPIAware();

        // 静态构造函数，在类首次使用时执行，设置 DPI 感知
        static Form1()
        {
            try
            {
                SetProcessDpiAwareness(2); // Per-Monitor DPI Aware
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

        [DllImport("user32.dll", SetLastError = true)]
        private static extern bool SetWindowPos(IntPtr hWnd, int hWndInsertAfter, int X, int Y, int cx, int cy, uint uFlags);

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

        // 硬件监控相关
        private System.Threading.Timer _hardwareMonitorTimer;
        private bool _wasOnline = false;
        private string _lastSSID = null;
        private HashSet<string> _lastBluetoothDevices = new HashSet<string>();
        private readonly object _hardwareLock = new object();

        public Form1()
        {
            CalculateScaledSizes();
            _currentWidth = IslandWidth;
            _currentHeight = IslandHeight;
            _targetWidth = IslandWidth;
            _targetHeight = IslandHeight;
            InitializeComponent();
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
            var screen = Screen.PrimaryScreen.WorkingArea;
            this.Location = new Point((screen.Width - WindowWidth) / 2, 0);
            this.FormBorderStyle = FormBorderStyle.None;
            this.ShowInTaskbar = false;
            this.Load += Form1_Load;

            float timeFontSize = 17f * _dpiScale;
            float dateFontSize = 11f * _dpiScale;
            float notificationFontSize = 22f * _dpiScale;

            _timeFont = new Font("Microsoft YaHei", timeFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _dateFont = new Font("Microsoft YaHei", dateFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _notificationFont = new Font("Microsoft YaHei", notificationFontSize, FontStyle.Bold, GraphicsUnit.Pixel);

            _stringFormat = new StringFormat
            {
                Alignment = StringAlignment.Center,
                LineAlignment = StringAlignment.Center
            };

            this.MouseMove += Form1_MouseMove;
            this.MouseLeave += Form1_MouseLeave;
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

            this.BeginInvoke(new Action(() =>
            {
                try
                {
                    if (_notifyIcon != null)
                    {
                        _notifyIcon.Visible = false;
                    }
                    CleanupResources();
                    Application.Exit();
                }
                catch (Exception ex)
                {
                    Environment.Exit(0);
                }
            }));
        }

        private void CleanupResources()
        {
            _renderTimer?.Dispose();
            _topmostTimer?.Dispose();
            _mousePollingTimer?.Stop();
            _mousePollingTimer?.Dispose();
            _autoPopupTimer?.Stop();
            _autoPopupTimer?.Dispose();
            _hardwareMonitorTimer?.Dispose();

            _currentContent = null;
            _nextContent = null;

            _timeFont?.Dispose();
            _dateFont?.Dispose();
            _notificationFont?.Dispose();
            _stringFormat?.Dispose();
            _bufferGraphics?.Dispose();
            _bufferBitmap?.Dispose();
            _shadowBitmap?.Dispose();

            if (_notifyIcon != null)
            {
                _notifyIcon.Dispose();
                _notifyIcon = null;
            }
            _contextMenu?.Dispose();
        }

        // ==================== 硬件监控功能 ====================

        /// <summary>
        /// 检查互联网连接状态
        /// </summary>
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

        /// <summary>
        /// 获取当前WiFi SSID
        /// </summary>
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

                // 解析SSID
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

        /// <summary>
        /// 获取已连接的蓝牙设备
        /// </summary>
        private HashSet<string> GetBluetoothDevices()
        {
            var devices = new HashSet<string>();
            try
            {
                // 使用WMI查询蓝牙设备
                using (var searcher = new ManagementObjectSearcher(
                    "SELECT * FROM Win32_PnPEntity WHERE ClassGuid='{e0cbf06c-cd8b-4647-bb8a-263b43f0f974}'"))
                {
                    foreach (ManagementObject obj in searcher.Get())
                    {
                        string status = obj["Status"]?.ToString();
                        string name = obj["Name"]?.ToString();

                        if (status == "OK" && !string.IsNullOrEmpty(name))
                        {
                            // 排除蓝牙适配器本身
                            string[] excludeKeywords = { "Enumerator", "枚举器", "Adapter", "适配器", "Radio", "无线电" };
                            if (!excludeKeywords.Any(k => name.Contains(k)))
                            {
                                devices.Add(name);
                            }
                        }
                    }
                }

                // 备用方案：使用PowerShell获取更详细的蓝牙信息
                if (devices.Count == 0)
                {
                    try
                    {
                        var psProcess = new Process
                        {
                            StartInfo = new ProcessStartInfo
                            {
                                FileName = "powershell",
                                Arguments = "-Command \"Get-PnpDevice -Class Bluetooth | Where-Object {$_.Status -eq 'OK'} | Select-Object -ExpandProperty FriendlyName\"",
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
                                string[] excludeKeywords = { "Enumerator", "枚举器", "Adapter", "适配器", "Radio", "无线电" };
                                if (!excludeKeywords.Any(k => name.Contains(k)))
                                {
                                    devices.Add(name);
                                }
                            }
                        }
                    }
                    catch { }
                }
            }
            catch { }
            return devices;
        }

        /// <summary>
        /// 硬件监控主循环
        /// </summary>
        private void HardwareMonitorLoop(object state)
        {
            try
            {
                // 网络检测
                bool isOnline = CheckInternetConnection();
                string currentSSID = GetWifiSSID();

                lock (_hardwareLock)
                {
                    // 网络状态变化检测
                    if (isOnline)
                    {
                        if (!_wasOnline)
                        {
                            // 从离线变为在线
                            string msg = !string.IsNullOrEmpty(currentSSID) ? $"{currentSSID}" : "网络已连接";
                            ShowNotification(msg, TimeSpan.FromSeconds(3));
                        }
                        else if (!string.IsNullOrEmpty(currentSSID) && currentSSID != _lastSSID)
                        {
                            // WiFi切换
                            ShowNotification($"{currentSSID}", TimeSpan.FromSeconds(3));
                        }
                    }

                    _wasOnline = isOnline;
                    _lastSSID = currentSSID;

                    // 蓝牙检测
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

        // ==================== 窗口生命周期 ====================

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
            _renderTimer = new System.Threading.Timer(RenderTick, null, 0, 8);

            _topmostTimer = new System.Threading.Timer(EnsureSuperTopMost, null, 0, 100);

            // 初始化硬件监控
            _wasOnline = CheckInternetConnection();
            _lastSSID = GetWifiSSID();
            _lastBluetoothDevices = GetBluetoothDevices();

            // 每4秒检查一次硬件状态
            _hardwareMonitorTimer = new System.Threading.Timer(HardwareMonitorLoop, null, TimeSpan.FromSeconds(2), TimeSpan.FromSeconds(4));

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
                Color = Color.White,
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
            if (_isAutoPopupActive) return;

            if (GetCursorPos(out POINT pt))
            {
                var islandScreenRect = GetIslandScreenRect();
                float hitPadding = 8 * _dpiScale;
                var hitRect = new RectangleF(islandScreenRect.X - hitPadding, islandScreenRect.Y - hitPadding,
                    islandScreenRect.Width + hitPadding * 2, islandScreenRect.Height + hitPadding * 2);
                bool inside = hitRect.Contains(pt.X, pt.Y);
                if (inside != _mouseInside)
                {
                    _mouseInside = inside;
                    SetExpanded(inside);
                }
            }
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
        }

        private void Form1_MouseLeave(object sender, EventArgs e)
        {
            _mouseTracking = false;
            _mouseInside = false;
            SetExpanded(false);
        }

        private void SetExpanded(bool expanded)
        {
            if (_isExpanded == expanded) return;
            _isExpanded = expanded;
            _targetWidth = expanded ? ExpandedWidth : IslandWidth;
            _targetHeight = expanded ? ExpandedHeight : IslandHeight;
            _isAnimating = true;
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
                    _currentContent.Font == _timeFont && !_isAutoPopupActive)
                {
                    string newTime = DateTime.Now.ToString("HH:mm:ss");
                    if (newTime != _currentContent.Text)
                    {
                        _currentContent.Text = newTime;
                        needsRender = true;
                    }
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
            using (var brush = new SolidBrush(Color.FromArgb(bodyAlpha, 0, 0, 0)))
            using (var path = GetRoundedRect(islandRect, radius))
            {
                g.FillPath(brush, path);
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

            if ((_isExpanded || _isAnimating) && !_isAutoPopupActive && expandProgress > 0.3f)
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
            if (_currentContent != null && _currentContent.CurrentAlpha > 0)
            {
                DrawContentItem(g, islandRect, _currentContent);
            }

            if (_nextContent != null && _nextContent.CurrentAlpha > 0)
            {
                DrawContentItem(g, islandRect, _nextContent);
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

            using (var brush = new SolidBrush(color))
            {
                g.DrawString(item.Text, item.Font, brush,
                    new RectangleF(islandRect.X, islandRect.Y + 2 * _dpiScale, islandRect.Width, islandRect.Height),
                    _stringFormat);
            }

            g.Restore(state);
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