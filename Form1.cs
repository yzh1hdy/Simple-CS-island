using System;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Drawing.Imaging;
using System.Runtime.InteropServices;
using System.Threading;
using System.Windows.Forms;
using Timer = System.Windows.Forms.Timer;

namespace DynamicIsland
{
    public class Form1 : Form
    {
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
        private static extern bool SetProcessDPIAware();

        [DllImport("shcore.dll")]
        private static extern int SetProcessDpiAwareness(int awareness);

        [DllImport("user32.dll")]
        private static extern int GetDpiForWindow(IntPtr hwnd);

        [DllImport("user32.dll")]
        private static extern IntPtr MonitorFromWindow(IntPtr hwnd, uint dwFlags);

        [DllImport("shcore.dll")]
        private static extern int GetDpiForMonitor(IntPtr hmonitor, int dpiType, out uint dpiX, out uint dpiY);

        private const uint MONITOR_DEFAULTTONEAREST = 2;

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

        private const uint TME_LEAVE = 0x00000002;
        private const int GWL_EXSTYLE = -20;
        private const int WS_EX_LAYERED = 0x80000;
        private const int WS_EX_TOOLWINDOW = 0x80;
        private const int WS_EX_TRANSPARENT = 0x20;
        private static readonly IntPtr HWND_TOPMOST = new IntPtr(-1);
        private const uint SWP_NOSIZE = 0x0001;
        private const uint SWP_NOMOVE = 0x0002;
        private const uint SWP_NOACTIVATE = 0x0010;
        private const uint SWP_SHOWWINDOW = 0x0040;
        private const uint SWP_FRAMECHANGED = 0x0020;
        private const uint ULW_ALPHA = 0x02;
        private const byte AC_SRC_OVER = 0x00;
        private const byte AC_SRC_ALPHA = 0x01;

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
        private const int BaseIslandWidth = 140;
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
        private readonly object _renderLock = new object();
        private long _lastTickTime;
        private float _animStartWidth, _animStartHeight;
        private float _animElapsed = 0f;
        private bool _isAnimating = false;

        // 弹簧物理参数
        private float _velocityX = 0f;
        private float _velocityY = 0f;
        private const float SpringStrength = 0.12f;
        private const float Damping = 0.82f;

        private bool _mouseTracking = false;
        private bool _mouseInside = false;
        private Timer _mousePollingTimer;

        private Font _timeFont;
        private Font _dateFont;
        private StringFormat _stringFormat;
        private Timer _clockTimer;

        private Bitmap _bufferBitmap;
        private Graphics _bufferGraphics;

        private Bitmap _shadowBitmap;
        private float _lastShadowWidth = -1;
        private float _lastShadowHeight = -1;
        private float shadowOpacity = 0.35f;

        private NotifyIcon _notifyIcon;
        private ContextMenuStrip _contextMenu;
        private bool _isExiting = false;

        public Form1()
        {
            InitializeDpiAwareness();
            CalculateScaledSizes();
            _currentWidth = IslandWidth;
            _currentHeight = IslandHeight;
            _targetWidth = IslandWidth;
            _targetHeight = IslandHeight;
            InitializeComponent();
        }

        private void InitializeDpiAwareness()
        {
            try { SetProcessDpiAwareness(2); }
            catch { try { SetProcessDPIAware(); } catch { } }
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
            _timeFont = new Font("Microsoft YaHei", timeFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _dateFont = new Font("Microsoft YaHei", dateFontSize, FontStyle.Bold, GraphicsUnit.Pixel);
            _stringFormat = new StringFormat { Alignment = StringAlignment.Center, LineAlignment = StringAlignment.Center };
            this.MouseMove += Form1_MouseMove;
            this.MouseLeave += Form1_MouseLeave;
        }

        private void InitializeTrayIcon()
        {
            _contextMenu = new ContextMenuStrip();
            ToolStripMenuItem exitMenuItem = new ToolStripMenuItem("退出");
            exitMenuItem.Click += ExitMenuItem_Click;
            _contextMenu.Items.Add(exitMenuItem);
            _notifyIcon = new NotifyIcon();
            _notifyIcon.Text = "Dynamic Island";
            _notifyIcon.Visible = true;
            _notifyIcon.ContextMenuStrip = _contextMenu;
            try { _notifyIcon.Icon = SystemIcons.Application; }
            catch
            {
                using (Bitmap bmp = new Bitmap(16, 16))
                {
                    using (Graphics g = Graphics.FromImage(bmp)) g.Clear(Color.Black);
                    _notifyIcon.Icon = Icon.FromHandle(bmp.GetHicon());
                }
            }
            _notifyIcon.DoubleClick += NotifyIcon_DoubleClick;
        }

        private void NotifyIcon_DoubleClick(object sender, EventArgs e)
        {
            if (this.Visible) this.Hide();
            else
            {
                this.Show();
                SetWindowPos(this.Handle, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_SHOWWINDOW);
            }
        }

        private void ExitMenuItem_Click(object sender, EventArgs e)
        {
            _isExiting = true;
            _notifyIcon.Visible = false;
            _notifyIcon.Dispose();
            Application.Exit();
        }

        private void Form1_Load(object sender, EventArgs e)
        {
            InitializeTrayIcon();
            int exStyle = GetWindowLong(this.Handle, GWL_EXSTYLE);
            SetWindowLong(this.Handle, GWL_EXSTYLE, exStyle | WS_EX_LAYERED | WS_EX_TOOLWINDOW | WS_EX_TRANSPARENT);
            SetWindowPos(this.Handle, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE | SWP_SHOWWINDOW | SWP_FRAMECHANGED);
            _bufferBitmap = new Bitmap(WindowWidth, WindowHeight, PixelFormat.Format32bppPArgb);
            _bufferGraphics = Graphics.FromImage(_bufferBitmap);
            _bufferGraphics.SmoothingMode = SmoothingMode.AntiAlias;
            _bufferGraphics.TextRenderingHint = System.Drawing.Text.TextRenderingHint.AntiAliasGridFit;
            _bufferGraphics.CompositingQuality = CompositingQuality.HighQuality;
            _bufferGraphics.InterpolationMode = InterpolationMode.HighQualityBicubic;
            _bufferGraphics.PixelOffsetMode = PixelOffsetMode.HighQuality;
            _clockTimer = new Timer { Interval = 1000 };
            _clockTimer.Tick += (s, ev) => RequestRender();
            _clockTimer.Start();
            _mousePollingTimer = new Timer { Interval = 8 };
            _mousePollingTimer.Tick += MousePollingTimer_Tick;
            _mousePollingTimer.Start();
            _lastTickTime = DateTime.UtcNow.Ticks;
            _renderTimer = new System.Threading.Timer(RenderTick, null, 0, 8);
            RequestRender();
        }

        private void MousePollingTimer_Tick(object sender, EventArgs e)
        {
            if (GetCursorPos(out POINT pt))
            {
                var islandScreenRect = GetIslandScreenRect();
                float hitPadding = 8 * _dpiScale;
                var hitRect = new RectangleF(islandScreenRect.X - hitPadding, islandScreenRect.Y - hitPadding, islandScreenRect.Width + hitPadding * 2, islandScreenRect.Height + hitPadding * 2);
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
                TRACKMOUSEEVENT tme = new TRACKMOUSEEVENT { cbSize = (uint)Marshal.SizeOf(typeof(TRACKMOUSEEVENT)), dwFlags = TME_LEAVE, hwndTrack = this.Handle, dwHoverTime = 0 };
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
            if (Math.Abs(displacementX) < threshold && Math.Abs(_velocityX) < threshold && Math.Abs(displacementY) < threshold && Math.Abs(_velocityY) < threshold)
            {
                _currentWidth = _targetWidth;
                _currentHeight = _targetHeight;
                _isAnimating = false;
                _velocityX = 0f;
                _velocityY = 0f;
            }
        }

        private void RenderTick(object state)
        {
            long now = DateTime.UtcNow.Ticks;
            float deltaMs = (now - _lastTickTime) / 10000f;
            _lastTickTime = now;
            bool needsRender = false;
            lock (_renderLock)
            {
                if (_isAnimating)
                {
                    UpdateSpringAnimation(deltaMs);
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

            // 透明度：缩小80%，展开100%
            int bodyAlpha = expandProgress > 0.9f ? 255 : (int)(204 + expandProgress * 51);

            using (var brush = new SolidBrush(Color.FromArgb(bodyAlpha, 0, 0, 0)))
            using (var path = GetRoundedRect(islandRect, radius))
            {
                g.FillPath(brush, path);
            }
            int highlightAlpha = (int)(20 + expandProgress * 20);
            using (var pen = new Pen(Color.FromArgb(highlightAlpha, 255, 255, 255), 1f * _dpiScale))
            {
                float offset = 1f * _dpiScale;
                var innerRect = new RectangleF(islandRect.X + offset, islandRect.Y + offset, islandRect.Width - offset * 2, islandRect.Height - offset * 2);
                using (var path = GetRoundedRect(innerRect, radius - offset)) g.DrawPath(pen, path);
            }
            string timeStr = DateTime.Now.ToString("HH:mm:ss");
            var timeRect = new RectangleF(islandRect.X, islandRect.Y + 2 * _dpiScale, islandRect.Width, islandRect.Height);
            using (var brush = new SolidBrush(Color.White)) g.DrawString(timeStr, _timeFont, brush, timeRect, _stringFormat);
            if (_isExpanded || _isAnimating)
            {
                float progress = (_currentWidth - IslandWidth) / (float)(ExpandedWidth - IslandWidth);
                progress = Math.Max(0, Math.Min(1, progress));
                if (progress > 0.3f)
                {
                    int alpha = (int)(255 * Math.Min(1f, (progress - 0.3f) / 0.7f));
                    string dateStr = DateTime.Now.ToString("MM/dd");
                    using (var brush = new SolidBrush(Color.FromArgb(alpha, 200, 200, 200)))
                    {
                        float dateWidth = 70 * _dpiScale;
                        float dateHeight = 24 * _dpiScale;
                        var dateRect = new RectangleF(islandRect.Right - dateWidth - 5 * _dpiScale, islandRect.Y + (islandRect.Height - dateHeight) / 2, dateWidth, dateHeight);
                        g.DrawString(dateStr, _dateFont, brush, dateRect, _stringFormat);
                    }
                }
            }
        }

        private void DrawShadow(Graphics g, RectangleF islandRect, float radius, float shadowOpacity)
        {
            bool needRegenerate = _shadowBitmap == null || Math.Abs(_lastShadowWidth - islandRect.Width) > 2 || Math.Abs(_lastShadowHeight - islandRect.Height) > 2;
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
                float[][] matrixItems = new float[][] { new float[] { 1, 0, 0, 0, 0 }, new float[] { 0, 1, 0, 0, 0 }, new float[] { 0, 0, 1, 0, 0 }, new float[] { 0, 0, 0, shadowOpacity, 0 }, new float[] { 0, 0, 0, 0, 1 } };
                ColorMatrix colorMatrix = new ColorMatrix(matrixItems);
                using (var imageAttributes = new ImageAttributes())
                {
                    imageAttributes.SetColorMatrix(colorMatrix, ColorMatrixFlag.Default, ColorAdjustType.Bitmap);
                    g.DrawImage(_shadowBitmap, new Rectangle((int)(islandRect.X - shadowPadding), (int)(islandRect.Y - shadowPadding + offsetY), _shadowBitmap.Width, _shadowBitmap.Height), 0, 0, _shadowBitmap.Width, _shadowBitmap.Height, GraphicsUnit.Pixel, imageAttributes);
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
                    using (var path = GetRoundedRect(shadowRect, radius + expand)) g.FillPath(brush, path);
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
                BLENDFUNCTION blend = new BLENDFUNCTION { BlendOp = AC_SRC_OVER, BlendFlags = 0, SourceConstantAlpha = 255, AlphaFormat = AC_SRC_ALPHA };
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
            if (!_isExiting) { e.Cancel = true; this.Hide(); return; }
            _renderTimer?.Dispose();
            _mousePollingTimer?.Stop();
            _mousePollingTimer?.Dispose();
            _clockTimer?.Stop();
            _clockTimer?.Dispose();
            _timeFont?.Dispose();
            _dateFont?.Dispose();
            _stringFormat?.Dispose();
            _bufferGraphics?.Dispose();
            _bufferBitmap?.Dispose();
            _shadowBitmap?.Dispose();
            _notifyIcon?.Dispose();
            _contextMenu?.Dispose();
            base.OnFormClosing(e);
        }

        protected override void OnPaint(PaintEventArgs e) { }
        protected override void OnPaintBackground(PaintEventArgs e) { }
    }
}