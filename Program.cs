using System;
using System.Runtime.InteropServices;
using System.Windows.Forms;

namespace DynamicIsland
{
    static class Program
    {
        // DPI 感知 API
        [DllImport("shcore.dll")]
        private static extern int SetProcessDpiAwareness(int awareness);

        [DllImport("user32.dll")]
        private static extern bool SetProcessDPIAware();

        private const int PROCESS_PER_MONITOR_DPI_AWARE = 2;

        [STAThread]
        static void Main()
        {
            // 在应用程序启动前设置 DPI 感知
            try
            {
                // Windows 8.1+ Per-Monitor DPI
                SetProcessDpiAwareness(PROCESS_PER_MONITOR_DPI_AWARE);
            }
            catch
            {
                try
                {
                    // Windows Vista/7 回退
                    SetProcessDPIAware();
                }
                catch { }
            }

            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);
            Application.Run(new Form1());
        }
    }
}
