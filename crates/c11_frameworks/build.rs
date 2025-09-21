fn main() {
    // 只在启用tauri特性时运行tauri-build
    #[cfg(feature = "tauri")]
    {
        // 设置环境变量以避免图标检查
        unsafe {
            std::env::set_var("TAURI_SKIP_ICON_GENERATION", "1");
        }
        
        // 尝试构建，如果失败则继续
        let _ = tauri_build::try_build(tauri_build::Attributes::new());
    }
}
