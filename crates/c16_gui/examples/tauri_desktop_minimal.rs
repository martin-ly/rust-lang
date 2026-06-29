//! 最小 Tauri 桌面应用核心逻辑示例。
//!
//! 本示例展示 Tauri 2.x 的命令注册与 Builder 配置模式。由于最小化目标，
//! 不调用 `tauri::generate_context!()` 与 `run()`，因此无需 `tauri.conf.json`
//! 即可通过 `cargo check`。

/// Tauri 命令：问候函数。
#[tauri::command]
fn greet(name: &str) -> String {
    format!("Hello, {name}!")
}

/// 配置 Tauri Builder 并注册命令处理器。
///
/// 在真实应用中，通常会调用 `.run(tauri::generate_context!())`。
fn configure_tauri_app() -> tauri::Builder<tauri::Wry> {
    tauri::Builder::default().invoke_handler(tauri::generate_handler![greet])
}

fn main() {
    // 仅展示 Builder 配置，不实际启动 WebView 窗口。
    let _builder = configure_tauri_app();
    println!("Tauri desktop minimal example configured (not running).");
}
