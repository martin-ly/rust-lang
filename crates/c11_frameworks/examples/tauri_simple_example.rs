//! Tauri 2.0 简化示例
//! 
//! 本示例展示了Tauri 2.0的基本用法

use tauri::{Manager, Listener};

/// 主应用状态
#[derive(Default)]
struct AppState {
    counter: std::sync::Mutex<i32>,
}

/// Tauri命令 - 获取计数器值
#[tauri::command]
fn get_counter(state: tauri::State<AppState>) -> Result<i32, String> {
    let counter = state.counter.lock().map_err(|e| e.to_string())?;
    Ok(*counter)
}

/// Tauri命令 - 增加计数器
#[tauri::command]
fn increment_counter(state: tauri::State<AppState>) -> Result<i32, String> {
    let mut counter = state.counter.lock().map_err(|e| e.to_string())?;
    *counter += 1;
    Ok(*counter)
}

/// Tauri命令 - 减少计数器
#[tauri::command]
fn decrement_counter(state: tauri::State<AppState>) -> Result<i32, String> {
    let mut counter = state.counter.lock().map_err(|e| e.to_string())?;
    *counter -= 1;
    Ok(*counter)
}

/// Tauri命令 - 重置计数器
#[tauri::command]
fn reset_counter(state: tauri::State<AppState>) -> Result<i32, String> {
    let mut counter = state.counter.lock().map_err(|e| e.to_string())?;
    *counter = 0;
    Ok(*counter)
}

/// Tauri命令 - 显示系统信息
#[tauri::command]
fn get_system_info() -> Result<SystemInfo, String> {
    Ok(SystemInfo {
        platform: std::env::consts::OS.to_string(),
        arch: std::env::consts::ARCH.to_string(),
        rust_version: "1.90.0".to_string(), // 简化版本
        tauri_version: "2.0.0".to_string(), // 简化版本
    })
}

/// 系统信息结构
#[derive(serde::Serialize)]
struct SystemInfo {
    platform: String,
    arch: String,
    rust_version: String,
    tauri_version: String,
}

/// 主函数
fn main() {
    tauri::Builder::default()
        .manage(AppState::default())
        .invoke_handler(tauri::generate_handler![
            get_counter,
            increment_counter,
            decrement_counter,
            reset_counter,
            get_system_info
        ])
        .setup(|app| {
            // 创建主窗口
            let window = app.get_webview_window("main").unwrap();
            
            // 设置窗口标题
            window.set_title("🚀 Tauri 2.0 简化示例").unwrap();
            
            // 监听窗口事件
            window.listen("window-close", |event| {
                println!("窗口关闭事件: {:?}", event);
            });

            Ok(())
        })
        .on_window_event(|_window, event| {
            match event {
                tauri::WindowEvent::CloseRequested { .. } => {
                    println!("窗口关闭请求");
                }
                tauri::WindowEvent::Focused(focused) => {
                    println!("窗口焦点状态: {}", focused);
                }
                tauri::WindowEvent::Resized(size) => {
                    println!("窗口大小改变: {:?}", size);
                }
                tauri::WindowEvent::Moved(position) => {
                    println!("窗口位置改变: {:?}", position);
                }
                _ => {}
            }
        })
        .run(tauri::generate_context!())
        .expect("运行Tauri应用时出错");
}

/// 测试模块
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_system_info() {
        let info = get_system_info().unwrap();
        assert!(!info.platform.is_empty());
        assert!(!info.arch.is_empty());
        assert!(!info.rust_version.is_empty());
        assert!(!info.tauri_version.is_empty());
    }

    #[test]
    fn test_counter_operations() {
        let state = AppState::default();
        
        // 测试初始值
        assert_eq!(get_counter(tauri::State::from(&state)).unwrap(), 0);
        
        // 测试增加
        assert_eq!(increment_counter(tauri::State::from(&state)).unwrap(), 1);
        assert_eq!(increment_counter(tauri::State::from(&state)).unwrap(), 2);
        
        // 测试减少
        assert_eq!(decrement_counter(tauri::State::from(&state)).unwrap(), 1);
        
        // 测试重置
        assert_eq!(reset_counter(tauri::State::from(&state)).unwrap(), 0);
    }
}
