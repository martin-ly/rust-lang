//! Tauri 2.0 基础示例
//! 
//! 本示例展示了Tauri 2.0的最基本用法

// use tauri::Manager; // 在完整Tauri应用中需要

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
        rust_version: "1.90.0".to_string(),
        tauri_version: "2.0.0".to_string(),
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
    // 注意：这是一个简化的Tauri示例
    // 完整的Tauri应用需要前端HTML文件和正确的配置
    println!("🚀 Tauri基础示例 - 命令函数已定义");
    println!("可用的Tauri命令:");
    println!("- get_counter: 获取计数器值");
    println!("- increment_counter: 增加计数器");
    println!("- decrement_counter: 减少计数器");
    println!("- reset_counter: 重置计数器");
    println!("- get_system_info: 获取系统信息");
    
    // 演示系统信息功能
    match get_system_info() {
        Ok(info) => {
            println!("系统信息:");
            println!("  平台: {}", info.platform);
            println!("  架构: {}", info.arch);
            println!("  Rust版本: {}", info.rust_version);
            println!("  Tauri版本: {}", info.tauri_version);
        }
        Err(e) => println!("获取系统信息失败: {}", e),
    }
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
