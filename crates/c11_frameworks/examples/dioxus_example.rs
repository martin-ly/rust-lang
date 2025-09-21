//! Dioxus 跨平台UI框架示例
//! 
//! 本示例展示了如何使用Dioxus构建跨平台的用户界面应用
//! 支持Web、Desktop和Mobile平台

use dioxus::prelude::*;

/// 主应用组件
fn App() -> Element {
    let mut count = use_signal(|| 0);
    let mut name = use_signal(|| "Rust开发者".to_string());

    rsx! {
        div {
            style: "text-align: center; font-family: Arial, sans-serif; padding: 20px;",
            
            h1 {
                style: "color: #2c3e50; margin-bottom: 30px;",
                "🚀 Dioxus 跨平台UI示例"
            }
            
            div {
                style: "background: #ecf0f1; padding: 20px; border-radius: 10px; margin: 20px 0;",
                
                h2 {
                    style: "color: #34495e; margin-bottom: 15px;",
                    "欢迎, {name}!"
                }
                
                input {
                    r#type: "text",
                    placeholder: "输入您的姓名",
                    value: "{name}",
                    oninput: move |evt| name.set(evt.value()),
                    style: "padding: 8px; margin: 10px; border: 1px solid #bdc3c7; border-radius: 5px; width: 200px;"
                }
            }
            
            div {
                style: "background: #3498db; color: white; padding: 20px; border-radius: 10px; margin: 20px 0;",
                
                h2 {
                    style: "margin-bottom: 15px;",
                    "计数器: {count}"
                }
                
                div {
                    style: "display: flex; gap: 10px; justify-content: center;",
                    
                    button {
                        onclick: move |_| count += 1,
                        style: "background: #e74c3c; color: white; border: none; padding: 10px 20px; border-radius: 5px; cursor: pointer; font-size: 16px;",
                        "➕ 增加"
                    }
                    
                    button {
                        onclick: move |_| count -= 1,
                        style: "background: #e67e22; color: white; border: none; padding: 10px 20px; border-radius: 5px; cursor: pointer; font-size: 16px;",
                        "➖ 减少"
                    }
                    
                    button {
                        onclick: move |_| count.set(0),
                        style: "background: #95a5a6; color: white; border: none; padding: 10px 20px; border-radius: 5px; cursor: pointer; font-size: 16px;",
                        "🔄 重置"
                    }
                }
            }
            
            div {
                style: "background: #2ecc71; color: white; padding: 20px; border-radius: 10px; margin: 20px 0;",
                
                h3 {
                    style: "margin-bottom: 15px;",
                    "📱 平台信息"
                }
                
                p {
                    "当前运行在: {get_platform()}"
                }
                
                p {
                    "Dioxus版本: 0.6.0"
                }
                
                p {
                    "Rust版本: 1.90.0"
                }
            }
            
            div {
                style: "background: #9b59b6; color: white; padding: 20px; border-radius: 10px; margin: 20px 0;",
                
                h3 {
                    style: "margin-bottom: 15px;",
                    "🎯 特性展示"
                }
                
                ul {
                    style: "text-align: left; max-width: 400px; margin: 0 auto;",
                    
                    li { "✅ 跨平台支持 (Web, Desktop, Mobile)" }
                    li { "✅ 类似React的组件模型" }
                    li { "✅ 高性能渲染" }
                    li { "✅ 类型安全" }
                    li { "✅ 响应式状态管理" }
                    li { "✅ 热重载支持" }
                }
            }
        }
    }
}

/// 获取当前平台信息
fn get_platform() -> &'static str {
    #[cfg(target_arch = "wasm32")]
    {
        return "Web (WASM)";
    }
    
    #[cfg(target_os = "windows")]
    {
        return "Windows Desktop";
    }
    
    #[cfg(target_os = "macos")]
    {
        return "macOS Desktop";
    }
    
    #[cfg(target_os = "linux")]
    {
        return "Linux Desktop";
    }
    
    #[cfg(target_os = "android")]
    {
        return "Android Mobile";
    }
    
    #[cfg(target_os = "ios")]
    {
        return "iOS Mobile";
    }
    
    #[cfg(not(any(
        target_arch = "wasm32",
        target_os = "windows",
        target_os = "macos",
        target_os = "linux",
        target_os = "android",
        target_os = "ios"
    )))]
    {
        return "Unknown Platform";
    }
}

/// 主函数 - Web平台
#[cfg(target_arch = "wasm32")]
fn main() {
    dioxus_web::launch(App);
}

/// 主函数 - Desktop平台
#[cfg(not(target_arch = "wasm32"))]
fn main() {
    dioxus_desktop::launch::launch(App, vec![], vec![]);
}

/// 测试模块
#[cfg(test)]
mod tests {
    use super::*;
    use dioxus::prelude::*;

    #[test]
    fn test_app_renders() {
        let mut app = VirtualDom::new(App);
        app.rebuild();
        
        // 验证应用能够正常渲染
        assert!(app.base_scope().root_element().is_some());
    }

    #[test]
    fn test_platform_detection() {
        let platform = get_platform();
        assert!(!platform.is_empty());
        assert!(platform != "Unknown Platform");
    }
}
