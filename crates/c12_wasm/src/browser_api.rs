//! WASM 浏览器 API 交互示例
//! 
//! 展示如何使用 web-sys 与浏览器 API 交互

use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use web_sys::{console, Document, HtmlElement, Window};

/// 获取窗口对象
pub fn window() -> Option<Window> {
    web_sys::window()
}

/// 获取文档对象
pub fn document() -> Option<Document> {
    window()?.document()
}

/// 在控制台打印日志
pub fn log(msg: &str) {
    console::log_1(&msg.into());
}

/// 在控制台打印警告
pub fn warn(msg: &str) {
    console::warn_1(&msg.into());
}

/// 在控制台打印错误
pub fn error(msg: &str) {
    console::error_1(&msg.into());
}

/// 获取元素 by ID
pub fn get_element_by_id(id: &str) -> Option<HtmlElement> {
    let document = document()?;
    document.get_element_by_id(id)?.dyn_into::<HtmlElement>().ok()
}

/// 设置元素文本内容
pub fn set_text_content(id: &str, content: &str) -> Result<(), JsValue> {
    if let Some(element) = get_element_by_id(id) {
        element.set_text_content(Some(content));
        Ok(())
    } else {
        Err(JsValue::from_str(&format!("Element '{}' not found", id)))
    }
}

/// 简单的计时器类
pub struct Timer {
    start: f64,
    name: String,
}

impl Timer {
    /// 创建新计时器
    pub fn new(name: &str) -> Self {
        let start = web_sys::window()
            .and_then(|w| w.performance())
            .map(|p| p.now())
            .unwrap_or(0.0);
        
        Self {
            start,
            name: name.to_string(),
        }
    }
    
    /// 结束计时并打印结果
    pub fn end(&self) {
        let end = web_sys::window()
            .and_then(|w| w.performance())
            .map(|p| p.now())
            .unwrap_or(0.0);
        
        let duration = end - self.start;
        log(&format!("[Timer] {}: {:.2}ms", self.name, duration));
    }
}

/// 本地存储操作
pub mod local_storage {
    use super::*;
    use web_sys::Storage;
    
    /// 获取 localStorage
    pub fn get_storage() -> Option<Storage> {
        web_sys::window()?.local_storage().ok()?
    }
    
    /// 设置值
    pub fn set_item(key: &str, value: &str) -> Result<(), JsValue> {
        if let Some(storage) = get_storage() {
            storage.set_item(key, value)?;
            Ok(())
        } else {
            Err(JsValue::from_str("localStorage not available"))
        }
    }
    
    /// 获取值
    pub fn get_item(key: &str) -> Option<String> {
        let storage = get_storage()?;
        storage.get_item(key).ok()?
    }
    
    /// 删除值
    pub fn remove_item(key: &str) -> Result<(), JsValue> {
        if let Some(storage) = get_storage() {
            storage.remove_item(key)?;
            Ok(())
        } else {
            Err(JsValue::from_str("localStorage not available"))
        }
    }
}

#[cfg(test)]
mod tests {
    #[allow(unused_imports)]
    use super::*;
    
    #[test]
    fn test_timer_creation() {
        // 注意: 在 Node.js 测试环境中可能没有 window
        // 这个测试主要验证编译通过
    }
}
