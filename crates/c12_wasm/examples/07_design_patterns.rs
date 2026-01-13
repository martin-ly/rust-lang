//! # 设计模式示例
//!
//! 展示如何在 WASM 中实现常见的设计模式
//!
//! ## 包含的设计模式
//! - 工厂模式 (Factory Pattern)
//! - 建造者模式 (Builder Pattern)
//! - 单例模式 (Singleton Pattern)
//! - 观察者模式 (Observer Pattern)
//! - 策略模式 (Strategy Pattern)

use std::sync::OnceLock;
use wasm_bindgen::prelude::*;

// ============================================================================
// 工厂模式 (Factory Pattern)
// ============================================================================

/// 渲染器工厂
///
/// 根据类型创建不同的渲染器实例
#[wasm_bindgen]
#[derive(Default)]
pub struct RendererFactory;

#[wasm_bindgen]
impl RendererFactory {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self
    }

    /// 渲染 HTML
    ///
    /// # 参数
    /// - `content`: 要渲染的内容
    ///
    /// # 返回值
    /// 返回 HTML 格式的字符串
    #[wasm_bindgen(js_name = "renderHtml")]
    pub fn render_html(&self, content: &str) -> String {
        format!("<div>{}</div>", content)
    }

    /// 渲染 Markdown
    #[wasm_bindgen(js_name = "renderMarkdown")]
    pub fn render_markdown(&self, content: &str) -> String {
        format!("**{}**", content)
    }

    /// 渲染纯文本
    #[wasm_bindgen(js_name = "renderText")]
    pub fn render_text(&self, content: &str) -> String {
        content.to_string()
    }
}


// ============================================================================
// 建造者模式 (Builder Pattern)
// ============================================================================

/// HTTP 配置
#[wasm_bindgen]
pub struct HttpConfig {
    timeout: u32,
    retries: u32,
    url: String,
    headers: Vec<String>,
}

#[wasm_bindgen]
impl HttpConfig {
    /// 获取超时时间
    #[wasm_bindgen(getter)]
    pub fn timeout(&self) -> u32 {
        self.timeout
    }

    /// 获取重试次数
    #[wasm_bindgen(getter)]
    pub fn retries(&self) -> u32 {
        self.retries
    }

    /// 获取 URL
    #[wasm_bindgen(getter)]
    pub fn url(&self) -> String {
        self.url.clone()
    }

    /// 获取配置描述
    #[wasm_bindgen(js_name = "describe")]
    pub fn describe(&self) -> String {
        format!(
            "HttpConfig {{ url: {}, timeout: {}ms, retries: {}, headers: {} }}",
            self.url,
            self.timeout,
            self.retries,
            self.headers.len()
        )
    }
}

/// HTTP 配置建造者
///
/// 使用建造者模式逐步构建配置对象
///
/// # 示例
/// ```javascript
/// const config = new HttpConfigBuilder()
///     .url('https://api.example.com')
///     .timeout(5000)
///     .retries(3)
///     .addHeader('Authorization: Bearer token')
///     .build();
/// console.log(config.describe());
/// ```
#[wasm_bindgen]
#[derive(Default)]
pub struct HttpConfigBuilder {
    timeout: Option<u32>,
    retries: Option<u32>,
    url: Option<String>,
    headers: Vec<String>,
}

#[wasm_bindgen]
impl HttpConfigBuilder {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            timeout: None,
            retries: None,
            url: None,
            headers: Vec::new(),
        }
    }

    /// 设置 URL
    pub fn url(mut self, url: String) -> Self {
        self.url = Some(url);
        self
    }

    /// 设置超时时间（毫秒）
    pub fn timeout(mut self, timeout: u32) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// 设置重试次数
    pub fn retries(mut self, retries: u32) -> Self {
        self.retries = Some(retries);
        self
    }

    /// 添加 HTTP 头
    #[wasm_bindgen(js_name = "addHeader")]
    pub fn add_header(mut self, header: String) -> Self {
        self.headers.push(header);
        self
    }

    /// 构建配置对象
    pub fn build(self) -> Result<HttpConfig, JsValue> {
        let url = self
            .url
            .ok_or_else(|| JsValue::from_str("URL is required"))?;

        Ok(HttpConfig {
            timeout: self.timeout.unwrap_or(3000),
            retries: self.retries.unwrap_or(1),
            url,
            headers: self.headers,
        })
    }
}


// ============================================================================
// 单例模式 (Singleton Pattern)
// ============================================================================

/// 应用配置单例
///
/// 使用 OnceLock 实现线程安全的单例模式
static APP_CONFIG: OnceLock<AppConfig> = OnceLock::new();

struct AppConfig {
    name: String,
    version: String,
}

/// 初始化应用配置
///
/// # 参数
/// - `name`: 应用名称
/// - `version`: 应用版本
///
/// # 返回值
/// 如果已经初始化过，返回 Err
#[wasm_bindgen(js_name = "initAppConfig")]
pub fn init_app_config(name: String, version: String) -> Result<(), JsValue> {
    APP_CONFIG
        .set(AppConfig { name, version })
        .map_err(|_| JsValue::from_str("AppConfig already initialized"))?;
    Ok(())
}

/// 获取应用名称
#[wasm_bindgen(js_name = "getAppName")]
pub fn get_app_name() -> Result<String, JsValue> {
    APP_CONFIG
        .get()
        .map(|config| config.name.clone())
        .ok_or_else(|| JsValue::from_str("AppConfig not initialized"))
}

/// 获取应用版本
#[wasm_bindgen(js_name = "getAppVersion")]
pub fn get_app_version() -> Result<String, JsValue> {
    APP_CONFIG
        .get()
        .map(|config| config.version.clone())
        .ok_or_else(|| JsValue::from_str("AppConfig not initialized"))
}

// ============================================================================
// 策略模式 (Strategy Pattern)
// ============================================================================

/// 排序策略
#[wasm_bindgen]
#[derive(Default)]
pub struct Sorter;

#[wasm_bindgen]
impl Sorter {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self
    }

    /// 冒泡排序
    #[wasm_bindgen(js_name = "bubbleSort")]
    pub fn bubble_sort(&self, mut arr: Vec<i32>) -> Vec<i32> {
        let len = arr.len();
        for i in 0..len {
            for j in 0..len - 1 - i {
                if arr[j] > arr[j + 1] {
                    arr.swap(j, j + 1);
                }
            }
        }
        arr
    }

    /// 快速排序
    #[wasm_bindgen(js_name = "quickSort")]
    pub fn quick_sort(&self, arr: Vec<i32>) -> Vec<i32> {
        if arr.len() <= 1 {
            return arr;
        }
        let mut arr = arr;
        let len = arr.len();
        Self::quick_sort_impl(&mut arr, 0, (len - 1) as isize);
        arr
    }

    /// 选择排序
    #[wasm_bindgen(js_name = "selectionSort")]
    pub fn selection_sort(&self, mut arr: Vec<i32>) -> Vec<i32> {
        let len = arr.len();
        for i in 0..len {
            let mut min_idx = i;
            for j in i + 1..len {
                if arr[j] < arr[min_idx] {
                    min_idx = j;
                }
            }
            arr.swap(i, min_idx);
        }
        arr
    }
}

impl Sorter {
    fn quick_sort_impl(arr: &mut [i32], low: isize, high: isize) {
        if low < high {
            let pi = Self::partition(arr, low, high);
            Self::quick_sort_impl(arr, low, pi - 1);
            Self::quick_sort_impl(arr, pi + 1, high);
        }
    }

    fn partition(arr: &mut [i32], low: isize, high: isize) -> isize {
        let pivot = arr[high as usize];
        let mut i = low - 1;
        for j in low..high {
            if arr[j as usize] < pivot {
                i += 1;
                arr.swap(i as usize, j as usize);
            }
        }
        arr.swap((i + 1) as usize, high as usize);
        i + 1
    }
}


// ============================================================================
// 观察者模式 (Observer Pattern)
// ============================================================================

/// 事件发射器
///
/// 简单的观察者模式实现
#[wasm_bindgen]
#[derive(Default)]
pub struct EventEmitter {
    listeners: Vec<js_sys::Function>,
}

#[wasm_bindgen]
impl EventEmitter {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            listeners: Vec::new(),
        }
    }

    /// 添加监听器
    ///
    /// # 参数
    /// - `callback`: JavaScript 回调函数
    #[wasm_bindgen(js_name = "addListener")]
    pub fn add_listener(&mut self, callback: js_sys::Function) {
        self.listeners.push(callback);
    }

    /// 触发事件
    ///
    /// # 参数
    /// - `data`: 要传递给监听器的数据
    pub fn emit(&self, data: &str) {
        let this = JsValue::null();
        let arg = JsValue::from_str(data);

        for listener in &self.listeners {
            let _ = listener.call1(&this, &arg);
        }
    }

    /// 获取监听器数量
    #[wasm_bindgen(js_name = "listenerCount")]
    pub fn listener_count(&self) -> usize {
        self.listeners.len()
    }

    /// 清除所有监听器
    #[wasm_bindgen(js_name = "clearListeners")]
    pub fn clear_listeners(&mut self) {
        self.listeners.clear();
    }
}


#[wasm_bindgen(start)]
#[allow(clippy::main_recursion)]
pub fn main() {
    #[cfg(target_arch = "wasm32")]
    {
        use web_sys::console;
        console::log_1(&"Design patterns example loaded!".into());
        console::log_1(
            &"Available patterns: Factory, Builder, Singleton, Strategy, Observer".into(),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_factory() {
        let factory = RendererFactory::new();
        assert_eq!(factory.render_html("test"), "<div>test</div>");
        assert_eq!(factory.render_markdown("test"), "**test**");
        assert_eq!(factory.render_text("test"), "test");
    }

    #[test]
    fn test_sorter() {
        let sorter = Sorter::new();
        let arr = vec![3, 1, 4, 1, 5, 9, 2, 6];

        let sorted = sorter.bubble_sort(arr.clone());
        assert_eq!(sorted, vec![1, 1, 2, 3, 4, 5, 6, 9]);

        let sorted = sorter.quick_sort(arr.clone());
        assert_eq!(sorted, vec![1, 1, 2, 3, 4, 5, 6, 9]);

        let sorted = sorter.selection_sort(arr);
        assert_eq!(sorted, vec![1, 1, 2, 3, 4, 5, 6, 9]);
    }

    #[test]
    fn test_event_emitter() {
        let mut emitter = EventEmitter::new();
        assert_eq!(emitter.listener_count(), 0);

        emitter.clear_listeners();
        assert_eq!(emitter.listener_count(), 0);
    }
}
