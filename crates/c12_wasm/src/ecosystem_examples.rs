//! # Rust 1.90 生态库示例代码
//!
//! 本模块展示了如何使用 Rust 1.90 新特性和成熟的 WASM 生态库

/// Rust 1.90 新特性示例
pub mod rust_190_features {
    /// let-else 模式示例
    ///
    /// Rust 1.90: 使用 let-else 简化错误处理
    pub fn process_data_with_let_else(data: Option<String>) -> Result<String, String> {
        // let-else 模式：如果匹配失败，执行 else 分支
        let Some(value) = data else {
            return Err("No data provided".to_string());
        };

        Ok(value.to_uppercase())
    }

    /// return-position impl Trait 示例
    ///
    /// Rust 1.90: 函数可以直接返回 impl Trait
    pub fn get_filtered_numbers(numbers: &[i32]) -> impl Iterator<Item = &i32> {
        numbers.iter().filter(|&&x| x > 0)
    }
}

/// 设计模式示例
pub mod design_patterns {
    use std::sync::OnceLock;
    use wasm_bindgen::prelude::*;

    /// 工厂模式示例
    pub mod factory {
        use super::*;

        pub trait Renderer {
            fn render(&self, content: &str) -> String;
        }

        pub struct HtmlRenderer;
        impl Renderer for HtmlRenderer {
            fn render(&self, content: &str) -> String {
                format!("<div>{}</div>", content)
            }
        }

        pub struct MarkdownRenderer;
        impl Renderer for MarkdownRenderer {
            fn render(&self, content: &str) -> String {
                format!("**{}**", content)
            }
        }

        pub enum RendererType {
            Html,
            Markdown,
        }

        pub fn create_renderer(renderer_type: RendererType) -> Box<dyn Renderer> {
            match renderer_type {
                RendererType::Html => Box::new(HtmlRenderer),
                RendererType::Markdown => Box::new(MarkdownRenderer),
            }
        }

        #[wasm_bindgen]
        pub struct WasmRendererFactory;

        #[wasm_bindgen]
        impl WasmRendererFactory {
            #[wasm_bindgen(constructor)]
            #[allow(clippy::new_without_default)]
            pub fn new() -> Self {
                Self
            }

            #[wasm_bindgen]
            pub fn render_html(&self, content: &str) -> String {
                let renderer = HtmlRenderer;
                renderer.render(content)
            }
        }
    }

    /// 建造者模式示例
    pub mod builder {
        use super::*;

        #[wasm_bindgen]
        pub struct Config {
            pub(crate) timeout: u32,
            pub(crate) retries: u32,
            pub(crate) url: String,
        }

        #[wasm_bindgen]
        pub struct ConfigBuilder {
            timeout: Option<u32>,
            retries: Option<u32>,
            url: Option<String>,
        }

        #[wasm_bindgen]
        impl ConfigBuilder {
            #[wasm_bindgen(constructor)]
            #[allow(clippy::new_without_default)]
            pub fn new() -> Self {
                Self {
                    timeout: None,
                    retries: None,
                    url: None,
                }
            }

            #[wasm_bindgen]
            pub fn timeout(mut self, timeout: u32) -> Self {
                self.timeout = Some(timeout);
                self
            }

            #[wasm_bindgen]
            pub fn retries(mut self, retries: u32) -> Self {
                self.retries = Some(retries);
                self
            }

            #[wasm_bindgen]
            pub fn url(mut self, url: String) -> Self {
                self.url = Some(url);
                self
            }

            #[wasm_bindgen]
            pub fn build(self) -> Result<WasmConfig, JsValue> {
                Ok(WasmConfig {
                    inner: Config {
                        timeout: self.timeout.unwrap_or(5000),
                        retries: self.retries.unwrap_or(3),
                        url: self
                            .url
                            .ok_or_else(|| JsValue::from_str("URL is required"))?,
                    },
                })
            }
        }

        // 提供 WASM 友好的包装
        #[wasm_bindgen]
        pub struct WasmConfig {
            inner: Config,
        }

        #[wasm_bindgen]
        impl WasmConfig {
            #[wasm_bindgen(getter)]
            pub fn timeout(&self) -> u32 {
                self.inner.timeout
            }

            #[wasm_bindgen(getter)]
            pub fn retries(&self) -> u32 {
                self.inner.retries
            }

            #[wasm_bindgen(getter)]
            pub fn url(&self) -> String {
                self.inner.url.clone()
            }
        }
    }

    /// 单例模式示例（使用 Rust 1.90+ 的 OnceLock）
    pub mod singleton {
        use super::*;

        static GLOBAL_CONFIG: OnceLock<AppConfig> = OnceLock::new();

        pub struct AppConfig {
            pub api_key: String,
            pub timeout: u32,
        }

        impl AppConfig {
            pub fn get() -> &'static AppConfig {
                GLOBAL_CONFIG.get_or_init(|| AppConfig {
                    api_key: "default".to_string(),
                    timeout: 5000,
                })
            }

            pub fn initialize(api_key: String, timeout: u32) -> Result<(), String> {
                GLOBAL_CONFIG
                    .set(AppConfig { api_key, timeout })
                    .map_err(|_| "Config already initialized".to_string())
            }
        }

        #[wasm_bindgen]
        pub struct WasmAppConfig;

        #[wasm_bindgen]
        impl WasmAppConfig {
            #[wasm_bindgen]
            pub fn initialize(api_key: String, timeout: u32) -> Result<(), JsValue> {
                AppConfig::initialize(api_key, timeout).map_err(|e| JsValue::from_str(&e))
            }

            #[wasm_bindgen]
            pub fn get_timeout() -> u32 {
                AppConfig::get().timeout
            }
        }
    }

    /// 观察者模式示例
    pub mod observer {
        use super::*;
        use std::cell::RefCell;
        use std::rc::Rc;

        pub trait Observer {
            fn update(&self, event: &str);
        }

        pub struct EventSubject {
            observers: Rc<RefCell<Vec<Box<dyn Observer>>>>,
        }

        impl EventSubject {
            #[allow(clippy::new_without_default)]
            pub fn new() -> Self {
                Self {
                    observers: Rc::new(RefCell::new(Vec::new())),
                }
            }

            pub fn attach(&self, observer: Box<dyn Observer>) {
                self.observers.borrow_mut().push(observer);
            }

            pub fn notify(&self, event: &str) {
                for observer in self.observers.borrow().iter() {
                    observer.update(event);
                }
            }
        }

        pub struct ConsoleObserver;

        impl Observer for ConsoleObserver {
            fn update(&self, event: &str) {
                web_sys::console::log_1(&JsValue::from_str(&format!("Event: {}", event)));
            }
        }

        #[wasm_bindgen]
        pub struct WasmEventSubject {
            inner: EventSubject,
        }

        #[wasm_bindgen]
        impl WasmEventSubject {
            #[wasm_bindgen(constructor)]
            #[allow(clippy::new_without_default)]
            pub fn new() -> Self {
                Self {
                    inner: EventSubject::new(),
                }
            }

            #[wasm_bindgen]
            pub fn notify(&self, event: &str) {
                self.inner.notify(event);
            }
        }
    }

    /// 策略模式示例
    pub mod strategy {
        use super::*;

        pub trait SortStrategy {
            fn sort(&self, data: &mut [i32]);
        }

        pub struct QuickSortStrategy;

        impl SortStrategy for QuickSortStrategy {
            fn sort(&self, data: &mut [i32]) {
                data.sort();
            }
        }

        pub struct BubbleSortStrategy;

        impl SortStrategy for BubbleSortStrategy {
            fn sort(&self, data: &mut [i32]) {
                let len = data.len();
                for i in 0..len {
                    for j in 0..len - i - 1 {
                        if data[j] > data[j + 1] {
                            data.swap(j, j + 1);
                        }
                    }
                }
            }
        }

        #[wasm_bindgen]
        pub struct Sorter {
            strategy: Box<dyn SortStrategy>,
        }

        #[wasm_bindgen]
        impl Sorter {
            #[wasm_bindgen(constructor)]
            pub fn new_quick_sort() -> Self {
                Self {
                    strategy: Box::new(QuickSortStrategy),
                }
            }

            #[wasm_bindgen]
            pub fn new_bubble_sort() -> Self {
                Self {
                    strategy: Box::new(BubbleSortStrategy),
                }
            }

            #[wasm_bindgen]
            pub fn sort(&self, mut data: Vec<i32>) -> Vec<i32> {
                self.strategy.sort(&mut data);
                data
            }
        }
    }

    /// 适配器模式示例
    pub mod adapter {
        use super::*;

        pub trait DataSource {
            fn get_data(&self) -> String;
        }

        pub struct JsonDataSource {
            data: String,
        }

        impl DataSource for JsonDataSource {
            fn get_data(&self) -> String {
                self.data.clone()
            }
        }

        pub struct CsvAdapter {
            csv_data: String,
        }

        impl DataSource for CsvAdapter {
            fn get_data(&self) -> String {
                format!("{{\"data\": \"{}\"}}", self.csv_data)
            }
        }

        #[wasm_bindgen]
        pub struct WasmDataAdapter {
            source: Box<dyn DataSource>,
        }

        #[wasm_bindgen]
        impl WasmDataAdapter {
            #[wasm_bindgen(constructor)]
            pub fn new_json(data: String) -> Self {
                Self {
                    source: Box::new(JsonDataSource { data }),
                }
            }

            #[wasm_bindgen]
            pub fn new_csv(csv_data: String) -> Self {
                Self {
                    source: Box::new(CsvAdapter { csv_data }),
                }
            }

            #[wasm_bindgen]
            pub fn get_data(&self) -> String {
                self.source.get_data()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_factory_pattern() {
        let factory = design_patterns::factory::WasmRendererFactory::new();
        let result = factory.render_html("Hello");
        assert_eq!(result, "<div>Hello</div>");
    }

    #[test]
    fn test_builder_pattern() {
        let config = design_patterns::builder::ConfigBuilder::new()
            .timeout(10000)
            .retries(5)
            .url("https://example.com".to_string())
            .build()
            .unwrap();
        assert_eq!(config.timeout(), 10000);
    }

    #[test]
    fn test_singleton_pattern() {
        design_patterns::singleton::WasmAppConfig::initialize("test-key".to_string(), 10000)
            .unwrap();
        assert_eq!(
            design_patterns::singleton::WasmAppConfig::get_timeout(),
            10000
        );
    }
}
