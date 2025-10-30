//! # 计数器类示例
//!
//! 展示如何导出 Rust 结构体到 JavaScript，实现有状态的对象
//!
//! ## JavaScript 使用示例
//!
//! ```javascript
//! import init, { Counter } from './pkg/c12_wasm.js';
//!
//! await init();
//!
//! const counter = new Counter();
//! console.log(counter.value);  // 0
//!
//! counter.increment();
//! console.log(counter.value);  // 1
//!
//! counter.increment();
//! counter.increment();
//! console.log(counter.value);  // 3
//!
//! counter.decrement();
//! console.log(counter.value);  // 2
//!
//! counter.add(10);
//! console.log(counter.value);  // 12
//!
//! counter.reset();
//! console.log(counter.value);  // 0
//! ```

use wasm_bindgen::prelude::*;

/// 计数器结构体
///
/// 这是一个简单的计数器示例，展示了如何在 Rust 和 JavaScript 之间共享状态
#[wasm_bindgen]
pub struct Counter {
    value: i32,
}

#[wasm_bindgen]
impl Counter {
    /// 创建新的计数器实例
    ///
    /// # 返回值
    /// 返回初始值为 0 的计数器
    ///
    /// # 示例
    /// ```javascript
    /// const counter = new Counter();
    /// ```
    #[wasm_bindgen(constructor)]
    pub fn new() -> Counter {
        Counter { value: 0 }
    }

    /// 使用指定初始值创建计数器
    ///
    /// # 参数
    /// - `initial_value`: 初始值
    ///
    /// # 示例
    /// ```javascript
    /// const counter = Counter.with_value(10);
    /// ```
    #[wasm_bindgen(js_name = "withValue")]
    pub fn with_value(initial_value: i32) -> Counter {
        Counter {
            value: initial_value,
        }
    }

    /// 增加计数器值
    ///
    /// 每次调用会将内部值加 1
    #[wasm_bindgen]
    pub fn increment(&mut self) {
        self.value += 1;
    }

    /// 减少计数器值
    ///
    /// 每次调用会将内部值减 1
    #[wasm_bindgen]
    pub fn decrement(&mut self) {
        self.value -= 1;
    }

    /// 增加指定的值
    ///
    /// # 参数
    /// - `amount`: 要增加的数量
    #[wasm_bindgen]
    pub fn add(&mut self, amount: i32) {
        self.value += amount;
    }

    /// 减少指定的值
    ///
    /// # 参数
    /// - `amount`: 要减少的数量
    #[wasm_bindgen]
    pub fn subtract(&mut self, amount: i32) {
        self.value -= amount;
    }

    /// 乘以指定的值
    ///
    /// # 参数
    /// - `factor`: 乘数
    #[wasm_bindgen]
    pub fn multiply(&mut self, factor: i32) {
        self.value *= factor;
    }

    /// 除以指定的值
    ///
    /// # 参数
    /// - `divisor`: 除数
    ///
    /// # 返回值
    /// 如果除数为0，返回 Err，否则返回 Ok
    #[wasm_bindgen]
    pub fn divide(&mut self, divisor: i32) -> Result<(), JsValue> {
        if divisor == 0 {
            return Err(JsValue::from_str("Cannot divide by zero"));
        }
        self.value /= divisor;
        Ok(())
    }

    /// 重置计数器
    ///
    /// 将计数器值重置为 0
    #[wasm_bindgen]
    pub fn reset(&mut self) {
        self.value = 0;
    }

    /// 设置计数器值
    ///
    /// # 参数
    /// - `value`: 新的值
    #[wasm_bindgen(js_name = "setValue")]
    pub fn set_value(&mut self, value: i32) {
        self.value = value;
    }

    /// 获取当前计数器值
    ///
    /// # 返回值
    /// 返回当前计数器的值
    #[wasm_bindgen(getter)]
    pub fn value(&self) -> i32 {
        self.value
    }

    /// 判断是否为正数
    #[wasm_bindgen(js_name = "isPositive")]
    pub fn is_positive(&self) -> bool {
        self.value > 0
    }

    /// 判断是否为负数
    #[wasm_bindgen(js_name = "isNegative")]
    pub fn is_negative(&self) -> bool {
        self.value < 0
    }

    /// 判断是否为零
    #[wasm_bindgen(js_name = "isZero")]
    pub fn is_zero(&self) -> bool {
        self.value == 0
    }

    /// 获取绝对值
    #[wasm_bindgen(js_name = "absoluteValue")]
    pub fn absolute_value(&self) -> i32 {
        self.value.abs()
    }

    /// 转换为字符串
    #[wasm_bindgen(js_name = "toString")]
    pub fn to_str(&self) -> String {
        format!("Counter(value: {})", self.value)
    }
}

impl Default for Counter {
    fn default() -> Self {
        Self::new()
    }
}

#[wasm_bindgen(start)]
#[allow(clippy::main_recursion)]
pub fn main() {
    #[cfg(target_arch = "wasm32")]
    {
        use web_sys::console;
        console::log_1(&"Counter class example loaded!".into());

        let mut counter = Counter::new();
        console::log_1(&format!("Initial: {}", counter.value()).into());

        counter.increment();
        counter.increment();
        counter.increment();
        console::log_1(&format!("After 3 increments: {}", counter.value()).into());

        counter.add(10);
        console::log_1(&format!("After add(10): {}", counter.value()).into());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let counter = Counter::new();
        assert_eq!(counter.value(), 0);
    }

    #[test]
    fn test_with_value() {
        let counter = Counter::with_value(10);
        assert_eq!(counter.value(), 10);
    }

    #[test]
    fn test_increment_decrement() {
        let mut counter = Counter::new();
        counter.increment();
        assert_eq!(counter.value(), 1);
        counter.increment();
        assert_eq!(counter.value(), 2);
        counter.decrement();
        assert_eq!(counter.value(), 1);
    }

    #[test]
    fn test_add_subtract() {
        let mut counter = Counter::new();
        counter.add(10);
        assert_eq!(counter.value(), 10);
        counter.subtract(3);
        assert_eq!(counter.value(), 7);
    }

    #[test]
    fn test_multiply() {
        let mut counter = Counter::with_value(5);
        counter.multiply(3);
        assert_eq!(counter.value(), 15);
    }

    #[test]
    fn test_divide() {
        let mut counter = Counter::with_value(12);
        assert!(counter.divide(3).is_ok());
        assert_eq!(counter.value(), 4);

        assert!(counter.divide(0).is_err());
    }

    #[test]
    fn test_predicates() {
        let counter = Counter::with_value(5);
        assert!(counter.is_positive());
        assert!(!counter.is_negative());
        assert!(!counter.is_zero());

        let counter = Counter::with_value(-5);
        assert!(!counter.is_positive());
        assert!(counter.is_negative());

        let counter = Counter::with_value(0);
        assert!(counter.is_zero());
    }

    #[test]
    fn test_absolute_value() {
        let counter = Counter::with_value(-10);
        assert_eq!(counter.absolute_value(), 10);
    }

    #[test]
    fn test_reset() {
        let mut counter = Counter::with_value(100);
        counter.reset();
        assert_eq!(counter.value(), 0);
    }
}
