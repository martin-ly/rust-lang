//! # C12 WASM - 核心示例代码
//!
//! 本模块提供了完整的 WASM 示例代码，包括：
//! - wasm-bindgen 基础用法
//! - JavaScript 互操作
//! - 性能优化技巧
//! - WASI 应用示例

// 引入生态库示例模块
pub mod ecosystem_examples;

// 引入 WasmEdge 示例模块
pub mod wasmedge_examples;

// Rust 1.91 新特性模块
pub mod rust_191_features;
// Rust 1.92.0 新特性模块
pub mod rust_192_features;
// Rust 1.93.0 新特性模块
pub mod rust_193_features;

/// wasm-bindgen 基础示例
pub mod basic_examples {
    use wasm_bindgen::prelude::*;

    /// 简单的加法函数
    ///
    /// # 参数
    /// - `a`: 第一个加数
    /// - `b`: 第二个加数
    ///
    /// # 返回值
    /// 返回两个数的和
    ///
    /// # 示例
    /// ```javascript
    /// import { add } from './pkg/hello_wasm';
    /// const result = add(2, 3); // 5
    /// ```
    #[wasm_bindgen]
    pub fn add(a: i32, b: i32) -> i32 {
        a + b
    }

    /// 字符串问候函数
    ///
    /// # 参数
    /// - `name`: 要问候的名字
    ///
    /// # 返回值
    /// 返回格式化的问候字符串
    ///
    /// # 示例
    /// ```javascript
    /// import { greet } from './pkg/hello_wasm';
    /// const message = greet("World"); // "Hello, World!"
    /// ```
    #[wasm_bindgen]
    pub fn greet(name: &str) -> String {
        format!("Hello, {}!", name)
    }

    /// 数组求和
    ///
    /// # 参数
    /// - `arr`: 要计算的整数数组
    ///
    /// # 返回值
    /// 返回数组中所有元素的和
    ///
    /// # 注意
    /// 这个函数会克隆数组，对于大数组可能不够高效
    ///
    /// # 示例
    /// ```javascript
    /// import { sum_array } from './pkg/hello_wasm';
    /// const result = sum_array(new Int32Array([1, 2, 3, 4, 5])); // 15
    /// ```
    #[wasm_bindgen]
    pub fn sum_array(arr: &[i32]) -> i32 {
        arr.iter().sum()
    }
}

/// 复杂类型示例
pub mod complex_types {
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
        #[wasm_bindgen(constructor)]
        #[allow(clippy::new_without_default)]
        pub fn new() -> Counter {
            Counter { value: 0 }
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

        /// 重置计数器
        ///
        /// 将计数器值重置为 0
        #[wasm_bindgen]
        pub fn reset(&mut self) {
            self.value = 0;
        }

        /// 获取当前计数器值
        ///
        /// # 返回值
        /// 返回当前计数器的值
        #[wasm_bindgen(getter)]
        pub fn value(&self) -> i32 {
            self.value
        }
    }

    /// 人员信息结构体
    ///
    /// 展示如何传递复杂对象
    #[wasm_bindgen]
    pub struct Person {
        name: String,
        age: u32,
    }

    #[wasm_bindgen]
    impl Person {
        /// 创建新的人员实例
        ///
        /// # 参数
        /// - `name`: 人员姓名
        /// - `age`: 人员年龄
        ///
        /// # 返回值
        /// 返回新的人员实例
        #[wasm_bindgen(constructor)]
        pub fn new(name: String, age: u32) -> Person {
            Person { name, age }
        }

        /// 获取姓名
        #[wasm_bindgen(getter)]
        pub fn name(&self) -> String {
            self.name.clone()
        }

        /// 获取年龄
        #[wasm_bindgen(getter)]
        pub fn age(&self) -> u32 {
            self.age
        }

        /// 设置年龄
        ///
        /// # 参数
        /// - `age`: 新的年龄值
        #[wasm_bindgen(setter)]
        pub fn set_age(&mut self, age: u32) {
            self.age = age;
        }

        /// 转换为字符串描述
        #[wasm_bindgen(js_name = "toString")]
        pub fn to_str(&self) -> String {
            format!("{} ({} years old)", self.name, self.age)
        }
    }
}

/// 数组和向量操作示例
pub mod array_examples {
    use wasm_bindgen::prelude::*;

    /// 计算数组的平均值
    ///
    /// # 参数
    /// - `numbers`: 数字数组
    ///
    /// # 返回值
    /// 返回平均值，如果数组为空则返回 0.0
    ///
    /// # 性能说明
    /// 这个函数会遍历整个数组一次，时间复杂度 O(n)
    #[wasm_bindgen]
    pub fn calculate_average(numbers: &[f64]) -> f64 {
        if numbers.is_empty() {
            return 0.0;
        }
        let sum: f64 = numbers.iter().sum();
        sum / (numbers.len() as f64)
    }

    /// 查找数组中的最大值
    ///
    /// # 参数
    /// - `numbers`: 数字数组
    ///
    /// # 返回值
    /// 返回最大值，如果数组为空则返回 None（JavaScript 中为 undefined）
    #[wasm_bindgen]
    pub fn find_max(numbers: &[i32]) -> Option<i32> {
        numbers.iter().max().copied()
    }

    /// 反转数组
    ///
    /// # 参数
    /// - `numbers`: 要反转的数组
    ///
    /// # 返回值
    /// 返回反转后的新数组
    ///
    /// # 注意
    /// 这个函数会创建一个新数组，内存使用 O(n)
    #[wasm_bindgen]
    pub fn reverse_array(numbers: &[i32]) -> Vec<i32> {
        numbers.iter().rev().copied().collect()
    }

    /// 过滤数组中的偶数
    ///
    /// # 参数
    /// - `numbers`: 要过滤的数组
    ///
    /// # 返回值
    /// 返回只包含偶数的新数组
    #[wasm_bindgen]
    pub fn filter_even(numbers: &[i32]) -> Vec<i32> {
        numbers.iter().filter(|&&x| x % 2 == 0).copied().collect()
    }
}

/// 字符串操作示例
pub mod string_examples {
    use wasm_bindgen::prelude::*;

    /// 反转字符串
    ///
    /// # 参数
    /// - `s`: 要反转的字符串
    ///
    /// # 返回值
    /// 返回反转后的字符串
    ///
    /// # 示例
    /// ```javascript
    /// import { reverse_string } from './pkg/hello_wasm';
    /// const result = reverse_string("hello"); // "olleh"
    /// ```
    #[wasm_bindgen]
    pub fn reverse_string(s: &str) -> String {
        s.chars().rev().collect()
    }

    /// 检查字符串是否为回文
    ///
    /// # 参数
    /// - `s`: 要检查的字符串
    ///
    /// # 返回值
    /// 如果是回文返回 true，否则返回 false
    #[wasm_bindgen]
    pub fn is_palindrome(s: &str) -> bool {
        let s_lower: String = s
            .chars()
            .filter(|c| c.is_alphanumeric())
            .collect::<String>()
            .to_lowercase();
        let reversed: String = s_lower.chars().rev().collect();
        s_lower == reversed
    }

    /// 统计字符串中的单词数
    ///
    /// # 参数
    /// - `s`: 要分析的字符串
    ///
    /// # 返回值
    /// 返回单词数量
    #[wasm_bindgen]
    pub fn count_words(s: &str) -> u32 {
        s.split_whitespace().count() as u32
    }

    /// 将字符串转换为大写
    ///
    /// # 参数
    /// - `s`: 要转换的字符串
    ///
    /// # 返回值
    /// 返回转换为大写的字符串
    #[wasm_bindgen]
    pub fn to_uppercase(s: &str) -> String {
        s.to_uppercase()
    }
}

/// 性能优化示例
pub mod performance_examples {
    use std::cell::RefCell;
    use wasm_bindgen::prelude::*;

    // 线程局部存储的缓冲区，用于重用内存
    thread_local! {
        static BUFFER: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
    }

    /// 优化的数组处理函数（重用缓冲区）
    ///
    /// 这个函数展示了如何重用缓冲区来减少内存分配
    ///
    /// # 参数
    /// - `data`: 要处理的字节数组
    ///
    /// # 返回值
    /// 返回处理后的字节数组
    ///
    /// # 性能说明
    /// 通过重用线程局部缓冲区，避免了每次调用都分配新内存
    #[wasm_bindgen]
    pub fn process_bytes_optimized(data: &[u8]) -> Vec<u8> {
        BUFFER.with(|buf| {
            let mut buffer = buf.borrow_mut();
            buffer.clear();

            // 预分配容量（如果需要）
            if buffer.capacity() < data.len() {
                buffer.reserve(data.len());
            }

            // 处理数据（示例：将每个字节乘以2）
            for &byte in data {
                buffer.push(byte.wrapping_mul(2));
            }

            buffer.clone()
        })
    }

    /// 预分配容量的向量创建
    ///
    /// # 参数
    /// - `size`: 向量大小
    ///
    /// # 返回值
    /// 返回预分配容量的向量
    #[wasm_bindgen]
    pub fn create_preallocated_vector(size: usize) -> Vec<i32> {
        let mut vec = Vec::with_capacity(size);
        for i in 0..size {
            vec.push(i as i32);
        }
        vec
    }
}

/// 错误处理示例
pub mod error_examples {
    use wasm_bindgen::prelude::*;

    /// 安全的除法运算
    ///
    /// # 参数
    /// - `a`: 被除数
    /// - `b`: 除数
    ///
    /// # 返回值
    /// 返回 `Result`，成功时包含商，失败时包含错误信息
    ///
    /// # 示例
    /// ```javascript
    /// import { safe_divide } from './pkg/hello_wasm';
    /// const result1 = await safe_divide(10, 2); // 5
    /// const result2 = await safe_divide(10, 0); // 抛出错误
    /// ```
    #[wasm_bindgen]
    pub fn safe_divide(a: f64, b: f64) -> Result<f64, JsValue> {
        if b == 0.0 {
            Err(JsValue::from_str("Division by zero"))
        } else {
            Ok(a / b)
        }
    }

    /// 验证输入字符串长度
    ///
    /// # 参数
    /// - `input`: 要验证的字符串
    /// - `min_length`: 最小长度
    /// - `max_length`: 最大长度
    ///
    /// # 返回值
    /// 如果验证通过返回字符串，否则返回错误
    #[wasm_bindgen]
    pub fn validate_string(
        input: &str,
        min_length: usize,
        max_length: usize,
    ) -> Result<String, JsValue> {
        let len = input.len();
        if len < min_length {
            Err(JsValue::from_str(&format!(
                "String too short (minimum {} characters)",
                min_length
            )))
        } else if len > max_length {
            Err(JsValue::from_str(&format!(
                "String too long (maximum {} characters)",
                max_length
            )))
        } else {
            Ok(input.to_string())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(basic_examples::add(2, 3), 5);
    }

    #[test]
    fn test_greet() {
        assert_eq!(basic_examples::greet("World"), "Hello, World!");
    }

    #[test]
    fn test_counter() {
        let mut counter = complex_types::Counter::new();
        assert_eq!(counter.value(), 0);
        counter.increment();
        assert_eq!(counter.value(), 1);
        counter.decrement();
        assert_eq!(counter.value(), 0);
    }

    #[test]
    fn test_reverse_string() {
        assert_eq!(string_examples::reverse_string("hello"), "olleh");
    }

    #[test]
    fn test_is_palindrome() {
        assert!(string_examples::is_palindrome("racecar"));
        assert!(!string_examples::is_palindrome("hello"));
    }
}
