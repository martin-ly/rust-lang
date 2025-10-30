//! # 字符串操作示例
//!
//! 展示如何在 Rust WASM 和 JavaScript 之间传递字符串
//!
//! ## 运行方式
//!
//! ```bash
//! # 使用 wasm-pack 构建
//! wasm-pack build --target web
//!
//! # 在 HTML 中使用
//! # 创建 index.html 并运行本地服务器
//! ```
//!
//! ## JavaScript 使用示例
//!
//! ```javascript
//! import init, { greet, reverse, to_uppercase } from './pkg/c12_wasm.js';
//!
//! await init();
//!
//! console.log(greet("Alice"));           // "Hello, Alice!"
//! console.log(reverse("hello"));          // "olleh"
//! console.log(to_uppercase("rust wasm")); // "RUST WASM"
//! ```

use wasm_bindgen::prelude::*;

/// 问候函数
///
/// # 参数
/// - `name`: 要问候的名字
///
/// # 返回值
/// 返回格式化的问候字符串
#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    format!("Hello, {}!", name)
}

/// 反转字符串
///
/// # 参数
/// - `s`: 要反转的字符串
///
/// # 返回值
/// 返回反转后的字符串
///
/// # 示例
/// ```
/// use c12_wasm::string_examples::reverse_string;
/// assert_eq!(reverse_string("hello"), "olleh");
/// ```
#[wasm_bindgen]
pub fn reverse(s: &str) -> String {
    s.chars().rev().collect()
}

/// 转换为大写
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

/// 转换为小写
#[wasm_bindgen]
pub fn to_lowercase(s: &str) -> String {
    s.to_lowercase()
}

/// 统计单词数
///
/// # 参数
/// - `s`: 要分析的字符串
///
/// # 返回值
/// 返回单词数量
#[wasm_bindgen]
pub fn count_words(s: &str) -> usize {
    s.split_whitespace().count()
}

/// 检查是否为回文
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

#[wasm_bindgen(start)]
#[allow(clippy::main_recursion)]
pub fn main() {
    #[cfg(target_arch = "wasm32")]
    {
        use web_sys::console;
        console::log_1(&"String operations example loaded!".into());
        console::log_1(&greet("WASM").into());
        console::log_1(&format!("Reverse 'hello': {}", reverse("hello")).into());
        console::log_1(&format!("'racecar' is palindrome: {}", is_palindrome("racecar")).into());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_greet() {
        assert_eq!(greet("World"), "Hello, World!");
    }

    #[test]
    fn test_reverse() {
        assert_eq!(reverse("hello"), "olleh");
        assert_eq!(reverse("rust"), "tsur");
    }

    #[test]
    fn test_case_conversion() {
        assert_eq!(to_uppercase("hello"), "HELLO");
        assert_eq!(to_lowercase("WORLD"), "world");
    }

    #[test]
    fn test_count_words() {
        assert_eq!(count_words("hello world"), 2);
        assert_eq!(count_words("rust wasm is awesome"), 4);
    }

    #[test]
    fn test_is_palindrome() {
        assert!(is_palindrome("racecar"));
        assert!(is_palindrome("A man a plan a canal Panama"));
        assert!(!is_palindrome("hello"));
    }
}
