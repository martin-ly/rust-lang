//! # 基础加法示例
//! # foundation example
//! ## 📐 知识结构
//! ## 📐 structure
//! ## 📐 知识structure
//! ### 核心概念
//! ### core concept
//!   - **属性**: 函数导出、类型转换、互操作
//!   - **attribute **: function 、type conversion 、
//! ### 思维导图
//! ###
//! WASM 基础示例
//! WASM foundation example
//! ├── Rust 函数
//! ├── Rust function
//! │   └── 导出函数
//! │ └── function
//! ├── 编译as WASM
//! ```
//!
//! ## 运行方式
//! ## Run way
//! ```bash
//! # 编译as WASM
//! # 查看Generate WASM 文件
//!
//! // 加载 WASM 模块
//! // WASM module
//! // 加载 WASM module
//! );
//!
//! // 调用 add 函数
//! // add function
//! console.log('5 + 3 =', result); // 输出: 5 + 3 = 8
use wasm_bindgen::prelude::*;

/// 简单的加法函数
/// simple function
/// # 参数
/// # parameter
/// - `a`: 第一个加数
/// - `a`: first
/// - `b`: 第二个加数
/// - `b`: second
/// # 返回值
/// # return value
/// 返回两个数的和
/// and
/// # 示例
/// # example
/// use c12_wasm::basic_examples::add;
/// assert_eq!(add(2, 3), 5);
/// ```
#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[wasm_bindgen]
pub fn multiply(a: i32, b: i32) -> i32 {
    a * b
}

#[wasm_bindgen]
pub fn subtract(a: i32, b: i32) -> i32 {
    a - b
}

#[wasm_bindgen(start)]
#[allow(clippy::main_recursion)]
pub fn main() {
    // 初始化日志（仅在浏览器环境中有效）
    #[cfg(target_arch = "wasm32")]
    {
        use web_sys::console;
        console::log_1(&"WASM module loaded!".into());
        console::log_1(&format!("2 + 3 = {}", add(2, 3)).into());
        console::log_1(&format!("2 * 3 = {}", multiply(2, 3)).into());
        console::log_1(&format!("5 - 3 = {}", subtract(5, 3)).into());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
        assert_eq!(add(-1, 1), 0);
        assert_eq!(add(0, 0), 0);
    }

    #[test]
    fn test_multiply() {
        assert_eq!(multiply(2, 3), 6);
        assert_eq!(multiply(-2, 3), -6);
        assert_eq!(multiply(0, 100), 0);
    }

    #[test]
    fn test_subtract() {
        assert_eq!(subtract(5, 3), 2);
        assert_eq!(subtract(3, 5), -2);
        assert_eq!(subtract(0, 0), 0);
    }
}
