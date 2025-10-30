//! # 基础加法示例
//!
//! 这是最简单的 WASM 示例，展示如何导出一个加法函数到 JavaScript。
//!
//! ## 运行方式
//!
//! ```bash
//! # 编译为 WASM
//! cargo build --example 01_basic_add --target wasm32-unknown-unknown --release
//!
//! # 查看生成的 WASM 文件
//! ls -lh target/wasm32-unknown-unknown/release/examples/01_basic_add.wasm
//! ```
//!
//! ## JavaScript 集成
//!
//! ```javascript
//! // 加载 WASM 模块
//! const wasmModule = await WebAssembly.instantiateStreaming(
//!     fetch('01_basic_add.wasm')
//! );
//!
//! // 调用 add 函数
//! const result = wasmModule.instance.exports.add(5, 3);
//! console.log('5 + 3 =', result); // 输出: 5 + 3 = 8
//! ```

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
/// ```
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
