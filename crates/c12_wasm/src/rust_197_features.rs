//! Rust 1.97 特性跟踪模块 —— WASM
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `std::pin::pin!` 和 `Vec::pop_if` 在 WASM 场景中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `pin!` 在栈上固定 WASM 内存缓冲区
    pub fn pin_wasm_buffer<T: Clone>(data: T) -> T {
        let pinned = std::pin::pin!(data);
        pinned.clone()
    }

    /// 使用 `Vec::pop_if` 从 WASM 导出表中条件移除
    pub fn pop_if_exported(exports: &mut Vec<String>, prefix: &str) -> Option<String> {
        exports.pop_if(|e| e.starts_with(prefix))
    }

    /// 组合两者管理 WASM 模块资源
    pub fn manage_wasm_exports(exports: &mut Vec<String>) -> (usize, Option<String>) {
        let len = exports.len();
        let main = exports.pop_if(|e| e == "_main");
        (len, main)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pin_wasm_buffer() {
        assert_eq!(
            Rust197Features::pin_wasm_buffer(vec![1u8, 2, 3]),
            vec![1, 2, 3]
        );
        assert_eq!(Rust197Features::pin_wasm_buffer("wasm".to_string()), "wasm");
    }

    #[test]
    fn test_pop_if_exported() {
        let mut exports = vec!["memory".to_string(), "_start".to_string()];
        assert_eq!(
            Rust197Features::pop_if_exported(&mut exports, "_"),
            Some("_start".to_string())
        );
        assert_eq!(exports, vec!["memory"]);
    }

    #[test]
    fn test_manage_wasm_exports() {
        let mut exports = vec!["memory".to_string(), "_main".to_string()];
        let (len, main) = Rust197Features::manage_wasm_exports(&mut exports);
        assert_eq!(len, 2);
        assert_eq!(main, Some("_main".to_string()));
        assert_eq!(exports, vec!["memory"]);
    }
}
