//! Rust 1.97 稳定特性 —— 控制流与函数
//!
//! 本模块演示 Rust 1.97 中稳定化的控制流/函数相关 API。
//! 实际代码使用等价的 Rust 1.96 兼容实现；1.97 原生调用以 `#[cfg(nightly)]`
//! 分支保留，可通过 `RUSTFLAGS="--cfg nightly" cargo build` 启用。
#![allow(clippy::incompatible_msrv)]
#![allow(unexpected_cfgs)]
#![allow(clippy::borrowed_box)]

use std::hash::BuildHasher;

/// 用于演示 `must_use` lint 扩展的标记类型
#[must_use]
#[derive(Debug, PartialEq)]
pub struct ImportantToken;

/// Rust 1.97 控制流/函数特性演示
///
/// 涉及特性：
/// - `must_use` lint 扩展：`Result<#[must_use] T, E>` / `ControlFlow<B, C>`
///   也会触发未使用警告（编译器行为变更，无对应运行时 API）
/// - `BuildHasherDefault::new` const 稳定
/// - `ptr::fn_addr_eq`
pub struct Rust197ControlFlowFeatures;

impl Rust197ControlFlowFeatures {
    /// 返回一个包含 `#[must_use]` 内部类型的 `Result`
    ///
    /// 在 Rust 1.97+ 中，忽略该 `Result` 会触发 `must_use` 警告；
    /// Rust 1.96 同样会因 `Result` 本身标记 `must_use` 而警告，
    /// 但 1.97 额外会将内部类型的 `must_use` 传播出来。
    pub fn give_token() -> Result<ImportantToken, std::io::Error> {
        Ok(ImportantToken)
    }

    /// 显式忽略 `Result`，消除 `must_use` 警告
    pub fn receive_token_silently() {
        let _ = Self::give_token();
    }

    /// 使用 `?` 处理 `Result<#[must_use] T, E>`，符合 1.97 lint 要求
    pub fn receive_token_with_q() -> Result<ImportantToken, std::io::Error> {
        Self::give_token()
    }

    /// 构造默认哈希器
    #[cfg(nightly)]
    pub const fn build_hasher_default_new()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }

    #[cfg(not(nightly))]
    pub fn build_hasher_default_new()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }

    /// 使用默认哈希器计算散列值
    pub fn hash_with_default_hasher(bytes: &[u8]) -> u64 {
        use std::hash::Hasher;
        let mut hasher = Self::build_hasher_default_new().build_hasher();
        hasher.write(bytes);
        hasher.finish()
    }

    /// 可移植的函数指针地址比较
    #[cfg(nightly)]
    pub fn fn_addr_eq(f: fn(), g: fn()) -> bool {
        std::ptr::fn_addr_eq(f, g)
    }

    #[cfg(not(nightly))]
    pub fn fn_addr_eq(f: fn(), g: fn()) -> bool {
        f as usize == g as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_give_token() {
        let token = Rust197ControlFlowFeatures::give_token().unwrap();
        assert_eq!(token, ImportantToken);
    }

    #[test]
    fn test_receive_token_silently() {
        Rust197ControlFlowFeatures::receive_token_silently();
    }

    #[test]
    fn test_receive_token_with_q() {
        assert_eq!(
            Rust197ControlFlowFeatures::receive_token_with_q().unwrap(),
            ImportantToken
        );
    }

    #[test]
    fn test_hash_with_default_hasher() {
        let h1 = Rust197ControlFlowFeatures::hash_with_default_hasher(b"hello");
        let h2 = Rust197ControlFlowFeatures::hash_with_default_hasher(b"hello");
        assert_eq!(h1, h2);
    }

    #[test]
    fn test_fn_addr_eq() {
        // 使用 #[inline(never)] 与不同体，避免编译器将两个空函数合并为同一地址。
        #[inline(never)]
        fn a() {
            std::hint::black_box(1);
        }
        #[inline(never)]
        fn b() {
            std::hint::black_box(2);
        }
        assert!(Rust197ControlFlowFeatures::fn_addr_eq(a, a));
        assert!(!Rust197ControlFlowFeatures::fn_addr_eq(a, b));
    }
}
