//! Rust 197 Features

#![allow(clippy::incompatible_msrv)]

use std::num::NonZeroU32;

/// # Rust 1.97 WASM 相关特性演示
/// # Rust 1.97 WASM feature demonstration
/// - `midpoint` / `isqrt` — 数值计算（WASM32 目标可用）
/// - `pointer::addr` / `with_addr` — Strict Provenance（WASM 内存模型安全）
/// - `Option::as_slice` — 零成本抽象
pub struct Rust197WasmFeatures;

impl Rust197WasmFeatures {
    /// 在 32 位 WASM 目标上，`(low + high) / 2` 可能溢出，
    /// in 32 WASM goal on ，`(low + high) / 2` may ，
    /// `midpoint` 使用位运算避免此问题。
    /// `midpoint` this problem 。
    /// `midpoint` Use位运算Avoidthisproblem。
    pub fn wasm_safe_midpoint(low: u32, high: u32) -> u32 {
        low.midpoint(high)
    }

    /// 使用 `u32::isqrt` 计算整数平方根（WASM 无浮点依赖）
    /// `u32::isqrt` （WASM point ）
    /// 纯整数算法，不依赖 WASM 浮点单元。
    /// algorithm ， WASM point 。
    pub fn wasm_integer_sqrt(n: u32) -> u32 {
        n.isqrt()
    }

    /// 使用 `pointer::addr` 获取线性内存地址
    /// `pointer::addr` line memory
    /// 在 WASM 中，指针即线性内存偏移量。`addr()` 安全地获取此值。
    /// in WASM in ，pointer line memory 。`addr()` this 。
    pub fn wasm_memory_addr<T>(ptr: *const T) -> usize {
        ptr.addr()
    }

    /// 通过切片视图避免额外的分支和内存分配。
    /// graph outside and memory 。
    /// outside and memory 。
    pub fn option_as_slice_for_wasm<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }

    pub fn format_nonzero_for_wasm(n: NonZeroU32) -> String {
        format!("{:e}", n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_safe_midpoint() {
        assert_eq!(Rust197WasmFeatures::wasm_safe_midpoint(0, 100), 50);
        assert_eq!(
            Rust197WasmFeatures::wasm_safe_midpoint(u32::MAX - 1, u32::MAX),
            u32::MAX - 1
        );
    }

    #[test]
    fn test_wasm_integer_sqrt() {
        assert_eq!(Rust197WasmFeatures::wasm_integer_sqrt(16), 4);
        assert_eq!(Rust197WasmFeatures::wasm_integer_sqrt(15), 3);
    }

    #[test]
    fn test_wasm_memory_addr() {
        let x = 42u32;
        let addr = Rust197WasmFeatures::wasm_memory_addr(&x);
        assert_eq!(addr, &x as *const u32 as usize);
    }

    #[test]
    fn test_option_as_slice_for_wasm() {
        let opt = Some(42);
        assert_eq!(Rust197WasmFeatures::option_as_slice_for_wasm(&opt), &[42]);

        let none: Option<i32> = None;
        assert!(Rust197WasmFeatures::option_as_slice_for_wasm(&none).is_empty());
    }

    #[test]
    fn test_format_nonzero_for_wasm() {
        let n = NonZeroU32::new(1000).unwrap();
        assert_eq!(Rust197WasmFeatures::format_nonzero_for_wasm(n), "1e3");
    }
}
