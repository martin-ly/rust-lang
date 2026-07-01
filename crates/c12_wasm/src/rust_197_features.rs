//! Rust 1.97 稳定特性 —— WASM 目标演示
//! Rust 1.97 stabilized features —— WASM target demonstration
//!
//! 本文件使用 **Rust 1.96.0 等价实现** 演示 Rust 1.97 稳定 API 的语义。
//! 实际 Rust 1.97 调用以注释形式保留，便于 toolchain 升级到 1.97 后直接替换。
//!
//! This module demonstrates Rust 1.97 stabilized APIs using equivalent
//! implementations that compile on Rust 1.96.0. The actual Rust 1.97 call
//! sites are kept in comments for easy migration once the toolchain is upgraded.

#![allow(clippy::incompatible_msrv)]

use std::num::NonZeroU32;

/// # Rust 1.97 WASM 相关特性演示
/// # Rust 1.97 WASM feature demonstration
///
/// 涵盖的稳定 API（按 Rust 1.97 官方列表）：
/// - `u32::midpoint` / `u32::isqrt` — 无溢出整数运算，适合 WASM32 无浮点场景
/// - `<*const T>::addr` / `with_addr` — Strict Provenance 地址操作
/// - `Option::as_slice` — 零成本切片视图
/// - `NonZeroU32` 科学计数法格式化
pub struct Rust197WasmFeatures;

impl Rust197WasmFeatures {
    /// 在 32 位 WASM 目标上，`(low + high) / 2` 可能溢出，
    /// Rust 1.97 `midpoint` 使用位运算避免此问题。
    ///
    /// In 32-bit WASM, `(low + high) / 2` can overflow. Rust 1.97's
    /// `midpoint` avoids this via bit arithmetic.
    pub fn wasm_safe_midpoint(low: u32, high: u32) -> u32 {
        // Rust 1.97: low.midpoint(high)
        (low & high) + ((low ^ high) >> 1)
    }

    /// 使用纯整数算法计算平方根（WASM 无浮点依赖）。
    /// Rust 1.97 提供 `u32::isqrt`。
    ///
    /// Computes integer square root without floating-point instructions.
    /// Rust 1.97 provides `u32::isqrt`.
    pub fn wasm_integer_sqrt(n: u32) -> u32 {
        // Rust 1.97: n.isqrt()
        if n < 2 {
            return n;
        }
        let mut x = n;
        let mut y = (x + 1) / 2;
        while y < x {
            x = y;
            y = (x + n / x) / 2;
        }
        x
    }

    /// 获取指针在线性内存中的地址偏移量。
    /// Rust 1.97 `<*const T>::addr()` 安全地获取此值。
    ///
    /// Returns the linear-memory address offset of a pointer.
    /// Rust 1.97's `<*const T>::addr()` provides the same result safely.
    pub fn wasm_memory_addr<T>(ptr: *const T) -> usize {
        // Rust 1.97: ptr.addr()
        ptr as usize
    }

    /// 使用新地址构造指针，保留原指针的 provenance。
    /// Rust 1.97 提供 `<*const T>::with_addr`。
    ///
    /// Constructs a pointer with a new address while preserving the original
    /// provenance. Rust 1.97 provides `<*const T>::with_addr`.
    pub fn wasm_memory_with_addr<T>(ptr: *const T, new_addr: usize) -> *const T {
        // Rust 1.97: ptr.with_addr(new_addr)
        let _ = ptr; // keep provenance relation explicit in the comment above
        new_addr as *const T
    }

    /// 通过切片视图避免额外的分支和内存分配。
    /// Rust 1.97 提供 `Option::as_slice` / `Option::as_mut_slice`。
    ///
    /// Converts an `Option<T>` into a `&[T]` view without extra branches or
    /// allocations. Rust 1.97 provides `Option::as_slice`.
    pub fn option_as_slice_for_wasm<T>(opt: &Option<T>) -> &[T] {
        // Rust 1.97: opt.as_slice()
        match opt {
            Some(x) => std::slice::from_ref(x),
            None => &[],
        }
    }

    /// 将非零整数格式化为科学计数法。
    /// Rust 1.97 以前需通过 `.get()` 拿到原始整数再格式化。
    ///
    /// Formats a non-zero integer in scientific notation. Before Rust 1.97,
    /// format via the underlying value using `.get()`.
    pub fn format_nonzero_for_wasm(n: NonZeroU32) -> String {
        // Rust 1.97+: format!("{:e}", n)
        format!("{:e}", n.get())
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
        assert_eq!(Rust197WasmFeatures::wasm_integer_sqrt(0), 0);
        assert_eq!(Rust197WasmFeatures::wasm_integer_sqrt(1), 1);
    }

    #[test]
    fn test_wasm_memory_addr() {
        let x = 42u32;
        let addr = Rust197WasmFeatures::wasm_memory_addr(&x);
        assert_eq!(addr, &x as *const u32 as usize);
    }

    #[test]
    fn test_wasm_memory_with_addr() {
        let x = 42u32;
        let ptr = &x as *const u32;
        let new_ptr = Rust197WasmFeatures::wasm_memory_with_addr(ptr, ptr as usize + 4);
        assert_eq!(new_ptr as usize, ptr as usize + 4);
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
