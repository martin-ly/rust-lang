//! Rust 1.97 稳定特性 —— 线程与并发
//!
//! 本模块演示 Rust 1.97.0 中稳定化的并发/原子相关 API。
//! 由于当前工具链为 Rust 1.96.0，实际代码使用等价的 1.96 兼容实现；
//! 对应的 1.97 原生 API 调用以注释形式保留。
#![allow(clippy::incompatible_msrv)]

use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;
use std::num::NonZeroU32;
use std::sync::atomic::AtomicU32;

/// Rust 1.97 线程/并发特性演示
///
/// 涉及特性：
/// - `cfg(target_has_atomic_equal_alignment = "ptr")`
/// - `BuildHasherDefault::new` const 稳定
/// - `Option<NonZero*>` niche 编码偏好 `-1`（影响跨线程 FFI 数据布局）
/// - `must_use` lint 向 `Result<T, E>` / `ControlFlow<B, C>` 内部类型传播
pub struct Rust197ThreadFeatures;

#[must_use]
#[derive(Debug, PartialEq)]
pub struct ImportantToken(pub u32);

impl Rust197ThreadFeatures {
    /// 构造默认哈希器（1.97 后可在 const 上下文调用）
    pub const fn build_hasher_default_new() -> BuildHasherDefault<DefaultHasher> {
        // 1.97+: const HASHER: BuildHasherDefault<DefaultHasher> = BuildHasherDefault::new();
        BuildHasherDefault::new()
    }

    /// 演示 `cfg(target_has_atomic_equal_alignment = "ptr")` 的使用位置
    ///
    /// Rust 1.97 新增该 cfg；在 1.96 上无对应条件，实际逻辑在注释中说明。
    pub fn optimized_ptr_atomic() -> &'static str {
        // 1.97+:
        // #[cfg(target_has_atomic_equal_alignment = "ptr")]
        // fn optimized_ptr_atomic() { /* 依赖指针大小原子与 usize 对齐相同的平台 */ }
        "atomic pointer alignment check requires Rust 1.97+ cfg"
    }

    /// 返回 `Option<NonZeroU32>` 在内存中的表示字节
    ///
    /// Rust 1.97 起 `Option<NonZero*>` 优先使用 `-1` 作为 `None` 的 niche 值，
    /// 优化 FFI 和序列化互操作。该函数展示在 1.96 上获取同样的字节表示。
    pub fn nonzero_option_bytes(opt: Option<NonZeroU32>) -> [u8; 4] {
        // 1.97+: 编译器内部表示直接使用 -1 作为 None 的 niche
        match opt {
            Some(nz) => nz.get().to_le_bytes(),
            None => (-1i32).to_le_bytes(),
        }
    }

    /// 获取原子引用（等效实现）
    ///
    /// # Safety
    /// 调用者必须确保指针有效、正确对齐，且在引用生命周期内独占访问该内存。
    pub unsafe fn atomic_from_ptr<'a>(ptr: *mut u32) -> &'a AtomicU32 {
        // 1.96 等效实现；1.97 没有稳定 Atomic*::from_ptr
        unsafe { &*(ptr as *const AtomicU32) }
    }

    /// 演示 `#[must_use]` 通过 `Result<T, E>` 传播
    pub fn give_token() -> Result<ImportantToken, std::io::Error> {
        Ok(ImportantToken(42))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering;

    #[test]
    fn test_build_hasher_default_new() {
        let _ = Rust197ThreadFeatures::build_hasher_default_new();
    }

    #[test]
    fn test_nonzero_option_bytes() {
        let some = NonZeroU32::new(1).unwrap();
        assert_eq!(
            Rust197ThreadFeatures::nonzero_option_bytes(Some(some)),
            1u32.to_le_bytes()
        );
        assert_eq!(
            Rust197ThreadFeatures::nonzero_option_bytes(None),
            (-1i32).to_le_bytes()
        );
    }

    #[test]
    fn test_atomic_from_ptr() {
        let mut value = 0u32;
        let atomic = unsafe { Rust197ThreadFeatures::atomic_from_ptr(&mut value) };
        atomic.store(42, Ordering::Relaxed);
        assert_eq!(value, 42);
    }

    #[test]
    fn test_must_use_propagation() {
        // Rust 1.97+ 中 `Result<#[must_use] T, E>` 会触发未使用警告。
        // 这里显式忽略以避免 lint。
        let _ = Rust197ThreadFeatures::give_token();
    }
}
