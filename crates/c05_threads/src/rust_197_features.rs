//! Rust 1.97 稳定特性 —— 线程与并发
//!
//! 本模块演示 Rust 1.97 中稳定化的并发/原子相关 API。
//! 实际代码使用等价的 Rust 1.96 兼容实现；1.97 原生调用以注释保留。
#![allow(clippy::incompatible_msrv)]

use std::sync::atomic::AtomicU32;

/// Rust 1.97 线程/并发特性演示
///
/// 涉及特性：
/// - `Atomic*::from_ptr`（const stable）
/// - `cfg(target_has_atomic_equal_alignment = "ptr")`
/// - `BuildHasherDefault::new` const 稳定
pub struct Rust197ThreadFeatures;

impl Rust197ThreadFeatures {
    /// 从裸指针创建 `AtomicU32` 引用
    ///
    /// # Safety
    /// 调用者必须确保指针有效、正确对齐，且在引用生命周期内独占访问该内存。
    pub unsafe fn atomic_from_ptr<'a>(ptr: *mut u32) -> &'a AtomicU32 {
        // 1.97+: AtomicU32::from_ptr(ptr) 返回 &'static AtomicU32
        unsafe { &*(ptr as *const AtomicU32) }
    }

    /// 构造默认哈希器
    pub fn build_hasher_default_new(
    ) -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        // 1.97+: const fn BuildHasherDefault::new()
        std::hash::BuildHasherDefault::new()
    }

    /// 演示 `cfg(target_has_atomic_equal_alignment = "ptr")` 的使用位置
    ///
    /// Rust 1.97 新增该 cfg；在 1.96 上无对应条件，因此使用 `#[cfg(all())]` 占位，
    /// 实际逻辑在注释中说明。
    #[cfg(all())]
    pub fn optimized_ptr_atomic() -> &'static str {
        // 1.97+:
        // #[cfg(target_has_atomic_equal_alignment = "ptr")]
        // fn optimized_ptr_atomic() { /* 依赖指针大小原子与 usize 对齐相同的平台 */ }
        "atomic pointer alignment check requires Rust 1.97+ cfg"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::Ordering;

    #[test]
    fn test_atomic_from_ptr() {
        let mut value = 0u32;
        let atomic = unsafe { Rust197ThreadFeatures::atomic_from_ptr(&mut value) };
        atomic.store(42, Ordering::Relaxed);
        assert_eq!(value, 42);
    }

    #[test]
    fn test_build_hasher_default_new() {
        let _ = Rust197ThreadFeatures::build_hasher_default_new();
    }
}
