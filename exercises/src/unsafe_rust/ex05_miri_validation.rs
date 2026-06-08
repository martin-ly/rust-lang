//! # 练习 5: Miri 验证与未定义行为识别 / Exercise 5: Miri Validation and UB Identification
//!
//! **难度 / Difficulty**: Hard  
//! **考点 / Focus**: Miri 工具使用、Stacked Borrows/Tree Borrows、未定义行为识别与修复
//!   Miri tool usage, Stacked Borrows/Tree Borrows, UB identification and fixing
//!
//! ## 题目描述 / Problem Description
//!
//! 下面提供了三段**包含微妙 UB** 的代码。你的任务是：
//! Below are three code snippets **containing subtle UB**. Your tasks:
//! 1. 找出每段代码中的 UB / Identify UB in each snippet
//! 2. 解释为什么它是 UB（从 Miri 的角度）/ Explain why it's UB (from Miri's perspective)
//! 3. 修复代码使其通过 `cargo miri test` 验证 / Fix code to pass `cargo miri test` validation
//!
//! 这三段代码分别考察：
//! These three snippets test:
//! - 悬垂指针解引用（use-after-free）/ Dangling pointer dereference (use-after-free)
//! - 违反别名规则（aliasing violation）/ Aliasing rule violation
//! - 越界指针偏移（out-of-bounds pointer offset）/ Out-of-bounds pointer offset
//!
//! ## 要求 / Requirements
//!
//! - 不要改变函数的公开签名 / Do not change function public signatures
//! - 修复后的代码必须能通过 Miri 验证 / Fixed code must pass Miri validation
//! - 每段代码的 UB 解释写在文档注释中 / UB explanations in doc comments
//!
//! ## 提示 / Hints
//!
//! - 运行 Miri：`cargo +nightly miri test`
//! - Miri 使用 Tree Borrows（默认）或 Stacked Borrows 模型检测 UB
//!   Miri uses Tree Borrows (default) or Stacked Borrows to detect UB
//! - 原始指针的别名规则比引用宽松，但并非完全没有限制
//!   Raw pointer aliasing rules are looser than references, but not unrestricted

// ============================================================================
// 代码段 1: 悬垂指针解引用 (Use-After-Free)
// Code snippet 1: Use-After-Free
// ============================================================================

/// 返回一个指向局部变量的原始指针
/// Returns a raw pointer to a local variable
///
/// # UB 说明 / UB Explanation
///
/// 此函数返回的指针指向栈上的局部变量 `x`。当函数返回时，`x` 被销毁，
/// The returned pointer points to local variable `x` on the stack. When function returns, `x` is destroyed,
/// 指针变成悬垂指针。解引用它将导致 use-after-free。
/// pointer becomes dangling. Dereferencing it causes use-after-free.
///
/// # 修复思路 / Fix Strategy
///
/// 使用 `Box::into_raw` 将数据分配到堆上，或者让调用者提供存储空间。
/// Use `Box::into_raw` to allocate on heap, or let caller provide storage.
#[allow(dangling_pointers_from_locals)]
pub fn get_dangling_pointer_bad() -> *const i32 {
    let x = 42;
    &x as *const i32
}

/// 修复版：返回堆分配的指针
/// Fixed version: returns heap-allocated pointer
///
/// 调用者负责在适当的时候用 `Box::from_raw` 释放内存。
/// Caller is responsible for freeing memory with `Box::from_raw` at appropriate time.
pub fn get_heap_pointer_fixed() -> *const i32 {
    let boxed = Box::new(42);
    Box::into_raw(boxed)
}

/// 安全封装：获取值并自动释放堆内存
/// Safe wrapper: gets value and automatically frees heap memory
///
/// 注意：这只是一个教学示例，实际中直接用 Box 返回更安全。
/// Note: This is an educational example; in practice returning Box directly is safer.
pub fn get_value_safely() -> i32 {
    let ptr = get_heap_pointer_fixed();
    // SAFETY: 我们知道 ptr 是由 Box::into_raw 产生的有效指针
    // SAFETY: We know ptr is a valid pointer produced by Box::into_raw
    let value = unsafe { *ptr };
    // 释放内存，避免泄漏 / Free memory to avoid leak
    // SAFETY: ptr 是由 Box::into_raw 产生的，且只被解引用一次
    // SAFETY: ptr was produced by Box::into_raw and only dereferenced once
    unsafe {
        let _ = Box::from_raw(ptr as *mut i32);
    }
    value
}

// ============================================================================
// 代码段 2: 违反别名规则 (Aliasing Violation)
// Code snippet 2: Aliasing Violation
// ============================================================================

/// 尝试同时通过引用和原始指针修改同一数据
/// Attempts to modify same data through both reference and raw pointer
///
/// # UB 说明 / UB Explanation
///
/// 在创建 `&mut i32`（`ref_mut`）之后，该引用拥有对 `data` 的独占访问权。
/// After creating `&mut i32` (`ref_mut`), this reference has exclusive access to `data`.
/// 此时通过原始指针 `raw` 写入数据违反了 Rust 的别名规则，
/// Writing through raw pointer `raw` at this time violates Rust's aliasing rules,
/// 即使原始指针是在引用之前创建的。
/// even though raw pointer was created before the reference.
///
/// 在 Stacked Borrows 模型下，`&mut` 的创建会使得之前的所有指针失效。
/// Under Stacked Borrows, `&mut` creation invalidates all previous pointers.
/// 在 Tree Borrows 模型下，虽然规则稍宽松，但这种模式仍然是 UB。
/// Under Tree Borrows, while rules are slightly looser, this pattern is still UB.
///
/// # 修复思路 / Fix Strategy
///
/// 要么只使用引用，要么只使用原始指针，不要混用。
/// Use only references or only raw pointers, don't mix.
pub fn aliasing_violation_bad() -> i32 {
    let mut data = 0i32;
    let raw = &mut data as *mut i32;

    let ref_mut = &mut data;
    *ref_mut = 1;

    // UB: 在 &mut data 活跃时通过 raw 写入
    // UB: writing through raw while &mut data is active
    unsafe {
        *raw = 2;
    }

    *ref_mut
}

/// 修复版：只使用原始指针操作
/// Fixed: use raw pointers only
pub fn aliasing_fixed_with_raw_only() -> i32 {
    let mut data = 0i32;
    let raw = &mut data as *mut i32;

    // SAFETY: raw 是唯一活跃的指针，没有并发的引用
    // SAFETY: raw is the only active pointer, no concurrent references
    unsafe {
        *raw = 1;
        *raw = 2;
        *raw
    }
}

/// 修复版：只使用引用操作
/// Fixed: use references only
pub fn aliasing_fixed_with_ref_only() -> i32 {
    let ref_mut = &mut 0i32;
    *ref_mut = 1;
    *ref_mut = 2;
    *ref_mut
}

// ============================================================================
// 代码段 3: 越界指针偏移 (Out-of-Bounds Pointer Offset)
// Code snippet 3: Out-of-Bounds Pointer Offset
// ============================================================================

/// 演示越界指针偏移的 UB
/// Demonstrates out-of-bounds pointer offset UB
///
/// # UB 说明 / UB Explanation
///
/// `pointer::add` 和 `pointer::offset` 要求结果指针必须保持在分配对象的边界内
/// `pointer::add` and `pointer::offset` require result pointer to stay within allocated object bounds
/// （或恰好在最后一个元素之后的一个位置）。偏移到完全不相关的内存区域是 UB，
/// (or exactly one position past last element). Offsetting to completely unrelated memory is UB,
/// 即使你不解引用它。
/// even if you don't dereference it.
///
/// # 修复思路 / Fix Strategy
///
/// 只进行在边界内的偏移，或使用 `pointer::wrapping_add`（仅在特定场景下允许）。
/// Only offset within bounds, or use `pointer::wrapping_add` (only in specific scenarios).
pub fn out_of_bounds_offset_bad() -> i32 {
    let arr = [1i32, 2, 3];
    let ptr = arr.as_ptr();

    // UB: 偏移 100 个元素远超数组边界
    // UB: offsetting 100 elements far exceeds array bounds
    let bad_ptr = unsafe { ptr.add(100) };

    // 即使不解引用，越界偏移本身就是 UB
    // Even without dereferencing, out-of-bounds offset itself is UB
    // 这里我们返回一个安全值以避免编译器优化掉整个函数
    // Return safe value to prevent compiler optimizing away entire function
    let _ = bad_ptr;
    0
}

/// 修复版：只在合法范围内偏移
/// Fixed: only offset within valid range
pub fn in_bounds_offset_fixed() -> i32 {
    let arr = [1i32, 2, 3];
    let ptr = arr.as_ptr();

    // 合法：偏移到第 3 个元素（索引 2）
    // Valid: offset to 3rd element (index 2)
    let third = unsafe { ptr.add(2) };

    // SAFETY: third 指向 arr[2]，在边界内
    // SAFETY: third points to arr[2], within bounds
    unsafe { *third }
}

/// 演示 wrapping_add 的合法使用场景
/// Demonstrates legal use of wrapping_add
///
/// `wrapping_add` 不会触发 UB，因为它不保证结果指针有效。
/// `wrapping_add` does not trigger UB because it doesn't guarantee result pointer validity.
/// 但解引用前必须验证指针在范围内。
/// But must verify pointer is within range before dereferencing.
pub fn wrapping_offset_example() -> bool {
    let arr = [1i32, 2, 3];
    let ptr = arr.as_ptr();

    // wrapping_add 本身不是 UB
    // wrapping_add itself is not UB
    let maybe_oob = ptr.wrapping_add(100);

    // 不解引用越界指针，只比较地址
    // Don't dereference OOB pointer, only compare addresses
    maybe_oob > ptr
}

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------------
    // 测试段 1: 悬垂指针修复 / Test section 1: Dangling pointer fix
    // ------------------------------------------------------------------------

    #[test]
    fn test_heap_pointer_value() {
        assert_eq!(get_value_safely(), 42);
    }

    #[test]
    fn test_heap_pointer_no_leak() {
        // 运行此测试时，Miri 会检测内存泄漏
        // Miri will detect memory leaks when running this test
        // 如果 get_value_safely 没有正确释放 Box，Miri 会报告 leak
        // If get_value_safely doesn't properly free Box, Miri will report leak
        for _ in 0..100 {
            let _ = get_value_safely();
        }
    }

    // ------------------------------------------------------------------------
    // 测试段 2: 别名规则修复 / Test section 2: Aliasing rule fix
    // ------------------------------------------------------------------------

    #[test]
    fn test_aliasing_raw_only() {
        assert_eq!(aliasing_fixed_with_raw_only(), 2);
    }

    #[test]
    fn test_aliasing_ref_only() {
        assert_eq!(aliasing_fixed_with_ref_only(), 2);
    }

    // ------------------------------------------------------------------------
    // 测试段 3: 越界偏移修复 / Test section 3: Out-of-bounds offset fix
    // ------------------------------------------------------------------------

    #[test]
    fn test_in_bounds_offset() {
        assert_eq!(in_bounds_offset_fixed(), 3);
    }

    #[test]
    fn test_wrapping_offset() {
        assert!(wrapping_offset_example());
    }

    // ------------------------------------------------------------------------
    // Miri 专用验证测试 / Miri-specific validation tests
    // ------------------------------------------------------------------------

    /// 综合验证：所有修复后的函数在 Miri 下都应该是安全的
    /// Comprehensive validation: all fixed functions should be safe under Miri
    #[test]
    fn test_all_miri_safe() {
        // 段 1 / Section 1
        let _ = get_value_safely();

        // 段 2 / Section 2
        let _ = aliasing_fixed_with_raw_only();
        let _ = aliasing_fixed_with_ref_only();

        // 段 3 / Section 3
        let _ = in_bounds_offset_fixed();
        let _ = wrapping_offset_example();
    }
}
