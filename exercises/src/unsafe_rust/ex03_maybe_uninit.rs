//! # 练习 3: MaybeUninit 与避免不必要的初始化 / Exercise 3: MaybeUninit
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: `MaybeUninit<T>`、假设初始化、手动 Drop、内存安全
//!   Assumed init, manual Drop, memory safety
//!
//! ## 题目描述 / Problem Description
//!
//! 当你需要一个固定大小的数组，但元素是通过某种外部逻辑（如迭代器、IO 读取）
//! 逐个生成的时，如果先用默认值填充再覆盖，会造成不必要的初始化开销。
//! When you need a fixed-size array but elements are produced one by one via external logic
//! (e.g., iterator, IO reads), filling with defaults first then overwriting causes unnecessary init overhead.
//!
//! 请实现一个函数 `collect_into_array<T, const N: usize>`，
//! 它接受一个恰好产生 `N` 个元素的迭代器，使用 `MaybeUninit` 直接写入数组槽位，
//! 最后返回 `[T; N]`。
//! Please implement `collect_into_array<T, const N: usize>` that accepts an iterator producing exactly `N` elements,
//! uses `MaybeUninit` to directly write array slots, and finally returns `[T; N]`.
//!
//! ## 要求 / Requirements
//!
//! - 使用 `MaybeUninit::uninit()` 创建未初始化的数组槽位
//!   Use `MaybeUninit::uninit()` to create uninitialized array slots
//! - 在确认所有 `N` 个元素都被成功写入后，使用 `assume_init()` 或等效方式转换
//!   After confirming all `N` elements are written, use `assume_init()` or equivalent
//! - 正确处理中途 panic 的内存安全（已初始化元素必须被正确 drop）
//!   Correctly handle mid-panic memory safety (initialized elements must be properly dropped)
//! - 如果迭代器元素不足或过多，panic
//!   Panic if iterator has too few or too many elements
//!
//! ## 提示 / Hints
//!
//! - `MaybeUninit<T>` 不会自动调用 `T` 的 `Drop`
//!   `MaybeUninit<T>` does not automatically call `T`'s `Drop`
//! - 如果迭代器在写入第 `k` 个元素后 panic，前 `k` 个已初始化的元素需要被正确 drop
//!   If iterator panics after writing the k-th element, first k initialized elements need proper dropping
//! - `std::array::from_fn` 可以安全地创建初始化的数组
//!   `std::array::from_fn` can safely create initialized arrays
//! - `[MaybeUninit<T>; N]` 与 `[T; N]` 具有相同的内存布局
//!   `[MaybeUninit<T>; N]` and `[T; N]` have identical memory layout

use std::mem::{self, MaybeUninit};

/// 将恰好产生 N 个元素的迭代器收集为定长数组
/// Collects an iterator producing exactly N elements into a fixed-size array
///
/// # 实现要点 / Implementation Notes
///
/// 1. 使用 `array::from_fn` 创建 `[MaybeUninit<T>; N]`（无需 unsafe）
///    Use `array::from_fn` to create `[MaybeUninit<T>; N]` (no unsafe needed)
/// 2. 使用结构体守卫（Guard）确保 panic 时正确 drop 已初始化元素
///    Use struct Guard to ensure proper dropping on panic
/// 3. 使用 `transmute_copy` 完成最终转换（利用 layout 相同保证）
///    Use `transmute_copy` for final conversion (leveraging same layout guarantee)
///
/// # Panics
///
/// 当迭代器元素不足或超过 N 时 panic / Panics when iterator has too few or too many elements
pub fn collect_into_array<T, const N: usize>(mut iter: impl Iterator<Item = T>) -> [T; N] {
    // 步骤 1: 创建未初始化的 MaybeUninit 数组
    // Step 1: Create uninitialized MaybeUninit array
    let array: [MaybeUninit<T>; N] = std::array::from_fn(|_| MaybeUninit::uninit());

    // 步骤 2: 定义 drop 守卫，处理 panic 时的清理
    // Step 2: Define drop guard for panic cleanup
    struct Guard<T, const N: usize> {
        array: [MaybeUninit<T>; N],
        initialized: usize,
    }

    impl<T, const N: usize> Drop for Guard<T, N> {
        fn drop(&mut self) {
            // SAFETY: 0..initialized 范围内的元素都已通过 write() 初始化
            // SAFETY: Elements in 0..initialized have been initialized via write()
            unsafe {
                for i in 0..self.initialized {
                    self.array[i].assume_init_drop();
                }
            }
        }
    }

    let mut guard = Guard {
        array,
        initialized: 0,
    };

    // 步骤 3: 从迭代器填充数组
    // Step 3: Fill array from iterator
    for i in 0..N {
        match iter.next() {
            Some(value) => {
                guard.array[i].write(value);
                guard.initialized += 1;
            }
            None => {
                panic!(
                    "迭代器元素不足，需要 {} 个，只得到 {} 个 / Iterator too short, need {}, got \
                     {}",
                    N, guard.initialized, N, guard.initialized
                );
            }
        }
    }

    // 步骤 4: 确认迭代器已耗尽
    // Step 4: Confirm iterator is exhausted
    if iter.next().is_some() {
        panic!(
            "迭代器元素过多，只需要 {} 个 / Iterator too long, only need {}",
            N, N
        );
    }

    // 步骤 5: 从 guard 中取出数组并取消 guard 的 drop
    // Step 5: Extract array from guard and prevent guard's drop
    let initialized = guard.initialized;
    assert_eq!(initialized, N);

    // SAFETY: 我们即将通过 transmute_copy 转移所有权，guard 的 drop 不应执行
    // SAFETY: We're about to transfer ownership via transmute_copy, guard's drop should not run
    let array = unsafe { std::ptr::read(&guard.array) };
    mem::forget(guard);

    // 步骤 6: 将 [MaybeUninit<T>; N] 转换为 [T; N]
    // Step 6: Convert [MaybeUninit<T>; N] to [T; N]
    // SAFETY: [MaybeUninit<T>; N] 与 [T; N] 保证具有相同内存布局
    // SAFETY: [MaybeUninit<T>; N] and [T; N] guaranteed to have identical layout
    // 且所有 N 个元素都已被初始化
    // and all N elements have been initialized
    unsafe { mem::transmute_copy(&array) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn test_collect_exact_integers() {
        let arr = collect_into_array::<i32, 5>(vec![1, 2, 3, 4, 5].into_iter());
        assert_eq!(arr, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_collect_strings() {
        let arr =
            collect_into_array::<String, 3>(vec!["a".into(), "b".into(), "c".into()].into_iter());
        assert_eq!(arr, ["a", "b", "c"]);
    }

    #[test]
    fn test_collect_empty() {
        let arr = collect_into_array::<i32, 0>(std::iter::empty());
        assert_eq!(arr, []);
    }

    #[test]
    #[should_panic(expected = "迭代器元素不足")]
    fn test_collect_too_few() {
        let _ = collect_into_array::<i32, 3>(vec![1, 2].into_iter());
    }

    #[test]
    #[should_panic(expected = "迭代器元素过多")]
    fn test_collect_too_many() {
        let _ = collect_into_array::<i32, 2>(vec![1, 2, 3].into_iter());
    }

    #[test]
    fn test_drop_safety_on_panic() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        #[allow(dead_code)]
        struct DropCounter(i32);
        impl Drop for DropCounter {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        DROP_COUNT.store(0, Ordering::SeqCst);

        let result = std::panic::catch_unwind(|| {
            let iter = vec![DropCounter(1), DropCounter(2), DropCounter(3)].into_iter();
            let _ = collect_into_array::<DropCounter, 5>(iter);
        });

        assert!(result.is_err());
        // 3 个已初始化的元素在 panic 时被 guard 正确 drop
        // 3 initialized elements properly dropped by guard on panic
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn test_no_unnecessary_initialization() {
        // 这个测试验证我们不会先初始化再覆盖
        // This test verifies we don't init then overwrite
        static INIT_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct CountOnNew;
        impl CountOnNew {
            fn new() -> Self {
                INIT_COUNT.fetch_add(1, Ordering::SeqCst);
                CountOnNew
            }
        }

        INIT_COUNT.store(0, Ordering::SeqCst);

        let _arr =
            collect_into_array::<CountOnNew, 3>(std::iter::repeat_with(CountOnNew::new).take(3));

        // 只有 3 次（来自迭代器），不是 6 次（3 次默认 + 3 次覆盖）
        // Only 3 times (from iterator), not 6 times (3 defaults + 3 overwrites)
        assert_eq!(INIT_COUNT.load(Ordering::SeqCst), 3);
    }
}
