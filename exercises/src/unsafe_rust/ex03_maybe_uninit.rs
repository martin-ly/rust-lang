//! # 练习 3: MaybeUninit 与避免不必要的初始化
//!
//! **难度**: Medium  
//! **考点**: `MaybeUninit<T>`、假设初始化、手动 Drop、内存安全
//!
//! ## 题目描述
//!
//! 当你需要一个固定大小的数组，但元素是通过某种外部逻辑（如迭代器、IO 读取）
//! 逐个生成的时，如果先用默认值填充再覆盖，会造成不必要的初始化开销。
//!
//! 请实现一个函数 `collect_into_array<T, const N: usize>`，
//! 它接受一个恰好产生 `N` 个元素的迭代器，使用 `MaybeUninit` 直接写入数组槽位，
//! 最后返回 `[T; N]`。
//!
//! ## 要求
//!
//! - 使用 `MaybeUninit::uninit()` 创建未初始化的数组槽位
//! - 在确认所有 `N` 个元素都被成功写入后，使用 `assume_init()` 或等效方式转换
//! - 正确处理中途 panic 的内存安全（已初始化元素必须被正确 drop）
//! - 如果迭代器元素不足或过多，panic
//!
//! ## 提示
//!
//! - `MaybeUninit<T>` 不会自动调用 `T` 的 `Drop`
//! - 如果迭代器在写入第 `k` 个元素后 panic，前 `k` 个已初始化的元素需要被正确 drop
//! - `std::array::from_fn` 可以安全地创建初始化的数组
//! - `[MaybeUninit<T>; N]` 与 `[T; N]` 具有相同的内存布局

use std::mem::{self, MaybeUninit};

/// 将恰好产生 N 个元素的迭代器收集为定长数组
///
/// # 实现要点
///
/// 1. 使用 `array::from_fn` 创建 `[MaybeUninit<T>; N]`（无需 unsafe）
/// 2. 使用结构体守卫（Guard）确保 panic 时正确 drop 已初始化元素
/// 3. 使用 `transmute_copy` 完成最终转换（利用 layout 相同保证）
///
/// # Panics
///
/// 当迭代器元素不足或超过 N 时 panic
pub fn collect_into_array<T, const N: usize>(mut iter: impl Iterator<Item = T>) -> [T; N] {
    // 步骤 1: 创建未初始化的 MaybeUninit 数组
    let array: [MaybeUninit<T>; N] = std::array::from_fn(|_| MaybeUninit::uninit());

    // 步骤 2: 定义 drop 守卫，处理 panic 时的清理
    struct Guard<T, const N: usize> {
        array: [MaybeUninit<T>; N],
        initialized: usize,
    }

    impl<T, const N: usize> Drop for Guard<T, N> {
        fn drop(&mut self) {
            // SAFETY: 0..initialized 范围内的元素都已通过 write() 初始化
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
    for i in 0..N {
        match iter.next() {
            Some(value) => {
                guard.array[i].write(value);
                guard.initialized += 1;
            }
            None => {
                panic!(
                    "迭代器元素不足，需要 {} 个，只得到 {} 个",
                    N, guard.initialized
                );
            }
        }
    }

    // 步骤 4: 确认迭代器已耗尽
    if iter.next().is_some() {
        panic!("迭代器元素过多，只需要 {} 个", N);
    }

    // 步骤 5: 从 guard 中取出数组并取消 guard 的 drop
    let initialized = guard.initialized;
    assert_eq!(initialized, N);

    // 将 guard.array 移出（通过 ptr::read）并遗忘 guard
    // SAFETY: 我们即将通过 transmute_copy 转移所有权，guard 的 drop 不应执行
    let array = unsafe { std::ptr::read(&guard.array) };
    mem::forget(guard);

    // 步骤 6: 将 [MaybeUninit<T>; N] 转换为 [T; N]
    // SAFETY: [MaybeUninit<T>; N] 与 [T; N] 保证具有相同内存布局
    // 且所有 N 个元素都已被初始化
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
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    #[test]
    fn test_no_unnecessary_initialization() {
        // 这个测试验证我们不会先初始化再覆盖
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
        assert_eq!(INIT_COUNT.load(Ordering::SeqCst), 3);
    }
}
