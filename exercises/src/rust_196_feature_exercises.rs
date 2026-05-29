#![forbid(unsafe_code)]

//! # Rust 1.96.0+ 特性练习
//!
//! 本模块提供 Rust 1.96.0 前瞻特性的 hands-on 练习。
//! 每道练习题包含：题目描述、起始代码（stub）、参考实现、测试用例。

use std::collections::VecDeque;
use std::ptr::NonNull;

// ============================================================
// GenBlockExercises
// ============================================================

/// # `gen` blocks 练习
///
/// `gen` 块允许使用 `yield` 关键字直接创建迭代器，
/// 无需手动实现 `Iterator` trait。
///
/// **注意**: 需要 nightly 编译器并启用 `#![feature(gen_blocks, yield_expr)]`。
pub struct GenBlockExercises;

impl GenBlockExercises {
    /// ## 练习 01: 使用 gen 块生成平方数序列
    ///
    /// 给定上限 `n`，生成 1 到 n 的平方数序列。
    ///
    /// ### 题目
    /// 使用 `gen` 块实现一个函数，返回 `1, 4, 9, ...` 直到 `n²`。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn squares_gen(n: usize) -> impl Iterator<Item = usize> {
    ///     // TODO: 使用 gen 块
    /// }
    /// ```
    pub fn exercise_01_squares_gen(n: usize) -> impl Iterator<Item = usize> {
        gen move {
            for i in 1..=n {
                yield i * i;
            }
        }
    }

    /// ## 练习 02: 使用 gen 块过滤偶数
    ///
    /// 给定一个迭代器，只产生其中的偶数。
    ///
    /// ### 题目
    /// 使用 `gen` 块实现过滤逻辑，无需分配新 Vec。
    ///
    /// ### 起始代码
    /// ```rust,ignore
    /// pub fn evens_gen<I>(iter: I) -> impl Iterator<Item = I::Item>
    /// where
    ///     I: IntoIterator<Item = usize>,
    /// {
    ///     // TODO: 使用 gen 块
    /// }
    /// ```
    pub fn exercise_02_evens_gen<I>(iter: I) -> impl Iterator<Item = usize>
    where
        I: IntoIterator<Item = usize>,
    {
        gen move {
            for x in iter {
                if x % 2 == 0 {
                    yield x;
                }
            }
        }
    }

    /// ## 练习 03: 使用 gen 块实现累积和
    ///
    /// 对输入迭代器产生累积和序列。
    ///
    /// ### 题目
    /// 输入 `[1, 2, 3, 4]`，输出 `[1, 3, 6, 10]`。
    pub fn exercise_03_cumulative_sum<I>(iter: I) -> impl Iterator<Item = i64>
    where
        I: IntoIterator<Item = i64>,
    {
        gen move {
            let mut sum = 0i64;
            for x in iter {
                sum += x;
                yield sum;
            }
        }
    }
}

// ============================================================
// ConstVecDequeExercises
// ============================================================

/// # `const VecDeque` 练习
///
/// `VecDeque::new` 在 Rust 1.68+ 即可在 const 上下文中使用，
/// 允许编译期初始化双端队列。
pub struct ConstVecDequeExercises;

impl ConstVecDequeExercises {
    /// ## 练习 01: 编译期初始化空队列
    ///
    /// 创建一个在编译期初始化的 `VecDeque<i32>`。
    ///
    /// ### 题目
    /// 定义一个 `const` 常量，其值为空的 `VecDeque<i32>`。
    pub const EXERCISE_01_EMPTY: VecDeque<i32> = VecDeque::new();
}

/// ## 练习 02: 编译期初始化并验证
///
/// 创建一个泛型结构体，内部包含 const 初始化的 `VecDeque<T>`。
pub struct ConstVecDequeRingBuffer<T, const N: usize> {
    buffer: VecDeque<T>,
}

impl<T, const N: usize> Default for ConstVecDequeRingBuffer<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> ConstVecDequeRingBuffer<T, N> {
    /// 编译期初始化
    pub const fn new() -> Self {
        Self {
            buffer: VecDeque::new(),
        }
    }

    /// 获取内部队列的可变引用
    pub fn inner_mut(&mut self) -> &mut VecDeque<T> {
        &mut self.buffer
    }

    /// 获取内部队列的引用
    pub fn inner(&self) -> &VecDeque<T> {
        &self.buffer
    }
}

// ============================================================
// BoolToFloatExercises
// ============================================================

/// # `bool` 到浮点数转换练习
///
/// `From<bool> for f32` 和 `From<bool> for f64` 在 Rust 1.68+ 已稳定，
/// 允许将 `true` 转为 `1.0`，`false` 转为 `0.0`。
pub struct BoolToFloatExercises;

impl BoolToFloatExercises {
    /// ## 练习 01: 布尔标志转 f32
    ///
    /// 将布尔传感器标志转换为归一化 f32 值。
    pub fn exercise_01_bool_to_f32(flag: bool) -> f32 {
        f32::from(flag)
    }

    /// ## 练习 02: 布尔数组占空比（f64）
    ///
    /// 计算布尔数组的平均值，返回 f64。
    pub fn exercise_02_bool_duty_cycle(flags: &[bool]) -> f64 {
        if flags.is_empty() {
            return 0.0;
        }
        let sum: f64 = flags.iter().copied().map(f64::from).sum();
        sum / flags.len() as f64
    }
}

// ============================================================
// ConstNonNullExercises
// ============================================================

/// # `const NonNull` 练习
///
/// Rust 1.96+ 扩展了 `NonNull::new` 的 const 上下文支持，
/// 允许在编译期安全构造非空裸指针。
pub struct ConstNonNullExercises;

impl ConstNonNullExercises {
    /// ## 练习 01: 编译期初始化空 NonNull
    ///
    /// 定义一个 const 常量，表示未初始化的 `NonNull<u8>`。
    pub const EXERCISE_01_UNINITIALIZED: Option<NonNull<u8>> = NonNull::new(std::ptr::null_mut());

    /// ## 练习 02: 从栈引用创建 NonNull
    ///
    /// 在运行时从可变引用创建 `NonNull<i32>`。
    pub fn exercise_02_from_mut_ref() -> NonNull<i32> {
        let mut value = 42i32;
        NonNull::new(&mut value).expect("引用非空")
    }
}

// ============================================================
// 测试
// ============================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --------------------------------------------------------
    // GenBlockExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_squares_gen() {
        let result: Vec<usize> = GenBlockExercises::exercise_01_squares_gen(4).collect();
        assert_eq!(result, vec![1, 4, 9, 16]);
    }

    #[test]
    fn test_exercise_02_evens_gen() {
        let data = vec![1, 2, 3, 4, 5, 6];
        let result: Vec<usize> = GenBlockExercises::exercise_02_evens_gen(data).collect();
        assert_eq!(result, vec![2, 4, 6]);
    }

    #[test]
    fn test_exercise_03_cumulative_sum() {
        let data = vec![1i64, 2, 3, 4];
        let result: Vec<i64> = GenBlockExercises::exercise_03_cumulative_sum(data).collect();
        assert_eq!(result, vec![1, 3, 6, 10]);
    }

    // --------------------------------------------------------
    // ConstVecDequeExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_const_empty() {
        let deque = ConstVecDequeExercises::EXERCISE_01_EMPTY;
        assert!(deque.is_empty());
    }

    #[test]
    fn test_exercise_02_ring_buffer() {
        let mut buf = ConstVecDequeRingBuffer::<i32, 4>::new();
        assert!(buf.inner().is_empty());
        buf.inner_mut().push_back(1);
        buf.inner_mut().push_back(2);
        assert_eq!(buf.inner().len(), 2);
        assert_eq!(buf.inner().front(), Some(&1));
    }

    // --------------------------------------------------------
    // BoolToFloatExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_bool_to_f32() {
        assert_eq!(BoolToFloatExercises::exercise_01_bool_to_f32(true), 1.0f32);
        assert_eq!(BoolToFloatExercises::exercise_01_bool_to_f32(false), 0.0f32);
    }

    #[test]
    fn test_exercise_02_bool_duty_cycle() {
        let flags = [true, false, true, true, false];
        let duty = BoolToFloatExercises::exercise_02_bool_duty_cycle(&flags);
        assert!((duty - 0.6).abs() < f64::EPSILON);
    }

    #[test]
    fn test_exercise_02_bool_duty_cycle_empty() {
        let flags: &[bool] = &[];
        assert_eq!(
            BoolToFloatExercises::exercise_02_bool_duty_cycle(flags),
            0.0
        );
    }

    // --------------------------------------------------------
    // ConstNonNullExercises tests
    // --------------------------------------------------------
    #[test]
    fn test_exercise_01_uninitialized() {
        assert!(ConstNonNullExercises::EXERCISE_01_UNINITIALIZED.is_none());
    }

    #[test]
    fn test_exercise_02_from_mut_ref() {
        let ptr = ConstNonNullExercises::exercise_02_from_mut_ref();
        // NonNull 保证非空，通过地址验证
        assert_ne!(ptr.as_ptr() as usize, 0);
    }
}
