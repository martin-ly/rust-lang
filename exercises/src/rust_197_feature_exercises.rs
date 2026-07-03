//! Rust 1.97 Nightly 前瞻/候选特性练习
//! **编译要求**: Rust 1.96.1+ stable（使用等效实现）
//! **说明**: 本文件使用等效实现模拟 1.97 特性（当前为 nightly 候选），待 1.97 稳定后将替换为实际 API 调用。

use std::collections::VecDeque;

// ============================================================================
// 1. VecDeque::truncate_front 练习
// ============================================================================

/// # `VecDeque::truncate_front` 练习
///
/// `truncate_front(n)` 截断前部，保留后部 `n` 个元素。
/// 与 `truncate(n)`（保留前部 `n` 个）对称。
pub struct VecDequeTruncateFrontExercises;

impl VecDequeTruncateFrontExercises {
    /// ## 练习 01: 实现 truncate_front 等效操作
    ///
    /// 给定一个 VecDeque 和整数 `n`，截断前部使长度变为 `n`，
    /// 保留后部的 `n` 个元素。
    pub fn exercise_01_truncate_front(deque: &mut VecDeque<i32>, n: usize) {
        // 当前等效实现（1.97 稳定后/候选 API 可用后将直接使用 deque.truncate_front(n)）
        while deque.len() > n {
            deque.pop_front();
        }
    }

    /// ## 练习 02: 使用 truncate_front 处理滑动窗口
    ///
    /// 维护一个固定大小的窗口，当新元素加入导致超过 `window_size` 时，
    /// 从头部移除多余元素。
    pub fn exercise_02_sliding_window(
        window: &mut VecDeque<i32>,
        new_value: i32,
        window_size: usize,
    ) {
        window.push_back(new_value);
        // 1.97+ nightly/候选: window.truncate_front(window_size);
        while window.len() > window_size {
            window.pop_front();
        }
    }
}

// ============================================================================
// 2. VecDeque::retain_back 练习
// ============================================================================

/// # `VecDeque::retain_back` 练习
///
/// `retain_back(f)` 从尾部开始保留满足条件的元素。
/// ⚠️ 状态更新 (2026-06-08): nightly 1.98.0 中尚未出现，可能推迟至 1.98+。
pub struct VecDequeRetainBackExercises;

impl VecDequeRetainBackExercises {
    /// ## 练习 01: 实现 retain_back 等效操作
    ///
    /// 从尾部遍历，移除不满足条件的元素。
    pub fn exercise_01_retain_back(deque: &mut VecDeque<i32>, predicate: impl Fn(&i32) -> bool) {
        let len = deque.len();
        for i in (0..len).rev() {
            if !predicate(&deque[i]) {
                deque.remove(i);
            }
        }
    }

    /// ## 练习 02: 从尾部保留偶数
    pub fn exercise_02_retain_even_from_back(deque: &mut VecDeque<i32>) {
        Self::exercise_01_retain_back(deque, |x| x % 2 == 0);
    }
}

// ============================================================================
// 3. box_vec_non_null 概念练习
// ============================================================================

/// # `box_vec_non_null` 概念练习
///
/// 理解 `Box`/`Vec` 与 `NonNull` 之间的转换语义。
pub struct BoxVecNonNullExercises;

impl BoxVecNonNullExercises {
    /// ## 练习 01: 将 Box 转换为 NonNull（等效实现）
    pub fn exercise_01_box_to_non_null(value: i32) -> std::ptr::NonNull<i32> {
        let ptr = Box::into_raw(Box::new(value));
        std::ptr::NonNull::new(ptr).expect("Box::into_raw never returns null")
    }

    /// ## 练习 02: 将 Vec 转换为 NonNull + 长度 + 容量（等效实现）
    pub fn exercise_02_vec_to_non_null(
        vec: Vec<i32>,
    ) -> (std::ptr::NonNull<i32>, usize, usize) {
        let mut vec = vec;
        let ptr = vec.as_mut_ptr();
        let len = vec.len();
        let cap = vec.capacity();
        std::mem::forget(vec);
        let non_null = std::ptr::NonNull::new(ptr).expect("Vec ptr is non-null");
        (non_null, len, cap)
    }
}

// ============================================================================
// 4. int_format_into 概念练习
// ============================================================================

/// # `int_format_into` 概念练习
///
/// 理解整数零分配格式化的设计目标。
pub struct IntFormatIntoExercises;

impl IntFormatIntoExercises {
    /// ## 练习 01: 将 i32 格式化为字节缓冲区（等效实现）
    ///
    /// 返回写入的字节数。
    pub fn exercise_01_format_into_buf(n: i32, buf: &mut [u8]) -> usize {
        let s = n.to_string();
        let bytes = s.as_bytes();
        let len = bytes.len().min(buf.len());
        buf[..len].copy_from_slice(&bytes[..len]);
        len
    }

    /// ## 练习 02: 计算格式化后的长度
    pub fn exercise_02_formatted_len(n: i32) -> usize {
        n.to_string().len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_truncate_front_basic() {
        let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);
        VecDequeTruncateFrontExercises::exercise_01_truncate_front(&mut deque, 2);
        assert_eq!(deque.make_contiguous(), &[4, 5]);
    }

    #[test]
    fn test_sliding_window() {
        let mut window = VecDeque::from([1, 2, 3]);
        VecDequeTruncateFrontExercises::exercise_02_sliding_window(&mut window, 4, 3);
        assert_eq!(window.make_contiguous(), &[2, 3, 4]);
    }

    #[test]
    fn test_retain_back_even() {
        let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);
        VecDequeRetainBackExercises::exercise_02_retain_even_from_back(&mut deque);
        assert_eq!(deque.make_contiguous(), &[2, 4]);
    }

    #[test]
    fn test_box_to_non_null() {
        let nn = BoxVecNonNullExercises::exercise_01_box_to_non_null(42);
        unsafe {
            assert_eq!(*nn.as_ptr(), 42);
            let _ = Box::from_raw(nn.as_ptr()); // 清理内存
        }
    }

    #[test]
    fn test_vec_to_non_null() {
        let vec = vec![1, 2, 3];
        let (nn, len, cap) = BoxVecNonNullExercises::exercise_02_vec_to_non_null(vec);
        assert_eq!(len, 3);
        assert_eq!(cap, 3);
        unsafe {
            let reconstructed = Vec::from_raw_parts(nn.as_ptr(), len, cap);
            assert_eq!(reconstructed, vec![1, 2, 3]);
        }
    }

    #[test]
    fn test_format_into_buf() {
        let mut buf = [0u8; 20];
        let written = IntFormatIntoExercises::exercise_01_format_into_buf(12345, &mut buf);
        assert_eq!(written, 5);
        assert_eq!(&buf[..5], b"12345");
    }
}
