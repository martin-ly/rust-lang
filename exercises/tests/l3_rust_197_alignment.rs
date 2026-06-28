//! L3 Rust 1.97.0 稳定特性对齐测验
//!
//! 覆盖 Rust 1.97.0（预计 2026-07-09 stable）引入的关键语言/库特性：
//! - `NonZero<T>::highest_one` / `lowest_one` / `bit_width`
//! - `char::is_control()` const 稳定化
//! - `VecDeque::truncate_front`（1.97 候选；若未稳定则使用等效实现）
//! - `VecDeque::retain_back`（1.97 候选；当前 nightly 尚未提供，使用等效实现）
//!
//! 发布日更新说明：
//! - 若 `truncate_front` / `retain_back` 已进入 1.97.0 stable，将下方 helper
//!   函数替换为直接调用真实 API。
//! - 若推迟至 1.98，保留等效实现并将注释中的版本号更新为 1.98。
//!
//! 运行: cargo test --test l3_rust_197_alignment

use std::collections::VecDeque;
use std::num::NonZeroU32;

// ============================================================================
// 等效实现（用于在 API 尚未稳定或推迟时保持测试可运行）
// ============================================================================

/// `VecDeque::truncate_front` 的等效实现
fn truncate_front<T>(deque: &mut VecDeque<T>, n: usize) {
    while deque.len() > n {
        deque.pop_front();
    }
}

/// `VecDeque::retain_back` 的等效实现
fn retain_back<T>(deque: &mut VecDeque<T>, mut f: impl FnMut(&T) -> bool) {
    let len = deque.len();
    for i in (0..len).rev() {
        if !f(&deque[i]) {
            deque.remove(i);
        }
    }
}

// ============================================================================
// 测验
// ============================================================================

/// 测验1: `NonZero<T>::highest_one()` — 最高 set bit 索引
#[test]
fn test_nonzero_highest_one() {
    let n = NonZeroU32::new(0b10100).unwrap();
    assert_eq!(n.highest_one(), 4);
}

/// 测验2: `NonZero<T>::lowest_one()` — 最低 set bit 索引
#[test]
fn test_nonzero_lowest_one() {
    let n = NonZeroU32::new(0b10100).unwrap();
    assert_eq!(n.lowest_one(), 2);
}

/// 测验3: `NonZero<T>::bit_width()` — 表示 self 所需的最少位数
#[test]
fn test_nonzero_bit_width() {
    let n = NonZeroU32::new(0b10100).unwrap();
    assert_eq!(n.bit_width(), NonZeroU32::new(5).unwrap());
}

/// 测验4: `char::is_control()` const 稳定化
/// Rust 1.97.0 起可在 const 上下文中调用。
#[test]
fn test_char_is_control_const() {
    const SPACE_CTRL: bool = ' '.is_control();
    const NUL_CTRL: bool = '\0'.is_control();

    assert!(!SPACE_CTRL);
    assert!(NUL_CTRL);
}

/// 测验5: `VecDeque::truncate_front(n)` — 截断前部，保留后部 n 个元素
/// 与 `truncate(n)`（保留前部）形成对称操作。
#[test]
fn test_vecdeque_truncate_front() {
    let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);

    truncate_front(&mut deque, 2);

    assert_eq!(deque.make_contiguous(), &[4, 5]);
}

/// 测验6: `VecDeque::truncate_front` 边界条件
#[test]
fn test_vecdeque_truncate_front_edge_cases() {
    // n >= len：不截断任何元素
    let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3]);
    truncate_front(&mut deque, 5);
    assert_eq!(deque.make_contiguous(), &[1, 2, 3]);

    // n == 0：清空
    let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3]);
    truncate_front(&mut deque, 0);
    assert!(deque.is_empty());

    // 空 deque
    let mut deque: VecDeque<i32> = VecDeque::new();
    truncate_front(&mut deque, 0);
    assert!(deque.is_empty());
}

/// 测验7: `VecDeque::retain_back(f)` — 从尾部开始保留满足条件的元素
/// 与 `retain`（从头部开始）互补。
#[test]
fn test_vecdeque_retain_back() {
    let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);

    retain_back(&mut deque, |x| x % 2 == 0);

    assert_eq!(deque.make_contiguous(), &[2, 4]);
}

/// 测验8: `VecDeque::retain_back` 早期终止语义
/// 从尾部遍历，保留的元素在结果中仍按原顺序排列。
#[test]
fn test_vecdeque_retain_back_order() {
    let mut deque: VecDeque<i32> = VecDeque::from([10, 20, 30, 40, 50]);

    // 从尾部保留大于 25 的元素
    retain_back(&mut deque, |x| *x > 25);

    assert_eq!(deque.make_contiguous(), &[30, 40, 50]);
}
