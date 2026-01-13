//! LeetCode 队列类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的队列类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用 VecDeque 高效队列操作
//! 2. **内存优化**: 队列内存管理优化

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::collections::VecDeque;

// ==================== 数据结构定义 ====================

/// 225. Implement Stack using Queues（用队列实现栈）
pub struct MyStack {
    queue: VecDeque<i32>,
}

impl MyStack {
    pub fn new() -> Self {
        MyStack {
            queue: VecDeque::new(),
        }
    }

    pub fn push(&mut self, x: i32) {
        let n = self.queue.len();
        self.queue.push_back(x);
        for _ in 0..n {
            let val = self.queue.pop_front().unwrap();
            self.queue.push_back(val);
        }
    }

    pub fn pop(&mut self) -> i32 {
        self.queue.pop_front().unwrap()
    }

    pub fn top(&self) -> i32 {
        *self.queue.front().unwrap()
    }

    pub fn empty(&self) -> bool {
        self.queue.is_empty()
    }
}

impl Default for MyStack {
    fn default() -> Self {
        Self::new()
    }
}

/// 232. Implement Queue using Stacks（用栈实现队列）
pub struct MyQueue {
    input: Vec<i32>,
    output: Vec<i32>,
}

impl MyQueue {
    pub fn new() -> Self {
        MyQueue {
            input: Vec::new(),
            output: Vec::new(),
        }
    }

    pub fn push(&mut self, x: i32) {
        self.input.push(x);
    }

    pub fn pop(&mut self) -> i32 {
        self.peek();
        self.output.pop().unwrap()
    }

    pub fn peek(&mut self) -> i32 {
        if self.output.is_empty() {
            while let Some(val) = self.input.pop() {
                self.output.push(val);
            }
        }
        *self.output.last().unwrap()
    }

    pub fn empty(&self) -> bool {
        self.input.is_empty() && self.output.is_empty()
    }
}

impl Default for MyQueue {
    fn default() -> Self {
        Self::new()
    }
}

/// 346. Moving Average from Data Stream（数据流中的移动平均值）
pub struct MovingAverage {
    size: usize,
    queue: VecDeque<i32>,
    sum: i32,
}

impl MovingAverage {
    pub fn new(size: i32) -> Self {
        MovingAverage {
            size: size as usize,
            queue: VecDeque::new(),
            sum: 0,
        }
    }

    pub fn next(&mut self, val: i32) -> f64 {
        if self.queue.len() == self.size {
            self.sum -= self.queue.pop_front().unwrap();
        }
        self.queue.push_back(val);
        self.sum += val;
        self.sum as f64 / self.queue.len() as f64
    }
}

// ==================== 经典题目实现 ====================

/// 239. Sliding Window Maximum（滑动窗口最大值）
///
/// ## 问题描述
/// 给你一个整数数组 nums，有一个大小为 k 的滑动窗口从数组的最左侧移动到数组的最右侧。
/// 你只可以看到在滑动窗口内的 k 个数字。滑动窗口每次只向右移动一位。
/// 返回 滑动窗口中的最大值 。
///
/// ## Rust 1.92 特性应用
/// - **单调队列**: 使用双端队列维护单调递减序列
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(k)
pub fn max_sliding_window_queue(nums: Vec<i32>, k: i32) -> Vec<i32> {
    let k = k as usize;
    let mut deque = VecDeque::new();
    let mut result = Vec::new();

    for i in 0..nums.len() {
        // 移除窗口外的元素
        while !deque.is_empty() && *deque.front().unwrap() < i as i32 - k as i32 + 1 {
            deque.pop_front();
        }

        // 维护单调递减队列
        while !deque.is_empty() && nums[*deque.back().unwrap() as usize] <= nums[i] {
            deque.pop_back();
        }

        deque.push_back(i as i32);

        // 窗口形成后，记录最大值
        if i >= k - 1 {
            result.push(nums[*deque.front().unwrap() as usize]);
        }
    }

    result
}

// ==================== 问题信息注册 ====================

/// 获取所有队列类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 225,
            title: "用队列实现栈".to_string(),
            title_en: "Implement Stack using Queues".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Stack, LeetCodeTag::Design, LeetCodeTag::Queue],
            description: "请你仅使用两个队列实现一个后入先出（LIFO）的栈，并支持普通栈的全部四种操作（push、top、pop 和 empty）。".to_string(),
            examples: vec!["输入：[\"MyStack\", \"push\", \"push\", \"top\", \"pop\", \"empty\"]\n[[], [1], [2], [], [], []]\n输出：[null, null, null, 2, 2, false]".to_string()],
            constraints: vec!["1 <= x <= 9".to_string()],
            rust_191_features: vec!["使用队列，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("push 操作需要 O(n) 时间".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 232,
            title: "用栈实现队列".to_string(),
            title_en: "Implement Queue using Stacks".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Stack, LeetCodeTag::Design, LeetCodeTag::Queue],
            description: "请你仅使用两个栈实现先入先出队列。队列应当支持一般队列支持的所有操作（push、pop、peek、empty）。".to_string(),
            examples: vec!["输入：[\"MyQueue\", \"push\", \"push\", \"peek\", \"pop\", \"empty\"]\n[[], [1], [2], [], [], []]\n输出：[null, null, null, 1, 1, false]".to_string()],
            constraints: vec!["1 <= x <= 9".to_string()],
            rust_191_features: vec!["使用双栈，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(1) 摊还".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("pop 和 peek 操作摊还时间复杂度为 O(1)".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 239,
            title: "滑动窗口最大值".to_string(),
            title_en: "Sliding Window Maximum".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Queue, LeetCodeTag::SlidingWindow, LeetCodeTag::MonotonicStack],
            description: "给你一个整数数组 nums，有一个大小为 k 的滑动窗口从数组的最左侧移动到数组的最右侧。你只可以看到在滑动窗口内的 k 个数字。滑动窗口每次只向右移动一位。返回 滑动窗口中的最大值 。".to_string(),
            examples: vec!["输入：nums = [1,3,-1,-3,5,3,6,7], k = 3\n输出：[3,3,5,5,6,7]".to_string()],
            constraints: vec!["1 <= nums.length <= 10^5".to_string()],
            rust_191_features: vec!["使用单调队列，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(k)".to_string(),
                explanation: Some("每个元素最多入队和出队一次".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 346,
            title: "数据流中的移动平均值".to_string(),
            title_en: "Moving Average from Data Stream".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Design, LeetCodeTag::Queue],
            description: "给定一个整数数据流和一个窗口大小，根据该滑动窗口的大小，计算其所有整数的移动平均值。".to_string(),
            examples: vec!["输入：[\"MovingAverage\", \"next\", \"next\", \"next\", \"next\"]\n[[3], [1], [10], [3], [5]]\n输出：[null, 1.0, 5.5, 4.66667, 6.0]".to_string()],
            constraints: vec!["1 <= size <= 1000".to_string()],
            rust_191_features: vec!["使用队列，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(1)".to_string(),
                space_complexity: "O(size)".to_string(),
                explanation: Some("所有操作都是 O(1) 时间复杂度".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_stack() {
        let mut stack = MyStack::new();
        stack.push(1);
        stack.push(2);
        assert_eq!(stack.top(), 2);
        assert_eq!(stack.pop(), 2);
        assert!(!stack.empty());
    }

    #[test]
    fn test_my_queue() {
        let mut queue = MyQueue::new();
        queue.push(1);
        queue.push(2);
        assert_eq!(queue.peek(), 1);
        assert_eq!(queue.pop(), 1);
        assert!(!queue.empty());
    }

    #[test]
    fn test_moving_average() {
        let mut ma = MovingAverage::new(3);
        assert!((ma.next(1) - 1.0).abs() < 1e-5);
        assert!((ma.next(10) - 5.5).abs() < 1e-5);
        assert!((ma.next(3) - 4.66667).abs() < 1e-2);
    }

    #[test]
    fn test_max_sliding_window_queue() {
        assert_eq!(
            max_sliding_window_queue(vec![1, 3, -1, -3, 5, 3, 6, 7], 3),
            vec![3, 3, 5, 5, 6, 7]
        );
    }
}
