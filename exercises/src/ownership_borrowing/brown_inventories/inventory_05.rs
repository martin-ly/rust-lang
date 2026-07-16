//! # Brown University CRP Ownership Inventory — Program 05
//!
//! **EN**: RAII and Drop Semantics
//! **Summary**: Observe how Rust releases resources automatically via RAII and how custom
//! `Drop` lets you observe or manage resource cleanup.
//! **Key Terms**: RAII, Drop trait, 析构函数 (destructor), 资源释放 (resource cleanup),
//! drop 顺序 (drop order), LIFO, 原子计数器 (atomic counter).
//! **Related Concepts**:
//! [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md),
//! [`concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md`](../../../../../concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md).
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: RAII 与 Drop 语义 / RAII and Drop Semantics
//!
//! ## 学习目标 / Learning Goal
//!
//! 理解 Rust 如何通过 RAII 自动释放资源，以及如何实现自定义 `Drop` 来观察或管理资源清理。
//! Understand how Rust automatically releases resources via RAII and how to implement
//! custom `Drop` to observe or manage resource cleanup.
//!
//! ## TODO / Tasks
//!
//! 1. 观察 `DropTracer` 被创建和销毁的时机。
//!    Observe when `DropTracer` instances are created and destroyed.
//! 2. 实现 `create_pair` 函数，返回两个 `DropTracer`，并预测它们的 drop 顺序。
//!    Implement `create_pair` to return two `DropTracer` instances and predict their drop order.
//! 3. 思考：如果 Rust 没有 RAII，我们需要手动管理哪些资源？
//!    Consider which resources would have to be managed manually if Rust had no RAII.

use std::sync::atomic::{AtomicUsize, Ordering};

static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

/// 一个用于追踪 Drop 调用的小工具。
/// A small utility to track Drop calls.
pub struct DropTracer {
    pub name: String,
}

impl Drop for DropTracer {
    fn drop(&mut self) {
        DROP_COUNT.fetch_add(1, Ordering::SeqCst);
        println!("Dropping: {}", self.name);
    }
}

/// 创建两个 DropTracer，返回它们。
/// Creates two DropTracer instances and returns them.
pub fn create_pair() -> (DropTracer, DropTracer) {
    // TODO: 创建两个 DropTracer，分别命名为 "first" 和 "second"。
    // TODO: Create two DropTracer instances named "first" and "second".
    // 观察测试结束时它们的 drop 顺序（与创建顺序相反）。
    // Observe their drop order at the end of the test (reverse of creation order).
    let first = DropTracer {
        name: String::from("first"),
    };
    let second = DropTracer {
        name: String::from("second"),
    };
    (first, second)
}

/// 获取当前已发生的 Drop 次数。
/// Returns the current number of observed Drop calls.
pub fn drop_count() -> usize {
    DROP_COUNT.load(Ordering::SeqCst)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_drop_order() {
        let initial = drop_count();
        {
            let (a, b) = create_pair();
            // 在作用域内，a 和 b 都存活
            assert_eq!(a.name, "first");
            assert_eq!(b.name, "second");
            // 离开作用域后，b 先 drop，然后 a drop（LIFO）
        }
        // TODO: 预测 drop_count 增加了多少。
        // TODO: Predict how much `drop_count` increases.
        assert_eq!(drop_count(), initial + 2);
    }
}
