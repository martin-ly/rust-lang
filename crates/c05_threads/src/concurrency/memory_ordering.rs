//! 内存排序（Memory Ordering）最小示例。
//!
//! 演示基于 `Relaxed` 与 `SeqCst` 的基本可编译示例，后续可扩展
//! Acquire/Release 与 AcqRel 的更复杂用例。

#![allow(dead_code)]

use std::sync::atomic::{AtomicUsize, Ordering};

/// 返回在不同内存序下的自增结果（用于展示 API，可编译通过）。
pub fn relaxed_increment(counter: &AtomicUsize) -> usize {
    counter.fetch_add(1, Ordering::Relaxed)
}

/// 使用 SeqCst 的自增（最强序保证）。
pub fn seqcst_increment(counter: &AtomicUsize) -> usize {
    counter.fetch_add(1, Ordering::SeqCst)
}


