// [来源: Rust Standard Library / The Rust Programming Language]
//! Concurrency primitives: threads, mutexes, channels, and atomic operations.
//! # Rust Concurrency and Threading Module
//!
//! This crate demonstrates safe concurrent programming patterns in Rust,
//! from basic thread spawning to advanced lock-free data structures.
//!
//! ## Module Overview
//!
//! - `threads`: Thread spawning and joining basics
//! - `concurrency`: Shared-state concurrency (Mutex, RwLock, Arc)
//! - `message_passing`: Channel-based communication (mpsc, oneshot)
//! - `synchronization`: Barriers, conditions, and memory ordering
//! - `lock_free_data_structures`: Lock-free queues and stacks
//! - `thread_pool_patterns`: Worker pool and task scheduling
//! - `performance_benchmarks`: Concurrent performance measurement
//! - `rust_196_features`: Rust 1.96 stable concurrency features
//!
//! ## Key Concepts Covered
//!
//! | Concept | Module | Rust Feature |
//! |:---|:---|:---|
//! | Shared Memory | `concurrency` | `Mutex`, `Arc`, `RwLock` |
//! | Message Passing | `message_passing` | `mpsc`, `crossbeam-channel` |
//! | Lock-Free | `lock_free_data_structures` | `Atomic*`, `compare_exchange` |
//! | Memory Ordering | `synchronization` | `Ordering::SeqCst`, `Relaxed` |
#![allow(clippy::items_after_test_module)]
#![allow(clippy::absurd_extreme_comparisons)]
#![allow(clippy::unnecessary_get_then_check)]
#![allow(clippy::assertions_on_constants)]
#![allow(clippy::missing_const_for_thread_local)]

#[cfg(test)]
mod tests {
    use super::concurrency::memory_ordering::{relaxed_increment, seqcst_increment};
    use std::sync::atomic::AtomicUsize;

    #[test]
    fn smoke_memory_ordering_increments() {
        let counter = AtomicUsize::new(0);
        let _ = relaxed_increment(&counter);
        let _ = seqcst_increment(&counter);
        // 只验证不 panic，可编译可运行
    }
}
pub mod advanced_concurrency;
pub mod archive;
pub mod concurrency;
pub mod demo;
pub mod demo_simple;
pub mod error;
pub mod lockfree;
pub mod message_passing;
pub mod paralelism;
pub mod performance_benchmarks;
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_192_features;
pub mod rust_193_features;
pub mod rust_194_features;
pub mod rust_195_features; // Rust 1.95 特性 (Atomic update, cold_path)
pub mod rust_196_features;
pub mod rust_197_features;

pub mod lock_free_data_structures;
pub mod synchronization;
pub mod thread_pool_patterns;
pub mod threads;

#[cfg(test)]
pub mod miri_tests;
