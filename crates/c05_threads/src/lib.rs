#![allow(clippy::type_complexity)]
#![allow(clippy::empty_line_after_doc_comments)]
#![allow(clippy::duplicated_attributes)]
#![allow(clippy::items_after_test_module)]
#![allow(clippy::unnecessary_get_then_check)]
#![allow(clippy::assertions_on_constants)]
#![allow(clippy::needless_borrows_for_generic_args)]
#![allow(clippy::overly_complex_bool_expr)]
#![allow(clippy::absurd_extreme_comparisons)]
#![allow(clippy::redundant_closure)]
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
pub mod lockfree;
pub mod message_passing;
pub mod paralelism;
pub mod performance_benchmarks;
pub mod rust_194_features;
pub mod synchronization;
pub mod threads;
