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
pub mod concurrency;
pub mod lockfree;
pub mod message_passing;
pub mod paralelism;
pub mod synchronization;
pub mod threads;
pub mod advanced_concurrency;
pub mod performance_benchmarks;
pub mod rust_189_threads;
pub mod demo;
pub mod demo_simple;
