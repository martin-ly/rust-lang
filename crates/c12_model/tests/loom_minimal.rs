// 最小 loom 并发模型测试（不默认运行，需手动 `cargo test --test loom_minimal -- --nocapture`）

#[cfg(loom)]
mod loom_tests {
    use loom::sync::atomic::{AtomicUsize, Ordering};
    use loom::thread;

    #[test]
    fn counter_increments() {
        loom::model(|| {
            let counter = AtomicUsize::new(0);
            let t1 = thread::spawn({
                let c = &counter;
                move || { c.fetch_add(1, Ordering::SeqCst); }
            });
            let t2 = thread::spawn({
                let c = &counter;
                move || { c.fetch_add(1, Ordering::SeqCst); }
            });
            t1.join().unwrap();
            t2.join().unwrap();
            assert_eq!(counter.load(Ordering::SeqCst), 2);
        });
    }
}


