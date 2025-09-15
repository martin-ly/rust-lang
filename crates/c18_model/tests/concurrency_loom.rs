// 最小 loom 并发验证示例：两个线程对计数器加一，验证无死锁与线性化

use loom::sync::atomic::{AtomicUsize, Ordering};
use loom::sync::Arc;
use loom::thread;
use loom::sync::Mutex;

#[test]
fn loom_counter() {
    loom::model(|| {
        let counter = Arc::new(AtomicUsize::new(0));
        let c1 = counter.clone();
        let c2 = counter.clone();

        let t1 = thread::spawn(move || {
            c1.fetch_add(1, Ordering::SeqCst);
        });
        let t2 = thread::spawn(move || {
            c2.fetch_add(1, Ordering::SeqCst);
        });

        t1.join().unwrap();
        t2.join().unwrap();

        let v = counter.load(Ordering::SeqCst);
        assert!(v == 1 || v == 2, "value should be 1 or 2 under exploration, got {}", v);
    });
}

#[test]
fn loom_mutex_counter() {
    loom::model(|| {
        let counter = Arc::new(Mutex::new(0usize));
        let c1 = counter.clone();
        let c2 = counter.clone();

        let t1 = thread::spawn(move || {
            let mut g = c1.lock().unwrap();
            *g += 1;
        });
        let t2 = thread::spawn(move || {
            let mut g = c2.lock().unwrap();
            *g += 1;
        });

        t1.join().unwrap();
        t2.join().unwrap();

        let v = *counter.lock().unwrap();
        assert_eq!(v, 2);
    });
}


