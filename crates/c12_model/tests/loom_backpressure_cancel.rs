#![allow(clippy::print_stdout)]

use loom::sync::atomic::{AtomicUsize, Ordering};
use loom::sync::Arc;
use loom::thread;

#[test]
fn backpressure_with_cancel_signal() {
    loom::model(|| {
        let cap = 2usize;
        let q = Arc::new(loom::sync::Mutex::new(std::collections::VecDeque::with_capacity(cap)));
        let produced = Arc::new(AtomicUsize::new(0));
        let consumed = Arc::new(AtomicUsize::new(0));
        let cancel = Arc::new(AtomicUsize::new(0));

        let qp = q.clone();
        let prod_c = produced.clone();
        let cancel_p = cancel.clone();
        let producer = thread::spawn(move || {
            for i in 0..5usize {
                if cancel_p.load(Ordering::SeqCst) == 1 { break; }
                let mut g = qp.lock().unwrap();
                if g.len() < cap { g.push_back(i); prod_c.fetch_add(1, Ordering::SeqCst); }
            }
        });

        let qc = q.clone();
        let cons_c = consumed.clone();
        let cancel_c = cancel.clone();
        let consumer = thread::spawn(move || {
            for _ in 0..5usize {
                let mut g = qc.lock().unwrap();
                if let Some(_v) = g.pop_front() { cons_c.fetch_add(1, Ordering::SeqCst); }
                else { cancel_c.store(1, Ordering::SeqCst); break; }
            }
        });

        producer.join().unwrap();
        consumer.join().unwrap();

        let p = produced.load(Ordering::SeqCst);
        let c = consumed.load(Ordering::SeqCst);
        assert!(p >= c);
        assert!(p <= 5);
    });
}


