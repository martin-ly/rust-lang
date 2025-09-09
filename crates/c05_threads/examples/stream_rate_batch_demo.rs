use std::sync::{Arc, atomic::{AtomicBool, Ordering}};
use std::time::Duration;
use std::thread;

use c05_threads::message_passing::{mpsc, stream::ReceiverStream};
use c05_threads::message_passing::backpressure_handling as bp;

fn main() {
    let bp_ch = Arc::new(bp::DroppingBackpressureChannel::new(256, 0.95));
    // 快速生产者
    {
        let ch = Arc::clone(&bp_ch);
        thread::spawn(move || {
            for i in 0..10_000 { let _ = ch.send(i); }
        });
    }

    // 限速桥接到 crossbeam
    let (tx, rx) = mpsc::unbounded::<i32>();
    let stop = Arc::new(AtomicBool::new(false));
    {
        let ch = Arc::clone(&bp_ch);
        let txc = tx.clone();
        let stopc = Arc::clone(&stop);
        thread::spawn(move || {
            bp::bridge_to_mpsc_rate_limited::<i32, _>(ch, txc, Duration::from_millis(1), Some(2000), Some(stopc));
        });
    }

    // 批量消费：最大等待 10ms 凑批，每批最多 64
    let stream = ReceiverStream::new(rx);
    let mut total = 0usize;
    for _ in 0..50 {
        let batch = stream.next_batch_with_max_wait(64, Duration::from_millis(10));
        if batch.is_empty() { break; }
        total += batch.len();
        // 演示：以限速迭代处理每批元素
        for _v in ReceiverStream::from(mpsc::unbounded::<i32>().1).rate_limit_iter(Duration::from_millis(0)) {
            break; // 占位示例，不实际使用
        }
    }
    stop.store(true, Ordering::Relaxed);
    println!("received total = {}", total);
}
