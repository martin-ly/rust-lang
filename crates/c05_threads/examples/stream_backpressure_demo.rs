use std::thread;
use std::time::Duration;
use std::sync::{Arc, atomic::{AtomicBool, Ordering}};

use c05_threads::message_passing::{
    mpsc,
    stream::ReceiverStream,
    backpressure_handling as bp,
};

fn main() {
    // 通过背压通道控制生产速率（多线程共享，需 Arc 包裹）
    let ch = Arc::new(bp::DroppingBackpressureChannel::new(64, 0.9));

    // 将背压通道输出桥接到 crossbeam 通道以形成流
    let (tx, rx) = mpsc::unbounded::<i32>();

    // 生产者：快
    let producer = {
        let ch = Arc::clone(&ch);
        thread::spawn(move || {
            let mut sent = 0u64;
            for i in 0..10_000 {
                if ch.send(i).is_ok() { sent += 1; }
            }
            println!("producer sent accepted = {}", sent);
        })
    };

    // 桥接器：使用通用桥接辅助；最多转发 5000 条或收到停止信号
    let stop = Arc::new(AtomicBool::new(false));
    let bridge = {
        let ch = Arc::clone(&ch);
        let tx = tx.clone();
        let stop_flag = Arc::clone(&stop);
        thread::spawn(move || {
            bp::bridge_to_mpsc::<i32, _>(ch, tx, Some(5000), Some(stop_flag));
            println!("bridge finished");
        })
    };

    // 消费者：以同步流形式消费，并带超时退出；消费结束后设置停止标志
    let consumer = {
        let stop_flag = Arc::clone(&stop);
        thread::spawn(move || {
            let stream = ReceiverStream::new(rx);
            let mut total = 0u64;
            loop {
                if let Some(v) = stream.next_once_with_timeout(Duration::from_millis(10)) {
                    total = total.wrapping_add(v as u64);
                } else {
                    // 超时视为没有新数据，结束
                    break;
                }
            }
            stop_flag.store(true, Ordering::Relaxed);
            println!("consumer total = {}", total);
        })
    };

    producer.join().unwrap();
    bridge.join().unwrap();
    consumer.join().unwrap();
}
