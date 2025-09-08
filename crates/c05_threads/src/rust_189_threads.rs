/*
Rust 1.89 并发方向对齐示例：
- 标准库 scoped 线程（thread::scope）更安全的借用跨线程
- crossbeam-channel vs std::mpsc 对比
- rayon 数据并行 map/reduce
- parking_lot 互斥/读写锁
*/

use std::thread;

pub fn demo_scoped_threads() {
    let mut data = vec![1, 2, 3, 4, 5];
    thread::scope(|s| {
        let mut_ref = &mut data;
        s.spawn(move || {
            for x in mut_ref.iter_mut() { *x *= 2; }
        });
        s.spawn(|| {
            // 可以并行做其他只读操作
        });
    });
    println!("scoped doubled: {:?}", data);
}

pub fn demo_mpsc_vs_crossbeam() {
    use std::sync::mpsc;
    // std::mpsc
    let (tx, rx) = mpsc::channel();
    let t = thread::spawn(move || {
        for i in 0..5 { tx.send(i).unwrap(); }
    });
    let mut collected = Vec::new();
    while let Ok(v) = rx.recv() { collected.push(v); if v == 4 { break; } }
    t.join().unwrap();
    println!("std::mpsc collected: {:?}", collected);

    // crossbeam-channel
    let (tx, rx) = crossbeam_channel::unbounded();
    let t = thread::spawn(move || {
        for i in 0..5 { tx.send(i).unwrap(); }
    });
    let out: Vec<_> = rx.iter().take(5).collect();
    t.join().unwrap();
    println!("crossbeam collected: {:?}", out);
}

pub fn demo_rayon_parallel() {
    use rayon::prelude::*;
    let v: Vec<i32> = (1..=1_000).collect();
    let seq: i64 = v.iter().map(|x| (*x as i64) * (*x as i64)).sum();
    let par: i64 = v.par_iter().map(|x| (*x as i64) * (*x as i64)).sum();
    let equal = seq == par;
    println!("rayon equal? {}", equal);
}

pub fn demo_parking_lot() {
    use parking_lot::{Mutex, RwLock};
    let counter = Mutex::new(0);
    let rw = RwLock::new(vec![1, 2, 3]);

    thread::scope(|s| {
        for _ in 0..4 {
            s.spawn(|| {
                for _ in 0..1000 { *counter.lock() += 1; }
            });
        }
        s.spawn(|| {
            let mut w = rw.write();
            w.push(4);
        });
        s.spawn(|| {
            let r = rw.read();
            let _sum: i32 = r.iter().sum();
        });
    });
    println!("parking_lot counter={}", *counter.lock());
}

pub fn demo_barrier_and_condvar() {
    use std::sync::{Arc, Barrier, Condvar, Mutex};
    use std::time::Duration;

    // Barrier：让一组线程在同一同步点汇合
    let barrier = Arc::new(Barrier::new(3));
    thread::scope(|s| {
        for i in 0..3 {
            let b = barrier.clone();
            s.spawn(move || {
                // do some work
                thread::sleep(Duration::from_millis(5 * (i + 1) as u64));
                b.wait();
            });
        }
    });
    println!("barrier done");

    // Condvar：条件变量等待/通知
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = pair.clone();
    thread::spawn(move || {
        // 模拟生产
        thread::sleep(Duration::from_millis(10));
        let (lock, cvar) = &*pair2;
        let mut ready = lock.lock().unwrap();
        *ready = true;
        cvar.notify_one();
    });
    let (lock, cvar) = &*pair;
    let mut ready = lock.lock().unwrap();
    while !*ready {
        ready = cvar.wait(ready).unwrap();
    }
    println!("condvar notified");
}

pub fn demonstrate_rust_189_threads() {
    println!("=== Rust 1.89 Threads Demos ===");
    demo_scoped_threads();
    demo_mpsc_vs_crossbeam();
    demo_rayon_parallel();
    demo_parking_lot();
    demo_barrier_and_condvar();
    demo_once_cell_and_once_lock();
    demo_thread_local();
    demo_sync_channel_backpressure();
    demo_concurrency_error_handling();
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_scoped_threads_runs() { demo_scoped_threads(); }
    #[test]
    fn test_mpsc_vs_crossbeam_runs() { demo_mpsc_vs_crossbeam(); }
    #[test]
    fn test_rayon_parallel_runs() { demo_rayon_parallel(); }
    #[test]
    fn test_parking_lot_runs() { demo_parking_lot(); }
    #[test]
    fn test_barrier_condvar_runs() { demo_barrier_and_condvar(); }
    #[test]
    fn test_once_cell_once_lock_runs() { demo_once_cell_and_once_lock(); }
    #[test]
    fn test_thread_local_runs() { demo_thread_local(); }
    #[test]
    fn test_sync_channel_backpressure_runs() { demo_sync_channel_backpressure(); }
    #[test]
    fn test_concurrency_error_handling_runs() { demo_concurrency_error_handling(); }
}

// 其他对齐示例：OnceCell/OnceLock、thread_local!、sync_channel 背压、并发错误处理
pub fn demo_once_cell_and_once_lock() {
    use once_cell::sync::OnceCell;
    use std::sync::OnceLock;

    static GLOBAL_ONCE_LOCK: OnceLock<String> = OnceLock::new();
    static GLOBAL_ONCE_CELL: OnceCell<String> = OnceCell::new();

    let _ = GLOBAL_ONCE_LOCK.set("init_once_lock".to_string());
    let _ = GLOBAL_ONCE_CELL.set("init_once_cell".to_string());

    println!(
        "OnceLock={}, OnceCell={}",
        GLOBAL_ONCE_LOCK.get().unwrap(),
        GLOBAL_ONCE_CELL.get().unwrap()
    );
}

pub fn demo_thread_local() {
    thread_local! {
        static TLS_COUNTER: std::cell::Cell<u32> = std::cell::Cell::new(0);
    }

    thread::scope(|s| {
        for _ in 0..3 {
            s.spawn(|| {
                TLS_COUNTER.with(|c| c.set(c.get() + 1));
                TLS_COUNTER.with(|c| println!("thread local counter={}", c.get()));
            });
        }
    });
}

pub fn demo_sync_channel_backpressure() {
    use std::sync::mpsc::sync_channel;
    use std::time::Duration;

    let (tx, rx) = sync_channel::<u32>(1); // 容量为1，产生背压
    let producer = thread::spawn(move || {
        for i in 0..3 {
            // 当通道满时，send 会阻塞直到有接收
            tx.send(i).unwrap();
        }
    });

    // 模拟缓慢消费者
    let consumer = thread::spawn(move || {
        for _ in 0..3 {
            thread::sleep(Duration::from_millis(5));
            let v = rx.recv().unwrap();
            println!("sync_channel recv={}", v);
        }
    });

    let _ = producer.join();
    let _ = consumer.join();
}

pub fn demo_concurrency_error_handling() {
    use anyhow::{Context, Result};
    use crossbeam_channel::{bounded, RecvTimeoutError};
    use std::time::Duration;
    use thiserror::Error;

    #[derive(Debug, Error)]
    enum ChanError {
        #[error("timeout waiting for message")]
        Timeout,
        #[error("channel disconnected")]
        Disconnected,
    }

    fn try_recv_with_timeout() -> Result<u32> {
        let (_tx, rx) = bounded::<u32>(0);
        // 没有发送者，超时将发生
        match rx.recv_timeout(Duration::from_millis(5)) {
            Ok(v) => Ok(v),
            Err(RecvTimeoutError::Timeout) => Err(ChanError::Timeout).context("recv with timeout"),
            Err(RecvTimeoutError::Disconnected) => Err(ChanError::Disconnected).context("recv with timeout"),
        }
    }

    let res = try_recv_with_timeout();
    println!("concurrency error handling: {}", res.unwrap_err());
}


