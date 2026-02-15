use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

use c05_threads::message_passing::backpressure_handling as bp;
use c05_threads::message_passing::{channel, mpsc, stream::ReceiverStream, sync_channel, watch};

#[test]
fn test_channel_helpers_send_all_and_drain() {
    let (tx, rx) = channel::channel::<i32>();
    channel::send_all(&tx, 0..3).unwrap();
    let v = channel::drain_n(&rx, 2);
    assert_eq!(v, vec![0, 1]);
    assert_eq!(rx.recv().unwrap(), 2);
}

#[test]
fn test_mpsc_helpers_send_all_and_try_recv_timeout() {
    let (tx, rx) = mpsc::unbounded::<i32>();
    mpsc::send_all(&tx, [10, 11, 12]).unwrap();
    assert_eq!(
        mpsc::try_recv_timeout(&rx, Duration::from_millis(1)),
        Some(10)
    );
}

#[test]
fn test_sync_channel_helpers() {
    let (tx, rx) = sync_channel::sync_channel::<i32>(2);
    sync_channel::send_all(&tx, [5, 6]).unwrap();
    let drained = sync_channel::drain_n(&rx, 3);
    assert_eq!(drained, vec![5, 6]);
}

#[test]
fn test_std_channel_basic() {
    let (tx, rx) = channel::channel::<i32>();
    thread::spawn(move || {
        tx.send(10).unwrap();
    })
    .join()
    .unwrap();
    assert_eq!(rx.recv().unwrap(), 10);
}

#[test]
fn test_crossbeam_unbounded_basic() {
    let (tx, rx) = mpsc::unbounded::<&'static str>();
    thread::spawn(move || {
        tx.send("a").unwrap();
        tx.send("b").unwrap();
    })
    .join()
    .unwrap();
    assert_eq!(rx.recv().unwrap(), "a");
    assert_eq!(rx.recv().unwrap(), "b");
}

#[test]
fn test_sync_channel_capacity() {
    let (tx, rx) = sync_channel::sync_channel::<u32>(1);
    let h = thread::spawn(move || {
        tx.send(1).unwrap();
        tx.send(2).unwrap();
    });
    // recv 两次
    assert_eq!(rx.recv().unwrap(), 1);
    assert_eq!(rx.recv().unwrap(), 2);
    h.join().unwrap();
}

#[test]
fn test_watch_changed_and_borrow() {
    let (tx, rx) = watch::channel(0u64);
    let mut ver = 0u64;
    let h = thread::spawn(move || {
        for i in 1..=2u64 {
            tx.send(i);
            thread::sleep(Duration::from_millis(5));
        }
        tx.close();
    });
    let first = rx.changed(&mut ver);
    let second = rx.changed(&mut ver);
    assert_eq!(first, 1);
    assert_eq!(second, 2);
    h.join().unwrap(); // 先 join 确保 sender 已 close
    assert!(rx.is_closed());
}

#[test]
fn test_watch_try_changed() {
    let (tx, rx) = watch::channel(100i32);
    let mut ver = u64::MAX; // 从未见过，首次 try_changed 返回初始值
    // 初次可见
    assert_eq!(rx.try_changed(&mut ver), Some(100));
    // 未变化时返回 None
    assert_eq!(rx.try_changed(&mut ver), None);
    // 更新后可见
    tx.send(101);
    assert_eq!(rx.try_changed(&mut ver), Some(101));
}

#[test]
fn test_watch_borrow_and_update_and_has_changed_and_drop_close() {
    let (tx, rx) = watch::channel(1u32);
    let mut ver = 0u64;
    // borrow_and_update 应更新版本
    let v = rx.borrow_and_update(&mut ver);
    assert_eq!(v, 1);
    assert!(!rx.has_changed(ver));
    // 发送更新
    tx.send(2);
    assert!(rx.has_changed(ver));
    // Drop sender 应自动关闭
    drop(tx);
    assert!(rx.is_closed());
}

#[test]
fn test_receiver_stream_iterates() {
    let (tx, rx) = mpsc::unbounded::<i32>();
    let h = thread::spawn(move || {
        for i in 1..=4 {
            tx.send(i).unwrap();
        }
    });
    let mut sum = 0;
    for v in ReceiverStream::new(rx) {
        sum += v;
        if sum >= 10 {
            break;
        }
    }
    h.join().unwrap();
    assert!(sum >= 10);
}

#[test]
fn test_receiver_stream_timeout_next() {
    let (_tx, rx) = mpsc::unbounded::<i32>();
    let stream = ReceiverStream::new(rx);
    // 由于没有元素，有限超时应返回 None
    let got = stream.next_once_with_timeout(Duration::from_millis(5));
    assert!(got.is_none());
}

#[test]
fn test_receiver_stream_try_next() {
    let (tx, rx) = mpsc::unbounded::<i32>();
    let stream = ReceiverStream::new(rx);
    assert!(stream.try_next().is_none());
    tx.send(42).unwrap();
    // 非阻塞应能立刻拿到
    assert_eq!(stream.try_next(), Some(42));
}

#[test]
fn test_receiver_stream_next_batch_max_and_take_until_timeout() {
    let (tx, rx) = mpsc::unbounded::<i32>();
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(i).unwrap();
        }
    })
    .join()
    .unwrap();
    let stream = ReceiverStream::new(rx);
    let batch = stream.next_batch_max(3, Duration::from_millis(5));
    assert_eq!(batch.len(), 3);

    let (_tx2, rx2) = mpsc::unbounded::<i32>();
    let stream2 = ReceiverStream::new(rx2);
    let taken = stream2.take_until_timeout(Duration::from_millis(10), Duration::from_millis(5));
    assert!(taken.is_empty());
}

#[test]
fn test_stream_rate_limit_iter_and_batch_with_max_wait() {
    let (tx, rx) = mpsc::unbounded::<i32>();
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(i).unwrap();
        }
    })
    .join()
    .unwrap();
    let stream = ReceiverStream::new(rx);
    let start = Instant::now();
    let v: Vec<_> = stream
        .rate_limit_iter(Duration::from_millis(1))
        .take(5)
        .collect();
    assert_eq!(v.len(), 5);
    assert!(start.elapsed() >= Duration::from_millis(4));

    let (tx2, rx2) = mpsc::unbounded::<i32>();
    thread::spawn(move || {
        for i in 0..3 {
            tx2.send(i).unwrap();
        }
    })
    .join()
    .unwrap();
    let stream2 = ReceiverStream::new(rx2);
    let batch = stream2.next_batch_with_max_wait(5, Duration::from_millis(5));
    assert!(!batch.is_empty());
}

#[test]
fn test_bridge_to_mpsc_max_forward_and_stop() {
    let bp_ch = Arc::new(bp::DroppingBackpressureChannel::new(32, 0.95));
    let (tx, rx) = mpsc::unbounded::<i32>();

    // 预先发送若干到背压通道
    for i in 0..100 {
        let _ = bp_ch.send(i);
    }

    let stop = Arc::new(AtomicBool::new(false));
    let bp_ch_clone = Arc::clone(&bp_ch);
    let tx_clone = tx.clone();
    let stop_clone = Arc::clone(&stop);

    let bridge = thread::spawn(move || {
        bp::bridge_to_mpsc::<i32, _>(bp_ch_clone, tx_clone, Some(10), Some(stop_clone));
    });

    // 消费 10 条
    let mut count = 0;
    while let Ok(_v) = rx.recv_timeout(Duration::from_millis(50)) {
        count += 1;
        if count >= 10 {
            break;
        }
    }
    // 通知停止
    stop.store(true, Ordering::Relaxed);
    bridge.join().unwrap();

    assert_eq!(count, 10);
}

#[test]
fn test_bridge_to_mpsc_rate_limited() {
    let bp_ch = Arc::new(bp::DroppingBackpressureChannel::new(64, 0.99));
    for i in 0..20 {
        let _ = bp_ch.send(i);
    }
    let (tx, rx) = mpsc::unbounded::<i32>();
    let stop = Arc::new(AtomicBool::new(false));
    let j = {
        let ch = Arc::clone(&bp_ch);
        let txc = tx.clone();
        let stopc = Arc::clone(&stop);
        thread::spawn(move || {
            bp::bridge_to_mpsc_rate_limited::<i32, _>(
                ch,
                txc,
                Duration::from_millis(1),
                Some(5),
                Some(stopc),
            );
        })
    };
    let mut cnt = 0;
    while let Ok(_v) = rx.recv_timeout(Duration::from_millis(20)) {
        cnt += 1;
        if cnt >= 5 {
            break;
        }
    }
    stop.store(true, Ordering::Relaxed);
    j.join().unwrap();
    assert_eq!(cnt, 5);
}
