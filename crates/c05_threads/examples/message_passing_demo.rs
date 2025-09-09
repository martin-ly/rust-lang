use std::thread;
use std::time::Duration;

use c05_threads::message_passing::{
    channel,
    mpsc,
    stream::ReceiverStream,
    sync_channel,
    watch,
};

fn demo_std_channel() {
    let (tx, rx) = channel::channel::<i32>();
    let handle = thread::spawn(move || {
        for i in 0..3 {
            tx.send(i).unwrap();
        }
    });
    handle.join().unwrap();
    let collected: Vec<_> = (0..3).map(|_| rx.recv().unwrap()).collect();
    println!("std channel -> {:?}", collected);
}

fn demo_crossbeam_unbounded() {
    let (tx, rx) = mpsc::unbounded::<&'static str>();
    let h = thread::spawn(move || {
        tx.send("hello").unwrap();
        tx.send("world").unwrap();
    });
    h.join().unwrap();
    let a = rx.recv().unwrap();
    let b = rx.recv().unwrap();
    println!("crossbeam unbounded -> {} {}", a, b);
}

fn demo_sync_channel() {
    let (tx, rx) = sync_channel::sync_channel::<u32>(1);
    let h = thread::spawn(move || {
        for v in 1..=3 {
            tx.send(v).unwrap();
        }
    });
    let mut out = Vec::new();
    for _ in 0..3 {
        out.push(rx.recv().unwrap());
    }
    h.join().unwrap();
    println!("sync_channel -> {:?}", out);
}

fn demo_watch() {
    let (tx, rx) = watch::channel(0u64);
    let mut ver = 0u64;
    let h = thread::spawn(move || {
        for i in 1..=3 {
            tx.send(i);
            thread::sleep(Duration::from_millis(10));
        }
    });
    // 监听三次变化
    let mut seen = Vec::new();
    for _ in 0..3 {
        let v = rx.changed(&mut ver);
        seen.push(v);
    }
    h.join().unwrap();
    println!("watch -> {:?}", seen);
}

fn demo_receiver_stream() {
    let (tx, rx) = mpsc::unbounded::<i32>();
    let h = thread::spawn(move || {
        for i in 1..=5 {
            tx.send(i).unwrap();
        }
    });
    let mut sum = 0;
    for v in ReceiverStream::new(rx) {
        sum += v;
        if sum >= 15 { // 收满后退出
            break;
        }
    }
    h.join().unwrap();
    println!("stream(sum) -> {}", sum);
}

fn main() {
    demo_std_channel();
    demo_crossbeam_unbounded();
    demo_sync_channel();
    demo_watch();
    demo_receiver_stream();
}
