// 并发案例：通道通信与同步
// 理论映射：对应“通道”与“同步”理论（见 01_formal_concurrency_model.md 附录）

use std::sync::mpsc;
use std::thread;

fn main() {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        tx.send(42).unwrap();
    });
    let received = rx.recv().unwrap();
    println!("收到: {}", received);
} 