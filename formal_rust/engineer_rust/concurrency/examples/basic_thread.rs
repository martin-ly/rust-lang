// 基本多线程示例 Basic Thread Example
use std::thread;

fn main() {
    let handle = thread::spawn(|| {
        println!("Hello from a new thread!");
    });
    handle.join().unwrap();
} 