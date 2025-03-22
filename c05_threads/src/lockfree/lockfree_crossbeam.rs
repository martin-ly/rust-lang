

use crossbeam::queue::ArrayQueue;
// use crossbeam::atomic::AtomicCell;
// use crossbeam::epoch::{Atomic, Owned, Shared};
// use std::sync::atomic::Ordering;
// use std::thread;

#[allow(unused)]
pub fn lockfree_crossbeam_demo01() {
    println!("lockfree_crossbeam_demo01");
    let queue = ArrayQueue::new(3); // 创建一个容量为 3 的无锁队列

    // 向队列中插入元素
    queue.push(1).unwrap();
    queue.push(2).unwrap();
    queue.push(3).unwrap();

    // 尝试插入超过容量的元素
    if queue.push(4).is_err() {
        println!("队列已满，无法插入 4");
    }

    // 从队列中弹出元素
    while let Some(value) = queue.pop() {
        println!("弹出元素: {}", value);
    }
}

#[allow(unused)]
pub fn lockfree_crossbeam_demo02() {
    println!("lockfree_crossbeam_demo02");


}

