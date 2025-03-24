/*
在 Rust 的 tokio 异步运行时中，
tokio::sync::RwLock 是一种用于在异步环境中实现读写锁的同步原语。
它允许多个异步任务同时读取数据，
但在写入数据时会阻止其他任务的读取和写入，从而确保数据的一致性和安全性。

定义

tokio::sync::RwLock 是一个异步读写锁，提供了以下功能：
    允许多个任务同时读取数据（共享访问）。
    允许一个任务独占地写入数据（排他访问），在写入期间阻止其他任务的读取和写入。

机制
RwLock 的基本机制如下：
    读锁：多个任务可以同时获取读锁，只要没有任务持有写锁。
    写锁：只有一个任务可以获取写锁，并且在写锁被持有时，其他任务无法获取读锁或写锁。
    当任务完成对数据的访问后，锁会自动释放。
解释

RwLock 适用于读多写少的场景，因为它允许多个并发的读取操作，从而提高了性能。
在需要对共享数据进行频繁读取的情况下，使用 RwLock 可以减少锁的竞争。
*/

use tokio::sync::RwLock;
use std::sync::Arc;

#[allow(unused)]
pub async fn rwlock_test01() {
    // 创建一个 Arc 包裹的 RwLock，内部数据为一个 Vec
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 启动多个异步任务进行读取
    let mut read_handles = vec![];
    for _ in 0..5 {
        let data_clone = Arc::clone(&data);
        let handle = tokio::spawn(async move {
            let read_guard = data_clone.read().await; // 获取读锁
            println!("Read data: {:?}", *read_guard);
        });
        read_handles.push(handle);
    }

    // 启动一个异步任务进行写入
    let data_clone = Arc::clone(&data);
    let write_handle = tokio::spawn(async move {
        let mut write_guard = data_clone.write().await; // 获取写锁
        write_guard.push(4); // 修改数据
        println!("Data modified");
    });

    // 等待所有任务完成
    let _ = tokio::join!(write_handle,  
        // 等待所有读取任务完成
        futures::future::join_all(read_handles)
    );
}
