use tokio::sync::Notify;
use std::sync::Arc;

/*
在 Rust 的 tokio 异步运行时中，Notify 是一种用于在异步任务之间进行通知的机制。
它允许一个任务等待另一个任务的通知，从而实现任务之间的协调和同步。

解释

tokio::sync::Notify 提供了一种简单的方式来实现异步等待和通知。
它的工作原理是，一个任务可以在 Notify 上调用 notified() 方法来等待通知，
而另一个任务可以调用 notify_one() 或 notify_waiters() 方法来发送通知。
    notified()：返回一个 Notified 结构体，表示当前任务正在等待通知。
    notify_one()：通知一个等待的任务。
    notify_waiters()：通知所有等待的任务。
这种机制非常适合用于实现条件变量或在某些条件满足时唤醒等待的任务。

机制

Notify 的基本机制如下：
    一个任务调用 notified() 进入等待状态。
    另一个任务在某个条件满足时调用 notify_one() 或 notify_waiters()，
    唤醒一个或所有等待的任务。
    被唤醒的任务继续执行。

*/

#[allow(unused)]
pub async fn notify_test01() {
    // 创建一个 Notify 实例
    let notify = Arc::new(Notify::new());

    // 克隆 Notify 的 Arc 以便在任务中共享
    let notify_clone = Arc::clone(&notify);

    // 启动一个异步任务，等待通知
    let waiting_task = tokio::spawn(async move {
        println!("Waiting for notification...");
        notify_clone.notified().await; // 等待通知
        println!("Received notification!");
    });

    // 启动另一个异步任务，发送通知
    let notifying_task = tokio::spawn(async move {
        // 模拟一些工作
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        println!("Sending notification...");
        notify.notify_one(); // 发送通知
    });

    // 等待两个任务完成
    let _ = tokio::join!(waiting_task, notifying_task);
}
