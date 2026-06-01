// [来源: tokio docs / Rust Reference]
//! 运行时说明与示例：Tokio/当前线程/多线程
//! runtime explain and example ：Tokio/when before thread /thread
use std::time::Duration;

/// 在当前线程创建一个临时运行时并执行异步任务
/// in when before thread temporary runtime and async task
pub fn block_on_local<F: std::future::Future<Output = T>, T>(fut: F) -> T {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_time()
        .build()
        .expect("build current_thread runtime");
    rt.block_on(fut)
}

/// 在多线程运行时中执行示例任务
/// in thread runtime in example task
pub fn spawn_multi_thread_tasks() -> i32 {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_time()
        .build()
        .expect("build multi_thread runtime");
    rt.block_on(async {
        let h1 = tokio::spawn(async {
            tokio::time::sleep(Duration::from_millis(5)).await;
            1
        });
        let h2 = tokio::spawn(async {
            tokio::time::sleep(Duration::from_millis(3)).await;
            2
        });
        let a = h1.await.expect("等待任务 1 完成不应失败");
        let b = h2.await.expect("等待任务 2 完成不应失败");
        a + b
    })
}
