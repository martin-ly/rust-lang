use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    // 使用 JoinSet 模拟结构化并发：在作用域内启动并等待所有子任务
    let mut set = tokio::task::JoinSet::new();
    set.spawn(async {
        tokio::time::sleep(Duration::from_millis(80)).await;
        println!("child A done");
    });
    set.spawn(async {
        tokio::time::sleep(Duration::from_millis(40)).await;
        println!("child B done");
    });
    while set.join_next().await.is_some() {}
}
