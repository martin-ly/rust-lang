use tokio::time::{Duration, sleep};

// 定义一个异步函数
async fn async_task(id: u32) {
    println!("任务 {} 开始", id);
    // 模拟异步操作
    sleep(Duration::from_secs(1)).await;
    println!("任务 {} 完成", id);
}

// 主异步函数
#[tokio::main]
async fn main() {
    // 创建多个异步任务
    let task1 = async_task(1);
    let task2 = async_task(2);
    let task3 = async_task(3);

    // 等待所有任务完成
    tokio::join!(task1, task2, task3);
}
