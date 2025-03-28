use tokio::time::{sleep, Duration};
use std::error::Error;

async fn async_task_with_error(id: u32) -> Result<(), Box<dyn Error>> {
    if id == 2 {
        return Err("任务失败".into());
    }
    println!("任务 {} 开始", id);
    sleep(Duration::from_secs(2)).await;
    println!("任务 {} 完成", id);
    Ok(())
}

#[tokio::main]
async fn main() {
    let tasks = vec![async_task_with_error(1), async_task_with_error(2), async_task_with_error(3)];

    for task in tasks {
        match task.await {
            Ok(_) => println!("任务成功"),
            Err(e) => println!("任务失败: {}", e),
        }
    }
}