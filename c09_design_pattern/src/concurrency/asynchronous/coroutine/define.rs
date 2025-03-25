use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

#[allow(unused)]
#[derive(Debug)]
enum Task {
    HighPriority(u32),
    LowPriority(u32),
}

#[allow(unused)]
async fn producer(tx: mpsc::Sender<Task>) {
    for i in 1..=5 {
        if i % 2 == 0 {
            println!("生产者生成高优先级任务: {}", i);
            tx.send(Task::HighPriority(i)).await.unwrap();
        } else {
            println!("生产者生成低优先级任务: {}", i);
            tx.send(Task::LowPriority(i)).await.unwrap();
        }
        sleep(Duration::from_secs(1)).await; // 模拟生产延迟
    }
}

#[allow(unused)]
async fn consumer(mut rx: mpsc::Receiver<Task>) {
    while let Some(task) = rx.recv().await {
        match task {
            Task::HighPriority(id) => {
                println!("消费者处理高优先级任务: {}", id);
                sleep(Duration::from_secs(1)).await; // 模拟处理延迟
            }
            Task::LowPriority(id) => {
                println!("消费者处理低优先级任务: {}", id);
                sleep(Duration::from_secs(2)).await; // 模拟处理延迟
            }
        }
    }
}

#[allow(unused)]
async fn state_machine() {
    let mut state = "开始";

    loop {
        match state {
            "开始" => {
                println!("状态机: 开始");
                sleep(Duration::from_secs(1)).await;
                state = "处理";
            }
            "处理" => {
                println!("状态机: 处理");
                sleep(Duration::from_secs(1)).await;
                state = "结束";
            }
            "结束" => {
                println!("状态机: 结束");
                break;
            }
            _ => {}
        }
    }
}

#[allow(unused)]
async fn coroutine() {
    let (tx, rx) = mpsc::channel(10);

    let prod = tokio::spawn(producer(tx));
    let cons = tokio::spawn(consumer(rx));
    let state = tokio::spawn(state_machine());

    // 等待生产者和消费者完成
    let _ = tokio::try_join!(prod, cons, state);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_coroutine01() {
        coroutine().await;
    }
}
