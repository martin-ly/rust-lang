use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use tokio::time::{Duration, sleep};

#[allow(unused)]
#[derive(Debug)]
enum Task {
    HighPriority(String),
    LowPriority(String),
}

#[allow(unused)]
#[derive(Clone)]
struct TaskScheduler {
    tasks: Arc<Mutex<VecDeque<Task>>>,
}

#[allow(unused)]
impl TaskScheduler {
    fn new() -> Self {
        TaskScheduler {
            tasks: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    async fn add_task(&self, task: Task) {
        let mut tasks = self.tasks.lock().unwrap();
        tasks.push_back(task);
    }

    async fn run(&self) {
        while let Some(task) = {
            let mut tasks = self.tasks.lock().unwrap();
            tasks.pop_front()
        } {
            match task {
                Task::HighPriority(msg) => {
                    println!("执行高优先级任务: {}", msg);
                    sleep(Duration::from_secs(1)).await;
                }
                Task::LowPriority(msg) => {
                    println!("执行低优先级任务: {}", msg);
                    sleep(Duration::from_secs(1)).await;
                }
            }
        }
    }
}

#[allow(unused)]
async fn task_scheduling() {
    let scheduler = TaskScheduler::new();

    // 启动任务调度器
    let scheduler_clone = scheduler.clone();
    let scheduler_task = tokio::spawn(async move {
        scheduler_clone.run().await;
    });

    // 添加任务
    scheduler
        .add_task(Task::HighPriority("任务 1".to_string()))
        .await;
    scheduler
        .add_task(Task::LowPriority("任务 2".to_string()))
        .await;
    scheduler
        .add_task(Task::HighPriority("任务 3".to_string()))
        .await;
    scheduler
        .add_task(Task::LowPriority("任务 4".to_string()))
        .await;

    // 等待一段时间后关闭
    sleep(Duration::from_secs(10)).await;

    // 等待任务完成
    //let _ = scheduler_task.await.unwrap();
    let _ = tokio::try_join!(scheduler_task);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_task_scheduling01() {
        task_scheduling().await;
    }
}
