use std::sync::{Arc, Mutex};
use tokio::time::{Duration, sleep};

#[allow(unused)]
#[derive(Debug, Clone)]
struct Promise<T> {
    result: Arc<Mutex<Option<T>>>,
}

#[allow(unused)]
impl<T> Promise<T> {
    fn new() -> Self {
        Promise {
            result: Arc::new(Mutex::new(None)),
        }
    }

    async fn resolve(&self, value: T) {
        let mut result = self.result.lock().unwrap();
        *result = Some(value);
    }

    async fn then<F, R>(&self, callback: F) -> Option<R>
    where
        F: FnOnce(T) -> R,
        T: Clone,
    {
        let result = self.result.lock().unwrap();
        if let Some(ref value) = *result {
            Some(callback(value.clone()))
        } else {
            None
        }
    }
}

#[allow(unused)]
async fn async_task() -> i32 {
    println!("开始异步任务...");
    sleep(Duration::from_secs(1)).await; // 模拟耗时操作
    println!("异步任务完成。");
    42 // 返回结果
}

#[allow(unused)]
async fn promise_future() {
    let promise = Promise::new();

    // 启动异步任务
    let promise_clone = promise.clone();
    tokio::spawn(async move {
        let result = async_task().await;
        promise_clone.resolve(result).await;
    });

    // 使用 then 方法处理结果
    let result = promise
        .then(|value| {
            println!("处理结果: {}", value);
            value + 1 // 处理后的结果
        })
        .await;

    if let Some(res) = result {
        println!("最终结果: {}", res);
    } else {
        println!("结果尚未准备好。");
    }

    // 等待一段时间以确保异步任务完成
    sleep(Duration::from_secs(3)).await;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_promise_future01() {
        promise_future().await;
    }
}
