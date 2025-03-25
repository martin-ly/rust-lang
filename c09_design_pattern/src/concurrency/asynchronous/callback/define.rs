use tokio::time::{sleep, Duration};

async fn perform_task<F, E>(callback: F) -> Result<String, E>
where
    F: FnOnce(Result<String, E>),
{
    // 模拟异步操作
    sleep(Duration::from_secs(1)).await;
    
    // 假设任务成功完成
    let result = Ok("任务完成".to_string());
    
    // 调用回调函数
    callback(result);
    Ok("任务已回调".to_string())
}

#[allow(unused)]
async fn callback() {
    // 使用回调模式
    perform_task::<_, String>(|result| {
        match result {
            Ok(message) => println!("{}", message),
            Err(e) => eprintln!("发生错误: {:?}", e),
        }
    }).await.unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_callback01() {
        callback().await;
    }
}