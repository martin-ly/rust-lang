// 异步背压行为测试（需要 tokio-adapter 特性）

#[cfg(feature = "tokio-adapter")]
mod tests_tokio {
    use async_channel::{bounded, TrySendError};

    #[tokio::test]
    async fn bounded_channel_capacity_enforced() {
        let (tx, _rx) = bounded::<u32>(2);
        tx.send(1).await.unwrap();
        tx.send(2).await.unwrap();
        // 第三个使用 try_send 应该返回 Full
        match tx.try_send(3) {
            Err(TrySendError::Full(3)) => {}
            other => panic!("unexpected: {:?}", other),
        }
    }
}


