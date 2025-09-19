// utils 组合演示：重试 + 超时 + 限流 + 取消（示例）

use c06_async::utils;
use std::time::Duration;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    // 1) 限流：最多 2 个并发
    let limiter = utils::SemaphoreLimiter::new(2);

    // 2) 为一组任务添加：超时(200ms) + 重试(3 次、起始 50ms)
    let handles: Vec<_> = (0..5)
        .map(|i| {
            let limiter = limiter.clone();
            tokio::spawn(async move {
                limiter
                    .run(async move {
                        let op = || async move {
                            // 模拟不稳定操作：前两次失败
                            if i % 3 != 0 {
                                Err::<&'static str, anyhow::Error>(anyhow::anyhow!("flaky"))
                            } else {
                                tokio::time::sleep(Duration::from_millis(80)).await;
                                Ok::<&'static str, anyhow::Error>("ok")
                            }
                        };

                        let fut = utils::retry_with_backoff(|attempt| async move {
                            if attempt < 3 { op().await } else { op().await }
                        }, 3, Duration::from_millis(50));

                        match utils::with_timeout(Duration::from_millis(200), fut).await {
                            Some(Ok(v)) => format!("task#{i}: {v}"),
                            Some(Err(e)) => format!("task#{i}: error={:#}", e),
                            None => format!("task#{i}: timeout"),
                        }
                    })
                    .await
            })
        })
        .collect();

    let results = futures::future::join_all(handles).await;
    for r in results {
        println!("{}", r.unwrap());
    }

    // 3) 取消演示
    let (scope, reg) = utils::CancelScope::new();
    let t = tokio::spawn(utils::abortable(reg, async {
        tokio::time::sleep(Duration::from_secs(1)).await;
        "never prints"
    }));
    tokio::time::sleep(Duration::from_millis(10)).await;
    scope.cancel();
    let _ = t.await.unwrap();

    Ok(())
}


