//! 运行方式：
//! cargo run -p c06_async --example utils_strategy_smoke

use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let runner = c06_async::utils::ExecStrategyBuilder::new()
        .concurrency(4)
        .attempts(3)
        .start_delay(Duration::from_millis(50))
        .timeout(Duration::from_secs(1))
        .build();

    let out = runner
        .run(
            |attempt| async move {
                if attempt < 2 { // 首次失败，第二次成功
                    Err(anyhow::anyhow!("transient error"))
                } else {
                    Ok::<_, anyhow::Error>(format!("ok on attempt {}", attempt))
                }
            },
            None::<fn(&anyhow::Error) -> bool>,
        )
        .await?;

    println!("result = {:?}", out);
    Ok(())
}


