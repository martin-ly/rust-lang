// 从 JSON 配置构建策略并运行一个请求

use c06_async::utils::{ExecStrategyBuilder, StrategyConfig};
use std::fs;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let _ = tracing_subscriber::fmt::try_init();
    let cfg_text = fs::read_to_string("./configs/strategy.json")?;
    let cfg: StrategyConfig = serde_json::from_str(&cfg_text)?;
    let runner = ExecStrategyBuilder::from_config(&cfg).build();

    let client = reqwest::Client::new();
    let url = "https://httpbin.org/status/200".to_string();
    let out = runner
        .run(
            move |_| {
                let client = client.clone();
                let url = url.clone();
                async move {
                    let r = client.get(&url).send().await?;
                    let s = r.status();
                    if s.is_success() { Ok(s) } else { Err(anyhow::anyhow!("status {s}")) }
                }
            },
            Some(|_e: &anyhow::Error| true),
        )
        .await;
    println!("result = {:?}", out);
    Ok(())
}


