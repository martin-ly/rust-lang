// 高级策略配置示例：展示所有可配置选项

use c06_async::utils::{ExecStrategyBuilder, StrategyConfig};
use std::fs;
use std::time::Duration;

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let _ = tracing_subscriber::fmt::try_init();
    
    // 读取高级配置
    let cfg_text = fs::read_to_string("./configs/strategy.json")?;
    let cfg: StrategyConfig = serde_json::from_str(&cfg_text)?;
    
    println!("配置参数:");
    println!("  并发数: {}", cfg.concurrency);
    println!("  最大重试: {}", cfg.max_attempts);
    println!("  初始延迟: {}ms", cfg.start_delay_ms);
    println!("  超时: {:?}ms", cfg.timeout_ms);
    println!("  熔断器: {:?}", cfg.enable_breaker);
    if let Some(tb) = &cfg.token_bucket {
        println!("  令牌桶: {} 容量, {}/s 速率", tb.capacity, tb.refill_per_sec);
    }
    if let Some(bt) = cfg.breaker_threshold {
        println!("  熔断阈值: {}", bt);
    }
    if let Some(bw) = cfg.breaker_window_ms {
        println!("  熔断窗口: {}ms", bw);
    }
    if let Some(bh) = cfg.breaker_half_open_max_calls {
        println!("  半开最大调用: {}", bh);
    }
    
    let runner = ExecStrategyBuilder::from_config(&cfg).build();

    // 模拟多个请求
    let client = reqwest::Client::new();
    let urls = [
        "https://httpbin.org/status/200",
        "https://httpbin.org/status/500", // 会失败
        "https://httpbin.org/status/200",
        "https://httpbin.org/delay/1",    // 可能超时
    ];

    for (i, url) in urls.iter().enumerate() {
        println!("\n请求 {}: {}", i + 1, url);
        let url = url.to_string();
        let client = client.clone();
        
        let result = runner
            .run(
                move |attempt| {
                    let client = client.clone();
                    let url = url.clone();
                    async move {
                        println!("  尝试 {}: {}", attempt, url);
                        let r = client.get(&url).send().await?;
                        let s = r.status();
                        if s.is_success() { 
                            Ok(format!("成功: {}", s)) 
                        } else { 
                            Err(anyhow::anyhow!("HTTP错误: {}", s)) 
                        }
                    }
                },
                Some(|e: &anyhow::Error| {
                    // 只对网络错误重试，HTTP 4xx 不重试
                    !e.to_string().contains("4")
                }),
            )
            .await;
            
        match result {
            Ok(Some(msg)) => println!("  结果: {}", msg),
            Ok(None) => println!("  结果: 超时或取消"),
            Err(e) => println!("  结果: 错误 - {}", e),
        }
        
        // 短暂延迟以观察令牌桶效果
        tokio::time::sleep(Duration::from_millis(100)).await;
    }

    Ok(())
}
