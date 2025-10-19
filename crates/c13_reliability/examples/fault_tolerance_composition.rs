//! 容错机制组合使用示例
//!
//! 本示例展示如何组合多种容错机制构建健壮的服务，包括：
//! - 熔断器使用
//! - 重试策略
//! - 限流机制
//!
//! # 运行示例
//!
//! ```bash
//! cargo run --example fault_tolerance_composition
//! ```

use c13_reliability::fault_tolerance::{
    CircuitBreaker, CircuitBreakerConfig, CircuitBreakerState, RetryStrategy, RetryPolicy, RetryConfig,
};
use c13_reliability::fault_tolerance::rate_limiting::{TokenBucket, RateLimiter};
use c13_reliability::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    println!("=== 容错机制组合使用示例 ===\n");

    // 示例 1: 熔断器使用
    demo_1_circuit_breaker().await?;

    println!("\n{}", "=".repeat(70));

    // 示例 2: 重试策略
    demo_2_retry_policy().await?;

    println!("\n{}", "=".repeat(70));

    // 示例 3: 限流机制
    demo_3_rate_limiting().await?;

    Ok(())
}

/// 示例 1: 熔断器使用
async fn demo_1_circuit_breaker() -> Result<(), UnifiedError> {
    println!("📝 示例 1: 熔断器使用\n");

    println!("🎯 场景: 保护不稳定的外部服务\n");

    // 配置熔断器
    let cb_config = CircuitBreakerConfig {
        failure_threshold: 3,           // 3次失败后熔断
        success_threshold: 2,            // 2次成功后关闭
        recovery_timeout: Duration::from_secs(5),
        half_open_max_requests: 2,
        sliding_window_size: Duration::from_secs(60),
        minimum_requests: 3,
    };

    let circuit_breaker = Arc::new(CircuitBreaker::new(cb_config));

    println!("配置:");
    println!("  失败阈值: 3 次");
    println!("  成功阈值: 2 次");
    println!("  恢复超时: 5 秒");

    println!("\n开始测试...\n");

    // 模拟一系列请求
    for i in 1..=10 {
        println!("━━━ 请求 #{} ━━━", i);

        let start = Instant::now();

        // 检查熔断器状态
        match circuit_breaker.state() {
            CircuitBreakerState::Open => {
                println!("  ⚡ 熔断器打开，快速失败");
                println!("  状态: {:?}\n", circuit_breaker.state());
                
                // 等待恢复超时
                if i == 7 {
                    println!("  ⏰ 等待恢复超时...");
                    sleep(Duration::from_secs(5)).await;
                }
                continue;
            }
            _ => {}
        }

        // 模拟服务调用
        let result = call_unstable_service(i).await;

        let elapsed = start.elapsed();

        match result {
            Ok(_) => {
                circuit_breaker.record_success();
                println!("  ✅ 成功 (耗时: {:?})", elapsed);
            }
            Err(e) => {
                circuit_breaker.record_failure();
                println!("  ❌ 失败: {} (耗时: {:?})", e, elapsed);
            }
        }

        println!("  状态: {:?}", circuit_breaker.state());

        sleep(Duration::from_millis(100)).await;
    }

    println!("💡 熔断器优势:");
    println!("  ✅ 快速失败: 避免等待超时");
    println!("  ✅ 防止雪崩: 保护下游服务");
    println!("  ✅ 自动恢复: Half-Open 状态探测");

    Ok(())
}

/// 示例 2: 重试策略
async fn demo_2_retry_policy() -> Result<(), UnifiedError> {
    println!("📝 示例 2: 重试策略\n");

    println!("🎯 场景: 应对瞬时故障\n");

    // 配置指数退避重试
    let retry_config = RetryConfig {
        max_attempts: 3,
        strategy: RetryStrategy::ExponentialBackoff {
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(5),
            multiplier: 2.0,
        },
        enabled: true,
        retry_conditions: vec![],
        no_retry_conditions: vec![],
    };

    let retry_policy = RetryPolicy::new(retry_config);

    println!("配置:");
    println!("  最多重试: 3 次");
    println!("  策略: 指数退避");
    println!("  初始延迟: 100ms");
    println!("  延迟倍数: 2.0");
    println!("  启用抖动: 是");

    println!("\n测试场景 1: 最终成功\n");

    // 使用共享计数器
    let attempt = Arc::new(std::sync::atomic::AtomicU32::new(0));
    let attempt_clone = attempt.clone();
    
    let result = retry_policy
        .execute(move || {
            let attempt = attempt_clone.clone();
            async move {
                let current = attempt.fetch_add(1, std::sync::atomic::Ordering::SeqCst) + 1;
                println!("  尝试 #{}", current);
                
                // 前2次失败，第3次成功
                if current < 3 {
                    Err(UnifiedError::new(
                        "Temporary failure",
                        ErrorSeverity::Medium,
                        "service",
                        ErrorContext::new(
                            "service",
                            "call",
                            file!(),
                            line!(),
                            ErrorSeverity::Medium,
                            "demo",
                        ),
                    ))
                } else {
                    println!("  ✅ 成功！");
                    Ok("Success".to_string())
                }
            }
        })
        .await;

    match result {
        Ok(_) => println!("\n✅ 最终成功\n"),
        Err(e) => println!("\n❌ 最终失败: {}\n", e),
    }

    println!("💡 重试策略优势:");
    println!("  ✅ 提高成功率: 应对瞬时故障");
    println!("  ✅ 指数退避: 避免过载");
    println!("  ✅ 随机抖动: 防止重试风暴");

    Ok(())
}

/// 示例 3: 限流机制
async fn demo_3_rate_limiting() -> Result<(), UnifiedError> {
    println!("📝 示例 3: 限流机制\n");

    println!("🎯 场景: 控制请求速率\n");

    // 配置限流器: 每秒10个请求
    let rate_limiter = Arc::new(TokenBucket::new(10, Duration::from_secs(1)));

    println!("配置:");
    println!("  容量: 10 个令牌");
    println!("  周期: 1 秒");

    println!("\n模拟突发流量...\n");

    let mut success_count = 0;
    let mut rate_limited_count = 0;

    // 模拟 30 个快速请求
    for i in 1..=30 {
        match rate_limiter.acquire().await {
            Ok(_) => {
                println!("请求 #{:02}: ✅ 通过", i);
                success_count += 1;
            }
            Err(_) => {
                println!("请求 #{:02}: 🚫 被限流", i);
                rate_limited_count += 1;
            }
        }

        // 快速发送
        sleep(Duration::from_millis(10)).await;
    }

    println!("\n📊 统计结果:");
    println!("  通过: {} 个", success_count);
    println!("  限流: {} 个", rate_limited_count);
    println!("  总计: 30 个");

    println!("\n💡 限流机制优势:");
    println!("  ✅ 流量控制: 防止过载");
    println!("  ✅ 公平性: 令牌桶算法");
    println!("  ✅ 保护系统: 第一道防线");

    Ok(())
}

// ============================================================================
// 模拟的服务调用
// ============================================================================

/// 模拟不稳定的服务调用
async fn call_unstable_service(request_id: i32) -> Result<String, UnifiedError> {
    // 模拟网络延迟
    sleep(Duration::from_millis(50)).await;

    // 30% 概率失败
    if request_id % 3 == 0 {
        Err(UnifiedError::new(
            "Service temporarily unavailable",
            ErrorSeverity::High,
            "service",
            ErrorContext::new(
                "service",
                "call_unstable_service",
                file!(),
                line!(),
                ErrorSeverity::High,
                "demo",
            ),
        ))
    } else {
        Ok(format!("Response for request {}", request_id))
    }
}
