//! Fallback / Degrade 韧性模式示例
//!
//! 展示异步服务调用中的 fallback 与 degrade 策略：
//! 1. 主服务失败或超时后自动回退到备用数据源；
//! 2. 主动降级开关控制服务范围；
//! 3. 结果枚举显式区分 Primary / Fallback / Degraded；
//! 4. 恢复探测逻辑演示。

use anyhow::Result;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use tokio::time::{sleep, timeout};
use tracing::{info, warn};

/// 服务调用结果，显式区分三种路径。
#[derive(Debug, Clone)]
pub enum ServiceOutcome<T> {
    /// 主路径成功。
    Primary(T),
    /// 主路径失败，使用回退结果。
    Fallback(T, FallbackReason),
    /// 主动降级模式下返回的受限结果。
    Degraded(T),
}

/// 触发 fallback 的原因。
#[derive(Debug, Clone)]
pub enum FallbackReason {
    /// 主路径超时。
    Timeout,
    /// 主路径明确失败。
    Failure(String),
}

/// 异步主服务：模拟一个可能失败或慢响应的远程依赖。
pub struct PrimaryService {
    /// 模拟失败概率：0..100
    failure_rate: u32,
    /// 模拟延迟毫秒
    latency_ms: u64,
}

impl PrimaryService {
    pub fn new(failure_rate: u32, latency_ms: u64) -> Self {
        Self {
            failure_rate: failure_rate.min(100),
            latency_ms,
        }
    }

    pub async fn fetch(&self, request: &str) -> Result<String> {
        sleep(Duration::from_millis(self.latency_ms)).await;

        if rand::random::<u32>() % 100 < self.failure_rate {
            return Err(anyhow::anyhow!("primary service failed for {}", request));
        }

        Ok(format!("primary[{}]", request))
    }
}

/// 备用服务：本地缓存或降级数据源，通常更快、更稳定。
pub struct FallbackService;

impl FallbackService {
    pub async fn fetch(&self, request: &str) -> Result<String> {
        // 模拟稳定的本地回退：不依赖主服务。
        sleep(Duration::from_millis(10)).await;
        Ok(format!("fallback[{}]", request))
    }
}

/// 韧性服务：封装主服务 + 备用服务 + 降级开关 + 恢复探测。
pub struct ResilientService {
    primary: PrimaryService,
    fallback: FallbackService,
    degraded: AtomicBool,
    fallback_timeout: Duration,
    recovery_probe_interval: u32,
    call_count: AtomicCounter,
}

struct AtomicCounter {
    value: std::sync::atomic::AtomicU64,
}

impl AtomicCounter {
    fn new() -> Self {
        Self {
            value: std::sync::atomic::AtomicU64::new(0),
        }
    }

    fn next(&self) -> u64 {
        self.value.fetch_add(1, Ordering::SeqCst)
    }
}

impl ResilientService {
    pub fn new(
        primary: PrimaryService,
        fallback: FallbackService,
        fallback_timeout: Duration,
        recovery_probe_interval: u32,
    ) -> Arc<Self> {
        Arc::new(Self {
            primary,
            fallback,
            degraded: AtomicBool::new(false),
            fallback_timeout,
            recovery_probe_interval,
            call_count: AtomicCounter::new(),
        })
    }

    /// 主动进入降级模式。
    pub fn enable_degradation(self: &Arc<Self>) {
        self.degraded.store(true, Ordering::SeqCst);
        warn!("降级模式已启用");
    }

    /// 主动退出降级模式。
    pub fn disable_degradation(self: &Arc<Self>) {
        self.degraded.store(false, Ordering::SeqCst);
        info!("降级模式已关闭");
    }

    /// 带韧性策略的服务调用。
    pub async fn call_with_resilience(
        self: &Arc<Self>,
        request: &str,
    ) -> Result<ServiceOutcome<String>> {
        // 若处于主动降级模式，直接返回降级结果。
        if self.degraded.load(Ordering::SeqCst) {
            let value = self.fallback.fetch(request).await?;
            return Ok(ServiceOutcome::Degraded(value));
        }

        // 否则尝试主路径，超时或失败则 fallback。
        let outcome = match timeout(self.fallback_timeout, self.primary.fetch(request)).await {
            Ok(Ok(value)) => ServiceOutcome::Primary(value),
            Ok(Err(e)) => {
                warn!("主路径失败，触发 fallback: {}", e);
                ServiceOutcome::Fallback(
                    self.fallback.fetch(request).await?,
                    FallbackReason::Failure(e.to_string()),
                )
            }
            Err(_) => {
                warn!("主路径超时，触发 fallback");
                ServiceOutcome::Fallback(
                    self.fallback.fetch(request).await?,
                    FallbackReason::Timeout,
                )
            }
        };

        // 恢复探测：每 N 次调用尝试一次主路径，以决定是否可以关闭降级。
        if matches!(outcome, ServiceOutcome::Fallback(_, _)) {
            let count = self.call_count.next();
            if count.is_multiple_of(u64::from(self.recovery_probe_interval)) {
                self.attempt_recovery(request).await;
            }
        }

        Ok(outcome)
    }

    /// 后台恢复探测：不阻塞当前请求结果，但可更新降级状态。
    async fn attempt_recovery(self: &Arc<Self>, request: &str) {
        let this = Arc::clone(self);
        let request = request.to_string();
        tokio::spawn(async move {
            match timeout(this.fallback_timeout, this.primary.fetch(&request)).await {
                Ok(Ok(_)) => {
                    info!("恢复探测成功，主路径可用");
                    this.degraded.store(false, Ordering::SeqCst);
                }
                Ok(Err(e)) => {
                    warn!("恢复探测失败: {}", e);
                }
                Err(_) => {
                    warn!("恢复探测超时");
                }
            }
        });
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("🚀 Fallback / Degrade 韧性模式示例启动");

    let primary = PrimaryService::new(60, 120); // 60% 失败率，120ms 延迟
    let fallback = FallbackService;
    let service = ResilientService::new(
        primary,
        fallback,
        Duration::from_millis(100), // 100ms 超时触发 fallback
        5,                          // 每 5 次 fallback 尝试一次恢复探测
    );

    // 阶段 1：正常运行，观察 fallback 触发。
    info!("--- 阶段 1：主服务不稳定，观察 fallback ---");
    for i in 0..10 {
        let request = format!("req-{}", i);
        match service.call_with_resilience(&request).await {
            Ok(outcome) => info!("请求 {}: {:?}", request, outcome),
            Err(e) => warn!("请求 {} 完全失败: {}", request, e),
        }
    }

    // 阶段 2：主动降级。
    info!("--- 阶段 2：主动启用降级模式 ---");
    service.enable_degradation();
    for i in 10..14 {
        let request = format!("req-{}", i);
        match service.call_with_resilience(&request).await {
            Ok(ServiceOutcome::Degraded(v)) => info!("请求 {} 降级结果: {}", request, v),
            Ok(other) => info!("请求 {} 非降级结果: {:?}", request, other),
            Err(e) => warn!("请求 {} 失败: {}", request, e),
        }
    }

    // 阶段 3：模拟主服务恢复，关闭降级。
    info!("--- 阶段 3：主服务恢复，关闭降级 ---");
    service.disable_degradation();

    // 用新的稳定主服务替换以演示恢复。
    let recovered_primary = PrimaryService::new(0, 20); // 0% 失败率，20ms 延迟
    let recovered_service = ResilientService::new(
        recovered_primary,
        FallbackService,
        Duration::from_millis(100),
        3,
    );

    for i in 14..18 {
        let request = format!("req-{}", i);
        match recovered_service.call_with_resilience(&request).await {
            Ok(outcome) => info!("请求 {}: {:?}", request, outcome),
            Err(e) => warn!("请求 {} 失败: {}", request, e),
        }
    }

    info!("✅ Fallback / Degrade 韧性模式示例结束");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_primary_path() {
        let primary = PrimaryService::new(0, 10);
        let fallback = FallbackService;
        let service = ResilientService::new(primary, fallback, Duration::from_millis(100), 5);

        let outcome = service.call_with_resilience("test-primary").await.unwrap();
        assert!(matches!(outcome, ServiceOutcome::Primary(_)));
    }

    #[tokio::test]
    async fn test_fallback_on_timeout() {
        // 主服务很慢，必然触发超时 fallback。
        let primary = PrimaryService::new(0, 500);
        let fallback = FallbackService;
        let service = ResilientService::new(primary, fallback, Duration::from_millis(50), 5);

        let outcome = service.call_with_resilience("test-timeout").await.unwrap();
        assert!(matches!(
            outcome,
            ServiceOutcome::Fallback(_, FallbackReason::Timeout)
        ));
    }

    #[tokio::test]
    async fn test_degraded_mode() {
        let primary = PrimaryService::new(0, 10);
        let fallback = FallbackService;
        let service = ResilientService::new(primary, fallback, Duration::from_millis(100), 5);

        service.enable_degradation();
        let outcome = service.call_with_resilience("test-degraded").await.unwrap();
        assert!(matches!(outcome, ServiceOutcome::Degraded(_)));
    }
}
