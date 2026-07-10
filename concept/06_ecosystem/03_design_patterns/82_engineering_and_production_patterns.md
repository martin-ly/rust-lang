> **内容分级**: [专家级]
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
> **代码状态**: ✅ 含可编译示例
>
# 工程实践与生产级模式
>
> **EN**: Engineering Practice and Production-Grade Patterns
> **Summary**: Rust production-grade patterns: circuit breaker, retry, rate limiting, graceful degradation, observability, safe configuration, and graceful shutdown.
>
> **受众**: [专家]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L6 生态工程
> **A/S/P 标记**: **A+S** — Application + Structure
> **前置概念**: [Architecture Patterns](35_architecture_patterns.md) · [Error Handling](../../02_intermediate/03_error_handling/04_error_handling.md) · [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md)
> **后置概念**: [Microservice Patterns](31_microservice_patterns.md) · [Event-Driven Architecture](32_event_driven_architecture.md)
> **相关概念**: [Pattern Implementation Comparison](36_pattern_implementation_comparison.md) · [Pattern Selection Best Practices](37_pattern_selection_best_practices.md) · [System Design Principles](05_system_design_principles.md) · [Algorithm Engineering Practice](../11_domain_applications/76_algorithm_engineering_practice.md)
>
> **来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) · [Release It! — Michael Nygard](https://pragprog.com/titles/mnee2/release-it-second-edition/) · [Site Reliability Engineering](https://sre.google/sre-book/table-of-contents/) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)

---

## 一、概述

生产级 Rust 应用需要在**弹性、可观测性、性能、安全、配置管理**五个维度建立系统化实践。与经典设计模式相比，工程与生产级模式更关注**故障模型、运行期行为与可运维性**，并充分利用 Rust 的所有权（Ownership）、类型安全和零成本抽象（Zero-Cost Abstraction）来在编译期消除一类运行时（Runtime）错误。

## 二、弹性模式

### 2.1 断路器（Circuit Breaker）

当下游服务持续失败时，快速失败以避免线程/连接池被耗尽，并在超时后进入半开状态探测恢复。

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

#[derive(Clone, Copy, PartialEq)]
pub enum State { Closed, Open, HalfOpen }

pub struct CircuitBreaker {
    threshold: usize,
    timeout: Duration,
    state: AtomicUsize,      // 0=Closed, 1=Open, 2=HalfOpen
    failures: AtomicUsize,
    last_failure: Mutex<Option<Instant>>,
}

impl CircuitBreaker {
    pub fn new(threshold: usize, timeout: Duration) -> Self {
        Self {
            threshold,
            timeout,
            state: AtomicUsize::new(0),
            failures: AtomicUsize::new(0),
            last_failure: Mutex::new(None),
        }
    }

    fn state(&self) -> State {
        match self.state.load(Ordering::Acquire) {
            1 => State::Open,
            2 => State::HalfOpen,
            _ => State::Closed,
        }
    }

    pub fn call<F, T, E>(&self, f: F) -> Result<T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        if self.state() == State::Open {
            let elapsed = self.last_failure.lock().unwrap()
                .map(|t| t.elapsed()).unwrap_or(Duration::MAX);
            if elapsed < self.timeout {
                // 生产环境中应返回自定义错误：断路器开启
                return f(); // 简化示例
            }
            self.state.store(2, Ordering::Release);
        }

        match f() {
            Ok(v) => {
                self.failures.store(0, Ordering::Release);
                self.state.store(0, Ordering::Release);
                Ok(v)
            }
            Err(e) => {
                let n = self.failures.fetch_add(1, Ordering::AcqRel) + 1;
                if n >= self.threshold {
                    *self.last_failure.lock().unwrap() = Some(Instant::now());
                    self.state.store(1, Ordering::Release);
                }
                Err(e)
            }
        }
    }
}
```

### 2.2 重试与指数退避（Retry + Backoff）

```rust
use std::thread;
use std::time::Duration;

pub fn with_retry<F, T, E>(mut op: F, max_attempts: u32) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
{
    let mut attempts = 0;
    loop {
        match op() {
            Ok(v) => return Ok(v),
            Err(e) => {
                attempts += 1;
                if attempts >= max_attempts {
                    return Err(e);
                }
                let backoff = Duration::from_millis(2u64.pow(attempts.min(6)) * 10);
                thread::sleep(backoff);
            }
        }
    }
}
```

### 2.3 令牌桶限流（Token Bucket Rate Limiter）

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

pub struct TokenBucket {
    max: usize,
    refill_per_sec: f64,
    tokens: AtomicUsize,
    last_refill: Mutex<Instant>,
}

impl TokenBucket {
    pub fn new(max: usize, refill_per_sec: f64) -> Self {
        Self {
            max,
            refill_per_sec,
            tokens: AtomicUsize::new(max),
            last_refill: Mutex::new(Instant::now()),
        }
    }

    pub fn acquire(&self, n: usize) -> bool {
        let mut last = self.last_refill.lock().unwrap();
        let elapsed = last.elapsed().as_secs_f64();
        let available = (self.tokens.load(Ordering::Acquire) as f64
            + elapsed * self.refill_per_sec).min(self.max as f64) as usize;
        self.tokens.store(available, Ordering::Release);
        *last = Instant::now();
        drop(last);

        if available < n {
            return false;
        }
        self.tokens.fetch_sub(n, Ordering::AcqRel) >= n
    }
}
```

## 三、弹性模式对比矩阵

| 模式 | 防御对象 | 触发条件 | 恢复策略 | Rust 关键类型 | 典型位置 |
|:---|:---|:---|:---|:---|:---|
| **Circuit Breaker** | 持续失败/级联故障 | 失败次数 ≥ 阈值 | 超时后半开探测 | `AtomicUsize` + `Mutex<Instant>` | 下游 RPC/数据库 |
| **Retry** | 瞬态网络抖动 | 返回可重试错误 | 指数退避 | `std::thread::sleep` | 客户端调用 |
| **Rate Limiter** | 流量过载 | 请求速率超过配额 | 令牌补充 | `AtomicUsize` + `Mutex<Instant>` | 网关/API 入口 |
| **Bulkhead** | 资源争用 | 线程池/信号量耗尽 | 隔离失败域 | `tokio::sync::Semaphore` | 关键依赖池 |
| **Fallback** | 功能不可用 | 主路径失败 | 返回默认值/缓存 | `match` + 静态值 | 读密集服务 |

## 四、模式选择决策树

```text
生产级弹性模式选择
│
├─ 错误是瞬态且可恢复？
│  ├─ 是 → Retry（指数退避 + 最大重试次数）
│  └─ 否 → Circuit Breaker
│
├─ 入口流量可能突增？
│  ├─ 是 → Rate Limiter
│  └─ 否 → 直接放行
│
├─ 多个下游依赖共享资源？
│  ├─ 是 → Bulkhead（舱壁隔离）
│  └─ 否 → 统一调度
│
└─ 需要保证最低可用性？
   ├─ 是 → Fallback（兜底/降级）
   └─ 否 → 快速失败
```

## 五、可观测性模式

| 模式 | 目的 | Rust 生态 |
|:---|:---|:---|
| 结构化日志 | 统一、可解析的日志输出 | `tracing` + `tracing-subscriber` |
| Metrics 收集 | 请求量、延迟、错误率量化 | `prometheus`, `metrics` |
| 分布式追踪 | 跨服务请求链路可视化 | `opentelemetry`, `tracing-opentelemetry` |

```rust,ignore
use tracing::{info, instrument};

#[instrument]
pub async fn handle_order(order_id: u64) -> Result<(), &'static str> {
    info!(order_id, "processing order");
    Ok(())
}
```

## 六、安全模式：输入验证与类型化边界

```rust
#[derive(Debug, Clone, PartialEq)]
pub struct SanitizedEmail(String);

impl SanitizedEmail {
    pub fn new(raw: &str) -> Result<Self, &'static str> {
        if raw.len() > 254 || !raw.contains('@') {
            return Err("invalid email format");
        }
        // 可继续集成 DNS/MX 检查、正则白名单等
        Ok(Self(raw.to_lowercase()))
    }

    pub fn as_str(&self) -> &str { &self.0 }
}
```

## 七、配置管理：热更新与能力令牌

```rust,ignore
use arc_swap::ArcSwap;
use std::sync::Arc;

pub struct AppConfig {
    pub max_retries: u32,
    pub timeout_ms: u64,
}

static CONFIG: ArcSwap<AppConfig> = ArcSwap::from_pointee(AppConfig {
    max_retries: 3,
    timeout_ms: 1000,
});

pub fn update_config(new: AppConfig) {
    CONFIG.store(Arc::new(new));
}

pub fn current_config() -> Arc<AppConfig> {
    CONFIG.load_full()
}
```

## 八、优雅关闭（Graceful Shutdown）

```rust,ignore
use tokio::sync::mpsc;

pub async fn server_loop(
    mut requests: mpsc::Receiver<Request>,
    mut shutdown: mpsc::Receiver<()>,
) {
    loop {
        tokio::select! {
            Some(req) = requests.recv() => process(req).await,
            _ = shutdown.recv() => {
                drain_remaining(&mut requests).await;
                break;
            }
        }
    }
}
```

## 九、生产部署检查清单

- [ ] 可观测性：结构化日志、指标、追踪已接入
- [ ] 弹性：Circuit Breaker、Retry、Rate Limiter 已配置
- [ ] 性能：关键路径已使用 Criterion 基准测试
- [ ] 安全：输入验证、依赖审计、密钥通过安全通道注入
- [ ] 配置：支持热更新且回滚策略明确
- [ ] 关闭：`SIGTERM` 触发优雅关闭，保证 inflight 请求完成

---

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-07-09 由 `crates/c09_design_pattern/docs/tier_04_advanced/04_engineering_and_production_patterns.md` 迁移整合；本次补全新增可编译 Rust 示例、弹性模式矩阵与决策树

**状态**: ✅ 权威页（canonical）

## 过渡段

> **过渡**: 从开发模式过渡到生产关注点，可以理解代码上线后面临的可靠性、可观测性与可维护性要求。
>
> **过渡**: 从韧性模式过渡到可观测性，可以建立“先防御、后洞察”的运维闭环。
>
> **过渡**: 从可观测性过渡到持续改进，可以将线上反馈反哺设计与实现。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 熔断器 ⟹ 故障隔离 | 快速失败并限制级联影响 | 提升系统整体可用性 |
| 结构化日志 ⟹ 快速恢复 | 统一日志格式与上下文 | 缩短平均故障定位时间 |
| 负载 shedding ⟹ 稳定性 | 在过载时保护核心路径 | 避免雪崩效应 |
