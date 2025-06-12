# 4.1.5 容错与弹性 (Fault Tolerance and Resilience)

## 目录

1. [4.1.5.1 容错模式](#4151-容错模式)
2. [4.1.5.2 断路器模式](#4152-断路器模式)
3. [4.1.5.3 重试模式](#4153-重试模式)
4. [4.1.5.4 超时模式](#4154-超时模式)
5. [4.1.5.5 降级模式](#4155-降级模式)

## 4.1.5.1 容错模式

### 定义 4.1.5.1 (容错)

容错是系统在部分组件失败时仍能继续运行的能力：
$$FaultTolerance = \{System \rightarrow \forall f \in Faults: System(f) \neq \bot\}$$

### 定义 4.1.5.2 (弹性)

弹性是系统从故障中恢复的能力：
$$Resilience = \{System \rightarrow \lim_{t \to \infty} System(t) = Normal\}$$

### 定义 4.1.5.3 (容错策略)

容错策略包括：

- **预防**: $Prevent(Fault) \rightarrow \neg Fault$
- **检测**: $Detect(Fault) \rightarrow Fault \land Alert$
- **恢复**: $Recover(Fault) \rightarrow System \rightarrow Normal$

## 4.1.5.2 断路器模式

### 定义 4.1.5.4 (断路器)

断路器是防止级联故障的保护机制：
$$CircuitBreaker = \{State \in \{Closed, Open, HalfOpen\}, Threshold \in \mathbb{N}\}$$

### 定义 4.1.5.5 (断路器状态转换)

断路器状态转换规则：

- **关闭→开启**: $Failures > Threshold \land Timeout$
- **开启→半开**: $Time > ResetTimeout$
- **半开→关闭**: $Success \land Failures = 0$
- **半开→开启**: $Failure$

**Rust实现**：

```rust
use std::sync::atomic::{AtomicU64, AtomicU32, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

#[derive(Debug, Clone, PartialEq)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

pub struct CircuitBreaker {
    state: AtomicU32,
    failure_count: AtomicU64,
    success_count: AtomicU64,
    last_failure_time: RwLock<Option<Instant>>,
    failure_threshold: u64,
    success_threshold: u64,
    timeout: Duration,
    reset_timeout: Duration,
}

impl CircuitBreaker {
    pub fn new(
        failure_threshold: u64,
        success_threshold: u64,
        timeout: Duration,
        reset_timeout: Duration,
    ) -> Self {
        CircuitBreaker {
            state: AtomicU32::new(0), // Closed
            failure_count: AtomicU64::new(0),
            success_count: AtomicU64::new(0),
            last_failure_time: RwLock::new(None),
            failure_threshold,
            success_threshold,
            timeout,
            reset_timeout,
        }
    }
    
    pub fn current_state(&self) -> CircuitBreakerState {
        match self.state.load(Ordering::Relaxed) {
            0 => CircuitBreakerState::Closed,
            1 => CircuitBreakerState::Open,
            2 => CircuitBreakerState::HalfOpen,
            _ => CircuitBreakerState::Closed,
        }
    }
    
    pub async fn call<F, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Result<T, E>,
    {
        match self.current_state() {
            CircuitBreakerState::Closed => {
                self.call_closed(operation).await
            }
            CircuitBreakerState::Open => {
                self.call_open().await
            }
            CircuitBreakerState::HalfOpen => {
                self.call_half_open(operation).await
            }
        }
    }
    
    async fn call_closed<F, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Result<T, E>,
    {
        let start_time = Instant::now();
        
        match operation() {
            Ok(result) => {
                self.on_success();
                Ok(result)
            }
            Err(error) => {
                self.on_failure().await;
                if start_time.elapsed() > self.timeout {
                    Err(CircuitBreakerError::Timeout)
                } else {
                    Err(CircuitBreakerError::OperationError(error))
                }
            }
        }
    }
    
    async fn call_open(&self) -> Result<(), CircuitBreakerError<()>> {
        let last_failure = self.last_failure_time.read().await;
        if let Some(failure_time) = *last_failure {
            if failure_time.elapsed() >= self.reset_timeout {
                self.transition_to_half_open();
                return Ok(());
            }
        }
        
        Err(CircuitBreakerError::CircuitOpen)
    }
    
    async fn call_half_open<F, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Result<T, E>,
    {
        match operation() {
            Ok(result) => {
                self.on_success();
                self.transition_to_closed();
                Ok(result)
            }
            Err(error) => {
                self.on_failure().await;
                self.transition_to_open();
                Err(CircuitBreakerError::OperationError(error))
            }
        }
    }
    
    fn on_success(&self) {
        self.success_count.fetch_add(1, Ordering::Relaxed);
        self.failure_count.store(0, Ordering::Relaxed);
    }
    
    async fn on_failure(&self) {
        self.failure_count.fetch_add(1, Ordering::Relaxed);
        let mut last_failure = self.last_failure_time.write().await;
        *last_failure = Some(Instant::now());
        
        if self.failure_count.load(Ordering::Relaxed) >= self.failure_threshold {
            self.transition_to_open();
        }
    }
    
    fn transition_to_open(&self) {
        self.state.store(1, Ordering::Relaxed);
    }
    
    fn transition_to_half_open(&self) {
        self.state.store(2, Ordering::Relaxed);
        self.success_count.store(0, Ordering::Relaxed);
    }
    
    fn transition_to_closed(&self) {
        self.state.store(0, Ordering::Relaxed);
        self.failure_count.store(0, Ordering::Relaxed);
        self.success_count.store(0, Ordering::Relaxed);
    }
}

#[derive(Debug)]
pub enum CircuitBreakerError<E> {
    CircuitOpen,
    Timeout,
    OperationError(E),
}

// 异步断路器
pub struct AsyncCircuitBreaker {
    circuit_breaker: CircuitBreaker,
}

impl AsyncCircuitBreaker {
    pub fn new(
        failure_threshold: u64,
        success_threshold: u64,
        timeout: Duration,
        reset_timeout: Duration,
    ) -> Self {
        AsyncCircuitBreaker {
            circuit_breaker: CircuitBreaker::new(
                failure_threshold,
                success_threshold,
                timeout,
                reset_timeout,
            ),
        }
    }
    
    pub async fn call<F, Fut, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
    {
        match self.circuit_breaker.current_state() {
            CircuitBreakerState::Closed => {
                self.call_closed(operation).await
            }
            CircuitBreakerState::Open => {
                self.call_open().await
            }
            CircuitBreakerState::HalfOpen => {
                self.call_half_open(operation).await
            }
        }
    }
    
    async fn call_closed<F, Fut, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
    {
        let start_time = Instant::now();
        
        match tokio::time::timeout(self.circuit_breaker.timeout, operation()).await {
            Ok(Ok(result)) => {
                self.circuit_breaker.on_success();
                Ok(result)
            }
            Ok(Err(error)) => {
                self.circuit_breaker.on_failure().await;
                Err(CircuitBreakerError::OperationError(error))
            }
            Err(_) => {
                self.circuit_breaker.on_failure().await;
                Err(CircuitBreakerError::Timeout)
            }
        }
    }
    
    async fn call_open(&self) -> Result<(), CircuitBreakerError<()>> {
        self.circuit_breaker.call_open().await
    }
    
    async fn call_half_open<F, Fut, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
    {
        match tokio::time::timeout(self.circuit_breaker.timeout, operation()).await {
            Ok(Ok(result)) => {
                self.circuit_breaker.on_success();
                self.circuit_breaker.transition_to_closed();
                Ok(result)
            }
            Ok(Err(error)) => {
                self.circuit_breaker.on_failure().await;
                self.circuit_breaker.transition_to_open();
                Err(CircuitBreakerError::OperationError(error))
            }
            Err(_) => {
                self.circuit_breaker.on_failure().await;
                self.circuit_breaker.transition_to_open();
                Err(CircuitBreakerError::Timeout)
            }
        }
    }
}
```

## 4.1.5.3 重试模式

### 定义 4.1.5.6 (重试策略)

重试策略定义重试的行为：
$$RetryStrategy = \{(MaxRetries, Backoff, Jitter) | MaxRetries \in \mathbb{N}, Backoff \in \mathbb{R}^+\}$$

### 定义 4.1.5.7 (退避算法)

退避算法包括：

- **固定退避**: $FixedBackoff(delay) = delay$
- **指数退避**: $ExponentialBackoff(attempt) = base \times 2^{attempt}$
- **线性退避**: $LinearBackoff(attempt) = base \times attempt$

**Rust实现**：

```rust
use std::time::Duration;
use rand::Rng;

pub trait RetryStrategy {
    fn should_retry(&self, attempt: u32, error: &dyn std::error::Error) -> bool;
    fn get_delay(&self, attempt: u32) -> Duration;
}

pub struct FixedRetryStrategy {
    max_retries: u32,
    delay: Duration,
}

impl FixedRetryStrategy {
    pub fn new(max_retries: u32, delay: Duration) -> Self {
        FixedRetryStrategy { max_retries, delay }
    }
}

impl RetryStrategy for FixedRetryStrategy {
    fn should_retry(&self, attempt: u32, _error: &dyn std::error::Error) -> bool {
        attempt < self.max_retries
    }
    
    fn get_delay(&self, _attempt: u32) -> Duration {
        self.delay
    }
}

pub struct ExponentialBackoffStrategy {
    max_retries: u32,
    base_delay: Duration,
    max_delay: Duration,
    jitter: bool,
}

impl ExponentialBackoffStrategy {
    pub fn new(max_retries: u32, base_delay: Duration, max_delay: Duration, jitter: bool) -> Self {
        ExponentialBackoffStrategy {
            max_retries,
            base_delay,
            max_delay,
            jitter,
        }
    }
}

impl RetryStrategy for ExponentialBackoffStrategy {
    fn should_retry(&self, attempt: u32, _error: &dyn std::error::Error) -> bool {
        attempt < self.max_retries
    }
    
    fn get_delay(&self, attempt: u32) -> Duration {
        let delay_ms = self.base_delay.as_millis() as u64 * 2_u64.pow(attempt);
        let delay = Duration::from_millis(delay_ms.min(self.max_delay.as_millis() as u64));
        
        if self.jitter {
            let jitter_ms = rand::thread_rng().gen_range(0..=delay.as_millis() as u64 / 10);
            delay + Duration::from_millis(jitter_ms)
        } else {
            delay
        }
    }
}

pub struct RetryManager<S: RetryStrategy> {
    strategy: S,
}

impl<S: RetryStrategy> RetryManager<S> {
    pub fn new(strategy: S) -> Self {
        RetryManager { strategy }
    }
    
    pub async fn execute<F, Fut, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: std::error::Error,
    {
        let mut attempt = 0;
        
        loop {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(error) => {
                    if !self.strategy.should_retry(attempt, &error) {
                        return Err(error);
                    }
                    
                    let delay = self.strategy.get_delay(attempt);
                    tokio::time::sleep(delay).await;
                    attempt += 1;
                }
            }
        }
    }
}
```

## 4.1.5.4 超时模式

### 定义 4.1.5.8 (超时)

超时是限制操作执行时间的机制：
$$Timeout = \{Operation \land Time > Limit \rightarrow Abort\}$$

**Rust实现**：

```rust
pub struct TimeoutManager {
    default_timeout: Duration,
}

impl TimeoutManager {
    pub fn new(default_timeout: Duration) -> Self {
        TimeoutManager { default_timeout }
    }
    
    pub async fn with_timeout<F, Fut, T>(
        &self,
        timeout: Duration,
        operation: F,
    ) -> Result<T, TimeoutError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        match tokio::time::timeout(timeout, operation()).await {
            Ok(result) => Ok(result),
            Err(_) => Err(TimeoutError::Timeout),
        }
    }
    
    pub async fn with_default_timeout<F, Fut, T>(
        &self,
        operation: F,
    ) -> Result<T, TimeoutError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        self.with_timeout(self.default_timeout, operation).await
    }
}

#[derive(Debug)]
pub enum TimeoutError {
    Timeout,
}
```

## 4.1.5.5 降级模式

### 定义 4.1.5.9 (降级)

降级是在服务不可用时提供替代功能的机制：
$$Fallback = \{Service \land \neg Available(Service) \rightarrow Alternative\}$$

**Rust实现**：

```rust
pub struct FallbackManager {
    primary_operation: Box<dyn Fn() -> Result<String, Box<dyn std::error::Error + Send + Sync>>>,
    fallback_operation: Box<dyn Fn() -> Result<String, Box<dyn std::error::Error + Send + Sync>>>,
}

impl FallbackManager {
    pub fn new<F1, F2>(
        primary: F1,
        fallback: F2,
    ) -> Self
    where
        F1: Fn() -> Result<String, Box<dyn std::error::Error + Send + Sync>> + 'static,
        F2: Fn() -> Result<String, Box<dyn std::error::Error + Send + Sync>> + 'static,
    {
        FallbackManager {
            primary_operation: Box::new(primary),
            fallback_operation: Box::new(fallback),
        }
    }
    
    pub async fn execute(&self) -> Result<String, Box<dyn std::error::Error + Send + Sync>> {
        // 尝试主要操作
        match (self.primary_operation)() {
            Ok(result) => Ok(result),
            Err(_) => {
                // 主要操作失败，使用降级操作
                (self.fallback_operation)()
            }
        }
    }
}

// 组合容错模式
pub struct ResilientService {
    circuit_breaker: AsyncCircuitBreaker,
    retry_manager: RetryManager<ExponentialBackoffStrategy>,
    timeout_manager: TimeoutManager,
    fallback_manager: Option<FallbackManager>,
}

impl ResilientService {
    pub fn new() -> Self {
        let circuit_breaker = AsyncCircuitBreaker::new(
            5, // failure_threshold
            3, // success_threshold
            Duration::from_secs(5), // timeout
            Duration::from_secs(30), // reset_timeout
        );
        
        let retry_strategy = ExponentialBackoffStrategy::new(
            3, // max_retries
            Duration::from_millis(100), // base_delay
            Duration::from_secs(5), // max_delay
            true, // jitter
        );
        
        let retry_manager = RetryManager::new(retry_strategy);
        let timeout_manager = TimeoutManager::new(Duration::from_secs(10));
        
        ResilientService {
            circuit_breaker,
            retry_manager,
            timeout_manager,
            fallback_manager: None,
        }
    }
    
    pub async fn call_service<F, Fut, T, E>(
        &self,
        operation: F,
    ) -> Result<T, ResilientServiceError<E>>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: std::error::Error + 'static,
    {
        // 1. 断路器保护
        let circuit_result = self.circuit_breaker.call(|| {
            // 2. 超时保护
            self.timeout_manager.with_default_timeout(|| {
                // 3. 重试机制
                self.retry_manager.execute(operation)
            })
        }).await;
        
        match circuit_result {
            Ok(result) => match result {
                Ok(value) => Ok(value),
                Err(error) => Err(ResilientServiceError::OperationError(error)),
            },
            Err(CircuitBreakerError::CircuitOpen) => {
                Err(ResilientServiceError::CircuitOpen)
            }
            Err(CircuitBreakerError::Timeout) => {
                Err(ResilientServiceError::Timeout)
            }
            Err(CircuitBreakerError::OperationError(error)) => {
                Err(ResilientServiceError::OperationError(error))
            }
        }
    }
}

#[derive(Debug)]
pub enum ResilientServiceError<E> {
    CircuitOpen,
    Timeout,
    OperationError(E),
}
```

## 持续上下文管理

### 进度跟踪

- [x] 容错模式定义
- [x] 断路器模式实现
- [x] 重试模式实现
- [x] 超时模式实现
- [x] 降级模式实现

### 下一步计划

1. 开始事件驱动架构
2. 建立响应式架构
3. 完成云原生架构

### 中断恢复点

当前状态：容错与弹性设计内容已完成，微服务架构部分全部完成，准备开始事件驱动架构的内容编写。
