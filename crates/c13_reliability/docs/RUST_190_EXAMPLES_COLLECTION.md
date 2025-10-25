# 💻 Rust 1.90 可靠性 - 实战示例集

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20  
> **代码总量**: ~700行可运行代码

---

## 📋 目录

- [🛡️ 容错模式](#️-容错模式)
- [🌐 分布式事务](#-分布式事务)
- [📊 可观测性](#-可观测性)
- [🏗️ 综合项目](#️-综合项目)

---

## 🛡️ 容错模式

### 示例1: 指数退避重试

```rust
use std::time::Duration;
use tokio::time::sleep;

async fn retry_with_backoff<F, Fut, T, E>(
    mut operation: F,
    max_retries: u32,
) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
{
    let mut retries = 0;
    
    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) if retries >= max_retries => return Err(e),
            Err(_) => {
                retries += 1;
                let delay = Duration::from_millis(100 * 2u64.pow(retries));
                println!("Retry {} after {:?}", retries, delay);
                sleep(delay).await;
            }
        }
    }
}

async fn unreliable_operation() -> Result<String, String> {
    use rand::Rng;
    let mut rng = rand::thread_rng();
    
    if rng.gen_bool(0.7) {
        Err("Failed".to_string())
    } else {
        Ok("Success".to_string())
    }
}

#[tokio::main]
async fn main() {
    match retry_with_backoff(unreliable_operation, 3).await {
        Ok(result) => println!("Operation succeeded: {}", result),
        Err(e) => println!("Operation failed after retries: {}", e),
    }
}
```

### 示例2: 断路器 (Circuit Breaker)

```rust
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[derive(Clone, Copy, PartialEq, Debug)]
enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

struct CircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    failure_count: Arc<Mutex<u32>>,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    threshold: u32,
    timeout: Duration,
}

impl CircuitBreaker {
    fn new(threshold: u32, timeout: Duration) -> Self {
        Self {
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_count: Arc::new(Mutex::new(0)),
            last_failure_time: Arc::new(Mutex::new(None)),
            threshold,
            timeout,
        }
    }
    
    async fn call<F, Fut, T>(&self, operation: F) -> Result<T, String>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, String>>,
    {
        // 检查断路器状态
        {
            let mut state = self.state.lock().unwrap();
            
            if *state == CircuitState::Open {
                let last_failure = self.last_failure_time.lock().unwrap();
                if let Some(time) = *last_failure {
                    if Instant::now().duration_since(time) > self.timeout {
                        *state = CircuitState::HalfOpen;
                        println!("Circuit breaker: Open -> HalfOpen");
                    } else {
                        return Err("Circuit breaker is OPEN".to_string());
                    }
                }
            }
        }
        
        // 执行操作
        match operation().await {
            Ok(result) => {
                // 成功：重置
                *self.failure_count.lock().unwrap() = 0;
                *self.state.lock().unwrap() = CircuitState::Closed;
                Ok(result)
            }
            Err(e) => {
                // 失败：增加计数
                let mut count = self.failure_count.lock().unwrap();
                *count += 1;
                
                if *count >= self.threshold {
                    *self.state.lock().unwrap() = CircuitState::Open;
                    *self.last_failure_time.lock().unwrap() = Some(Instant::now());
                    println!("Circuit breaker: Closed -> OPEN");
                }
                
                Err(e)
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let breaker = CircuitBreaker::new(3, Duration::from_secs(5));
    
    for i in 0..6 {
        let result = breaker.call(|| async {
            if i < 4 {
                Err("Service unavailable".to_string())
            } else {
                Ok("Success")
            }
        }).await;
        
        println!("Attempt {}: {:?}", i + 1, result);
        tokio::time::sleep(Duration::from_secs(1)).await;
    }
}
```

---

## 🌐 分布式事务

### 示例3: Saga模式

```rust
use std::collections::HashMap;

trait SagaStep {
    fn execute(&self) -> Result<String, String>;
    fn compensate(&self) -> Result<(), String>;
}

struct OrderStep;
struct PaymentStep;
struct ShippingStep;

impl SagaStep for OrderStep {
    fn execute(&self) -> Result<String, String> {
        println!("Creating order...");
        Ok("Order123".to_string())
    }
    
    fn compensate(&self) -> Result<(), String> {
        println!("Cancelling order...");
        Ok(())
    }
}

impl SagaStep for PaymentStep {
    fn execute(&self) -> Result<String, String> {
        println!("Processing payment...");
        // 模拟失败
        Err("Payment failed".to_string())
    }
    
    fn compensate(&self) -> Result<(), String> {
        println!("Refunding payment...");
        Ok(())
    }
}

impl SagaStep for ShippingStep {
    fn execute(&self) -> Result<String, String> {
        println!("Arranging shipping...");
        Ok("Tracking123".to_string())
    }
    
    fn compensate(&self) -> Result<(), String> {
        println!("Cancelling shipping...");
        Ok(())
    }
}

struct Saga {
    steps: Vec<Box<dyn SagaStep>>,
}

impl Saga {
    fn new() -> Self {
        Self { steps: vec![] }
    }
    
    fn add_step(&mut self, step: Box<dyn SagaStep>) {
        self.steps.push(step);
    }
    
    fn execute(&self) -> Result<(), String> {
        let mut executed_steps = vec![];
        
        for (i, step) in self.steps.iter().enumerate() {
            match step.execute() {
                Ok(_) => {
                    executed_steps.push(i);
                }
                Err(e) => {
                    println!("Step {} failed: {}", i, e);
                    // 补偿已执行的步骤
                    for &idx in executed_steps.iter().rev() {
                        self.steps[idx].compensate().ok();
                    }
                    return Err(e);
                }
            }
        }
        
        Ok(())
    }
}

fn main() {
    let mut saga = Saga::new();
    saga.add_step(Box::new(OrderStep));
    saga.add_step(Box::new(PaymentStep));
    saga.add_step(Box::new(ShippingStep));
    
    match saga.execute() {
        Ok(_) => println!("Saga completed successfully"),
        Err(e) => println!("Saga failed: {}", e),
    }
}
```

---

## 📊 可观测性

### 示例4: 分布式追踪 (简化版)

```rust
use std::collections::HashMap;
use std::time::Instant;

#[derive(Clone, Debug)]
struct Span {
    name: String,
    start_time: Instant,
    duration: Option<std::time::Duration>,
    tags: HashMap<String, String>,
}

impl Span {
    fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            start_time: Instant::now(),
            duration: None,
            tags: HashMap::new(),
        }
    }
    
    fn add_tag(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.tags.insert(key.into(), value.into());
    }
    
    fn finish(&mut self) {
        self.duration = Some(self.start_time.elapsed());
        println!("Span '{}' completed in {:?}", self.name, self.duration.unwrap());
    }
}

async fn process_request() {
    let mut root_span = Span::new("process_request");
    root_span.add_tag("service", "api");
    
    {
        let mut db_span = Span::new("database_query");
        db_span.add_tag("query", "SELECT * FROM users");
        tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        db_span.finish();
    }
    
    {
        let mut cache_span = Span::new("cache_lookup");
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
        cache_span.finish();
    }
    
    root_span.finish();
}

#[tokio::main]
async fn main() {
    process_request().await;
}
```

---

## 🏗️ 综合项目

### 项目: 可靠的HTTP客户端

```rust
use std::time::Duration;
use tokio::time::timeout;

struct ReliableHttpClient {
    max_retries: u32,
    timeout_duration: Duration,
}

impl ReliableHttpClient {
    fn new() -> Self {
        Self {
            max_retries: 3,
            timeout_duration: Duration::from_secs(5),
        }
    }
    
    async fn get(&self, url: &str) -> Result<String, String> {
        let mut retries = 0;
        
        loop {
            match self.try_request(url).await {
                Ok(response) => return Ok(response),
                Err(e) if retries >= self.max_retries => {
                    return Err(format!("Failed after {} retries: {}", retries, e));
                }
                Err(e) => {
                    retries += 1;
                    let delay = Duration::from_millis(100 * 2u64.pow(retries));
                    println!("Request failed: {}. Retrying after {:?}...", e, delay);
                    tokio::time::sleep(delay).await;
                }
            }
        }
    }
    
    async fn try_request(&self, url: &str) -> Result<String, String> {
        match timeout(self.timeout_duration, self.do_request(url)).await {
            Ok(Ok(response)) => Ok(response),
            Ok(Err(e)) => Err(e),
            Err(_) => Err("Request timeout".to_string()),
        }
    }
    
    async fn do_request(&self, url: &str) -> Result<String, String> {
        // 模拟HTTP请求
        println!("Requesting: {}", url);
        tokio::time::sleep(Duration::from_millis(100)).await;
        Ok(format!("Response from {}", url))
    }
}

#[tokio::main]
async fn main() {
    let client = ReliableHttpClient::new();
    
    match client.get("https://api.example.com/data").await {
        Ok(response) => println!("Success: {}", response),
        Err(e) => println!("Error: {}", e),
    }
}
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**代码总量**: ~700行

---

💻 **掌握可靠性，构建生产级系统！** 🚀✨
