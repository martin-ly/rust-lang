# API设计指南

## 概述

本文档提供Rust安全关键系统API设计的最佳实践，确保接口的安全性、可用性和可维护性。

---

## 1. 安全API设计原则

### 1.1 类型安全

```rust
/// ✅ 使用类型系统防止错误

/// 类型状态模式
pub struct Uninitialized;
pub struct Initialized;
pub struct Running;

pub struct Device<State> {
    _state: PhantomData<State>,
    handle: RawHandle,
}

impl Device<Uninitialized> {
    pub fn new() -> Self {
        // 构造时确保安全
        Self {
            _state: PhantomData,
            handle: unsafe { RawHandle::create() },
        }
    }

    pub fn init(self, config: Config) -> Result<Device<Initialized>, Error> {
        // 验证配置
        config.validate()?;

        Ok(Device {
            _state: PhantomData,
            handle: self.handle,
        })
    }
}

impl Device<Initialized> {
    pub fn start(self) -> Device<Running> {
        Device {
            _state: PhantomData,
            handle: self.handle,
        }
    }
}

/// 无法错误地调用
/// device.start(); // 编译错误!
```

### 1.2 不可变优先

```rust
/// ✅ 默认不可变

pub struct Config {
    timeout: Duration,
    retries: u32,
}

impl Config {
    /// 构造器模式
    pub fn new() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            retries: 3,
        }
    }

    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = timeout;
        self
    }

    pub fn with_retries(mut self, retries: u32) -> Self {
        self.retries = retries;
        self
    }
}

/// 使用
let config = Config::new()
    .with_timeout(Duration::from_secs(60))
    .with_retries(5);
```

---

## 2. 错误处理设计

### 2.1 错误类型设计

```rust
/// 结构化错误类型
#[derive(Debug, Clone)]
pub enum DeviceError {
    /// 配置错误
    Config {
        field: &'static str,
        reason: &'static str,
    },
    /// 通信错误
    Communication {
        endpoint: String,
        kind: CommunicationErrorKind,
    },
    /// 超时错误
    Timeout {
        operation: &'static str,
        duration: Duration,
    },
    /// 内部错误(不暴露细节)
    Internal,
}

#[derive(Debug, Clone)]
pub enum CommunicationErrorKind {
    Disconnected,
    Corrupted,
    Refused,
}

/// 实现std::error::Error
impl std::error::Error for DeviceError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl std::fmt::Display for DeviceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DeviceError::Config { field, reason } => {
                write!(f, "配置错误: 字段 '{}' {}", field, reason)
            }
            DeviceError::Communication { endpoint, kind } => {
                write!(f, "通信错误: 端点 '{}' {:?}", endpoint, kind)
            }
            DeviceError::Timeout { operation, duration } => {
                write!(f, "超时: 操作 '{}' 在 {:?} 后", operation, duration)
            }
            DeviceError::Internal => {
                write!(f, "内部错误")
            }
        }
    }
}
```

### 2.2 错误恢复策略

```rust
/// 可恢复操作
pub trait Recoverable {
    type Error;

    fn retry<F, T>(
        &self,
        operation: F,
        max_attempts: u32,
    ) -> Result<T, Self::Error>
    where
        F: Fn() -> Result<T, Self::Error>,
    {
        let mut last_error = None;

        for attempt in 1..=max_attempts {
            match operation() {
                Ok(result) => return Ok(result),
                Err(e) => {
                    last_error = Some(e);
                    if attempt < max_attempts {
                        self.backoff(attempt);
                    }
                }
            }
        }

        Err(last_error.unwrap())
    }

    fn backoff(&self, attempt: u32) {
        let delay = Duration::from_millis(100 * 2_u64.pow(attempt));
        std::thread::sleep(delay);
    }
}
```

---

## 3. 资源管理

### 3.1 RAII模式

```rust
/// 资源自动管理
pub struct ResourceHandle {
    id: u64,
}

impl ResourceHandle {
    pub fn acquire() -> Result<Self, Error> {
        let id = unsafe { acquire_resource() };
        if id == 0 {
            return Err(Error::ResourceExhausted);
        }
        Ok(Self { id })
    }
}

impl Drop for ResourceHandle {
    fn drop(&mut self) {
        unsafe { release_resource(self.id); }
    }
}

/// 作用域守卫
pub struct ScopeGuard<F: FnOnce()> {
    f: Option<F>,
}

impl<F: FnOnce()> ScopeGuard<F> {
    pub fn new(f: F) -> Self {
        Self { f: Some(f) }
    }

    pub fn dismiss(mut self) {
        self.f = None;
    }
}

impl<F: FnOnce()> Drop for ScopeGuard<F> {
    fn drop(&mut self) {
        if let Some(f) = self.f.take() {
            f();
        }
    }
}

/// 使用
{
    let guard = ScopeGuard::new(|| println!("清理资源"));
    // 操作...
    // 自动调用清理
}
```

### 3.2 借用设计

```rust
/// 智能借用模式

/// 读锁
pub struct ReadGuard<'a, T> {
    inner: &'a T,
}

impl<'a, T> Deref for ReadGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.inner
    }
}

/// 写锁
pub struct WriteGuard<'a, T> {
    inner: &'a mut T,
}

impl<'a, T> Deref for WriteGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.inner
    }
}

impl<'a, T> DerefMut for WriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.inner
    }
}

/// 使用
impl DataStore {
    pub fn read(&self) -> ReadGuard<Data> {
        ReadGuard { inner: &self.data }
    }

    pub fn write(&mut self) -> WriteGuard<Data> {
        WriteGuard { inner: &mut self.data }
    }
}
```

---

## 4. 异步API设计

### 4.1 安全异步接口

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

/// 超时包装器
pub struct Timeout<F> {
    future: F,
    deadline: Instant,
}

impl<F: Future> Future for Timeout<F> {
    type Output = Result<F::Output, TimeoutError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if Instant::now() >= self.deadline {
            return Poll::Ready(Err(TimeoutError));
        }

        // 轮询内部future
        // ...

        Poll::Pending
    }
}

/// 取消安全
pub struct CancelSafe<F> {
    future: F,
    cleanup: Box<dyn FnOnce()>,
}

impl<F: Future> Future for CancelSafe<F> {
    type Output = F::Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 确保取消时调用清理
        // ...
        Poll::Pending
    }
}

impl<F> Drop for CancelSafe<F> {
    fn drop(&mut self) {
        // 执行清理
    }
}
```

### 4.2 流式API

```rust
use futures::stream::Stream;

/// 安全数据流
pub struct SensorStream {
    sensor: Sensor,
    buffer: Vec<Sample, 1024>,
}

impl Stream for SensorStream {
    type Item = Result<Sample, SensorError>;

    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>
    ) -> Poll<Option<Self::Item>> {
        // 安全地读取传感器数据
        // 背压处理
        // 错误恢复
        Poll::Ready(Some(Ok(Sample::default())))
    }
}

/// 使用
async fn process_stream() {
    let stream = SensorStream::new();

    stream
        .filter(|s| s.temperature > 0.0)
        .take(100)
        .for_each(|s| async move {
            println!("Sample: {:?}", s);
        })
        .await;
}
```

---

## 5. 文档和示例

### 5.1 文档规范

```rust
/// 安全关键温度传感器驱动
///
/// # 安全声明
///
/// 此驱动实现了以下安全机制:
/// - 范围验证
/// - 故障检测
/// - 看门狗集成
///
/// # 示例
///
/// ```
/// use safety_drivers::TemperatureSensor;
///
/// let mut sensor = TemperatureSensor::new()
///     .with_range(-40.0, 125.0)
///     .with_watchdog();
///
/// match sensor.read() {
///     Ok(temp) => println!("温度: {}°C", temp),
///     Err(e) => eprintln!("传感器错误: {}", e),
/// }
/// ```
///
/// # 错误处理
///
/// 可能的错误:
/// - `SensorError::Disconnected`: 硬件连接问题
/// - `SensorError::OutOfRange`: 读数超出有效范围
/// - `SensorError::FaultDetected`: 内部故障
///
/// # 实现注意
///
/// - 使用DMA进行数据传输
/// - 中断驱动的读取
/// - 无堆分配
pub struct TemperatureSensor {
    // ...
}
```

### 5.2 示例代码

```rust
/// examples/temperature_monitor.rs

use safety_drivers::{TemperatureSensor, Watchdog};
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化看门狗
    let mut wdg = Watchdog::new(Duration::from_millis(100));

    // 创建传感器
    let mut sensor = TemperatureSensor::new()
        .with_range(-40.0, 125.0)
        .with_watchdog(&mut wdg);

    // 监控循环
    loop {
        match sensor.read() {
            Ok(temp) => {
                if temp > 80.0 {
                    println!("警告: 高温 {}", temp);
                }
            }
            Err(e) => {
                eprintln!("错误: {}", e);
                // 进入安全模式
                break;
            }
        }

        wdg.pet();
        std::thread::sleep(Duration::from_millis(10));
    }

    Ok(())
}
```

---

## 6. 版本兼容性

### 6.1 语义化版本

```rust
/// 版本兼容性指南
///
/// 主版本: 破坏性变更
/// - API移除
/// - 行为改变
/// - 错误类型变更
///
/// 次版本: 功能添加
/// - 新API
/// - 性能改进
/// - 新特性(向后兼容)
///
/// 补丁版本: Bug修复
/// - 安全修复
/// - 文档更新
/// - 内部优化

/// 废弃API处理
#[deprecated(
    since = "2.0.0",
    note = "请使用 `new_method` 替代"
)]
pub fn old_method() {
    // ...
}

/// 新API
pub fn new_method() {
    // ...
}
```

### 6.2 特性标志

```toml
# Cargo.toml
[features]
default = ["std"]

std = []
no-std = []
async = ["futures"]
safety-d = ["formal-verification"]
```

---

## 7. API审查检查表

### 安全性

- [ ] 类型系统防止错误使用
- [ ] 无效状态不可表示
- [ ] 资源正确管理
- [ ] 错误处理完整
- [ ] unsafe代码有文档

### 可用性

- [ ] 命名清晰一致
- [ ] 文档完整有示例
- [ ] 错误信息友好
- [ ] 学习曲线平缓
- [ ] 常见用法简单

### 性能

- [ ] 零成本抽象
- [ ] 无意外分配
- [ ] 支持no_std
- [ ] 编译时优化

### 兼容性

- [ ] 语义化版本
- [ ] 废弃策略
- [ ] 特性标志
- [ ] 平台支持

---

**文档版本**: 1.0
**最后更新**: 2026-03-18

---

*好的API设计是安全关键系统成功的基础。*
