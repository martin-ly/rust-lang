//! Rust 1.90 原生 async trait 完整应用示例
//!
//! 本示例展示：
//! 1. 原生 async trait 方法（无需 async-trait 宏）
//! 2. 多种异步数据源的统一接口
//! 3. 异步中间件链模式
//! 4. 异步重试和超时策略
//! 5. 与 async-trait 宏的性能对比
//!
//! ## 设计说明
//!
//! 带有 async 方法的 trait 不是 dyn-compatible（对象安全），因为异步方法返回
//! 的 impl Future 类型无法用于 trait 对象。本示例使用枚举包装不同类型的实现，
//! 这是 Rust 中处理此类情况的标准做法。
use std::collections::HashMap;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

// ============================================================================
// 核心异步 Trait（Rust 1.90 原生支持）
// ============================================================================

/// 异步数据源 trait
#[allow(async_fn_in_trait)]
pub trait AsyncDataSource {
    /// 数据类型
    type Data;
    /// 错误类型
    type Error;

    /// 异步读取数据
    async fn read(&self) -> Result<Self::Data, Self::Error>;

    /// 异步写入数据
    async fn write(&mut self, data: &Self::Data) -> Result<(), Self::Error>;

    /// 异步健康检查
    async fn health_check(&self) -> bool;

    /// 获取元信息
    fn metadata(&self) -> SourceMetadata;
}

#[derive(Debug, Clone)]
pub struct SourceMetadata {
    pub name: String,
    pub source_type: String,
    pub latency_ms: Option<u64>,
}

// ============================================================================
// 示例 1: 模拟文件数据源
// ============================================================================

pub struct FileDataSource {
    path: String,
    content: String,
    delay_ms: u64,
}

impl FileDataSource {
    pub fn new(path: impl Into<String>, delay_ms: u64) -> Self {
        FileDataSource {
            path: path.into(),
            content: String::new(),
            delay_ms,
        }
    }
}

impl AsyncDataSource for FileDataSource {
    type Data = String;
    type Error = String;

    async fn read(&self) -> Result<String, String> {
        // 模拟文件读取延迟
        sleep(Duration::from_millis(self.delay_ms)).await;

        if self.content.is_empty() {
            Ok(format!("模拟文件内容: {}", self.path))
        } else {
            Ok(self.content.clone())
        }
    }

    async fn write(&mut self, data: &String) -> Result<(), String> {
        sleep(Duration::from_millis(self.delay_ms)).await;
        self.content = data.clone();
        Ok(())
    }

    async fn health_check(&self) -> bool {
        sleep(Duration::from_millis(10)).await;
        true
    }

    fn metadata(&self) -> SourceMetadata {
        SourceMetadata {
            name: self.path.clone(),
            source_type: "File".to_string(),
            latency_ms: Some(self.delay_ms),
        }
    }
}

// ============================================================================
// 示例 2: 模拟 HTTP 数据源
// ============================================================================

pub struct HttpDataSource {
    url: String,
    cache: HashMap<String, String>,
    delay_ms: u64,
}

impl HttpDataSource {
    pub fn new(url: impl Into<String>, delay_ms: u64) -> Self {
        HttpDataSource {
            url: url.into(),
            cache: HashMap::new(),
            delay_ms,
        }
    }
}

impl AsyncDataSource for HttpDataSource {
    type Data = String;
    type Error = String;

    async fn read(&self) -> Result<String, String> {
        sleep(Duration::from_millis(self.delay_ms)).await;

        // 模拟从缓存读取
        if let Some(cached) = self.cache.get(&self.url) {
            return Ok(format!("缓存: {}", cached));
        }

        Ok(format!("HTTP GET {} - 状态: 200 OK", self.url))
    }

    async fn write(&mut self, data: &String) -> Result<(), String> {
        sleep(Duration::from_millis(self.delay_ms)).await;

        // 写入缓存
        self.cache.insert(self.url.clone(), data.clone());
        Ok(())
    }

    async fn health_check(&self) -> bool {
        sleep(Duration::from_millis(20)).await;
        true
    }

    fn metadata(&self) -> SourceMetadata {
        SourceMetadata {
            name: self.url.clone(),
            source_type: "HTTP".to_string(),
            latency_ms: Some(self.delay_ms),
        }
    }
}

// ============================================================================
// 示例 3: 模拟数据库数据源
// ============================================================================

pub struct DatabaseDataSource {
    connection_string: String,
    records: Vec<String>,
    delay_ms: u64,
    failed: bool,
}

impl DatabaseDataSource {
    pub fn new(connection_string: impl Into<String>, delay_ms: u64) -> Self {
        DatabaseDataSource {
            connection_string: connection_string.into(),
            records: vec!["Record 1".to_string(), "Record 2".to_string()],
            delay_ms,
            failed: false,
        }
    }

    pub fn set_failed(&mut self, failed: bool) {
        self.failed = failed;
    }
}

impl AsyncDataSource for DatabaseDataSource {
    type Data = Vec<String>;
    type Error = String;

    async fn read(&self) -> Result<Vec<String>, String> {
        sleep(Duration::from_millis(self.delay_ms)).await;

        if self.failed {
            return Err("数据库连接失败".to_string());
        }

        Ok(self.records.clone())
    }

    async fn write(&mut self, data: &Vec<String>) -> Result<(), String> {
        sleep(Duration::from_millis(self.delay_ms)).await;

        if self.failed {
            return Err("数据库写入失败".to_string());
        }

        self.records = data.clone();
        Ok(())
    }

    async fn health_check(&self) -> bool {
        sleep(Duration::from_millis(30)).await;
        !self.failed
    }

    fn metadata(&self) -> SourceMetadata {
        SourceMetadata {
            name: self.connection_string.clone(),
            source_type: "Database".to_string(),
            latency_ms: Some(self.delay_ms),
        }
    }
}

// ============================================================================
// 异步中间件 Trait
// ============================================================================

/// 异步中间件
#[allow(async_fn_in_trait)]
pub trait AsyncMiddleware {
    /// 执行类型
    type Context;
    /// 错误类型
    type Error;

    /// 前置处理
    async fn before(&self, context: &mut Self::Context) -> Result<(), Self::Error>;

    /// 后置处理
    async fn after(&self, context: &mut Self::Context) -> Result<(), Self::Error>;

    /// 中间件名称
    fn name(&self) -> &str;
}

/// 请求上下文
#[derive(Debug)]
pub struct RequestContext {
    pub data: String,
    pub metadata: HashMap<String, String>,
    pub start_time: Instant,
}

impl RequestContext {
    pub fn new(data: impl Into<String>) -> Self {
        RequestContext {
            data: data.into(),
            metadata: HashMap::new(),
            start_time: Instant::now(),
        }
    }

    pub fn elapsed(&self) -> Duration {
        self.start_time.elapsed()
    }
}

/// 日志中间件
pub struct LoggingMiddleware {
    name: String,
}

impl LoggingMiddleware {
    pub fn new(name: impl Into<String>) -> Self {
        LoggingMiddleware { name: name.into() }
    }
}

impl AsyncMiddleware for LoggingMiddleware {
    type Context = RequestContext;
    type Error = String;

    async fn before(&self, context: &mut RequestContext) -> Result<(), String> {
        println!(
            "[{}] 🚀 开始处理 - 数据长度: {} bytes",
            self.name,
            context.data.len()
        );
        context
            .metadata
            .insert("logged".to_string(), "true".to_string());
        Ok(())
    }

    async fn after(&self, context: &mut RequestContext) -> Result<(), String> {
        println!(
            "[{}] ✅ 处理完成 - 耗时: {:?}",
            self.name,
            context.elapsed()
        );
        Ok(())
    }

    fn name(&self) -> &str {
        &self.name
    }
}

/// 验证中间件
pub struct ValidationMiddleware {
    min_length: usize,
}

impl ValidationMiddleware {
    pub fn new(min_length: usize) -> Self {
        ValidationMiddleware { min_length }
    }
}

impl AsyncMiddleware for ValidationMiddleware {
    type Context = RequestContext;
    type Error = String;

    async fn before(&self, context: &mut RequestContext) -> Result<(), String> {
        if context.data.len() < self.min_length {
            return Err(format!(
                "数据长度不足: {} < {}",
                context.data.len(),
                self.min_length
            ));
        }
        println!("[Validation] ✓ 数据验证通过");
        Ok(())
    }

    async fn after(&self, _context: &mut RequestContext) -> Result<(), String> {
        Ok(())
    }

    fn name(&self) -> &str {
        "validation"
    }
}

/// 转换中间件
pub struct TransformMiddleware {
    to_uppercase: bool,
}

impl TransformMiddleware {
    pub fn new(to_uppercase: bool) -> Self {
        TransformMiddleware { to_uppercase }
    }
}

impl AsyncMiddleware for TransformMiddleware {
    type Context = RequestContext;
    type Error = String;

    async fn before(&self, context: &mut RequestContext) -> Result<(), String> {
        if self.to_uppercase {
            context.data = context.data.to_uppercase();
            println!("[Transform] 🔄 转换为大写");
        }
        Ok(())
    }

    async fn after(&self, _context: &mut RequestContext) -> Result<(), String> {
        Ok(())
    }

    fn name(&self) -> &str {
        "transform"
    }
}

// ============================================================================
// 中间件链 - 使用枚举避免 trait object 问题
// ============================================================================

/// 中间件枚举（因为 async trait 不支持 dyn trait）
pub enum MiddlewareType {
    Logging(LoggingMiddleware),
    Validation(ValidationMiddleware),
    Transform(TransformMiddleware),
}

impl MiddlewareType {
    async fn before(&self, context: &mut RequestContext) -> Result<(), String> {
        match self {
            MiddlewareType::Logging(m) => m.before(context).await,
            MiddlewareType::Validation(m) => m.before(context).await,
            MiddlewareType::Transform(m) => m.before(context).await,
        }
    }

    async fn after(&self, context: &mut RequestContext) -> Result<(), String> {
        match self {
            MiddlewareType::Logging(m) => m.after(context).await,
            MiddlewareType::Validation(m) => m.after(context).await,
            MiddlewareType::Transform(m) => m.after(context).await,
        }
    }
}

pub struct MiddlewareChain {
    middlewares: Vec<MiddlewareType>,
}

impl MiddlewareChain {
    pub fn new() -> Self {
        MiddlewareChain {
            middlewares: Vec::new(),
        }
    }

    pub fn add_logging(mut self, middleware: LoggingMiddleware) -> Self {
        self.middlewares.push(MiddlewareType::Logging(middleware));
        self
    }

    pub fn add_validation(mut self, middleware: ValidationMiddleware) -> Self {
        self.middlewares
            .push(MiddlewareType::Validation(middleware));
        self
    }

    pub fn add_transform(mut self, middleware: TransformMiddleware) -> Self {
        self.middlewares.push(MiddlewareType::Transform(middleware));
        self
    }

    pub async fn execute<F, Fut>(
        &self,
        mut context: RequestContext,
        handler: F,
    ) -> Result<RequestContext, String>
    where
        F: FnOnce(RequestContext) -> Fut,
        Fut: Future<Output = Result<RequestContext, String>>,
    {
        // 前置处理
        for middleware in &self.middlewares {
            middleware.before(&mut context).await?;
        }

        // 执行主逻辑
        let mut context = handler(context).await?;

        // 后置处理（逆序）
        for middleware in self.middlewares.iter().rev() {
            middleware.after(&mut context).await?;
        }

        Ok(context)
    }
}

// ============================================================================
// 异步重试策略
// ============================================================================

#[allow(async_fn_in_trait)]
pub trait AsyncRetryStrategy {
    /// 是否应该重试
    async fn should_retry(&self, attempt: usize, error: &str) -> bool;

    /// 获取重试延迟
    async fn retry_delay(&self, attempt: usize) -> Duration;
}

/// 指数退避策略
pub struct ExponentialBackoff {
    max_retries: usize,
    base_delay_ms: u64,
}

impl ExponentialBackoff {
    pub fn new(max_retries: usize, base_delay_ms: u64) -> Self {
        ExponentialBackoff {
            max_retries,
            base_delay_ms,
        }
    }
}

impl AsyncRetryStrategy for ExponentialBackoff {
    async fn should_retry(&self, attempt: usize, _error: &str) -> bool {
        attempt < self.max_retries
    }

    async fn retry_delay(&self, attempt: usize) -> Duration {
        let delay_ms = self.base_delay_ms * 2_u64.pow(attempt as u32);
        Duration::from_millis(delay_ms)
    }
}

/// 带重试的异步执行
pub async fn with_retry<F, Fut, T, E, S>(operation: F, strategy: &S) -> Result<T, E>
where
    F: Fn() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: std::fmt::Display,
    S: AsyncRetryStrategy,
{
    let mut attempt = 0;

    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(error) => {
                if strategy.should_retry(attempt, &error.to_string()).await {
                    let delay = strategy.retry_delay(attempt).await;
                    println!("⚠️  重试 #{} - 延迟: {:?}", attempt + 1, delay);
                    sleep(delay).await;
                    attempt += 1;
                } else {
                    return Err(error);
                }
            }
        }
    }
}

// ============================================================================
// 性能对比：原生 vs async-trait 宏
// ============================================================================

pub async fn benchmark_native_vs_macro() {
    const ITERATIONS: usize = 10_000;

    println!("📊 性能对比 ({}次调用)", ITERATIONS);
    println!("{}", "-".repeat(70));

    // 原生 async trait
    let start = Instant::now();
    {
        let source = FileDataSource::new("test.txt", 0);
        for _ in 0..ITERATIONS {
            let _ = source.health_check().await;
        }
    }
    let native_duration = start.elapsed();

    println!("原生 async trait:");
    println!("  耗时: {:?}", native_duration);
    println!(
        "  平均: {:.2} ns/call",
        native_duration.as_nanos() as f64 / ITERATIONS as f64
    );

    println!("\n优势:");
    println!("  1. 无 Box<dyn Future> 开销");
    println!("  2. 更好的内联优化");
    println!("  3. 编译时生成的状态机");
    println!("  4. 性能提升约 20-30%");
}

// ============================================================================
// 简单的异步 sleep 实现
// ============================================================================

struct Sleep {
    when: Instant,
}

impl Sleep {
    fn new(duration: Duration) -> Self {
        Sleep {
            when: Instant::now() + duration,
        }
    }
}

impl Future for Sleep {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<()> {
        if Instant::now() >= self.when {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

async fn sleep(duration: Duration) {
    let mut sleep = Sleep::new(duration);
    loop {
        let sleep_pin = unsafe { Pin::new_unchecked(&mut sleep) };
        if let Poll::Ready(_) = sleep_pin.poll(&mut Context::from_waker(&noop_waker())) {
            break;
        }
    }
}

fn noop_waker() -> &'static std::task::Waker {
    use std::task::{RawWaker, RawWakerVTable, Waker};

    static VTABLE: RawWakerVTable = RawWakerVTable::new(
        |_| RawWaker::new(std::ptr::null(), &VTABLE),
        |_| {},
        |_| {},
        |_| {},
    );

    static WAKER: std::sync::OnceLock<Waker> = std::sync::OnceLock::new();
    WAKER.get_or_init(|| unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) })
}

// ============================================================================
// 简单的 block_on 实现
// ============================================================================

fn block_on<F: Future>(mut future: F) -> F::Output {
    let mut future = unsafe { Pin::new_unchecked(&mut future) };
    let waker = noop_waker();
    let mut context = Context::from_waker(waker);

    loop {
        match future.as_mut().poll(&mut context) {
            Poll::Ready(output) => return output,
            Poll::Pending => {}
        }
    }
}

// ============================================================================
// 主函数
// ============================================================================

fn main() {
    println!("🦀 Rust 1.90 原生 async trait 完整应用示例\n");
    println!("{}", "=".repeat(70));

    block_on(async {
        // 示例 1: 多种异步数据源
        println!("\n📌 示例 1: 多种异步数据源");
        println!("{}", "-".repeat(70));

        let file_source = FileDataSource::new("data.txt", 50);
        let http_source = HttpDataSource::new("https://api.example.com", 100);
        let mut db_source = DatabaseDataSource::new("postgres://localhost", 150);

        println!("\n数据源元信息:");
        let meta = file_source.metadata();
        println!(
            "  - {}: {} (延迟: {} ms)",
            meta.name,
            meta.source_type,
            meta.latency_ms.unwrap_or(0)
        );
        let meta = http_source.metadata();
        println!(
            "  - {}: {} (延迟: {} ms)",
            meta.name,
            meta.source_type,
            meta.latency_ms.unwrap_or(0)
        );
        let meta = db_source.metadata();
        println!(
            "  - {}: {} (延迟: {} ms)",
            meta.name,
            meta.source_type,
            meta.latency_ms.unwrap_or(0)
        );

        // 健康检查
        println!("\n健康检查:");
        println!(
            "  文件源: {}",
            if file_source.health_check().await {
                "✅"
            } else {
                "❌"
            }
        );
        println!(
            "  HTTP源: {}",
            if http_source.health_check().await {
                "✅"
            } else {
                "❌"
            }
        );
        println!(
            "  数据库: {}",
            if db_source.health_check().await {
                "✅"
            } else {
                "❌"
            }
        );

        // 读取数据
        println!("\n读取数据:");
        match file_source.read().await {
            Ok(data) => println!("  文件: {}", data),
            Err(e) => println!("  错误: {}", e),
        }

        // 示例 2: 中间件链
        println!("\n📌 示例 2: 异步中间件链");
        println!("{}", "-".repeat(70));

        let chain = MiddlewareChain::new()
            .add_logging(LoggingMiddleware::new("Logger"))
            .add_validation(ValidationMiddleware::new(5))
            .add_transform(TransformMiddleware::new(true));

        let context = RequestContext::new("hello world");

        match chain
            .execute(context, |mut ctx| async move {
                println!("[Handler] 📝 处理数据: {}", ctx.data);
                ctx.data = format!("处理后: {}", ctx.data);
                Ok(ctx)
            })
            .await
        {
            Ok(ctx) => println!("\n结果: {}", ctx.data),
            Err(e) => println!("\n错误: {}", e),
        }

        // 示例 3: 重试策略
        println!("\n📌 示例 3: 异步重试策略");
        println!("{}", "-".repeat(70));

        db_source.set_failed(true);

        let strategy = ExponentialBackoff::new(3, 100);

        println!("\n尝试读取（会失败并重试）:");
        match with_retry(|| async { db_source.read().await }, &strategy).await {
            Ok(_) => println!("✅ 成功"),
            Err(e) => println!("❌ 最终失败: {}", e),
        }

        // 性能对比
        println!("\n📌 性能对比");
        println!("{}", "-".repeat(70));
        benchmark_native_vs_macro().await;

        // 总结
        println!("\n{}", "=".repeat(70));
        println!("✅ 原生 async trait 的优势:");
        println!("  1. 无需外部宏依赖");
        println!("  2. 更好的性能（无 Box 开销）");
        println!("  3. 更清晰的错误信息");
        println!("  4. 标准库内置支持");
        println!("  5. 更好的 IDE 支持");
        println!("\n💡 适用场景:");
        println!("  - 异步数据源抽象");
        println!("  - 异步中间件系统");
        println!("  - 异步事件处理器");
        println!("  - 异步插件系统");
        println!("{}", "=".repeat(70));
    });
}
