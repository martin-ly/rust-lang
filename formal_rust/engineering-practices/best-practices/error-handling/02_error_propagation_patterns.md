# 🚀 Rust错误传播模式最佳实践

## 概述

本文档基于MIT 6.172、Stanford CS110、CMU 15-410等著名大学Rust课程的标准，详细分析Rust错误传播的各种模式和实践技巧。

## 1. 错误传播基础模式

### 1.1 早期返回模式 (Early Return Pattern)

```rust
use std::fs::File;
use std::io::{self, Read, Write};
use std::path::Path;

// MIT 6.172风格：清晰的错误传播
pub fn process_file_content(file_path: &Path) -> io::Result<String> {
    // 早期返回：立即处理错误
    let mut file = File::open(file_path)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    
    // 验证内容
    if content.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "File is empty"
        ));
    }
    
    Ok(content)
}

// Stanford CS110风格：函数式错误处理
pub fn process_file_content_functional(file_path: &Path) -> io::Result<String> {
    File::open(file_path)
        .and_then(|mut file| {
            let mut content = String::new();
            file.read_to_string(&mut content)
                .map(|_| content)
        })
        .and_then(|content| {
            if content.is_empty() {
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "File is empty"
                ))
            } else {
                Ok(content)
            }
        })
}
```

### 1.2 错误转换模式 (Error Conversion Pattern)

```rust
use std::error::Error;
use std::fmt;

// CMU 15-410风格：自定义错误类型
#[derive(Debug)]
pub enum ProcessingError {
    IoError(io::Error),
    ParseError(String),
    ValidationError(String),
    BusinessLogicError(String),
}

impl fmt::Display for ProcessingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProcessingError::IoError(e) => write!(f, "IO error: {}", e),
            ProcessingError::ParseError(e) => write!(f, "Parse error: {}", e),
            ProcessingError::ValidationError(e) => write!(f, "Validation error: {}", e),
            ProcessingError::BusinessLogicError(e) => write!(f, "Business logic error: {}", e),
        }
    }
}

impl Error for ProcessingError {}

// 实现From特征进行错误转换
impl From<io::Error> for ProcessingError {
    fn from(err: io::Error) -> Self {
        ProcessingError::IoError(err)
    }
}

impl From<std::num::ParseIntError> for ProcessingError {
    fn from(err: std::num::ParseIntError) -> Self {
        ProcessingError::ParseError(err.to_string())
    }
}

// 使用错误转换的函数
pub fn process_data_with_conversion(data: &str) -> Result<i32, ProcessingError> {
    let parsed = data.trim().parse::<i32>()?; // 自动转换ParseIntError
    
    if parsed < 0 {
        return Err(ProcessingError::ValidationError(
            "Value must be non-negative".to_string()
        ));
    }
    
    Ok(parsed)
}
```

## 2. 高级错误传播模式

### 2.1 错误包装模式 (Error Wrapping Pattern)

```rust
use std::error::Error as StdError;

// MIT 6.172风格：上下文错误包装
pub struct ErrorContext<T> {
    inner: T,
    context: String,
}

impl<T: StdError> ErrorContext<T> {
    pub fn new(error: T, context: impl Into<String>) -> Self {
        ErrorContext {
            inner: error,
            context: context.into(),
        }
    }
    
    pub fn context(&self) -> &str {
        &self.context
    }
}

impl<T: StdError> fmt::Display for ErrorContext<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.context, self.inner)
    }
}

impl<T: StdError> StdError for ErrorContext<T> {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        Some(&self.inner)
    }
}

// 使用错误包装的扩展特征
pub trait ResultExt<T, E> {
    fn with_context<C>(self, context: C) -> Result<T, ErrorContext<E>>
    where
        C: Into<String>;
}

impl<T, E: StdError> ResultExt<T, E> for Result<T, E> {
    fn with_context<C>(self, context: C) -> Result<T, ErrorContext<E>>
    where
        C: Into<String>,
    {
        self.map_err(|e| ErrorContext::new(e, context))
    }
}

// 使用示例
pub fn process_file_with_context(file_path: &Path) -> Result<String, ErrorContext<io::Error>> {
    File::open(file_path)
        .with_context(format!("Failed to open file: {:?}", file_path))?
        .read_to_string(&mut String::new())
        .with_context("Failed to read file content")
}
```

### 2.2 错误聚合模式 (Error Aggregation Pattern)

```rust
use std::collections::VecDeque;

// Stanford CS110风格：错误聚合
#[derive(Debug)]
pub struct ErrorAggregator {
    errors: VecDeque<Box<dyn StdError + Send + Sync>>,
    max_errors: usize,
}

impl ErrorAggregator {
    pub fn new(max_errors: usize) -> Self {
        ErrorAggregator {
            errors: VecDeque::new(),
            max_errors,
        }
    }
    
    pub fn add_error<E: StdError + Send + Sync + 'static>(&mut self, error: E) {
        if self.errors.len() < self.max_errors {
            self.errors.push_back(Box::new(error));
        }
    }
    
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
    
    pub fn into_result<T>(self, success_value: T) -> Result<T, AggregatedError> {
        if self.has_errors() {
            Err(AggregatedError::new(self.errors))
        } else {
            Ok(success_value)
        }
    }
}

#[derive(Debug)]
pub struct AggregatedError {
    errors: VecDeque<Box<dyn StdError + Send + Sync>>,
}

impl AggregatedError {
    pub fn new(errors: VecDeque<Box<dyn StdError + Send + Sync>>) -> Self {
        AggregatedError { errors }
    }
    
    pub fn errors(&self) -> &VecDeque<Box<dyn StdError + Send + Sync>> {
        &self.errors
    }
}

impl fmt::Display for AggregatedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Multiple errors occurred:")?;
        for (i, error) in self.errors.iter().enumerate() {
            writeln!(f, "  {}. {}", i + 1, error)?;
        }
        Ok(())
    }
}

impl StdError for AggregatedError {}

// 使用错误聚合的批处理函数
pub fn process_multiple_files(file_paths: &[&Path]) -> Result<Vec<String>, AggregatedError> {
    let mut aggregator = ErrorAggregator::new(10);
    let mut results = Vec::new();
    
    for path in file_paths {
        match process_file_content(path) {
            Ok(content) => results.push(content),
            Err(e) => aggregator.add_error(e),
        }
    }
    
    aggregator.into_result(results)
}
```

## 3. 异步错误传播模式

### 3.1 异步错误传播 (Async Error Propagation)

```rust
use tokio::fs::File;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

// MIT 6.172风格：异步错误传播
pub async fn async_process_file(file_path: &Path) -> io::Result<String> {
    let mut file = File::open(file_path).await?;
    let mut content = String::new();
    file.read_to_string(&mut content).await?;
    
    if content.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "File is empty"
        ));
    }
    
    Ok(content)
}

// Stanford CS110风格：异步错误转换
pub async fn async_process_with_conversion(
    file_path: &Path
) -> Result<String, ProcessingError> {
    let content = async_process_file(file_path).await?;
    
    // 异步验证
    if content.len() > 1000 {
        return Err(ProcessingError::ValidationError(
            "File too large".to_string()
        ));
    }
    
    Ok(content)
}

// CMU 15-410风格：异步错误聚合
pub async fn async_process_multiple_files(
    file_paths: &[&Path]
) -> Result<Vec<String>, AggregatedError> {
    let mut aggregator = ErrorAggregator::new(10);
    let mut results = Vec::new();
    
    for path in file_paths {
        match async_process_file(path).await {
            Ok(content) => results.push(content),
            Err(e) => aggregator.add_error(e),
        }
    }
    
    aggregator.into_result(results)
}
```

### 3.2 流式错误处理 (Stream Error Handling)

```rust
use tokio::stream::{Stream, StreamExt};
use futures::future::join_all;

// 流式错误处理模式
pub async fn process_stream_with_errors<S>(
    mut stream: S
) -> Result<Vec<String>, ProcessingError>
where
    S: Stream<Item = Result<String, ProcessingError>> + Unpin,
{
    let mut results = Vec::new();
    
    while let Some(item) = stream.next().await {
        match item {
            Ok(content) => results.push(content),
            Err(e) => return Err(e), // 早期返回
        }
    }
    
    Ok(results)
}

// 流式错误聚合
pub async fn process_stream_with_aggregation<S>(
    mut stream: S
) -> Result<Vec<String>, AggregatedError>
where
    S: Stream<Item = Result<String, ProcessingError>> + Unpin,
{
    let mut aggregator = ErrorAggregator::new(10);
    let mut results = Vec::new();
    
    while let Some(item) = stream.next().await {
        match item {
            Ok(content) => results.push(content),
            Err(e) => aggregator.add_error(e),
        }
    }
    
    aggregator.into_result(results)
}
```

## 4. 错误恢复模式

### 4.1 重试模式 (Retry Pattern)

```rust
use std::time::Duration;
use tokio::time::sleep;

// MIT 6.172风格：指数退避重试
pub async fn retry_with_backoff<F, T, E>(
    mut operation: F,
    max_retries: usize,
    initial_delay: Duration,
) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
    E: std::fmt::Debug,
{
    let mut delay = initial_delay;
    
    for attempt in 0..=max_retries {
        match operation() {
            Ok(result) => return Ok(result),
            Err(e) => {
                if attempt == max_retries {
                    return Err(e);
                }
                
                eprintln!("Attempt {} failed: {:?}, retrying in {:?}", attempt + 1, e, delay);
                sleep(delay).await;
                delay *= 2; // 指数退避
            }
        }
    }
    
    unreachable!()
}

// Stanford CS110风格：条件重试
pub async fn retry_with_condition<F, T, E>(
    mut operation: F,
    should_retry: impl Fn(&E) -> bool,
    max_retries: usize,
) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
    E: std::fmt::Debug,
{
    for attempt in 0..=max_retries {
        match operation() {
            Ok(result) => return Ok(result),
            Err(e) => {
                if attempt == max_retries || !should_retry(&e) {
                    return Err(e);
                }
                
                eprintln!("Attempt {} failed: {:?}, retrying...", attempt + 1, e);
                sleep(Duration::from_millis(100 * (attempt + 1) as u64)).await;
            }
        }
    }
    
    unreachable!()
}
```

### 4.2 降级模式 (Fallback Pattern)

```rust
// CMU 15-410风格：降级处理
pub async fn process_with_fallback(
    primary_path: &Path,
    fallback_path: &Path,
) -> Result<String, ProcessingError> {
    // 尝试主要路径
    match async_process_file(primary_path).await {
        Ok(content) => Ok(content),
        Err(_) => {
            // 降级到备用路径
            async_process_file(fallback_path)
                .await
                .map_err(ProcessingError::from)
        }
    }
}

// 多级降级
pub async fn process_with_multiple_fallbacks(
    paths: &[&Path],
) -> Result<String, ProcessingError> {
    for path in paths {
        if let Ok(content) = async_process_file(path).await {
            return Ok(content);
        }
    }
    
    Err(ProcessingError::IoError(io::Error::new(
        io::ErrorKind::NotFound,
        "No valid file found in any path",
    )))
}
```

## 5. 错误监控和日志

### 5.1 错误监控模式 (Error Monitoring Pattern)

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

// MIT 6.172风格：错误监控
#[derive(Debug)]
pub struct ErrorMonitor {
    error_count: Arc<AtomicU64>,
    last_error: Arc<parking_lot::RwLock<Option<String>>>,
}

impl ErrorMonitor {
    pub fn new() -> Self {
        ErrorMonitor {
            error_count: Arc::new(AtomicU64::new(0)),
            last_error: Arc::new(parking_lot::RwLock::new(None)),
        }
    }
    
    pub fn record_error<E: std::fmt::Display>(&self, error: &E) {
        self.error_count.fetch_add(1, Ordering::Relaxed);
        *self.last_error.write() = Some(error.to_string());
    }
    
    pub fn error_count(&self) -> u64 {
        self.error_count.load(Ordering::Relaxed)
    }
    
    pub fn last_error(&self) -> Option<String> {
        self.last_error.read().clone()
    }
}

// 带监控的错误处理
pub async fn monitored_process_file(
    file_path: &Path,
    monitor: &ErrorMonitor,
) -> Result<String, ProcessingError> {
    match async_process_file(file_path).await {
        Ok(content) => Ok(content),
        Err(e) => {
            monitor.record_error(&e);
            Err(ProcessingError::from(e))
        }
    }
}
```

### 5.2 结构化错误日志 (Structured Error Logging)

```rust
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};

// Stanford CS110风格：结构化错误日志
#[derive(Debug, Serialize, Deserialize)]
pub struct ErrorLogEntry {
    timestamp: DateTime<Utc>,
    error_type: String,
    error_message: String,
    context: serde_json::Value,
    stack_trace: Option<String>,
}

impl ErrorLogEntry {
    pub fn new<E: StdError>(
        error: &E,
        context: serde_json::Value,
    ) -> Self {
        ErrorLogEntry {
            timestamp: Utc::now(),
            error_type: std::any::type_name::<E>().to_string(),
            error_message: error.to_string(),
            context,
            stack_trace: None, // 在实际应用中可以使用backtrace crate
        }
    }
}

// 结构化日志记录器
pub struct StructuredLogger {
    entries: Arc<parking_lot::RwLock<Vec<ErrorLogEntry>>>,
}

impl StructuredLogger {
    pub fn new() -> Self {
        StructuredLogger {
            entries: Arc::new(parking_lot::RwLock::new(Vec::new())),
        }
    }
    
    pub fn log_error<E: StdError>(
        &self,
        error: &E,
        context: serde_json::Value,
    ) {
        let entry = ErrorLogEntry::new(error, context);
        self.entries.write().push(entry);
    }
    
    pub fn get_entries(&self) -> Vec<ErrorLogEntry> {
        self.entries.read().clone()
    }
}
```

## 6. 测试和验证

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::NamedTempFile;
    use std::io::Write;

    #[tokio::test]
    async fn test_error_propagation() {
        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path();
        
        // 测试成功情况
        let result = process_file_content(path).await;
        assert!(result.is_ok());
        
        // 测试错误情况
        let result = process_file_content(Path::new("nonexistent.txt"));
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_error_aggregation() {
        let paths = vec![
            Path::new("file1.txt"),
            Path::new("file2.txt"),
            Path::new("file3.txt"),
        ];
        
        let result = process_multiple_files(&paths);
        assert!(result.is_err());
        
        if let Err(AggregatedError { errors }) = result {
            assert_eq!(errors.len(), 3);
        }
    }

    #[tokio::test]
    async fn test_retry_pattern() {
        let mut attempts = 0;
        let operation = || {
            attempts += 1;
            if attempts < 3 {
                Err(io::Error::new(io::ErrorKind::WouldBlock, "Temporary failure"))
            } else {
                Ok("success")
            }
        };
        
        let result = retry_with_backoff(
            operation,
            5,
            Duration::from_millis(10),
        ).await;
        
        assert!(result.is_ok());
        assert_eq!(attempts, 3);
    }

    #[tokio::test]
    async fn test_error_monitoring() {
        let monitor = ErrorMonitor::new();
        let error = io::Error::new(io::ErrorKind::NotFound, "File not found");
        
        monitor.record_error(&error);
        
        assert_eq!(monitor.error_count(), 1);
        assert!(monitor.last_error().is_some());
    }
}
```

## 7. 最佳实践总结

### 7.1 错误传播原则

1. **早期返回**: 在发现错误时立即返回，避免深层嵌套
2. **错误转换**: 使用`From`特征实现自动错误转换
3. **上下文保持**: 保留原始错误信息，添加有用的上下文
4. **错误聚合**: 在批处理场景中收集多个错误
5. **异步友好**: 在异步代码中正确处理错误传播

### 7.2 性能考虑

1. **零成本抽象**: 错误处理不应影响性能
2. **内存效率**: 避免不必要的错误对象克隆
3. **并发安全**: 在多线程环境中安全地处理错误

### 7.3 可维护性

1. **类型安全**: 使用强类型错误，避免字符串错误
2. **文档完整**: 为所有错误类型提供清晰的文档
3. **测试覆盖**: 全面测试错误处理逻辑

这些模式和实践基于国际一流大学的Rust课程标准，为构建健壮、可维护的Rust应用程序提供了坚实的基础。
