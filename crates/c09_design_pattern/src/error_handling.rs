use std::error::Error;
/// 设计模式错误处理模块
///
/// 提供统一的错误处理机制，支持各种设计模式的错误场景
/// 使用Rust 1.89的新特性优化错误处理性能
use std::fmt;

/// 设计模式通用错误类型
#[derive(Debug, Clone)]
pub enum DesignPatternError {
    /// 单例模式错误
    SingletonError(String),
    /// 工厂模式错误
    FactoryError(String),
    /// 代理模式错误
    ProxyError(String),
    /// 享元模式错误
    FlyweightError(String),
    /// 责任链模式错误
    ChainError(String),
    /// 观察者模式错误
    ObserverError(String),
    /// 并发模式错误
    ConcurrencyError(String),
    /// 内存分配错误
    MemoryError(String),
    /// 配置错误
    ConfigurationError(String),
}

impl fmt::Display for DesignPatternError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DesignPatternError::SingletonError(msg) => write!(f, "单例模式错误: {}", msg),
            DesignPatternError::FactoryError(msg) => write!(f, "工厂模式错误: {}", msg),
            DesignPatternError::ProxyError(msg) => write!(f, "代理模式错误: {}", msg),
            DesignPatternError::FlyweightError(msg) => write!(f, "享元模式错误: {}", msg),
            DesignPatternError::ChainError(msg) => write!(f, "责任链模式错误: {}", msg),
            DesignPatternError::ObserverError(msg) => write!(f, "观察者模式错误: {}", msg),
            DesignPatternError::ConcurrencyError(msg) => write!(f, "并发模式错误: {}", msg),
            DesignPatternError::MemoryError(msg) => write!(f, "内存错误: {}", msg),
            DesignPatternError::ConfigurationError(msg) => write!(f, "配置错误: {}", msg),
        }
    }
}

impl Error for DesignPatternError {}

/// 错误处理结果类型
pub type PatternResult<T> = Result<T, DesignPatternError>;

/// 错误恢复策略
#[derive(Debug, Clone)]
pub enum RecoveryStrategy {
    /// 重试策略
    Retry { max_attempts: u32, delay_ms: u64 },
    /// 降级策略
    Fallback,
    /// 忽略错误
    Ignore,
    /// 抛出错误
    Propagate,
}

/// 错误处理器
pub struct ErrorHandler {
    strategy: RecoveryStrategy,
    error_count: std::sync::atomic::AtomicU32,
}

impl ErrorHandler {
    pub fn new(strategy: RecoveryStrategy) -> Self {
        Self {
            strategy,
            error_count: std::sync::atomic::AtomicU32::new(0),
        }
    }

    /// 处理错误并尝试恢复
    pub fn handle_error<T, F>(&self, mut operation: F) -> PatternResult<T>
    where
        F: FnMut() -> PatternResult<T>,
    {
        match &self.strategy {
            RecoveryStrategy::Retry {
                max_attempts,
                delay_ms,
            } => self.handle_with_retry(operation, *max_attempts, *delay_ms),
            RecoveryStrategy::Fallback => self.handle_with_fallback(operation),
            RecoveryStrategy::Ignore => {
                operation().map_err(|_| DesignPatternError::ConfigurationError(
                        "操作被忽略".to_string(),
                    ))
            }
            RecoveryStrategy::Propagate => operation(),
        }
    }

    fn handle_with_retry<T, F>(
        &self,
        mut operation: F,
        max_attempts: u32,
        delay_ms: u64,
    ) -> PatternResult<T>
    where
        F: FnMut() -> PatternResult<T>,
    {
        let mut last_error = None;

        for attempt in 1..=max_attempts {
            match operation() {
                Ok(result) => return Ok(result),
                Err(error) => {
                    last_error = Some(error);
                    if attempt < max_attempts {
                        std::thread::sleep(std::time::Duration::from_millis(delay_ms));
                    }
                }
            }
        }

        Err(last_error
            .unwrap_or_else(|| DesignPatternError::ConfigurationError("重试次数耗尽".to_string())))
    }

    fn handle_with_fallback<T, F>(&self, mut operation: F) -> PatternResult<T>
    where
        F: FnMut() -> PatternResult<T>,
    {
        operation().map_err(|error| {
            // 记录错误
            self.error_count
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);

            // 返回降级结果
            DesignPatternError::ConfigurationError(format!(
                "降级处理: {}",
                error
            ))
        })
    }

    pub fn get_error_count(&self) -> u32 {
        self.error_count.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn reset_error_count(&self) {
        self.error_count
            .store(0, std::sync::atomic::Ordering::Relaxed);
    }
}

/// 单例模式错误处理
pub struct SingletonErrorHandler {
    handler: ErrorHandler,
}

impl Default for SingletonErrorHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl SingletonErrorHandler {
    pub fn new() -> Self {
        Self {
            handler: ErrorHandler::new(RecoveryStrategy::Retry {
                max_attempts: 3,
                delay_ms: 100,
            }),
        }
    }

    pub fn create_singleton<T, F>(&self, initializer: F) -> PatternResult<T>
    where
        F: FnMut() -> PatternResult<T>,
    {
        self.handler.handle_error(initializer)
    }
}

/// 工厂模式错误处理
pub struct FactoryErrorHandler {
    handler: ErrorHandler,
}

impl Default for FactoryErrorHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl FactoryErrorHandler {
    pub fn new() -> Self {
        Self {
            handler: ErrorHandler::new(RecoveryStrategy::Fallback),
        }
    }

    pub fn create_product<T, F>(&self, factory_fn: F) -> PatternResult<T>
    where
        F: FnMut() -> PatternResult<T>,
    {
        self.handler.handle_error(factory_fn)
    }
}

/// 代理模式错误处理
pub struct ProxyErrorHandler {
    handler: ErrorHandler,
}

impl Default for ProxyErrorHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl ProxyErrorHandler {
    pub fn new() -> Self {
        Self {
            handler: ErrorHandler::new(RecoveryStrategy::Retry {
                max_attempts: 2,
                delay_ms: 50,
            }),
        }
    }

    pub fn handle_request<T, F>(&self, request_fn: F) -> PatternResult<T>
    where
        F: FnMut() -> PatternResult<T>,
    {
        self.handler.handle_error(request_fn)
    }
}

/// 享元模式错误处理
pub struct FlyweightErrorHandler {
    handler: ErrorHandler,
}

impl Default for FlyweightErrorHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl FlyweightErrorHandler {
    pub fn new() -> Self {
        Self {
            handler: ErrorHandler::new(RecoveryStrategy::Ignore),
        }
    }

    pub fn get_flyweight<T, F>(&self, get_fn: F) -> PatternResult<T>
    where
        F: FnMut() -> PatternResult<T>,
    {
        self.handler.handle_error(get_fn)
    }
}

/// 错误监控器
pub struct ErrorMonitor {
    error_log: std::sync::Mutex<Vec<DesignPatternError>>,
    max_log_size: usize,
}

impl ErrorMonitor {
    pub fn new(max_log_size: usize) -> Self {
        Self {
            error_log: std::sync::Mutex::new(Vec::new()),
            max_log_size,
        }
    }

    pub fn log_error(&self, error: DesignPatternError) {
        let mut log = self.error_log.lock().unwrap();

        if log.len() >= self.max_log_size {
            log.remove(0); // 移除最旧的错误
        }

        log.push(error);
    }

    pub fn get_error_count(&self) -> usize {
        self.error_log.lock().unwrap().len()
    }

    pub fn get_recent_errors(&self, count: usize) -> Vec<DesignPatternError> {
        let log = self.error_log.lock().unwrap();
        let start = if log.len() > count {
            log.len() - count
        } else {
            0
        };

        log[start..].to_vec()
    }

    pub fn clear_errors(&self) {
        self.error_log.lock().unwrap().clear();
    }
}

lazy_static::lazy_static! {
    pub static ref GLOBAL_ERROR_MONITOR: ErrorMonitor = ErrorMonitor::new(1000);
}

/// 错误处理宏
#[macro_export]
macro_rules! handle_pattern_error {
    ($result:expr, $error_type:ident, $message:expr) => {
        $result.map_err(|e| DesignPatternError::$error_type(format!("{}: {}", $message, e)))
    };
}

#[macro_export]
macro_rules! log_pattern_error {
    ($error:expr) => {
        GLOBAL_ERROR_MONITOR.log_error($error);
    };
}

/// 错误处理工具函数
pub mod utils {
    use super::*;

    /// 安全执行操作，自动处理错误
    pub fn safe_execute<T, F>(operation: F) -> PatternResult<T>
    where
        F: Fn() -> PatternResult<T>,
    {
        match operation() {
            Ok(result) => Ok(result),
            Err(error) => {
                log_pattern_error!(error.clone());
                Err(error)
            }
        }
    }

    /// 验证输入参数
    pub fn validate_input<T>(value: Option<T>, name: &str) -> PatternResult<T> {
        let Some(v) = value else {
            return Err(DesignPatternError::ConfigurationError(format!("{} 不能为空", name)));
        };
        Ok(v)
    }

    /// 验证数值范围
    pub fn validate_range(value: i32, min: i32, max: i32, name: &str) -> PatternResult<i32> {
        if value >= min && value <= max {
            Ok(value)
        } else {
            Err(DesignPatternError::ConfigurationError(format!(
                "{} 必须在 {} 到 {} 之间，当前值: {}",
                name, min, max, value
            )))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_handler_retry() {
        let handler = ErrorHandler::new(RecoveryStrategy::Retry {
            max_attempts: 3,
            delay_ms: 1,
        });

        let mut attempt_count = 0;
        let result = handler.handle_error(|| {
            attempt_count += 1;
            if attempt_count < 3 {
                Err(DesignPatternError::SingletonError("测试错误".to_string()))
            } else {
                Ok("成功".to_string())
            }
        });

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
        assert_eq!(attempt_count, 3);
    }

    #[test]
    fn test_error_handler_fallback() {
        let handler = ErrorHandler::new(RecoveryStrategy::Fallback);

        let result: Result<(), _> =
            handler.handle_error(|| Err(DesignPatternError::FactoryError("工厂错误".to_string())));

        assert!(result.is_err());
        assert_eq!(handler.get_error_count(), 1);
    }

    #[test]
    fn test_error_monitor() {
        let monitor = ErrorMonitor::new(5);

        for i in 0..7 {
            monitor.log_error(DesignPatternError::SingletonError(format!("错误 {}", i)));
        }

        assert_eq!(monitor.get_error_count(), 5);

        let recent_errors = monitor.get_recent_errors(3);
        assert_eq!(recent_errors.len(), 3);
    }

    #[test]
    fn test_validation_utils() {
        // 测试输入验证
        let result = utils::validate_input(Some(42), "测试值");
        assert!(result.is_ok());

        let result = utils::validate_input::<i32>(None, "测试值");
        assert!(result.is_err());

        // 测试范围验证
        let result = utils::validate_range(5, 1, 10, "测试范围");
        assert!(result.is_ok());

        let result = utils::validate_range(15, 1, 10, "测试范围");
        assert!(result.is_err());
    }
}
