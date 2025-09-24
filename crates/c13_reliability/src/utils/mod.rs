//! 工具模块
//!
//! 提供可靠性框架的通用工具函数和扩展。

use std::time::Duration;
//use std::fmt;
// use serde::{Serialize, Deserialize};
//use tracing::{debug, warn, error, info};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 性能工具
pub struct PerformanceUtils;

impl PerformanceUtils {
    /// 测量函数执行时间
    pub fn measure_time<F, T>(f: F) -> (T, Duration)
    where
        F: FnOnce() -> T,
    {
        let start = std::time::Instant::now();
        let result = f();
        let duration = start.elapsed();
        (result, duration)
    }
}

/// 配置工具
pub struct ConfigUtils;

impl ConfigUtils {
    /// 获取环境变量
    pub fn get_env_var(key: &str) -> Option<String> {
        std::env::var(key).ok()
    }
    
    /// 获取环境变量或默认值
    pub fn get_env_var_or_default(key: &str, default: &str) -> String {
        std::env::var(key).unwrap_or_else(|_| default.to_string())
    }
}

/// 错误处理器
pub struct ErrorHandler;

impl ErrorHandler {
    /// 处理错误
    pub fn handle_error(error: &UnifiedError, context: &str) {
        tracing::error!("错误处理: {} - {}", context, error);
    }
}

/// 持续时间扩展
pub trait DurationExt {
    /// 获取人类可读的持续时间表示
    fn human_readable(&self) -> String;
    
    /// 获取持续时间的毫秒数
    fn as_millis(&self) -> u128;
    
    /// 获取持续时间的微秒数
    fn as_micros(&self) -> u128;
    
    /// 获取持续时间的纳秒数
    fn as_nanos(&self) -> u128;
    
    /// 从毫秒创建持续时间
    fn from_millis(millis: u64) -> Self;
    
    /// 从微秒创建持续时间
    fn from_micros(micros: u64) -> Self;
    
    /// 从纳秒创建持续时间
    fn from_nanos(nanos: u64) -> Self;
    
    /// 格式化持续时间
    fn format_duration(&self) -> String;
    
    /// 检查是否在范围内
    fn in_range(&self, start: Self, end: Self) -> bool;
}

impl DurationExt for Duration {
    fn human_readable(&self) -> String {
        let total_seconds = self.as_secs();
        let days = total_seconds / 86400;
        let hours = (total_seconds % 86400) / 3600;
        let minutes = (total_seconds % 3600) / 60;
        let seconds = total_seconds % 60;
        let millis = self.subsec_millis();
        
        if days > 0 {
            format!("{}d {}h {}m {}s {}ms", days, hours, minutes, seconds, millis)
        } else if hours > 0 {
            format!("{}h {}m {}s {}ms", hours, minutes, seconds, millis)
        } else if minutes > 0 {
            format!("{}m {}s {}ms", minutes, seconds, millis)
        } else if seconds > 0 {
            format!("{}s {}ms", seconds, millis)
        } else {
            format!("{}ms", millis)
        }
    }
    
    fn as_millis(&self) -> u128 {
        self.as_millis()
    }
    
    fn as_micros(&self) -> u128 {
        self.as_micros()
    }
    
    fn as_nanos(&self) -> u128 {
        self.as_nanos()
    }
    
    fn from_millis(millis: u64) -> Self {
        Duration::from_millis(millis)
    }
    
    fn from_micros(micros: u64) -> Self {
        Duration::from_micros(micros)
    }
    
    fn from_nanos(nanos: u64) -> Self {
        Duration::from_nanos(nanos)
    }
    
    fn format_duration(&self) -> String {
        // 简化实现，返回时间戳
        format!("{}", self.as_millis())
    }
    
    fn in_range(&self, start: Self, end: Self) -> bool {
        *self >= start && *self <= end
    }
}

/// 结果扩展trait
pub trait ResultExt<T, E> {
    /// 转换为统一错误
    fn into_unified_error(self, context: &str) -> Result<T, UnifiedError>;
    
    /// 处理错误并返回默认值
    fn unwrap_or_log_error(self, default: T, context: &str) -> T;
}

impl<T, E> ResultExt<T, E> for Result<T, E>
where
    E: std::fmt::Display + std::fmt::Debug + Send + Sync + 'static,
{
    fn into_unified_error(self, context: &str) -> Result<T, UnifiedError> {
        match self {
            Ok(value) => Ok(value),
            Err(error) => {
                let unified_error = UnifiedError::new(
                    &format!("{}: {}", context, error),
                    ErrorSeverity::Medium,
                    "operation",
                    ErrorContext::new("utils", "into_unified_error", file!(), line!(), ErrorSeverity::Medium, "operation")
                );
                Err(unified_error)
            }
        }
    }
    
    fn unwrap_or_log_error(self, default: T, context: &str) -> T {
        match self {
            Ok(value) => value,
            Err(error) => {
                tracing::error!("{}: {}", context, error);
                default
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_duration_ext() {
        let duration = Duration::from_secs(3661);
        let readable = duration.human_readable();
        assert!(readable.contains("1h"));
        assert!(readable.contains("1m"));
        assert!(readable.contains("1s"));
    }

    #[test]
    fn test_performance_utils() {
        let (result, duration) = PerformanceUtils::measure_time(|| {
            std::thread::sleep(Duration::from_millis(10));
            "test"
        });
        
        assert_eq!(result, "test");
        assert!(duration >= Duration::from_millis(10));
    }

    #[test]
    fn test_config_utils() {
        // 测试环境变量获取
        let path = ConfigUtils::get_env_var("PATH");
        assert!(path.is_some());
        
        // 测试默认值
        let default = ConfigUtils::get_env_var_or_default("NON_EXISTENT_VAR", "default");
        assert_eq!(default, "default");
    }

    #[test]
    fn test_error_handler() {
        let error = UnifiedError::new(
            "测试错误",
            ErrorSeverity::Low,
            "test",
            ErrorContext::new("test", "test", file!(), line!(), ErrorSeverity::Low, "test")
        );
        ErrorHandler::handle_error(&error, "测试上下文");
    }
}