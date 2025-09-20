//! # OTLP错误处理模块
//! 
//! 提供统一的错误类型和处理机制，支持Rust 1.90的错误处理特性。

use std::fmt;
use thiserror::Error;

/// OTLP操作结果类型
pub type Result<T> = std::result::Result<T, OtlpError>;

/// OTLP错误类型定义
#[derive(Error, Debug)]
pub enum OtlpError {
    /// 网络传输错误
    #[error("网络传输错误: {0}")]
    Transport(#[from] TransportError),
    
    /// 序列化/反序列化错误
    #[error("序列化错误: {0}")]
    Serialization(#[from] SerializationError),
    
    /// 配置错误
    #[error("配置错误: {0}")]
    Configuration(#[from] ConfigurationError),
    
    /// 数据处理错误
    #[error("数据处理错误: {0}")]
    Processing(#[from] ProcessingError),
    
    /// 导出器错误
    #[error("导出器错误: {0}")]
    Export(#[from] ExportError),
    
    /// 超时错误
    #[error("操作超时: {operation} (超时时间: {timeout:?})")]
    Timeout {
        operation: String,
        timeout: std::time::Duration,
    },
    
    /// 并发错误
    #[error("并发操作错误: {0}")]
    Concurrency(String),
    
    /// 资源不足错误
    #[error("资源不足: {resource} (当前: {current}, 需要: {required})")]
    ResourceExhausted {
        resource: String,
        current: usize,
        required: usize,
    },
    
    /// 协议版本不兼容
    #[error("协议版本不兼容: 当前版本 {current}, 支持版本 {supported}")]
    VersionMismatch {
        current: String,
        supported: String,
    },
    
    /// 内部错误
    #[error("内部错误: {0}")]
    Internal(#[from] anyhow::Error),
}

/// 传输层错误
#[derive(Error, Debug)]
pub enum TransportError {
    /// gRPC错误
    #[error("gRPC错误: {0}")]
    Grpc(#[from] tonic::Status),
    
    /// HTTP错误
    #[error("HTTP错误: {0}")]
    Http(#[from] reqwest::Error),
    
    /// 连接错误
    #[error("连接错误: {endpoint} - {reason}")]
    Connection {
        endpoint: String,
        reason: String,
    },
    
    /// TLS错误
    #[error("TLS错误: {0}")]
    Tls(String),
    
    /// DNS解析错误
    #[error("DNS解析错误: {hostname}")]
    DnsResolution { hostname: String },
    
    /// 网络不可达
    #[error("网络不可达: {endpoint}")]
    NetworkUnreachable { endpoint: String },
}

/// 序列化错误
#[derive(Error, Debug)]
pub enum SerializationError {
    /// Protobuf序列化错误
    #[error("Protobuf序列化错误: {0}")]
    Protobuf(#[from] prost::EncodeError),
    
    /// JSON序列化错误
    #[error("JSON序列化错误: {0}")]
    Json(#[from] serde_json::Error),
    
    /// 数据格式错误
    #[error("数据格式错误: {message}")]
    Format { message: String },
    
    /// 编码错误
    #[error("编码错误: {encoding} - {reason}")]
    Encoding {
        encoding: String,
        reason: String,
    },
}

/// 配置错误
#[derive(Error, Debug)]
pub enum ConfigurationError {
    /// 无效的端点URL
    #[error("无效的端点URL: {url}")]
    InvalidEndpoint { url: String },
    
    /// 无效的超时配置
    #[error("无效的超时配置: {timeout:?}")]
    InvalidTimeout { timeout: std::time::Duration },
    
    /// 无效的批处理配置
    #[error("无效的批处理配置: {message}")]
    InvalidBatchConfig { message: String },
    
    /// 缺少必需的配置项
    #[error("缺少必需的配置项: {field}")]
    MissingRequiredField { field: String },
    
    /// 配置值超出范围
    #[error("配置值超出范围: {field} = {value} (范围: {min} - {max})")]
    ValueOutOfRange {
        field: String,
        value: f64,
        min: f64,
        max: f64,
    },
}

/// 数据处理错误
#[derive(Error, Debug)]
pub enum ProcessingError {
    /// 数据验证失败
    #[error("数据验证失败: {field} - {reason}")]
    ValidationFailed { field: String, reason: String },
    
    /// 数据转换错误
    #[error("数据转换错误: {from} -> {to}")]
    ConversionFailed { from: String, to: String },
    
    /// 批处理错误
    #[error("批处理错误: {message}")]
    BatchProcessing { message: String },
    
    /// 过滤错误
    #[error("过滤错误: {filter} - {reason}")]
    Filtering { filter: String, reason: String },
    
    /// 聚合错误
    #[error("聚合错误: {operation} - {reason}")]
    Aggregation { operation: String, reason: String },
}

/// 导出器错误
#[derive(Error, Debug)]
pub enum ExportError {
    /// 导出失败
    #[error("导出失败: {reason}")]
    ExportFailed { reason: String },
    
    /// 部分导出失败
    #[error("部分导出失败: 成功 {success}, 失败 {failed}")]
    PartialExport { success: usize, failed: usize },
    
    /// 重试次数耗尽
    #[error("重试次数耗尽: 尝试了 {attempts} 次")]
    RetryExhausted { attempts: usize },
    
    /// 导出器未初始化
    #[error("导出器未初始化")]
    NotInitialized,
    
    /// 导出器已关闭
    #[error("导出器已关闭")]
    Shutdown,
}

impl OtlpError {
    /// 创建超时错误
    pub fn timeout(operation: impl Into<String>, timeout: std::time::Duration) -> Self {
        Self::Timeout {
            operation: operation.into(),
            timeout,
        }
    }
    
    /// 创建并发错误
    pub fn concurrency(reason: impl Into<String>) -> Self {
        Self::Concurrency(reason.into())
    }
    
    /// 创建资源不足错误
    pub fn resource_exhausted(
        resource: impl Into<String>,
        current: usize,
        required: usize,
    ) -> Self {
        Self::ResourceExhausted {
            resource: resource.into(),
            current,
            required,
        }
    }
    
    /// 创建版本不兼容错误
    pub fn version_mismatch(current: impl Into<String>, supported: impl Into<String>) -> Self {
        Self::VersionMismatch {
            current: current.into(),
            supported: supported.into(),
        }
    }
    
    /// 判断是否为可重试的错误
    pub fn is_retryable(&self) -> bool {
        match self {
            Self::Transport(TransportError::Connection { .. }) => true,
            Self::Transport(TransportError::NetworkUnreachable { .. }) => true,
            Self::Timeout { .. } => true,
            Self::Export(ExportError::ExportFailed { .. }) => true,
            _ => false,
        }
    }
    
    /// 获取错误严重程度
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            Self::Transport(_) => ErrorSeverity::High,
            Self::Serialization(_) => ErrorSeverity::Medium,
            Self::Configuration(_) => ErrorSeverity::High,
            Self::Processing(_) => ErrorSeverity::Medium,
            Self::Export(_) => ErrorSeverity::Medium,
            Self::Timeout { .. } => ErrorSeverity::Medium,
            Self::Concurrency(_) => ErrorSeverity::High,
            Self::ResourceExhausted { .. } => ErrorSeverity::High,
            Self::VersionMismatch { .. } => ErrorSeverity::High,
            Self::Internal(_) => ErrorSeverity::Critical,
        }
    }
}

/// 错误严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ErrorSeverity {
    /// 低严重程度 - 不影响核心功能
    Low,
    /// 中等严重程度 - 影响部分功能
    Medium,
    /// 高严重程度 - 影响主要功能
    High,
    /// 严重程度 - 系统不可用
    Critical,
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorSeverity::Low => write!(f, "低"),
            ErrorSeverity::Medium => write!(f, "中等"),
            ErrorSeverity::High => write!(f, "高"),
            ErrorSeverity::Critical => write!(f, "严重"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_error_creation() {
        let timeout_err = OtlpError::timeout("test_operation", Duration::from_secs(5));
        assert!(matches!(timeout_err, OtlpError::Timeout { .. }));
        
        let concurrency_err = OtlpError::concurrency("test_reason");
        assert!(matches!(concurrency_err, OtlpError::Concurrency(_)));
        
        let resource_err = OtlpError::resource_exhausted("memory", 100, 200);
        assert!(matches!(resource_err, OtlpError::ResourceExhausted { .. }));
    }

    #[test]
    fn test_error_retryable() {
        let retryable_err = OtlpError::Transport(TransportError::Connection {
            endpoint: "test".to_string(),
            reason: "test".to_string(),
        });
        assert!(retryable_err.is_retryable());
        
        let non_retryable_err = OtlpError::Configuration(ConfigurationError::InvalidEndpoint {
            url: "test".to_string(),
        });
        assert!(!non_retryable_err.is_retryable());
    }

    #[test]
    fn test_error_severity() {
        let high_severity = OtlpError::Transport(TransportError::Connection {
            endpoint: "test".to_string(),
            reason: "test".to_string(),
        });
        assert_eq!(high_severity.severity(), ErrorSeverity::High);
        
        let critical_severity = OtlpError::Internal(anyhow::anyhow!("test"));
        assert_eq!(critical_severity.severity(), ErrorSeverity::Critical);
    }
}
