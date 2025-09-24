//! 错误处理宏
//!
//! 提供便捷的宏来简化错误处理代码。

/// 创建统一错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = ErrorContext::new("module", "function", "file.rs", 42, ErrorSeverity::Medium, "category");
/// let error = unified_error!("操作失败", ErrorSeverity::High, "operation", context);
/// ```
#[macro_export]
macro_rules! unified_error {
    ($message:expr, $severity:expr, $category:expr, $context:expr) => {
        $crate::error_handling::UnifiedError::new($message, $severity, $category, $context)
    };
}

/// 创建带代码的统一错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = ErrorContext::new("module", "function", "file.rs", 42, ErrorSeverity::Medium, "category");
/// let error = unified_error_with_code!("操作失败", ErrorSeverity::High, "operation", "OP_001", $context);
/// ```
#[macro_export]
macro_rules! unified_error_with_code {
    ($message:expr, $severity:expr, $category:expr, $code:expr, $context:expr) => {
        $crate::error_handling::UnifiedError::new($message, $severity, $category, $context)
            .with_code($code)
    };
}

/// 创建带建议的统一错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = ErrorContext::new("module", "function", "file.rs", 42, ErrorSeverity::Medium, "category");
/// let error = unified_error_with_suggestion!("操作失败", ErrorSeverity::High, "operation", "请检查输入参数", $context);
/// ```
#[macro_export]
macro_rules! unified_error_with_suggestion {
    ($message:expr, $severity:expr, $category:expr, $suggestion:expr, $context:expr) => {
        $crate::error_handling::UnifiedError::new($message, $severity, $category, $context)
            .with_suggestion($suggestion)
    };
}

/// 创建完整的统一错误（包含代码和建议）
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = ErrorContext::new("module", "function", "file.rs", 42, ErrorSeverity::Medium, "category");
/// let error = unified_error_full!("操作失败", ErrorSeverity::High, "operation", "OP_001", "请检查输入参数", $context);
/// ```
#[macro_export]
macro_rules! unified_error_full {
    ($message:expr, $severity:expr, $category:expr, $code:expr, $suggestion:expr, $context:expr) => {
        $crate::error_handling::UnifiedError::new($message, $severity, $category, $context)
            .with_code($code)
            .with_suggestion($suggestion)
    };
}

/// 创建错误上下文
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = error_context!(ErrorSeverity::Medium, "category");
/// ```
#[macro_export]
macro_rules! error_context {
    ($severity:expr, $category:expr) => {
        $crate::error_handling::ErrorContext::new(
            module_path!(),
            function_name!(),
            file!(),
            line!(),
            $severity,
            $category
        )
    };
}

/// 创建带标签的错误上下文
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = error_context_with_tags!(ErrorSeverity::Medium, "category", "tag1", "tag2");
/// ```
#[macro_export]
macro_rules! error_context_with_tags {
    ($severity:expr, $category:expr, $($tag:expr),+) => {
        {
            let mut context = $crate::error_handling::ErrorContext::new(
                module_path!(),
                function_name!(),
                file!(),
                line!(),
                $severity,
                $category
            );
            $(context = context.with_tag($tag);)+
            context
        }
    };
}

/// 创建带元数据的错误上下文
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = error_context_with_metadata!(ErrorSeverity::Medium, "category", ("key1", "value1"), ("key2", "value2"));
/// ```
#[macro_export]
macro_rules! error_context_with_metadata {
    ($severity:expr, $category:expr, $(($key:expr, $value:expr)),+) => {
        {
            let mut context = $crate::error_handling::ErrorContext::new(
                module_path!(),
                function_name!(),
                file!(),
                line!(),
                $severity,
                $category
            );
            $(context = context.with_metadata($key, $value);)+
            context
        }
    };
}

/// 记录错误到全局监控器
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = error_context!(ErrorSeverity::Medium, "category");
/// let error = unified_error!("操作失败", ErrorSeverity::High, "operation", context);
/// log_error!(error);
/// ```
#[macro_export]
macro_rules! log_error {
    ($error:expr) => {
        $crate::error_handling::GlobalErrorMonitor::record_error($error)
    };
}

/// 安全执行操作并记录错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let result = safe_execute!(|| {
///     // 可能失败的操作
///     Ok::<String, String>("成功".to_string())
/// }, ErrorSeverity::Medium, "operation");
/// ```
#[macro_export]
macro_rules! safe_execute {
    ($operation:expr, $severity:expr, $category:expr) => {
        {
            let context = $crate::error_handling::ErrorContext::new(
                module_path!(),
                function_name!(),
                file!(),
                line!(),
                $severity,
                $category
            );
            
            match $operation {
                Ok(result) => Ok(result),
                Err(error) => {
                    let unified_error = $crate::error_handling::UnifiedError::from_std_error(error, context);
                    $crate::error_handling::GlobalErrorMonitor::record_error(unified_error.clone());
                    Err(unified_error)
                }
            }
        }
    };
}

/// 带重试的安全执行
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let result = safe_execute_with_retry!(|| async {
///     // 可能失败的操作
///     Ok::<String, String>("成功".to_string())
/// }, 3, Duration::from_millis(100), ErrorSeverity::Medium, "operation").await;
/// ```
#[macro_export]
macro_rules! safe_execute_with_retry {
    ($operation:expr, $max_attempts:expr, $delay:expr, $severity:expr, $category:expr) => {
        {
            let context = $crate::error_handling::ErrorContext::new(
                module_path!(),
                function_name!(),
                file!(),
                line!(),
                $severity,
                $category
            );
            
            let retry_config = $crate::error_handling::RetryConfig {
                max_attempts: $max_attempts,
                initial_delay: $delay,
                backoff_multiplier: 2.0,
                max_delay: std::time::Duration::from_secs(30),
                use_jitter: true,
                jitter_range: 0.1,
            };
            
            let recovery = $crate::error_handling::ErrorRecovery::new(
                $crate::error_handling::RecoveryStrategy::Retry(retry_config)
            );
            
            recovery.recover(|| $operation).await
        }
    };
}

/// 验证条件并返回错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let value = 42;
/// ensure!(value > 0, "值必须大于0", ErrorSeverity::Medium, "validation");
/// ```
#[macro_export]
macro_rules! ensure {
    ($condition:expr, $message:expr, $severity:expr, $category:expr) => {
        if !$condition {
            let context = $crate::error_handling::ErrorContext::new(
                module_path!(),
                function_name!(),
                file!(),
                line!(),
                $severity,
                $category
            );
            return Err($crate::error_handling::UnifiedError::new($message, $severity, $category, context));
        }
    };
}

/// 验证条件并返回带代码的错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let value = 42;
/// ensure_with_code!(value > 0, "值必须大于0", "VAL_001", ErrorSeverity::Medium, "validation");
/// ```
#[macro_export]
macro_rules! ensure_with_code {
    ($condition:expr, $message:expr, $code:expr, $severity:expr, $category:expr) => {
        if !$condition {
            let context = $crate::error_handling::ErrorContext::new(
                module_path!(),
                function_name!(),
                file!(),
                line!(),
                $severity,
                $category
            );
            return Err($crate::error_handling::UnifiedError::new($message, $severity, $category, context)
                .with_code($code));
        }
    };
}

/// 验证Option并返回错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let value: Option<String> = Some("test".to_string());
/// let result = require!(value, "值不能为空", ErrorSeverity::Medium, "validation");
/// ```
#[macro_export]
macro_rules! require {
    ($option:expr, $message:expr, $severity:expr, $category:expr) => {
        match $option {
            Some(value) => value,
            None => {
                let context = $crate::error_handling::ErrorContext::new(
                    module_path!(),
                    function_name!(),
                    file!(),
                    line!(),
                    $severity,
                    $category
                );
                return Err($crate::error_handling::UnifiedError::new($message, $severity, $category, context));
            }
        }
    };
}

/// 验证Result并返回统一错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let result: Result<String, std::io::Error> = Ok("test".to_string());
/// let value = require_result!(result, ErrorSeverity::Medium, "io");
/// ```
#[macro_export]
macro_rules! require_result {
    ($result:expr, $severity:expr, $category:expr) => {
        match $result {
            Ok(value) => value,
            Err(error) => {
                let context = $crate::error_handling::ErrorContext::new(
                    module_path!(),
                    function_name!(),
                    file!(),
                    line!(),
                    $severity,
                    $category
                );
                return Err($crate::error_handling::UnifiedError::from_std_error(error, context));
            }
        }
    };
}

/// 创建预定义错误
/// 
/// # 示例
/// ```rust
/// use c00_reliability::error_handling::*;
/// 
/// let context = error_context!(ErrorSeverity::High, "network");
/// let error = network_error!("连接失败", context);
/// ```
#[macro_export]
macro_rules! network_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::network_error($message, $context)
    };
}

#[macro_export]
macro_rules! database_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::database_error($message, $context)
    };
}

#[macro_export]
macro_rules! configuration_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::configuration_error($message, $context)
    };
}

#[macro_export]
macro_rules! permission_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::permission_error($message, $context)
    };
}

#[macro_export]
macro_rules! resource_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::resource_error($message, $context)
    };
}

#[macro_export]
macro_rules! timeout_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::timeout_error($message, $context)
    };
}

#[macro_export]
macro_rules! validation_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::validation_error($message, $context)
    };
}

#[macro_export]
macro_rules! serialization_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::serialization_error($message, $context)
    };
}

#[macro_export]
macro_rules! concurrency_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::concurrency_error($message, $context)
    };
}

#[macro_export]
macro_rules! system_error {
    ($message:expr, $context:expr) => {
        $crate::error_handling::predefined::system_error($message, $context)
    };
}

/// 获取函数名（用于错误上下文）
#[macro_export]
macro_rules! function_name {
    () => {{
        fn f() {}
        fn type_name_of<T>(_: T) -> &'static str {
            std::any::type_name::<T>()
        }
        let name = type_name_of(f);
        &name[..name.len() - 3]
    }};
}

#[cfg(test)]
mod tests {
    //use super::*;
    use crate::error_handling::{ErrorSeverity, ErrorContext, UnifiedError};

    #[test]
    fn test_unified_error_macro() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        let error = unified_error!("测试错误", ErrorSeverity::High, "test", context);
        
        assert_eq!(error.message(), "测试错误");
        assert_eq!(error.severity(), ErrorSeverity::High);
        assert_eq!(error.category(), "test");
    }

    #[test]
    fn test_unified_error_with_code_macro() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        let error = unified_error_with_code!("测试错误", ErrorSeverity::High, "test", "TEST_001", context);
        
        assert_eq!(error.message(), "测试错误");
        assert_eq!(error.code(), Some("TEST_001"));
    }

    #[test]
    fn test_error_context_macro() {
        let context = error_context!(ErrorSeverity::Medium, "test");
        
        assert_eq!(context.severity, ErrorSeverity::Medium);
        assert_eq!(context.category, "test");
        assert!(!context.module.is_empty());
        assert!(!context.function.is_empty());
    }

    #[test]
    fn test_error_context_with_tags_macro() {
        let context = error_context_with_tags!(ErrorSeverity::Medium, "test", "tag1", "tag2");
        
        assert_eq!(context.severity, ErrorSeverity::Medium);
        assert_eq!(context.category, "test");
        assert!(context.tags.contains(&"tag1".to_string()));
        assert!(context.tags.contains(&"tag2".to_string()));
    }

    #[test]
    fn test_error_context_with_metadata_macro() {
        let context = error_context_with_metadata!(ErrorSeverity::Medium, "test", ("key1", "value1"), ("key2", "value2"));
        
        assert_eq!(context.severity, ErrorSeverity::Medium);
        assert_eq!(context.category, "test");
        assert_eq!(context.metadata.get("key1"), Some(&"value1".to_string()));
        assert_eq!(context.metadata.get("key2"), Some(&"value2".to_string()));
    }

    #[test]
    fn test_ensure_macro() {
        let result = (|| -> Result<(), UnifiedError> {
            let value = 42;
            ensure!(value > 0, "值必须大于0", ErrorSeverity::Medium, "validation");
            Ok(())
        })();
        
        assert!(result.is_ok());
        
        let result = (|| -> Result<(), UnifiedError> {
            let value = -1;
            ensure!(value > 0, "值必须大于0", ErrorSeverity::Medium, "validation");
            Ok(())
        })();
        
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.message().contains("值必须大于0"));
    }

    #[test]
    fn test_require_macro() {
        let result = (|| -> Result<String, UnifiedError> {
            let value: Option<String> = Some("test".to_string());
            let result = require!(value, "值不能为空", ErrorSeverity::Medium, "validation");
            Ok(result)
        })();
        
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "test");
        
        let result = (|| -> Result<String, UnifiedError> {
            let value: Option<String> = None;
            let result = require!(value, "值不能为空", ErrorSeverity::Medium, "validation");
            Ok(result)
        })();
        
        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.message().contains("值不能为空"));
    }

    #[test]
    fn test_predefined_error_macros() {
        let context = error_context!(ErrorSeverity::High, "network");
        let error = network_error!("连接失败", context);
        
        assert_eq!(error.category(), "network");
        assert_eq!(error.code(), Some("NET_001"));
        assert!(error.suggestion().unwrap().contains("网络连接"));
    }

    #[test]
    fn test_function_name_macro() {
        let name = function_name!();
        assert!(!name.is_empty());
    }
}
