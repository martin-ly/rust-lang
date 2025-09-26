//! Rust 1.90 高级错误处理演示
//!
//! 本示例展示了 Rust 1.90 中的高级错误处理特性

use c02_type_system::advanced_error_handling::*;
use std::collections::HashMap;

fn main() {
    println!("=== Rust 1.90 高级错误处理演示程序 ===\n");
    
    // 运行所有高级错误处理演示
    demonstrate_advanced_error_handling();
    
    // 运行交互式演示
    interactive_error_handling_demo();
    
    // 运行错误处理最佳实践演示
    error_handling_best_practices_demo();
}

/// 交互式错误处理演示
fn interactive_error_handling_demo() {
    println!("\n=== 交互式错误处理演示 ===\n");
    
    // 1. 交互式错误创建和显示
    println!("1. 交互式错误创建和显示:");
    interactive_error_creation();
    
    // 2. 交互式错误上下文
    println!("\n2. 交互式错误上下文:");
    interactive_error_context();
    
    // 3. 交互式错误恢复
    println!("\n3. 交互式错误恢复:");
    interactive_error_recovery();
    
    // 4. 交互式错误转换
    println!("\n4. 交互式错误转换:");
    interactive_error_transformation();
    
    // 5. 交互式错误监控
    println!("\n5. 交互式错误监控:");
    interactive_error_monitoring();
}

/// 交互式错误创建和显示
fn interactive_error_creation() {
    // 创建各种类型的错误
    let errors = vec![
        ("验证错误", AppError::Validation(ValidationError {
            field: "username".to_string(),
            message: "用户名长度必须在3-20个字符之间".to_string(),
            value: Some("ab".to_string()),
        })),
        ("网络错误", AppError::Network(NetworkError {
            url: "https://api.example.com/users".to_string(),
            status_code: Some(500),
            message: "内部服务器错误".to_string(),
        })),
        ("数据库错误", AppError::Database(DatabaseError {
            operation: "INSERT".to_string(),
            table: Some("users".to_string()),
            message: "唯一约束违反".to_string(),
            sql_state: Some("23505".to_string()),
        })),
        ("业务逻辑错误", AppError::Business(BusinessError {
            code: "USER_ALREADY_EXISTS".to_string(),
            message: "用户已存在".to_string(),
            context: {
                let mut map = HashMap::new();
                map.insert("username".to_string(), "john_doe".to_string());
                map.insert("email".to_string(), "john@example.com".to_string());
                map
            },
        })),
        ("系统错误", AppError::System(SystemError {
            component: "memory_manager".to_string(),
            message: "内存不足".to_string(),
            error_code: Some(-1),
        })),
        ("配置错误", AppError::Config(ConfigError {
            key: "database.url".to_string(),
            message: "配置项不存在".to_string(),
            file: Some("config.toml".to_string()),
        })),
        ("权限错误", AppError::Permission(PermissionError {
            resource: "user:123".to_string(),
            action: "delete".to_string(),
            user_id: Some("user:456".to_string()),
        })),
        ("资源错误", AppError::Resource(ResourceError {
            resource_type: "file".to_string(),
            resource_id: "document.pdf".to_string(),
            message: "文件不存在".to_string(),
        })),
        ("超时错误", AppError::Timeout(TimeoutError {
            operation: "database_query".to_string(),
            timeout_duration: 5000,
            message: "查询超时".to_string(),
        })),
        ("未知错误", AppError::Unknown("发生了未知错误".to_string())),
    ];
    
    for (error_type, error) in errors {
        println!("  {}: {}", error_type, error);
    }
}

/// 交互式错误上下文
fn interactive_error_context() {
    // 创建不同场景的错误上下文
    let contexts = vec![
        ("用户注册", ErrorContext::new("user_service".to_string(), "register_user".to_string())
            .with_request_id("req-001".to_string())
            .with_user_id("anonymous".to_string())
            .with_metadata("ip".to_string(), "192.168.1.100".to_string())
            .with_metadata("user_agent".to_string(), "Mozilla/5.0".to_string())),
        
        ("支付处理", ErrorContext::new("payment_service".to_string(), "process_payment".to_string())
            .with_request_id("req-002".to_string())
            .with_user_id("user-123".to_string())
            .with_metadata("amount".to_string(), "99.99".to_string())
            .with_metadata("currency".to_string(), "USD".to_string())),
        
        ("文件上传", ErrorContext::new("file_service".to_string(), "upload_file".to_string())
            .with_request_id("req-003".to_string())
            .with_user_id("user-456".to_string())
            .with_metadata("file_size".to_string(), "1048576".to_string())
            .with_metadata("file_type".to_string(), "image/jpeg".to_string())),
    ];
    
    for (scenario, context) in contexts {
        println!("  {} 上下文:", scenario);
        println!("    组件: {}", context.component);
        println!("    操作: {}", context.operation);
        println!("    请求ID: {:?}", context.request_id);
        println!("    用户ID: {:?}", context.user_id);
        println!("    元数据: {:?}", context.metadata);
        println!();
    }
    
    // 演示错误链
    let base_error = AppError::Validation(ValidationError {
        field: "email".to_string(),
        message: "邮箱格式无效".to_string(),
        value: Some("invalid-email".to_string()),
    });
    
    let base_context = ErrorContext::new("validation_service".to_string(), "validate_email".to_string());
    let base_contextual_error = ContextualError::new(base_error, base_context);
    
    let business_error = AppError::Business(BusinessError {
        code: "VALIDATION_FAILED".to_string(),
        message: "用户输入验证失败".to_string(),
        context: HashMap::new(),
    });
    
    let business_context = ErrorContext::new("user_service".to_string(), "create_user".to_string())
        .with_request_id("req-004".to_string());
    let business_contextual_error = ContextualError::new(business_error, business_context)
        .with_cause(base_contextual_error);
    
    println!("  错误链演示:");
    println!("    错误链: {}", business_contextual_error);
    println!("    链长度: {}", business_contextual_error.chain_length());
    println!("    根本原因: {}", business_contextual_error.get_root_cause());
}

/// 交互式错误恢复
fn interactive_error_recovery() {
    let mut recovery = ErrorRecovery::new();
    
    // 添加各种恢复策略
    recovery.add_strategy("network".to_string(), RecoveryStrategy::Retry {
        max_attempts: 3,
        delay_ms: 1000,
    });
    
    recovery.add_strategy("database".to_string(), RecoveryStrategy::Retry {
        max_attempts: 2,
        delay_ms: 500,
    });
    
    recovery.add_strategy("validation".to_string(), RecoveryStrategy::Fallback {
        default_value: "default@example.com".to_string(),
    });
    
    recovery.add_strategy("permission".to_string(), RecoveryStrategy::Skip);
    
    recovery.add_strategy("system".to_string(), RecoveryStrategy::Degrade {
        fallback_service: "backup_service".to_string(),
    });
    
    recovery.add_strategy("business".to_string(), RecoveryStrategy::Fail);
    
    println!("  已添加恢复策略:");
    println!("    网络错误: 重试3次，延迟1秒");
    println!("    数据库错误: 重试2次，延迟500毫秒");
    println!("    验证错误: 回退到默认值");
    println!("    权限错误: 跳过操作");
    println!("    系统错误: 降级到备用服务");
    println!("    业务错误: 直接失败");
    
    // 模拟错误恢复
    let test_errors = vec![
        ("网络错误", AppError::Network(NetworkError {
            url: "https://api.example.com".to_string(),
            status_code: Some(500),
            message: "服务暂时不可用".to_string(),
        })),
        ("验证错误", AppError::Validation(ValidationError {
            field: "email".to_string(),
            message: "邮箱格式无效".to_string(),
            value: Some("invalid".to_string()),
        })),
        ("权限错误", AppError::Permission(PermissionError {
            resource: "admin_panel".to_string(),
            action: "access".to_string(),
            user_id: Some("user-123".to_string()),
        })),
    ];
    
    for (error_type, error) in test_errors {
        println!("  测试 {} 恢复策略:", error_type);
        let result: Result<(), AppError> = recovery.recover(&error, || Err(error.clone()));
        match result {
            Ok(_) => println!("    恢复成功"),
            Err(e) => println!("    恢复失败: {}", e),
        }
    }
}

/// 交互式错误转换
fn interactive_error_transformation() {
    let mut transformer = ErrorTransformer::new();
    
    // 添加错误转换规则
    transformer.add_mapping("network".to_string(), |error| {
        if let AppError::Network(network_error) = error {
            AppError::Business(BusinessError {
                code: "EXTERNAL_SERVICE_ERROR".to_string(),
                message: format!("外部服务错误: {}", network_error.message),
                context: {
                    let mut map = HashMap::new();
                    map.insert("service_url".to_string(), network_error.url);
                    if let Some(status) = network_error.status_code {
                        map.insert("status_code".to_string(), status.to_string());
                    }
                    map
                },
            })
        } else {
            error
        }
    });
    
    transformer.add_mapping("database".to_string(), |error| {
        if let AppError::Database(db_error) = error {
            AppError::Business(BusinessError {
                code: "DATA_OPERATION_FAILED".to_string(),
                message: format!("数据操作失败: {}", db_error.message),
                context: {
                    let mut map = HashMap::new();
                    map.insert("operation".to_string(), db_error.operation);
                    if let Some(table) = db_error.table {
                        map.insert("table".to_string(), table);
                    }
                    if let Some(sql_state) = db_error.sql_state {
                        map.insert("sql_state".to_string(), sql_state);
                    }
                    map
                },
            })
        } else {
            error
        }
    });
    
    transformer.add_mapping("validation".to_string(), |error| {
        if let AppError::Validation(validation_error) = error {
            AppError::Business(BusinessError {
                code: "INVALID_INPUT".to_string(),
                message: format!("输入验证失败: {}", validation_error.message),
                context: {
                    let mut map = HashMap::new();
                    map.insert("field".to_string(), validation_error.field);
                    if let Some(value) = validation_error.value {
                        map.insert("value".to_string(), value);
                    }
                    map
                },
            })
        } else {
            error
        }
    });
    
    println!("  已添加错误转换规则:");
    println!("    网络错误 -> 业务错误");
    println!("    数据库错误 -> 业务错误");
    println!("    验证错误 -> 业务错误");
    
    // 测试错误转换
    let test_errors = vec![
        ("网络错误", AppError::Network(NetworkError {
            url: "https://api.example.com".to_string(),
            status_code: Some(404),
            message: "Not Found".to_string(),
        })),
        ("数据库错误", AppError::Database(DatabaseError {
            operation: "SELECT".to_string(),
            table: Some("users".to_string()),
            message: "Connection timeout".to_string(),
            sql_state: Some("08006".to_string()),
        })),
        ("验证错误", AppError::Validation(ValidationError {
            field: "password".to_string(),
            message: "密码强度不足".to_string(),
            value: Some("123".to_string()),
        })),
        ("系统错误", AppError::System(SystemError {
            component: "memory".to_string(),
            message: "内存不足".to_string(),
            error_code: Some(-1),
        })),
    ];
    
    for (error_type, error) in test_errors {
        println!("  转换 {}:", error_type);
        println!("    原始: {}", error);
        let transformed = transformer.transform(error);
        println!("    转换后: {}", transformed);
        println!();
    }
}

/// 交互式错误监控
fn interactive_error_monitoring() {
    let monitor = ErrorMonitor::new();
    
    // 模拟不同场景的错误
    let error_scenarios = vec![
        ("用户注册失败", AppError::Validation(ValidationError {
            field: "email".to_string(),
            message: "邮箱格式无效".to_string(),
            value: Some("invalid-email".to_string()),
        }), ErrorContext::new("user_service".to_string(), "register".to_string()), ErrorLevel::Warning),
        
        ("支付服务不可用", AppError::Network(NetworkError {
            url: "https://payment.example.com".to_string(),
            status_code: Some(503),
            message: "Service Unavailable".to_string(),
        }), ErrorContext::new("payment_service".to_string(), "process_payment".to_string()), ErrorLevel::Error),
        
        ("数据库连接失败", AppError::Database(DatabaseError {
            operation: "CONNECT".to_string(),
            table: None,
            message: "Connection refused".to_string(),
            sql_state: Some("08001".to_string()),
        }), ErrorContext::new("database_service".to_string(), "connect".to_string()), ErrorLevel::Critical),
        
        ("权限不足", AppError::Permission(PermissionError {
            resource: "admin_panel".to_string(),
            action: "access".to_string(),
            user_id: Some("user-123".to_string()),
        }), ErrorContext::new("auth_service".to_string(), "check_permission".to_string()), ErrorLevel::Warning),
        
        ("系统内存不足", AppError::System(SystemError {
            component: "memory_manager".to_string(),
            message: "Out of memory".to_string(),
            error_code: Some(-1),
        }), ErrorContext::new("system".to_string(), "allocate_memory".to_string()), ErrorLevel::Critical),
    ];
    
    // 记录错误
    for (scenario, error, context, level) in error_scenarios {
        println!("  记录错误: {}", scenario);
        monitor.log_error(error, context, level);
    }
    
    // 显示监控统计
    let metrics = monitor.get_metrics();
    println!("\n  错误监控统计:");
    println!("    总错误数: {}", metrics.total_errors);
    println!("    按类型分布:");
    for (error_type, count) in &metrics.errors_by_type {
        println!("      {}: {}", error_type, count);
    }
    println!("    按级别分布:");
    for (level, count) in &metrics.errors_by_level {
        println!("      {:?}: {}", level, count);
    }
    println!("    按组件分布:");
    for (component, count) in &metrics.errors_by_component {
        println!("      {}: {}", component, count);
    }
    
    // 显示最近错误
    let recent_errors = monitor.get_recent_errors(3);
    println!("\n  最近错误 (最多3条):");
    for (i, error_entry) in recent_errors.iter().enumerate() {
        println!("    {}. [{}] {} - {}", 
                i + 1, 
                error_entry.timestamp, 
                error_entry.context.component, 
                error_entry.error);
    }
}

/// 错误处理最佳实践演示
fn error_handling_best_practices_demo() {
    println!("\n=== 错误处理最佳实践演示 ===\n");
    
    // 1. 完整的错误处理流程
    println!("1. 完整的错误处理流程:");
    let mut error_handler = ErrorHandler::new();
    
    // 配置恢复策略
    error_handler.add_recovery_strategy("network".to_string(), RecoveryStrategy::Retry {
        max_attempts: 3,
        delay_ms: 1000,
    });
    
    error_handler.add_recovery_strategy("validation".to_string(), RecoveryStrategy::Fallback {
        default_value: "default@example.com".to_string(),
    });
    
    // 配置错误转换
    error_handler.add_error_transformation("network".to_string(), |error| {
        if let AppError::Network(network_error) = error {
            AppError::Business(BusinessError {
                code: "EXTERNAL_SERVICE_ERROR".to_string(),
                message: format!("外部服务不可用: {}", network_error.url),
                context: HashMap::new(),
            })
        } else {
            error
        }
    });
    
    // 模拟错误处理
    let test_errors = vec![
        ("网络错误", AppError::Network(NetworkError {
            url: "https://api.example.com".to_string(),
            status_code: Some(500),
            message: "Internal Server Error".to_string(),
        }), ErrorContext::new("api_client".to_string(), "fetch_data".to_string())),
        
        ("验证错误", AppError::Validation(ValidationError {
            field: "email".to_string(),
            message: "邮箱格式无效".to_string(),
            value: Some("invalid".to_string()),
        }), ErrorContext::new("user_service".to_string(), "validate_input".to_string())),
        
        ("业务错误", AppError::Business(BusinessError {
            code: "INSUFFICIENT_BALANCE".to_string(),
            message: "余额不足".to_string(),
            context: HashMap::new(),
        }), ErrorContext::new("payment_service".to_string(), "process_payment".to_string())),
    ];
    
    for (error_type, error, context) in test_errors {
        println!("  处理 {}:", error_type);
        match error_handler.handle_error(error, context) {
            Ok(_) => println!("    处理成功"),
            Err(e) => println!("    处理失败: {}", e),
        }
    }
    
    // 显示处理后的统计
    let stats = error_handler.get_error_stats();
    println!("\n  处理后的错误统计:");
    println!("    总错误数: {}", stats.total_errors);
    println!("    按类型分布: {:?}", stats.errors_by_type);
    println!("    按级别分布: {:?}", stats.errors_by_level);
    
    // 2. 错误处理性能测试
    println!("\n2. 错误处理性能测试:");
    let start = std::time::Instant::now();
    
    for i in 0..1000 {
        let error = AppError::Validation(ValidationError {
            field: format!("field_{}", i),
            message: "测试错误".to_string(),
            value: None,
        });
        let context = ErrorContext::new("test_service".to_string(), "test_operation".to_string());
        let _ = error_handler.handle_error(error, context);
    }
    
    let duration = start.elapsed();
    println!("  处理1000个错误耗时: {:?}", duration);
    println!("  平均每个错误: {:?}", duration / 1000);
    
    // 3. 错误处理最佳实践总结
    println!("\n3. 错误处理最佳实践总结:");
    println!("  ✅ 使用自定义错误类型提供清晰的错误信息");
    println!("  ✅ 添加上下文信息帮助调试和监控");
    println!("  ✅ 实现错误恢复机制提高系统稳定性");
    println!("  ✅ 使用错误转换统一错误格式");
    println!("  ✅ 建立错误监控和日志系统");
    println!("  ✅ 根据错误类型和严重程度进行分类处理");
    println!("  ✅ 提供详细的错误统计和分析");
    println!("  ✅ 实现错误链追踪根本原因");
}

