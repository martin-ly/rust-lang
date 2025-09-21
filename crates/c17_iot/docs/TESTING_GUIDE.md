# c17_iot 测试指南

## 概述

本文档介绍了 `c17_iot` 项目的测试策略、测试覆盖率和测试最佳实践。

## 测试架构

### 测试层次结构

```text
c17_iot/
├── unit_tests/          # 单元测试
├── integration_tests/   # 集成测试
├── performance_tests/   # 性能测试
├── security_tests/      # 安全测试
└── e2e_tests/          # 端到端测试
```

### 测试类型

1. **单元测试** - 测试单个函数或模块
2. **集成测试** - 测试模块间的交互
3. **性能测试** - 测试系统性能和基准
4. **安全测试** - 测试安全功能和漏洞
5. **端到端测试** - 测试完整的用户场景

## 单元测试

### 设备管理测试

```rust
#[cfg(test)]
mod device_management_tests {
    use super::*;
    use c17_iot::device_management::*;
    use tokio_test;

    #[tokio::test]
    async fn test_register_device() {
        let mut device_manager = DeviceManager::new();
        
        // 测试正常注册
        let result = device_manager.register_device(
            "test_device_001", 
            "temperature_sensor", 
            "room1"
        ).await;
        
        assert!(result.is_ok());
        
        // 验证设备已注册
        let devices = device_manager.get_all_devices().await.unwrap();
        assert_eq!(devices.len(), 1);
        assert_eq!(devices[0].id, "test_device_001");
    }

    #[tokio::test]
    async fn test_register_duplicate_device() {
        let mut device_manager = DeviceManager::new();
        
        // 注册第一个设备
        device_manager.register_device("device_001", "sensor", "room1").await.unwrap();
        
        // 尝试注册重复设备
        let result = device_manager.register_device("device_001", "sensor", "room1").await;
        
        assert!(matches!(result, Err(DeviceManagementError::DeviceAlreadyExists)));
    }

    #[tokio::test]
    async fn test_get_device_status() {
        let mut device_manager = DeviceManager::new();
        
        // 注册设备
        device_manager.register_device("device_001", "sensor", "room1").await.unwrap();
        
        // 获取设备状态
        let status = device_manager.get_device_status("device_001").await.unwrap();
        assert_eq!(status.device_id, "device_001");
        assert_eq!(status.status, DeviceStatus::Active);
    }

    #[tokio::test]
    async fn test_get_nonexistent_device_status() {
        let device_manager = DeviceManager::new();
        
        // 获取不存在设备的状态
        let result = device_manager.get_device_status("nonexistent").await;
        
        assert!(matches!(result, Err(DeviceManagementError::DeviceNotFound)));
    }
}
```

### 传感器网络测试

```rust
#[cfg(test)]
mod sensor_network_tests {
    use super::*;
    use c17_iot::sensor_network::*;

    #[tokio::test]
    async fn test_add_sensor() {
        let mut sensor_network = SensorNetwork::new();
        
        let result = sensor_network.add_sensor("sensor_001", "temperature", "room1").await;
        assert!(result.is_ok());
        
        let sensors = sensor_network.get_all_sensors().await.unwrap();
        assert_eq!(sensors.len(), 1);
        assert_eq!(sensors[0].id, "sensor_001");
    }

    #[tokio::test]
    async fn test_data_collection_lifecycle() {
        let mut sensor_network = SensorNetwork::new();
        sensor_network.add_sensor("sensor_001", "temperature", "room1").await.unwrap();
        
        // 开始数据采集
        sensor_network.start_data_collection().await.unwrap();
        assert!(sensor_network.is_collecting().await);
        
        // 暂停数据采集
        sensor_network.pause_data_collection().await.unwrap();
        assert!(!sensor_network.is_collecting().await);
        
        // 恢复数据采集
        sensor_network.resume_data_collection().await.unwrap();
        assert!(sensor_network.is_collecting().await);
        
        // 停止数据采集
        sensor_network.stop_data_collection().await.unwrap();
        assert!(!sensor_network.is_collecting().await);
    }

    #[tokio::test]
    async fn test_sensor_data_storage() {
        let mut sensor_network = SensorNetwork::new();
        sensor_network.add_sensor("sensor_001", "temperature", "room1").await.unwrap();
        sensor_network.start_data_collection().await.unwrap();
        
        // 等待数据采集
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        
        // 获取最新数据
        let latest_data = sensor_network.get_latest_data("sensor_001").await.unwrap();
        assert!(latest_data.timestamp <= chrono::Utc::now());
        assert!(latest_data.value.is_finite());
    }
}
```

### 规则引擎测试

```rust
#[cfg(test)]
mod rule_engine_tests {
    use super::*;
    use c17_iot::edge_computing::*;
    use c17_iot::edge_computing::rule_engine::*;

    #[tokio::test]
    async fn test_simple_rule_evaluation() {
        let (mut rule_engine, _) = RuleEngine::new();
        
        // 创建简单规则
        let condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };
        
        let rule = Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        rule_engine.add_rule(rule).await.unwrap();
        
        // 创建测试上下文
        let context = RuleContext {
            data: std::collections::HashMap::from([
                ("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(35.0).unwrap())),
            ]),
            timestamp: chrono::Utc::now(),
            device_id: "sensor_001".to_string(),
            event_type: Some("sensor_data".to_string()),
            metadata: std::collections::HashMap::new(),
        };
        
        // 评估规则
        let results = rule_engine.evaluate_rules(context).await.unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].rule_id, "temp_alert");
    }

    #[tokio::test]
    async fn test_complex_rule_evaluation() {
        let (mut rule_engine, _) = RuleEngine::new();
        
        // 创建复合条件规则
        let temp_condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let humidity_condition = Condition::Simple {
            field: "humidity".to_string(),
            operator: Operator::LessThan,
            value: serde_json::Value::Number(serde_json::Number::from_f64(20.0).unwrap()),
        };
        
        let combined_condition = Condition::And {
            conditions: vec![temp_condition, humidity_condition],
        };
        
        let action = Action::SendAlert {
            message: "温湿度异常".to_string(),
            recipients: vec!["operator@example.com".to_string()],
            level: AlertLevel::Critical,
        };
        
        let rule = Rule::new(
            "temp_humidity_alert".to_string(),
            "温湿度告警".to_string(),
            combined_condition,
            action,
            1,
        );
        
        rule_engine.add_rule(rule).await.unwrap();
        
        // 测试满足条件的情况
        let context1 = RuleContext {
            data: std::collections::HashMap::from([
                ("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(35.0).unwrap())),
                ("humidity".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(15.0).unwrap())),
            ]),
            timestamp: chrono::Utc::now(),
            device_id: "sensor_001".to_string(),
            event_type: Some("sensor_data".to_string()),
            metadata: std::collections::HashMap::new(),
        };
        
        let results1 = rule_engine.evaluate_rules(context1).await.unwrap();
        assert_eq!(results1.len(), 1);
        
        // 测试不满足条件的情况
        let context2 = RuleContext {
            data: std::collections::HashMap::from([
                ("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(25.0).unwrap())),
                ("humidity".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(15.0).unwrap())),
            ]),
            timestamp: chrono::Utc::now(),
            device_id: "sensor_001".to_string(),
            event_type: Some("sensor_data".to_string()),
            metadata: std::collections::HashMap::new(),
        };
        
        let results2 = rule_engine.evaluate_rules(context2).await.unwrap();
        assert_eq!(results2.len(), 0);
    }
}
```

### 安全认证测试

```rust
#[cfg(test)]
mod security_tests {
    use super::*;
    use c17_iot::security::*;
    use c17_iot::security::authentication::*;

    #[test]
    fn test_device_authentication() {
        let auth_config = AuthenticationConfig {
            token_expiry_hours: 24,
            max_active_tokens: 1000,
            enable_token_refresh: true,
            refresh_token_expiry_days: 30,
            enable_mfa: true,
        };
        let mut authenticator = DeviceAuthenticator::new(auth_config);
        
        // 创建有效证书
        let certificate = DeviceCertificate {
            device_id: "device_001".to_string(),
            public_key: "valid_key".to_string().into_bytes(),
            issued_at: chrono::Utc::now(),
            expires_at: chrono::Utc::now() + chrono::Duration::days(365),
            issuer: "Test CA".to_string(),
            signature: vec![],
            certificate_chain: vec![],
            extensions: std::collections::HashMap::new(),
        };
        
        let result = authenticator.authenticate_device("device_001", &certificate);
        assert!(result.is_ok());
        
        let token = result.unwrap();
        assert!(!token.is_empty());
    }

    #[test]
    fn test_token_verification() {
        let auth_config = AuthenticationConfig::default();
        let mut authenticator = DeviceAuthenticator::new(auth_config);
        
        // 创建证书并认证
        let certificate = DeviceCertificate {
            device_id: "device_001".to_string(),
            public_key: "valid_key".to_string().into_bytes(),
            issued_at: chrono::Utc::now(),
            expires_at: chrono::Utc::now() + chrono::Duration::days(365),
            issuer: "Test CA".to_string(),
            signature: vec![],
            certificate_chain: vec![],
            extensions: std::collections::HashMap::new(),
        };
        
        let token = authenticator.authenticate_device("device_001", &certificate).unwrap();
        
        // 验证令牌
        let is_valid = authenticator.verify_token(&token);
        assert!(is_valid);
        
        // 验证无效令牌
        let is_invalid = authenticator.verify_token("invalid_token");
        assert!(!is_invalid);
    }

    #[test]
    fn test_access_control() {
        let auth_config = AuthenticationConfig::default();
        let mut authenticator = DeviceAuthenticator::new(auth_config);
        
        // 添加访问策略
        let access_rule = AccessRule {
            resource: "sensors/temperature".to_string(),
            action: "read".to_string(),
            effect: AccessEffect::Allow,
            conditions: vec![],
        };
        
        let access_policy = AccessPolicy {
            id: "sensor_read_policy".to_string(),
            name: "传感器读取策略".to_string(),
            description: "允许读取温度传感器".to_string(),
            rules: vec![access_rule],
            priority: 1,
            enabled: true,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        
        authenticator.add_access_policy(access_policy).unwrap();
        
        // 测试允许的访问
        let has_access = authenticator.check_access("device_001", "sensors/temperature", "read");
        assert!(has_access);
        
        // 测试拒绝的访问
        let no_access = authenticator.check_access("device_001", "sensors/temperature", "write");
        assert!(!no_access);
    }
}
```

## 集成测试

### 设备管理集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use c17_iot::*;

    #[tokio::test]
    async fn test_device_sensor_integration() {
        // 创建设备管理器
        let mut device_manager = device_management::DeviceManager::new();
        
        // 创建传感器网络
        let mut sensor_network = sensor_network::SensorNetwork::new();
        
        // 注册设备
        device_manager.register_device("sensor_001", "temperature", "room1").await.unwrap();
        
        // 添加传感器
        sensor_network.add_sensor("sensor_001", "temperature", "room1").await.unwrap();
        
        // 开始数据采集
        sensor_network.start_data_collection().await.unwrap();
        
        // 等待数据采集
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        
        // 验证数据
        let latest_data = sensor_network.get_latest_data("sensor_001").await.unwrap();
        assert!(latest_data.value.is_finite());
        
        // 验证设备状态
        let device_status = device_manager.get_device_status("sensor_001").await.unwrap();
        assert_eq!(device_status.status, device_management::DeviceStatus::Active);
    }

    #[tokio::test]
    async fn test_rule_engine_integration() {
        // 创建规则引擎
        let (mut rule_engine, _) = edge_computing::RuleEngine::new();
        
        // 创建传感器网络
        let mut sensor_network = sensor_network::SensorNetwork::new();
        sensor_network.add_sensor("sensor_001", "temperature", "room1").await.unwrap();
        
        // 添加规则
        let condition = edge_computing::Condition::Simple {
            field: "temperature".to_string(),
            operator: edge_computing::rule_engine::Operator::GreaterThan,
            value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = edge_computing::Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: edge_computing::rule_engine::AlertLevel::Warning,
        };
        
        let rule = edge_computing::Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        rule_engine.add_rule(rule).await.unwrap();
        
        // 开始数据采集
        sensor_network.start_data_collection().await.unwrap();
        
        // 等待数据采集
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        
        // 获取数据并评估规则
        let latest_data = sensor_network.get_latest_data("sensor_001").await.unwrap();
        
        let context = edge_computing::rule_engine::RuleContext {
            data: std::collections::HashMap::from([
                ("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(latest_data.value).unwrap())),
            ]),
            timestamp: chrono::Utc::now(),
            device_id: "sensor_001".to_string(),
            event_type: Some("sensor_data".to_string()),
            metadata: std::collections::HashMap::new(),
        };
        
        let results = rule_engine.evaluate_rules(context).await.unwrap();
        // 根据实际数据值验证规则是否触发
        if latest_data.value > 30.0 {
            assert_eq!(results.len(), 1);
        } else {
            assert_eq!(results.len(), 0);
        }
    }
}
```

## 性能测试

### 基准测试

```rust
#[cfg(test)]
mod performance_tests {
    use super::*;
    use std::time::Instant;

    #[tokio::test]
    async fn test_device_registration_performance() {
        let mut device_manager = device_management::DeviceManager::new();
        
        let start = Instant::now();
        
        // 批量注册设备
        for i in 0..1000 {
            device_manager.register_device(
                &format!("device_{}", i),
                "sensor",
                "room1"
            ).await.unwrap();
        }
        
        let duration = start.elapsed();
        println!("注册1000个设备耗时: {:?}", duration);
        
        // 验证性能要求（例如：1000个设备注册应在1秒内完成）
        assert!(duration.as_secs() < 1);
    }

    #[tokio::test]
    async fn test_sensor_data_collection_performance() {
        let mut sensor_network = sensor_network::SensorNetwork::new();
        
        // 添加多个传感器
        for i in 0..100 {
            sensor_network.add_sensor(
                &format!("sensor_{}", i),
                "temperature",
                "room1"
            ).await.unwrap();
        }
        
        sensor_network.start_data_collection().await.unwrap();
        
        let start = Instant::now();
        
        // 等待数据采集
        tokio::time::sleep(std::time::Duration::from_secs(1)).await;
        
        let duration = start.elapsed();
        
        // 验证所有传感器都有数据
        for i in 0..100 {
            let data = sensor_network.get_latest_data(&format!("sensor_{}", i)).await.unwrap();
            assert!(data.value.is_finite());
        }
        
        println!("100个传感器数据采集耗时: {:?}", duration);
    }

    #[tokio::test]
    async fn test_rule_engine_performance() {
        let (mut rule_engine, _) = edge_computing::RuleEngine::new();
        
        // 添加多个规则
        for i in 0..100 {
            let condition = edge_computing::Condition::Simple {
                field: "temperature".to_string(),
                operator: edge_computing::rule_engine::Operator::GreaterThan,
                value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
            };
            
            let action = edge_computing::Action::SendAlert {
                message: format!("告警 {}", i),
                recipients: vec!["admin@example.com".to_string()],
                level: edge_computing::rule_engine::AlertLevel::Warning,
            };
            
            let rule = edge_computing::Rule::new(
                format!("rule_{}", i),
                format!("规则 {}", i),
                condition,
                action,
                i,
            );
            
            rule_engine.add_rule(rule).await.unwrap();
        }
        
        let start = Instant::now();
        
        // 评估规则
        let context = edge_computing::rule_engine::RuleContext {
            data: std::collections::HashMap::from([
                ("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(35.0).unwrap())),
            ]),
            timestamp: chrono::Utc::now(),
            device_id: "sensor_001".to_string(),
            event_type: Some("sensor_data".to_string()),
            metadata: std::collections::HashMap::new(),
        };
        
        let results = rule_engine.evaluate_rules(context).await.unwrap();
        
        let duration = start.elapsed();
        println!("评估100个规则耗时: {:?}", duration);
        
        // 验证性能要求
        assert!(duration.as_millis() < 100); // 应在100ms内完成
        assert_eq!(results.len(), 100); // 所有规则都应该触发
    }
}
```

## 安全测试

### 认证安全测试

```rust
#[cfg(test)]
mod security_tests {
    use super::*;
    use c17_iot::security::*;
    use c17_iot::security::authentication::*;

    #[test]
    fn test_certificate_validation() {
        let auth_config = AuthenticationConfig::default();
        let mut authenticator = DeviceAuthenticator::new(auth_config);
        
        // 测试过期证书
        let expired_certificate = DeviceCertificate {
            device_id: "device_001".to_string(),
            public_key: "valid_key".to_string().into_bytes(),
            issued_at: chrono::Utc::now() - chrono::Duration::days(400),
            expires_at: chrono::Utc::now() - chrono::Duration::days(1), // 过期
            issuer: "Test CA".to_string(),
            signature: vec![],
            certificate_chain: vec![],
            extensions: std::collections::HashMap::new(),
        };
        
        let result = authenticator.authenticate_device("device_001", &expired_certificate);
        assert!(result.is_err());
    }

    #[test]
    fn test_token_security() {
        let auth_config = AuthenticationConfig::default();
        let mut authenticator = DeviceAuthenticator::new(auth_config);
        
        // 创建有效证书
        let certificate = DeviceCertificate {
            device_id: "device_001".to_string(),
            public_key: "valid_key".to_string().into_bytes(),
            issued_at: chrono::Utc::now(),
            expires_at: chrono::Utc::now() + chrono::Duration::days(365),
            issuer: "Test CA".to_string(),
            signature: vec![],
            certificate_chain: vec![],
            extensions: std::collections::HashMap::new(),
        };
        
        let token = authenticator.authenticate_device("device_001", &certificate).unwrap();
        
        // 测试令牌长度（应该足够长以确保安全性）
        assert!(token.len() >= 32);
        
        // 测试令牌唯一性
        let token2 = authenticator.authenticate_device("device_002", &certificate).unwrap();
        assert_ne!(token, token2);
    }

    #[test]
    fn test_access_control_security() {
        let auth_config = AuthenticationConfig::default();
        let mut authenticator = DeviceAuthenticator::new(auth_config);
        
        // 添加限制性访问策略
        let access_rule = AccessRule {
            resource: "sensors/temperature".to_string(),
            action: "read".to_string(),
            effect: AccessEffect::Allow,
            conditions: vec![],
        };
        
        let access_policy = AccessPolicy {
            id: "restrictive_policy".to_string(),
            name: "限制性策略".to_string(),
            description: "只允许读取温度传感器".to_string(),
            rules: vec![access_rule],
            priority: 1,
            enabled: true,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        
        authenticator.add_access_policy(access_policy).unwrap();
        
        // 测试允许的操作
        assert!(authenticator.check_access("device_001", "sensors/temperature", "read"));
        
        // 测试拒绝的操作
        assert!(!authenticator.check_access("device_001", "sensors/temperature", "write"));
        assert!(!authenticator.check_access("device_001", "sensors/humidity", "read"));
        assert!(!authenticator.check_access("device_001", "admin/control", "read"));
    }
}
```

## 端到端测试

### 完整场景测试

```rust
#[cfg(test)]
mod e2e_tests {
    use super::*;
    use c17_iot::*;

    #[tokio::test]
    async fn test_complete_iot_scenario() {
        // 1. 创建设备管理器
        let mut device_manager = device_management::DeviceManager::new();
        
        // 2. 创建传感器网络
        let mut sensor_network = sensor_network::SensorNetwork::new();
        
        // 3. 创建规则引擎
        let (mut rule_engine, _) = edge_computing::RuleEngine::new();
        
        // 4. 创建安全认证器
        let auth_config = security::authentication::AuthenticationConfig::default();
        let mut authenticator = security::DeviceAuthenticator::new(auth_config);
        
        // 5. 创建监控仪表盘
        let config = monitoring::dashboard::DashboardConfig::default();
        let mut dashboard = monitoring::dashboard::MonitoringDashboard::new(config);
        
        // 6. 注册设备
        device_manager.register_device("sensor_001", "temperature", "room1").await.unwrap();
        
        // 7. 添加传感器
        sensor_network.add_sensor("sensor_001", "temperature", "room1").await.unwrap();
        
        // 8. 添加规则
        let condition = edge_computing::Condition::Simple {
            field: "temperature".to_string(),
            operator: edge_computing::rule_engine::Operator::GreaterThan,
            value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };
        
        let action = edge_computing::Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: edge_computing::rule_engine::AlertLevel::Warning,
        };
        
        let rule = edge_computing::Rule::new(
            "temp_alert".to_string(),
            "温度告警".to_string(),
            condition,
            action,
            1,
        );
        
        rule_engine.add_rule(rule).await.unwrap();
        
        // 9. 开始数据采集
        sensor_network.start_data_collection().await.unwrap();
        
        // 10. 等待数据采集
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        
        // 11. 获取数据并评估规则
        let latest_data = sensor_network.get_latest_data("sensor_001").await.unwrap();
        
        let context = edge_computing::rule_engine::RuleContext {
            data: std::collections::HashMap::from([
                ("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(latest_data.value).unwrap())),
            ]),
            timestamp: chrono::Utc::now(),
            device_id: "sensor_001".to_string(),
            event_type: Some("sensor_data".to_string()),
            metadata: std::collections::HashMap::new(),
        };
        
        let results = rule_engine.evaluate_rules(context).await.unwrap();
        
        // 12. 更新监控仪表盘
        dashboard.update_system_status().await.unwrap();
        
        // 13. 验证端到端流程
        assert!(latest_data.value.is_finite());
        assert!(latest_data.timestamp <= chrono::Utc::now());
        
        if latest_data.value > 30.0 {
            assert_eq!(results.len(), 1);
            assert_eq!(results[0].rule_id, "temp_alert");
        }
        
        // 14. 清理资源
        sensor_network.stop_data_collection().await.unwrap();
    }
}
```

## 测试覆盖率

### 覆盖率目标

- **单元测试覆盖率**: ≥ 90%
- **集成测试覆盖率**: ≥ 80%
- **端到端测试覆盖率**: ≥ 70%

### 覆盖率报告

```bash
# 运行测试并生成覆盖率报告
cargo test --coverage

# 查看覆盖率报告
open target/coverage/index.html
```

### 覆盖率监控

```rust
// 在测试中添加覆盖率检查
#[cfg(test)]
mod coverage_tests {
    use super::*;

    #[test]
    fn test_all_public_methods() {
        // 确保所有公共方法都有测试覆盖
        let device_manager = device_management::DeviceManager::new();
        // ... 测试所有公共方法
    }
}
```

## 测试最佳实践

### 1. 测试命名

```rust
// 好的测试命名
#[test]
fn test_register_device_success() { }

#[test]
fn test_register_device_duplicate_error() { }

#[test]
fn test_register_device_invalid_input() { }

// 不好的测试命名
#[test]
fn test1() { }

#[test]
fn test_device() { }
```

### 2. 测试结构

```rust
#[test]
fn test_register_device() {
    // Arrange - 准备测试数据
    let mut device_manager = DeviceManager::new();
    let device_id = "test_device";
    let device_type = "sensor";
    let location = "room1";
    
    // Act - 执行被测试的操作
    let result = device_manager.register_device(device_id, device_type, location);
    
    // Assert - 验证结果
    assert!(result.is_ok());
    assert_eq!(device_manager.get_device_count(), 1);
}
```

### 3. 测试数据管理

```rust
// 使用测试辅助函数
fn create_test_device_manager() -> DeviceManager {
    DeviceManager::new()
}

fn create_test_certificate(device_id: &str) -> DeviceCertificate {
    DeviceCertificate {
        device_id: device_id.to_string(),
        public_key: "test_key".to_string().into_bytes(),
        issued_at: chrono::Utc::now(),
        expires_at: chrono::Utc::now() + chrono::Duration::days(365),
        issuer: "Test CA".to_string(),
        signature: vec![],
        certificate_chain: vec![],
        extensions: std::collections::HashMap::new(),
    }
}
```

### 4. 异步测试

```rust
#[tokio::test]
async fn test_async_operation() {
    let mut device_manager = DeviceManager::new();
    
    // 使用 tokio::time::timeout 设置超时
    let result = tokio::time::timeout(
        std::time::Duration::from_secs(5),
        device_manager.register_device("device_001", "sensor", "room1")
    ).await;
    
    assert!(result.is_ok());
}
```

### 5. 错误测试

```rust
#[test]
fn test_error_handling() {
    let device_manager = DeviceManager::new();
    
    // 测试错误情况
    let result = device_manager.get_device_status("nonexistent");
    assert!(matches!(result, Err(DeviceManagementError::DeviceNotFound)));
}
```

## 持续集成

### GitHub Actions 配置

```yaml
name: Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v2
    
    - name: Setup Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable
        components: rustfmt, clippy
    
    - name: Run tests
      run: cargo test --verbose
    
    - name: Run clippy
      run: cargo clippy -- -D warnings
    
    - name: Run fmt
      run: cargo fmt -- --check
    
    - name: Generate coverage
      run: cargo test --coverage
    
    - name: Upload coverage
      uses: codecov/codecov-action@v1
```

### 测试命令

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_register_device

# 运行集成测试
cargo test --test integration_tests

# 运行性能测试
cargo test --test performance_tests --release

# 运行安全测试
cargo test --test security_tests

# 运行端到端测试
cargo test --test e2e_tests
```

## 总结

本测试指南提供了 `c17_iot` 项目的完整测试策略，包括：

1. **单元测试** - 确保每个模块的正确性
2. **集成测试** - 验证模块间的交互
3. **性能测试** - 确保系统性能满足要求
4. **安全测试** - 验证安全功能
5. **端到端测试** - 测试完整的用户场景

通过遵循这些测试最佳实践，可以确保 `c17_iot` 项目的质量和可靠性。
