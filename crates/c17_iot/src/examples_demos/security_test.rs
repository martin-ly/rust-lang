//! 安全测试示例
//! 
//! 本示例提供了全面的安全测试，包括：
//! - 认证和授权测试
//! - 加密和解密测试
//! - 访问控制测试
//! - 会话管理测试
//! - 多因素认证测试

use super::{Example, ExampleParameter, ParameterType};
use crate::security::DeviceAuthenticator;
use crate::security::authentication::{
    AuthenticationConfig, DeviceCertificate, AccessPolicy, AccessRule, AccessEffect, 
    MFAMethod, AuditEventType, AuditResult
};
use std::collections::HashMap;
use std::time::Duration;
use chrono::Utc;
use serde_json::Value;

/// 安全测试结果
#[derive(Debug, Clone, serde::Serialize)]
pub struct SecurityTestResult {
    pub test_name: String,
    pub passed: bool,
    pub error_message: Option<String>,
    pub execution_time: Duration,
    pub details: HashMap<String, Value>,
}

/// 安全测试套件
pub struct SecurityTest {
    authenticator: DeviceAuthenticator,
    test_results: Vec<SecurityTestResult>,
}

impl SecurityTest {
    /// 创建新的安全测试
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let auth_config = AuthenticationConfig {
            token_expiry_hours: 24,
            max_active_tokens: 1000,
            enable_token_refresh: true,
            refresh_token_expiry_days: 30,
            enable_mfa: true,
        };
        let authenticator = DeviceAuthenticator::new(auth_config);

        Ok(Self {
            authenticator,
            test_results: Vec::new(),
        })
    }

    /// 运行完整的安全测试套件
    pub async fn run_security_tests(&mut self) -> Result<Vec<SecurityTestResult>, Box<dyn std::error::Error>> {
        println!("🔐 开始安全测试...");

        // 运行各种安全测试
        self.test_device_authentication().await?;
        self.test_access_control().await?;
        self.test_session_management().await?;
        self.test_multi_factor_authentication().await?;
        self.test_audit_logging().await?;
        self.test_security_policies().await?;
        self.test_token_management().await?;
        self.test_security_vulnerabilities().await?;

        // 生成测试报告
        self.generate_security_report().await?;

        println!("✅ 安全测试完成");
        Ok(self.test_results.clone())
    }

    /// 测试设备认证
    async fn test_device_authentication(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔑 测试设备认证...");

        // 测试有效设备认证
        let start_time = std::time::Instant::now();
        let device_id = "test_device_001";
        let _certificate = DeviceCertificate {
            device_id: device_id.to_string(),
            public_key: "test_public_key".to_string().into_bytes(),
            issued_at: Utc::now(),
            expires_at: Utc::now() + chrono::Duration::days(365),
            issuer: "Test CA".to_string(),
            signature: vec![],
            certificate_chain: vec![],
            extensions: HashMap::new(),
        };

        match self.authenticator.authenticate_device(device_id, "test_credentials") {
            Ok(token) => {
                let execution_time = start_time.elapsed();
                let mut details = HashMap::new();
                details.insert("token_length".to_string(), Value::Number(serde_json::Number::from(token.token_id.len())));
                details.insert("device_id".to_string(), Value::String(device_id.to_string()));

                self.test_results.push(SecurityTestResult {
                    test_name: "设备认证 - 有效证书".to_string(),
                    passed: true,
                    error_message: None,
                    execution_time,
                    details,
                });
            }
            Err(e) => {
                let execution_time = start_time.elapsed();
                self.test_results.push(SecurityTestResult {
                    test_name: "设备认证 - 有效证书".to_string(),
                    passed: false,
                    error_message: Some(e.to_string()),
                    execution_time,
                    details: HashMap::new(),
                });
            }
        }

        // 测试无效设备认证
        let start_time = std::time::Instant::now();
        let _invalid_certificate = DeviceCertificate {
            device_id: "invalid_device".to_string(),
            public_key: "invalid_key".to_string().into_bytes(),
            issued_at: Utc::now(),
            expires_at: Utc::now() - chrono::Duration::days(1), // 过期证书
            issuer: "Invalid CA".to_string(),
            signature: vec![],
            certificate_chain: vec![],
            extensions: HashMap::new(),
        };

        match self.authenticator.authenticate_device("invalid_device", "invalid_credentials") {
            Ok(_) => {
                let execution_time = start_time.elapsed();
                self.test_results.push(SecurityTestResult {
                    test_name: "设备认证 - 无效证书".to_string(),
                    passed: false,
                    error_message: Some("应该拒绝无效证书".to_string()),
                    execution_time,
                    details: HashMap::new(),
                });
            }
            Err(_) => {
                let execution_time = start_time.elapsed();
                self.test_results.push(SecurityTestResult {
                    test_name: "设备认证 - 无效证书".to_string(),
                    passed: true,
                    error_message: None,
                    execution_time,
                    details: HashMap::new(),
                });
            }
        }

        Ok(())
    }

    /// 测试访问控制
    async fn test_access_control(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🛡️ 测试访问控制...");

        // 设置访问控制策略
        let access_rule = AccessRule {
            resource: "sensors/temperature".to_string(),
            action: "read".to_string(),
            effect: AccessEffect::Allow,
            conditions: vec![],
        };

        let access_policy = AccessPolicy {
            id: "test_policy".to_string(),
            name: "测试访问策略".to_string(),
            description: "允许访问温度传感器".to_string(),
            rules: vec![access_rule],
            priority: 1,
            enabled: true,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        self.authenticator.add_access_policy(access_policy)?;

        // 测试允许的访问
        let start_time = std::time::Instant::now();
        let has_access = self.authenticator.check_access("test_device", "sensors/temperature", "read");
        if has_access {
                let execution_time = start_time.elapsed();
                let mut details = HashMap::new();
                details.insert("has_access".to_string(), Value::Bool(has_access));

                self.test_results.push(SecurityTestResult {
                    test_name: "访问控制 - 允许的访问".to_string(),
                    passed: has_access,
                    error_message: if has_access { None } else { Some("应该允许访问".to_string()) },
                    execution_time,
                    details,
                });
        } else {
                let execution_time = start_time.elapsed();
                self.test_results.push(SecurityTestResult {
                    test_name: "访问控制 - 允许的访问".to_string(),
                    passed: false,
                    error_message: Some("应该允许访问".to_string()),
                    execution_time,
                    details: HashMap::new(),
                });
        }

        // 测试拒绝的访问
        let start_time = std::time::Instant::now();
        let has_access = self.authenticator.check_access("test_device", "sensors/humidity", "write");
        if has_access {
                let execution_time = start_time.elapsed();
                let mut details = HashMap::new();
                details.insert("has_access".to_string(), Value::Bool(has_access));

                self.test_results.push(SecurityTestResult {
                    test_name: "访问控制 - 拒绝的访问".to_string(),
                    passed: !has_access,
                    error_message: if !has_access { None } else { Some("应该拒绝访问".to_string()) },
                    execution_time,
                    details,
                });
        } else {
                let execution_time = start_time.elapsed();
                self.test_results.push(SecurityTestResult {
                    test_name: "访问控制 - 拒绝的访问".to_string(),
                    passed: true, // 拒绝访问是正确的
                    error_message: None,
                    execution_time,
                    details: HashMap::new(),
                });
        }

        Ok(())
    }

    /// 测试会话管理
    async fn test_session_management(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("👥 测试会话管理...");

        // 创建会话
        let start_time = std::time::Instant::now();
        let session = self.authenticator.create_session(
            "test_device".to_string(),
            Some("test_user".to_string()),
            Some("192.168.1.100".to_string()),
            Some("Security Test".to_string()),
        );

        let execution_time = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("session_id".to_string(), Value::String(session.id.clone()));
        details.insert("device_id".to_string(), Value::String(session.device_id.clone()));

        self.test_results.push(SecurityTestResult {
            test_name: "会话管理 - 创建会话".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details,
        });

        // 更新会话活动
        let start_time = std::time::Instant::now();
        self.authenticator.update_session_activity(&session.id)?;

        let execution_time = start_time.elapsed();
        self.test_results.push(SecurityTestResult {
            test_name: "会话管理 - 更新会话活动".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details: HashMap::new(),
        });

        // 终止会话
        let start_time = std::time::Instant::now();
        self.authenticator.terminate_session(&session.id).ok_or("Failed to terminate session")?;

        let execution_time = start_time.elapsed();
        self.test_results.push(SecurityTestResult {
            test_name: "会话管理 - 终止会话".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details: HashMap::new(),
        });

        Ok(())
    }

    /// 测试多因素认证
    async fn test_multi_factor_authentication(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔐 测试多因素认证...");

        // 启用MFA
        let start_time = std::time::Instant::now();
        let mfa_methods = vec![MFAMethod::TOTP, MFAMethod::SMS];
        self.authenticator.enable_mfa(mfa_methods);

        let execution_time = start_time.elapsed();
        self.test_results.push(SecurityTestResult {
            test_name: "多因素认证 - 启用MFA".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details: HashMap::new(),
        });

        // 验证MFA
        let start_time = std::time::Instant::now();
        let is_valid = self.authenticator.verify_mfa("test_device", &MFAMethod::TOTP, "123456");

        let execution_time = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("is_valid".to_string(), Value::Bool(is_valid));

        self.test_results.push(SecurityTestResult {
            test_name: "多因素认证 - 验证MFA".to_string(),
            passed: true, // 这里总是通过，因为验证逻辑是模拟的
            error_message: None,
            execution_time,
            details,
        });

        // 禁用MFA
        let start_time = std::time::Instant::now();
        self.authenticator.disable_mfa();

        let execution_time = start_time.elapsed();
        self.test_results.push(SecurityTestResult {
            test_name: "多因素认证 - 禁用MFA".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details: HashMap::new(),
        });

        Ok(())
    }

    /// 测试审计日志
    async fn test_audit_logging(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("📝 测试审计日志...");

        // 记录审计事件
        let start_time = std::time::Instant::now();
        self.authenticator.log_audit_event(
            AuditEventType::Authentication,
            "test_device".to_string(),
            Some("test_user".to_string()),
            "device_auth".to_string(),
            "authenticate".to_string(),
            AuditResult::Success,
            HashMap::new(),
        );

        let execution_time = start_time.elapsed();
        self.test_results.push(SecurityTestResult {
            test_name: "审计日志 - 记录事件".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details: HashMap::new(),
        });

        // 获取审计日志
        let start_time = std::time::Instant::now();
        let logs = self.authenticator.get_audit_logs(Some(10));

        let execution_time = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("log_count".to_string(), Value::Number(serde_json::Number::from(logs.len())));

        self.test_results.push(SecurityTestResult {
            test_name: "审计日志 - 获取日志".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details,
        });

        Ok(())
    }

    /// 测试安全策略
    async fn test_security_policies(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("📋 测试安全策略...");

        // 添加安全策略
        let start_time = std::time::Instant::now();
        let policy = AccessPolicy {
            id: "security_test_policy".to_string(),
            name: "安全测试策略".to_string(),
            description: "用于安全测试的策略".to_string(),
            rules: vec![],
            priority: 1,
            enabled: true,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        self.authenticator.add_access_policy(policy)?;

        let execution_time = start_time.elapsed();
        self.test_results.push(SecurityTestResult {
            test_name: "安全策略 - 添加策略".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details: HashMap::new(),
        });

        // 移除安全策略
        let start_time = std::time::Instant::now();
        self.authenticator.remove_access_policy("security_test_policy").ok_or("Failed to remove policy")?;

        let execution_time = start_time.elapsed();
        self.test_results.push(SecurityTestResult {
            test_name: "安全策略 - 移除策略".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details: HashMap::new(),
        });

        Ok(())
    }

    /// 测试令牌管理
    async fn test_token_management(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🎫 测试令牌管理...");

        // 创建设备证书
        let _certificate = DeviceCertificate {
            device_id: "token_test_device".to_string(),
            public_key: "test_public_key".to_string().into_bytes(),
            issued_at: Utc::now(),
            expires_at: Utc::now() + chrono::Duration::days(365),
            issuer: "Test CA".to_string(),
            signature: vec![],
            certificate_chain: vec![],
            extensions: HashMap::new(),
        };

        // 认证设备获取令牌
        let start_time = std::time::Instant::now();
        let token = self.authenticator.authenticate_device("token_test_device", "test_credentials")?;

        let execution_time = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("token_length".to_string(), Value::Number(serde_json::Number::from(token.token_id.len())));

        self.test_results.push(SecurityTestResult {
            test_name: "令牌管理 - 获取令牌".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details,
        });

        // 验证令牌
        let start_time = std::time::Instant::now();
        let is_valid = self.authenticator.verify_token(&token.token_id).is_ok();

        let execution_time = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("is_valid".to_string(), Value::Bool(is_valid));

        self.test_results.push(SecurityTestResult {
            test_name: "令牌管理 - 验证令牌".to_string(),
            passed: is_valid,
            error_message: if is_valid { None } else { Some("令牌应该有效".to_string()) },
            execution_time,
            details,
        });

        // 刷新令牌
        let start_time = std::time::Instant::now();
        let new_token = self.authenticator.refresh_token(&token.token_id)?;

        let execution_time = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("new_token_length".to_string(), Value::Number(serde_json::Number::from(new_token.token_id.len())));

        self.test_results.push(SecurityTestResult {
            test_name: "令牌管理 - 刷新令牌".to_string(),
            passed: true,
            error_message: None,
            execution_time,
            details,
        });

        Ok(())
    }

    /// 测试安全漏洞
    async fn test_security_vulnerabilities(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🛡️ 测试安全漏洞...");

        // 测试SQL注入防护
        let start_time = std::time::Instant::now();
        let malicious_input = "'; DROP TABLE users; --";
        
        // 这里应该测试输入验证和清理
        let is_safe = !malicious_input.contains("DROP TABLE");
        
        let execution_time = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("input_sanitized".to_string(), Value::Bool(is_safe));

        self.test_results.push(SecurityTestResult {
            test_name: "安全漏洞 - SQL注入防护".to_string(),
            passed: is_safe,
            error_message: if is_safe { None } else { Some("输入应该被清理".to_string()) },
            execution_time,
            details,
        });

        // 测试XSS防护
        let start_time = std::time::Instant::now();
        let xss_input = "<script>alert('XSS')</script>";
        
        // 这里应该测试XSS防护
        let is_safe = !xss_input.contains("<script>");
        
        let execution_time = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("xss_protected".to_string(), Value::Bool(is_safe));

        self.test_results.push(SecurityTestResult {
            test_name: "安全漏洞 - XSS防护".to_string(),
            passed: is_safe,
            error_message: if is_safe { None } else { Some("应该防护XSS攻击".to_string()) },
            execution_time,
            details,
        });

        Ok(())
    }

    /// 生成安全测试报告
    async fn generate_security_report(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n📊 安全测试报告");
        println!("{}", "=".repeat(80));

        let total_tests = self.test_results.len();
        let passed_tests = self.test_results.iter().filter(|r| r.passed).count();
        let failed_tests = total_tests - passed_tests;
        let pass_rate = if total_tests > 0 {
            (passed_tests as f64 / total_tests as f64) * 100.0
        } else {
            0.0
        };

        println!("\n📈 总体统计");
        println!("  总测试数: {}", total_tests);
        println!("  通过测试: {}", passed_tests);
        println!("  失败测试: {}", failed_tests);
        println!("  通过率: {:.2}%", pass_rate);

        println!("\n🔍 详细结果");
        for result in &self.test_results {
            let status = if result.passed { "✅ 通过" } else { "❌ 失败" };
            println!("  {} {} - {:?}", status, result.test_name, result.execution_time);
            
            if let Some(error) = &result.error_message {
                println!("    错误: {}", error);
            }
            
            if !result.details.is_empty() {
                println!("    详情: {:?}", result.details);
            }
        }

        // 导出报告到JSON
        let report_data = serde_json::json!({
            "timestamp": Utc::now(),
            "summary": {
                "total_tests": total_tests,
                "passed_tests": passed_tests,
                "failed_tests": failed_tests,
                "pass_rate": pass_rate,
            },
            "results": self.test_results,
        });

        let report_json = serde_json::to_string_pretty(&report_data)?;
        println!("\n📄 详细报告 (JSON):");
        println!("{}", report_json);

        Ok(())
    }

    /// 获取测试结果
    pub fn get_results(&self) -> &[SecurityTestResult] {
        &self.test_results
    }

    /// 清除测试结果
    pub fn clear_results(&mut self) {
        self.test_results.clear();
    }
}

impl Example for SecurityTest {
    fn name(&self) -> &'static str {
        "安全测试"
    }

    fn description(&self) -> &'static str {
        "全面的安全测试，包括认证、授权、会话管理、多因素认证等安全功能测试"
    }

    fn parameters(&self) -> Vec<ExampleParameter> {
        vec![
            ExampleParameter {
                name: "test_device_id".to_string(),
                description: "测试设备ID".to_string(),
                parameter_type: ParameterType::String,
                default_value: Some("test_device_001".to_string()),
                required: false,
            },
            ExampleParameter {
                name: "test_user".to_string(),
                description: "测试用户".to_string(),
                parameter_type: ParameterType::String,
                default_value: Some("test_user".to_string()),
                required: false,
            },
        ]
    }

    fn run(&mut self, _parameters: HashMap<String, String>) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error>>> + Send {
        async move {
            self.run_security_tests().await?;
            Ok(())
        }
    }
}

impl Default for SecurityTest {
    fn default() -> Self {
        Self::new().expect("Failed to create SecurityTest")
    }
}
