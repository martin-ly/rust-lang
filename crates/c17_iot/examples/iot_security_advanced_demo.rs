//! 高级IoT安全演示示例
//! 
//! 展示如何使用c17_iot的高级安全功能进行零信任架构、量子加密和安全审计

use c17_iot::iot_security_advanced::{
    AdvancedIoTSecurityManager, SecurityConfig, SecurityEvent, ZeroTrustPolicy,
    QuantumEncryptionConfig, SecurityAuditRecord, SecurityThreatType, ThreatLevel,
    SecurityEventType, SecurityEventStatus, ZeroTrustPolicyType,
    QuantumEncryptionAlgorithm, QKDProtocol, AuditType, AuditResult, ComplianceStatus,
    ZeroTrustRule, RuleCondition, RuleAction, ConditionType, ConditionOperator, ActionType,
    RuleStatus, PolicyStatus, EncryptionStatus
};
use std::time::Duration;
use std::collections::HashMap;
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动高级IoT安全演示...");

    println!("📊 开始演示IoT系统高级安全功能...");

    // 1. 高级安全管理器创建和配置
    println!("\n1️⃣ 高级安全管理器创建和配置");
    demo_security_manager_creation().await?;

    // 2. 安全事件管理
    println!("\n2️⃣ 安全事件管理");
    demo_security_event_management().await?;

    // 3. 零信任架构
    println!("\n3️⃣ 零信任架构");
    demo_zero_trust_architecture().await?;

    // 4. 量子加密
    println!("\n4️⃣ 量子加密");
    demo_quantum_encryption().await?;

    // 5. 安全审计
    println!("\n5️⃣ 安全审计");
    demo_security_audit().await?;

    // 6. 威胁检测
    println!("\n6️⃣ 威胁检测");
    demo_threat_detection().await?;

    // 7. 自动响应
    println!("\n7️⃣ 自动响应");
    demo_auto_response().await?;

    // 8. 安全统计和报告
    println!("\n8️⃣ 安全统计和报告");
    demo_security_statistics().await?;

    println!("\n✅ 高级IoT安全演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 安全事件管理");
    println!("  - 零信任架构");
    println!("  - 量子加密");
    println!("  - 安全审计");
    println!("  - 威胁检测和自动响应");

    Ok(())
}

/// 高级安全管理器创建和配置演示
async fn demo_security_manager_creation() -> Result<(), Box<dyn std::error::Error>> {
    // 创建安全配置
    let config = SecurityConfig {
        enable_advanced_security: true,
        enable_zero_trust: true,
        enable_quantum_encryption: true,
        enable_security_audit: true,
        threat_detection_threshold: 0.7,
        enable_auto_response: true,
        audit_interval: Duration::from_secs(3600),
        custom_params: HashMap::new(),
    };

    println!("  创建高级安全管理器...");
    let security_manager = AdvancedIoTSecurityManager::new(config);
    
    // 获取初始统计信息
    let stats = security_manager.get_security_stats().await;
    println!("  初始安全统计:");
    println!("    总安全事件数: {}", stats.total_security_events);
    println!("    活跃威胁数: {}", stats.active_threats);
    println!("    已解决威胁数: {}", stats.resolved_threats);
    println!("    平均响应时间: {:?}", stats.avg_response_time);
    println!("    零信任策略数: {}", stats.zero_trust_policies_count);
    println!("    量子加密配置数: {}", stats.quantum_encryption_configs_count);
    println!("    审计记录数: {}", stats.audit_records_count);
    println!("    合规率: {:.2}%", stats.compliance_rate * 100.0);

    Ok(())
}

/// 安全事件管理演示
async fn demo_security_event_management() -> Result<(), Box<dyn std::error::Error>> {
    let security_manager = AdvancedIoTSecurityManager::new(SecurityConfig::default());
    
    println!("  创建安全事件...");
    
    // 创建不同类型的安全事件
    let security_events = vec![
        create_security_event("malware_event", SecurityThreatType::Malware, ThreatLevel::High, "检测到恶意软件"),
        create_security_event("network_attack", SecurityThreatType::NetworkAttack, ThreatLevel::Critical, "检测到网络攻击"),
        create_security_event("data_breach", SecurityThreatType::DataBreach, ThreatLevel::Emergency, "检测到数据泄露"),
        create_security_event("identity_spoofing", SecurityThreatType::IdentitySpoofing, ThreatLevel::Medium, "检测到身份伪造"),
        create_security_event("dos_attack", SecurityThreatType::DoSAttack, ThreatLevel::High, "检测到拒绝服务攻击"),
    ];
    
    for event in security_events {
        let event_id = security_manager.create_security_event(event.clone()).await?;
        println!("    安全事件已创建: {} - {:?}", event_id, event.threat_type);
    }
    
    // 获取安全事件列表
    let all_events = security_manager.get_security_events(None, None).await;
    println!("  安全事件统计:");
    println!("    总事件数: {}", all_events.len());
    
    let mut threat_type_count = HashMap::new();
    for event in &all_events {
        *threat_type_count.entry(&event.threat_type).or_insert(0) += 1;
    }
    
    for (threat_type, count) in threat_type_count {
        println!("    {:?}: {} 个", threat_type, count);
    }
    
    // 按状态统计
    let new_events = security_manager.get_security_events(Some(SecurityEventStatus::New), None).await;
    let investigating_events = security_manager.get_security_events(Some(SecurityEventStatus::Investigating), None).await;
    let resolved_events = security_manager.get_security_events(Some(SecurityEventStatus::Resolved), None).await;
    
    println!("  事件状态统计:");
    println!("    新事件: {} 个", new_events.len());
    println!("    调查中: {} 个", investigating_events.len());
    println!("    已解决: {} 个", resolved_events.len());

    Ok(())
}

/// 零信任架构演示
async fn demo_zero_trust_architecture() -> Result<(), Box<dyn std::error::Error>> {
    let security_manager = AdvancedIoTSecurityManager::new(SecurityConfig::default());
    
    println!("  创建零信任策略...");
    
    // 创建身份验证策略
    let auth_policy = ZeroTrustPolicy {
        policy_id: "auth_policy_001".to_string(),
        policy_name: "身份验证策略".to_string(),
        policy_type: ZeroTrustPolicyType::AuthenticationPolicy,
        rules: vec![
            ZeroTrustRule {
                rule_id: "auth_rule_001".to_string(),
                rule_name: "多因子认证规则".to_string(),
                conditions: vec![
                    RuleCondition {
                        condition_type: ConditionType::UserIdentity,
                        field: "user_role".to_string(),
                        operator: ConditionOperator::Equals,
                        value: "admin".to_string(),
                    },
                    RuleCondition {
                        condition_type: ConditionType::RiskScore,
                        field: "risk_score".to_string(),
                        operator: ConditionOperator::GreaterThan,
                        value: "0.5".to_string(),
                    },
                ],
                actions: vec![
                    RuleAction {
                        action_type: ActionType::RequireAdditionalAuth,
                        parameters: HashMap::from([
                            ("auth_method".to_string(), "mfa".to_string()),
                            ("timeout".to_string(), "300".to_string()),
                        ]),
                    },
                ],
                priority: 1,
                status: RuleStatus::Enabled,
            },
        ],
        status: PolicyStatus::Active,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
        description: "管理员用户多因子认证策略".to_string(),
    };
    
    let auth_policy_id = security_manager.create_zero_trust_policy(auth_policy).await?;
    println!("    身份验证策略已创建: {}", auth_policy_id);
    
    // 创建网络访问策略
    let network_policy = ZeroTrustPolicy {
        policy_id: "network_policy_001".to_string(),
        policy_name: "网络访问策略".to_string(),
        policy_type: ZeroTrustPolicyType::NetworkAccessPolicy,
        rules: vec![
            ZeroTrustRule {
                rule_id: "network_rule_001".to_string(),
                rule_name: "设备访问控制规则".to_string(),
                conditions: vec![
                    RuleCondition {
                        condition_type: ConditionType::DeviceType,
                        field: "device_type".to_string(),
                        operator: ConditionOperator::Equals,
                        value: "iot_device".to_string(),
                    },
                    RuleCondition {
                        condition_type: ConditionType::NetworkLocation,
                        field: "network_segment".to_string(),
                        operator: ConditionOperator::NotEquals,
                        value: "trusted_network".to_string(),
                    },
                ],
                actions: vec![
                    RuleAction {
                        action_type: ActionType::Deny,
                        parameters: HashMap::new(),
                    },
                    RuleAction {
                        action_type: ActionType::Log,
                        parameters: HashMap::from([
                            ("log_level".to_string(), "warning".to_string()),
                        ]),
                    },
                ],
                priority: 2,
                status: RuleStatus::Enabled,
            },
        ],
        status: PolicyStatus::Active,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
        description: "IoT设备网络访问控制策略".to_string(),
    };
    
    let network_policy_id = security_manager.create_zero_trust_policy(network_policy).await?;
    println!("    网络访问策略已创建: {}", network_policy_id);
    
    // 创建数据保护策略
    let data_policy = ZeroTrustPolicy {
        policy_id: "data_policy_001".to_string(),
        policy_name: "数据保护策略".to_string(),
        policy_type: ZeroTrustPolicyType::DataProtectionPolicy,
        rules: vec![
            ZeroTrustRule {
                rule_id: "data_rule_001".to_string(),
                rule_name: "敏感数据访问规则".to_string(),
                conditions: vec![
                    RuleCondition {
                        condition_type: ConditionType::DataSensitivity,
                        field: "data_classification".to_string(),
                        operator: ConditionOperator::Equals,
                        value: "confidential".to_string(),
                    },
                ],
                actions: vec![
                    RuleAction {
                        action_type: ActionType::RequireAdditionalAuth,
                        parameters: HashMap::from([
                            ("auth_method".to_string(), "biometric".to_string()),
                        ]),
                    },
                    RuleAction {
                        action_type: ActionType::Log,
                        parameters: HashMap::from([
                            ("log_level".to_string(), "info".to_string()),
                        ]),
                    },
                ],
                priority: 1,
                status: RuleStatus::Enabled,
            },
        ],
        status: PolicyStatus::Active,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
        description: "敏感数据访问控制策略".to_string(),
    };
    
    let data_policy_id = security_manager.create_zero_trust_policy(data_policy).await?;
    println!("    数据保护策略已创建: {}", data_policy_id);
    
    // 获取零信任策略列表
    let policies = security_manager.get_zero_trust_policies().await;
    println!("  零信任策略统计:");
    println!("    总策略数: {}", policies.len());
    
    let mut policy_type_count = HashMap::new();
    for policy in &policies {
        *policy_type_count.entry(&policy.policy_type).or_insert(0) += 1;
    }
    
    for (policy_type, count) in policy_type_count {
        println!("    {:?}: {} 个", policy_type, count);
    }

    Ok(())
}

/// 量子加密演示
async fn demo_quantum_encryption() -> Result<(), Box<dyn std::error::Error>> {
    let security_manager = AdvancedIoTSecurityManager::new(SecurityConfig::default());
    
    println!("  创建量子加密配置...");
    
    // 创建BB84量子密钥分发配置
    let bb84_config = QuantumEncryptionConfig {
        config_id: "bb84_config_001".to_string(),
        algorithm: QuantumEncryptionAlgorithm::BB84,
        key_length: 256,
        qkd_protocol: QKDProtocol::BB84,
        security_parameters: HashMap::from([
            ("photon_count".to_string(), "1000".to_string()),
            ("error_threshold".to_string(), "0.11".to_string()),
            ("sift_rate".to_string(), "0.5".to_string()),
        ]),
        status: EncryptionStatus::Active,
        created_at: chrono::Utc::now(),
    };
    
    let bb84_config_id = security_manager.create_quantum_encryption_config(bb84_config).await?;
    println!("    BB84量子密钥分发配置已创建: {}", bb84_config_id);
    
    // 创建E91量子密钥分发配置
    let e91_config = QuantumEncryptionConfig {
        config_id: "e91_config_001".to_string(),
        algorithm: QuantumEncryptionAlgorithm::E91,
        key_length: 512,
        qkd_protocol: QKDProtocol::E91,
        security_parameters: HashMap::from([
            ("entanglement_source".to_string(), "spontaneous_parametric_down_conversion".to_string()),
            ("detection_efficiency".to_string(), "0.8".to_string()),
            ("visibility".to_string(), "0.95".to_string()),
        ]),
        status: EncryptionStatus::Active,
        created_at: chrono::Utc::now(),
    };
    
    let e91_config_id = security_manager.create_quantum_encryption_config(e91_config).await?;
    println!("    E91量子密钥分发配置已创建: {}", e91_config_id);
    
    // 创建后量子密码学配置
    let pqc_config = QuantumEncryptionConfig {
        config_id: "pqc_config_001".to_string(),
        algorithm: QuantumEncryptionAlgorithm::PostQuantumCryptography,
        key_length: 1024,
        qkd_protocol: QKDProtocol::Custom("NIST_PQC".to_string()),
        security_parameters: HashMap::from([
            ("algorithm_family".to_string(), "lattice_based".to_string()),
            ("security_level".to_string(), "128".to_string()),
            ("key_exchange".to_string(), "kyber".to_string()),
        ]),
        status: EncryptionStatus::Testing,
        created_at: chrono::Utc::now(),
    };
    
    let pqc_config_id = security_manager.create_quantum_encryption_config(pqc_config).await?;
    println!("    后量子密码学配置已创建: {}", pqc_config_id);
    
    // 获取量子加密配置列表
    let configs = security_manager.get_quantum_encryption_configs().await;
    println!("  量子加密配置统计:");
    println!("    总配置数: {}", configs.len());
    
    let mut algorithm_count = HashMap::new();
    for config in &configs {
        *algorithm_count.entry(&config.algorithm).or_insert(0) += 1;
    }
    
    for (algorithm, count) in algorithm_count {
        println!("    {:?}: {} 个", algorithm, count);
    }
    
    // 显示配置详情
    for config in &configs {
        println!("    配置 {}: {:?} - 密钥长度: {} 位, 状态: {:?}", 
                config.config_id, 
                config.algorithm, 
                config.key_length, 
                config.status);
    }

    Ok(())
}

/// 安全审计演示
async fn demo_security_audit() -> Result<(), Box<dyn std::error::Error>> {
    let security_manager = AdvancedIoTSecurityManager::new(SecurityConfig::default());
    
    println!("  创建安全审计记录...");
    
    // 创建安全配置审计记录
    let config_audit = SecurityAuditRecord {
        record_id: "config_audit_001".to_string(),
        audit_type: AuditType::SecurityConfigurationAudit,
        audit_target: "system_security_config".to_string(),
        audit_result: AuditResult::Pass,
        audit_time: chrono::Utc::now(),
        auditor: "security_auditor_001".to_string(),
        audit_details: HashMap::from([
            ("firewall_rules".to_string(), "compliant".to_string()),
            ("access_controls".to_string(), "compliant".to_string()),
            ("encryption_settings".to_string(), "compliant".to_string()),
        ]),
        compliance_status: ComplianceStatus::Compliant,
        recommendations: vec![
            "保持当前安全配置".to_string(),
            "定期更新安全策略".to_string(),
        ],
    };
    
    let config_audit_id = security_manager.create_audit_record(config_audit).await?;
    println!("    安全配置审计记录已创建: {}", config_audit_id);
    
    // 创建访问控制审计记录
    let access_audit = SecurityAuditRecord {
        record_id: "access_audit_001".to_string(),
        audit_type: AuditType::AccessControlAudit,
        audit_target: "user_access_controls".to_string(),
        audit_result: AuditResult::Warning,
        audit_time: chrono::Utc::now(),
        auditor: "security_auditor_002".to_string(),
        audit_details: HashMap::from([
            ("privileged_accounts".to_string(), "2 found".to_string()),
            ("inactive_accounts".to_string(), "5 found".to_string()),
            ("password_policy".to_string(), "compliant".to_string()),
        ]),
        compliance_status: ComplianceStatus::PartiallyCompliant,
        recommendations: vec![
            "清理非活跃账户".to_string(),
            "审查特权账户权限".to_string(),
        ],
    };
    
    let access_audit_id = security_manager.create_audit_record(access_audit).await?;
    println!("    访问控制审计记录已创建: {}", access_audit_id);
    
    // 创建数据保护审计记录
    let data_audit = SecurityAuditRecord {
        record_id: "data_audit_001".to_string(),
        audit_type: AuditType::DataProtectionAudit,
        audit_target: "sensitive_data_protection".to_string(),
        audit_result: AuditResult::Fail,
        audit_time: chrono::Utc::now(),
        auditor: "security_auditor_003".to_string(),
        audit_details: HashMap::from([
            ("data_encryption".to_string(), "incomplete".to_string()),
            ("data_backup".to_string(), "compliant".to_string()),
            ("data_retention".to_string(), "non_compliant".to_string()),
        ]),
        compliance_status: ComplianceStatus::NonCompliant,
        recommendations: vec![
            "实施完整的数据加密".to_string(),
            "更新数据保留策略".to_string(),
            "加强数据访问控制".to_string(),
        ],
    };
    
    let data_audit_id = security_manager.create_audit_record(data_audit).await?;
    println!("    数据保护审计记录已创建: {}", data_audit_id);
    
    // 创建渗透测试记录
    let pentest_audit = SecurityAuditRecord {
        record_id: "pentest_audit_001".to_string(),
        audit_type: AuditType::PenetrationTest,
        audit_target: "iot_network_security".to_string(),
        audit_result: AuditResult::Warning,
        audit_time: chrono::Utc::now(),
        auditor: "penetration_tester_001".to_string(),
        audit_details: HashMap::from([
            ("vulnerabilities_found".to_string(), "3".to_string()),
            ("critical_issues".to_string(), "0".to_string()),
            ("high_issues".to_string(), "1".to_string()),
            ("medium_issues".to_string(), "2".to_string()),
        ]),
        compliance_status: ComplianceStatus::PartiallyCompliant,
        recommendations: vec![
            "修复SQL注入漏洞".to_string(),
            "加强输入验证".to_string(),
            "更新Web应用框架".to_string(),
        ],
    };
    
    let pentest_audit_id = security_manager.create_audit_record(pentest_audit).await?;
    println!("    渗透测试记录已创建: {}", pentest_audit_id);
    
    // 获取审计记录列表
    let audit_records = security_manager.get_audit_records(None).await;
    println!("  安全审计统计:");
    println!("    总审计记录数: {}", audit_records.len());
    
    let mut audit_type_count = HashMap::new();
    let mut compliance_count = HashMap::new();
    for record in &audit_records {
        *audit_type_count.entry(&record.audit_type).or_insert(0) += 1;
        *compliance_count.entry(format!("{:?}", record.compliance_status)).or_insert(0) += 1;
    }
    
    println!("  审计类型统计:");
    for (audit_type, count) in audit_type_count {
        println!("    {:?}: {} 个", audit_type, count);
    }
    
    println!("  合规状态统计:");
    for (compliance_status, count) in compliance_count {
        println!("    {:?}: {} 个", compliance_status, count);
    }

    Ok(())
}

/// 威胁检测演示
async fn demo_threat_detection() -> Result<(), Box<dyn std::error::Error>> {
    let security_manager = AdvancedIoTSecurityManager::new(SecurityConfig::default());
    
    println!("  启动威胁检测...");
    
    // 启动威胁检测引擎
    let security_manager_arc = Arc::new(security_manager);
    security_manager_arc.clone().start_threat_detection().await;
    
    println!("    威胁检测引擎已启动");
    
    // 等待一段时间让威胁检测运行
    println!("    等待威胁检测运行...");
    tokio::time::sleep(Duration::from_secs(3)).await;
    
    // 检查检测到的威胁
    let detected_events = security_manager_arc.get_security_events(Some(SecurityEventStatus::New), None).await;
    println!("  威胁检测结果:");
    println!("    检测到的新威胁: {} 个", detected_events.len());
    
    for event in &detected_events {
        println!("      威胁: {:?} - 级别: {:?} - 描述: {}", 
                event.threat_type, 
                event.threat_level, 
                event.description);
        if let Some(source_ip) = &event.source_ip {
            println!("        源IP: {}", source_ip);
        }
        if let Some(target_device) = &event.target_device {
            println!("        目标设备: {}", target_device);
        }
    }

    Ok(())
}

/// 自动响应演示
async fn demo_auto_response() -> Result<(), Box<dyn std::error::Error>> {
    let security_manager = AdvancedIoTSecurityManager::new(SecurityConfig::default());
    
    println!("  测试自动响应机制...");
    
    // 创建不同级别的安全事件来测试自动响应
    let test_events = vec![
        (SecurityThreatType::Malware, ThreatLevel::Critical, "测试恶意软件威胁"),
        (SecurityThreatType::NetworkAttack, ThreatLevel::High, "测试网络攻击威胁"),
        (SecurityThreatType::DataBreach, ThreatLevel::Emergency, "测试数据泄露威胁"),
        (SecurityThreatType::IdentitySpoofing, ThreatLevel::Medium, "测试身份伪造威胁"),
    ];
    
    for (threat_type, threat_level, description) in test_events {
        let event = create_security_event(
            &format!("auto_response_test_{:?}", threat_type),
            threat_type.clone(),
            threat_level.clone(),
            description,
        );
        
        let event_id = security_manager.create_security_event(event).await?;
        println!("    创建测试事件: {} - {:?} ({:?})", event_id, threat_type, threat_level);
        
        // 等待自动响应
        tokio::time::sleep(Duration::from_millis(500)).await;
        
        // 检查响应结果
        let event = security_manager.get_security_event(&event_id).await?;
        println!("      事件状态: {:?}", event.status);
        println!("      响应措施数量: {}", event.response_actions.len());
        
        for (i, response) in event.response_actions.iter().enumerate() {
            println!("        响应 {}: {:?} - {:?}", 
                    i + 1, 
                    response.response_type, 
                    response.result);
        }
    }

    Ok(())
}

/// 安全统计和报告演示
async fn demo_security_statistics() -> Result<(), Box<dyn std::error::Error>> {
    let security_manager = AdvancedIoTSecurityManager::new(SecurityConfig::default());
    
    println!("  生成安全统计报告...");
    
    // 执行一些操作以生成统计数据
    // 创建一些安全事件
    for i in 1..=5 {
        let event = create_security_event(
            &format!("stats_event_{}", i),
            SecurityThreatType::Malware,
            ThreatLevel::Medium,
            &format!("统计测试事件 {}", i),
        );
        security_manager.create_security_event(event).await?;
    }
    
    // 创建一些零信任策略
    for i in 1..=3 {
        let policy = ZeroTrustPolicy {
            policy_id: format!("stats_policy_{}", i),
            policy_name: format!("统计测试策略 {}", i),
            policy_type: ZeroTrustPolicyType::AuthenticationPolicy,
            rules: vec![],
            status: PolicyStatus::Active,
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
            description: format!("统计测试策略 {}", i),
        };
        security_manager.create_zero_trust_policy(policy).await?;
    }
    
    // 创建一些量子加密配置
    for i in 1..=2 {
        let config = QuantumEncryptionConfig {
            config_id: format!("stats_quantum_config_{}", i),
            algorithm: QuantumEncryptionAlgorithm::BB84,
            key_length: 256,
            qkd_protocol: QKDProtocol::BB84,
            security_parameters: HashMap::new(),
            status: EncryptionStatus::Active,
            created_at: chrono::Utc::now(),
        };
        security_manager.create_quantum_encryption_config(config).await?;
    }
    
    // 创建一些审计记录
    for i in 1..=4 {
        let record = SecurityAuditRecord {
            record_id: format!("stats_audit_{}", i),
            audit_type: AuditType::SecurityConfigurationAudit,
            audit_target: format!("stats_target_{}", i),
            audit_result: if i % 2 == 0 { AuditResult::Pass } else { AuditResult::Warning },
            audit_time: chrono::Utc::now(),
            auditor: "stats_auditor".to_string(),
            audit_details: HashMap::new(),
            compliance_status: if i % 2 == 0 { ComplianceStatus::Compliant } else { ComplianceStatus::PartiallyCompliant },
            recommendations: vec!["测试建议".to_string()],
        };
        security_manager.create_audit_record(record).await?;
    }
    
    // 获取统计信息
    let stats = security_manager.get_security_stats().await;
    println!("  安全统计报告:");
    println!("    总安全事件数: {}", stats.total_security_events);
    println!("    活跃威胁数: {}", stats.active_threats);
    println!("    已解决威胁数: {}", stats.resolved_threats);
    println!("    平均响应时间: {:?}", stats.avg_response_time);
    println!("    零信任策略数: {}", stats.zero_trust_policies_count);
    println!("    量子加密配置数: {}", stats.quantum_encryption_configs_count);
    println!("    审计记录数: {}", stats.audit_records_count);
    println!("    合规率: {:.2}%", stats.compliance_rate * 100.0);
    println!("    最后更新时间: {}", stats.last_updated.format("%Y-%m-%d %H:%M:%S"));
    
    // 获取安全事件列表
    let all_events = security_manager.get_security_events(None, Some(10)).await;
    println!("  最近安全事件 ({} 个):", all_events.len());
    for (i, event) in all_events.iter().enumerate() {
        println!("    {}: {:?} - {:?} ({:?})", 
                i + 1, 
                event.threat_type, 
                event.threat_level, 
                event.status);
        println!("      描述: {}", event.description);
        println!("      时间: {}", event.timestamp.format("%H:%M:%S"));
    }
    
    // 获取零信任策略列表
    let policies = security_manager.get_zero_trust_policies().await;
    println!("  零信任策略列表 ({} 个):", policies.len());
    for (i, policy) in policies.iter().enumerate() {
        println!("    {}: {} ({:?})", 
                i + 1, 
                policy.policy_name, 
                policy.policy_type);
        println!("      状态: {:?}", policy.status);
        println!("      规则数: {}", policy.rules.len());
    }
    
    // 获取量子加密配置列表
    let configs = security_manager.get_quantum_encryption_configs().await;
    println!("  量子加密配置列表 ({} 个):", configs.len());
    for (i, config) in configs.iter().enumerate() {
        println!("    {}: {:?} - 密钥长度: {} 位", 
                i + 1, 
                config.algorithm, 
                config.key_length);
        println!("      协议: {:?}", config.qkd_protocol);
        println!("      状态: {:?}", config.status);
    }
    
    // 获取审计记录列表
    let audit_records = security_manager.get_audit_records(Some(5)).await;
    println!("  最近审计记录 ({} 个):", audit_records.len());
    for (i, record) in audit_records.iter().enumerate() {
        println!("    {}: {:?} - {:?} ({:?})", 
                i + 1, 
                record.audit_type, 
                record.audit_result, 
                record.compliance_status);
        println!("      审计对象: {}", record.audit_target);
        println!("      审计员: {}", record.auditor);
        println!("      建议数量: {}", record.recommendations.len());
    }

    Ok(())
}

/// 创建安全事件的辅助函数
fn create_security_event(id: &str, threat_type: SecurityThreatType, threat_level: ThreatLevel, description: &str) -> SecurityEvent {
    SecurityEvent {
        event_id: id.to_string(),
        event_type: SecurityEventType::ThreatDetected,
        threat_type,
        threat_level,
        description: description.to_string(),
        source_ip: Some("192.168.1.100".to_string()),
        target_device: Some("device_001".to_string()),
        timestamp: chrono::Utc::now(),
        status: SecurityEventStatus::New,
        event_data: HashMap::new(),
        response_actions: Vec::new(),
        impact_assessment: None,
    }
}
