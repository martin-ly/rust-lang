//! 高级IoT安全模块
//! 
//! 提供零信任架构、量子加密、安全审计等高级IoT安全功能
#[allow(unused_imports)]
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{
    Duration, 
    //SystemTime, 
    //UNIX_EPOCH,
};
use tokio::sync::{
    RwLock, 
    Mutex,
};
use serde::{
    Deserialize, 
    Serialize,
};
use chrono::{
    DateTime, 
    Utc,
};
use thiserror::Error;

/// 安全威胁类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum SecurityThreatType {
    /// 恶意软件
    Malware,
    /// 网络攻击
    NetworkAttack,
    /// 数据泄露
    DataBreach,
    /// 身份伪造
    IdentitySpoofing,
    /// 拒绝服务攻击
    DoSAttack,
    /// 中间人攻击
    ManInTheMiddle,
    /// 侧信道攻击
    SideChannelAttack,
    /// 量子攻击
    QuantumAttack,
    /// 物理攻击
    PhysicalAttack,
    /// 供应链攻击
    SupplyChainAttack,
    /// 自定义威胁
    Custom(String),
}

/// 安全威胁级别
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum ThreatLevel {
    /// 低风险
    Low = 1,
    /// 中等风险
    Medium = 2,
    /// 高风险
    High = 3,
    /// 严重风险
    Critical = 4,
    /// 紧急风险
    Emergency = 5,
}

/// 安全事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityEvent {
    /// 事件ID
    pub event_id: String,
    /// 事件类型
    pub event_type: SecurityEventType,
    /// 威胁类型
    pub threat_type: SecurityThreatType,
    /// 威胁级别
    pub threat_level: ThreatLevel,
    /// 事件描述
    pub description: String,
    /// 源IP地址
    pub source_ip: Option<String>,
    /// 目标设备
    pub target_device: Option<String>,
    /// 事件时间
    pub timestamp: DateTime<Utc>,
    /// 事件状态
    pub status: SecurityEventStatus,
    /// 事件数据
    pub event_data: HashMap<String, String>,
    /// 响应措施
    pub response_actions: Vec<SecurityResponse>,
    /// 事件影响
    pub impact_assessment: Option<ImpactAssessment>,
}

/// 安全事件类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum SecurityEventType {
    /// 检测到威胁
    ThreatDetected,
    /// 攻击尝试
    AttackAttempt,
    /// 安全违规
    SecurityViolation,
    /// 异常行为
    AnomalousBehavior,
    /// 系统入侵
    SystemIntrusion,
    /// 数据泄露
    DataExfiltration,
    /// 权限提升
    PrivilegeEscalation,
    /// 配置错误
    ConfigurationError,
    /// 自定义事件
    Custom(String),
}

/// 安全事件状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum SecurityEventStatus {
    /// 新事件
    New,
    /// 调查中
    Investigating,
    /// 已确认
    Confirmed,
    /// 已缓解
    Mitigated,
    /// 已解决
    Resolved,
    /// 误报
    FalsePositive,
    /// 已忽略
    Ignored,
}

/// 安全响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityResponse {
    /// 响应ID
    pub response_id: String,
    /// 响应类型
    pub response_type: SecurityResponseType,
    /// 响应描述
    pub description: String,
    /// 执行时间
    pub executed_at: DateTime<Utc>,
    /// 执行结果
    pub result: SecurityResponseResult,
    /// 响应参数
    pub parameters: HashMap<String, String>,
}

/// 安全响应类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum SecurityResponseType {
    /// 阻止连接
    BlockConnection,
    /// 隔离设备
    IsolateDevice,
    /// 重置密码
    ResetPassword,
    /// 撤销权限
    RevokePermissions,
    /// 发送告警
    SendAlert,
    /// 启动备份
    StartBackup,
    /// 切换网络
    SwitchNetwork,
    /// 启动应急响应
    ActivateEmergencyResponse,
    /// 自定义响应
    Custom(String),
}

/// 安全响应结果
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum SecurityResponseResult {
    /// 成功
    Success,
    /// 失败
    Failed,
    /// 部分成功
    PartialSuccess,
    /// 超时
    Timeout,
    /// 未执行
    NotExecuted,
}

/// 影响评估
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImpactAssessment {
    /// 影响级别
    pub impact_level: ThreatLevel,
    /// 影响范围
    pub affected_systems: Vec<String>,
    /// 数据影响
    pub data_impact: DataImpact,
    /// 业务影响
    pub business_impact: BusinessImpact,
    /// 恢复时间
    pub estimated_recovery_time: Duration,
    /// 影响描述
    pub impact_description: String,
}

/// 数据影响
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum DataImpact {
    /// 无影响
    None,
    /// 数据泄露
    DataBreach,
    /// 数据损坏
    DataCorruption,
    /// 数据丢失
    DataLoss,
    /// 数据不可用
    DataUnavailable,
}

/// 业务影响
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum BusinessImpact {
    /// 无影响
    None,
    /// 服务中断
    ServiceDisruption,
    /// 性能下降
    PerformanceDegradation,
    /// 功能受限
    FunctionalityLimited,
    /// 完全停止
    CompleteShutdown,
}

/// 零信任策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZeroTrustPolicy {
    /// 策略ID
    pub policy_id: String,
    /// 策略名称
    pub policy_name: String,
    /// 策略类型
    pub policy_type: ZeroTrustPolicyType,
    /// 策略规则
    pub rules: Vec<ZeroTrustRule>,
    /// 策略状态
    pub status: PolicyStatus,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 更新时间
    pub updated_at: DateTime<Utc>,
    /// 策略描述
    pub description: String,
}

/// 零信任策略类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ZeroTrustPolicyType {
    /// 身份验证策略
    AuthenticationPolicy,
    /// 授权策略
    AuthorizationPolicy,
    /// 网络访问策略
    NetworkAccessPolicy,
    /// 数据保护策略
    DataProtectionPolicy,
    /// 设备安全策略
    DeviceSecurityPolicy,
    /// 应用安全策略
    ApplicationSecurityPolicy,
    /// 自定义策略
    Custom(String),
}

/// 零信任规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ZeroTrustRule {
    /// 规则ID
    pub rule_id: String,
    /// 规则名称
    pub rule_name: String,
    /// 规则条件
    pub conditions: Vec<RuleCondition>,
    /// 规则动作
    pub actions: Vec<RuleAction>,
    /// 规则优先级
    pub priority: u32,
    /// 规则状态
    pub status: RuleStatus,
}

/// 规则条件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuleCondition {
    /// 条件类型
    pub condition_type: ConditionType,
    /// 条件字段
    pub field: String,
    /// 条件操作符
    pub operator: ConditionOperator,
    /// 条件值
    pub value: String,
}

/// 条件类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ConditionType {
    /// 用户身份
    UserIdentity,
    /// 设备类型
    DeviceType,
    /// 网络位置
    NetworkLocation,
    /// 时间范围
    TimeRange,
    /// 应用类型
    ApplicationType,
    /// 数据敏感度
    DataSensitivity,
    /// 风险评分
    RiskScore,
    /// 自定义条件
    Custom(String),
}

/// 条件操作符
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ConditionOperator {
    /// 等于
    Equals,
    /// 不等于
    NotEquals,
    /// 包含
    Contains,
    /// 不包含
    NotContains,
    /// 大于
    GreaterThan,
    /// 小于
    LessThan,
    /// 在范围内
    InRange,
    /// 不在范围内
    NotInRange,
}

/// 规则动作
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuleAction {
    /// 动作类型
    pub action_type: ActionType,
    /// 动作参数
    pub parameters: HashMap<String, String>,
}

/// 动作类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ActionType {
    /// 允许
    Allow,
    /// 拒绝
    Deny,
    /// 要求额外验证
    RequireAdditionalAuth,
    /// 记录日志
    Log,
    /// 发送告警
    Alert,
    /// 隔离
    Quarantine,
    /// 自定义动作
    Custom(String),
}

/// 策略状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum PolicyStatus {
    /// 活跃
    Active,
    /// 非活跃
    Inactive,
    /// 测试中
    Testing,
    /// 已删除
    Deleted,
}

/// 规则状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum RuleStatus {
    /// 启用
    Enabled,
    /// 禁用
    Disabled,
    /// 测试中
    Testing,
}

/// 量子加密配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuantumEncryptionConfig {
    /// 配置ID
    pub config_id: String,
    /// 加密算法
    pub algorithm: QuantumEncryptionAlgorithm,
    /// 密钥长度
    pub key_length: u32,
    /// 量子密钥分发协议
    pub qkd_protocol: QKDProtocol,
    /// 安全参数
    pub security_parameters: HashMap<String, String>,
    /// 配置状态
    pub status: EncryptionStatus,
    /// 创建时间
    pub created_at: DateTime<Utc>,
}

/// 量子加密算法
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum QuantumEncryptionAlgorithm {
    /// BB84协议
    BB84,
    /// E91协议
    E91,
    /// SARG04协议
    SARG04,
    /// 量子密钥分发
    QuantumKeyDistribution,
    /// 量子随机数生成
    QuantumRandomNumberGeneration,
    /// 量子数字签名
    QuantumDigitalSignature,
    /// 后量子密码学
    PostQuantumCryptography,
    /// 自定义算法
    Custom(String),
}

/// 量子密钥分发协议
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum QKDProtocol {
    /// BB84协议
    BB84,
    /// E91协议
    E91,
    /// SARG04协议
    SARG04,
    /// 连续变量QKD
    ContinuousVariableQKD,
    /// 测量设备无关QKD
    MeasurementDeviceIndependentQKD,
    /// 自定义协议
    Custom(String),
}

/// 加密状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum EncryptionStatus {
    /// 活跃
    Active,
    /// 非活跃
    Inactive,
    /// 测试中
    Testing,
    /// 错误
    Error,
}

/// 安全审计记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityAuditRecord {
    /// 记录ID
    pub record_id: String,
    /// 审计类型
    pub audit_type: AuditType,
    /// 审计对象
    pub audit_target: String,
    /// 审计结果
    pub audit_result: AuditResult,
    /// 审计时间
    pub audit_time: DateTime<Utc>,
    /// 审计员
    pub auditor: String,
    /// 审计详情
    pub audit_details: HashMap<String, String>,
    /// 合规状态
    pub compliance_status: ComplianceStatus,
    /// 建议措施
    pub recommendations: Vec<String>,
}

/// 审计类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum AuditType {
    /// 安全配置审计
    SecurityConfigurationAudit,
    /// 访问控制审计
    AccessControlAudit,
    /// 数据保护审计
    DataProtectionAudit,
    /// 网络安全审计
    NetworkSecurityAudit,
    /// 设备安全审计
    DeviceSecurityAudit,
    /// 合规性审计
    ComplianceAudit,
    /// 渗透测试
    PenetrationTest,
    /// 漏洞扫描
    VulnerabilityScan,
    /// 自定义审计
    Custom(String),
}

/// 审计结果
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum AuditResult {
    /// 通过
    Pass,
    /// 失败
    Fail,
    /// 警告
    Warning,
    /// 信息
    Info,
    /// 不适用
    NotApplicable,
}

/// 合规状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ComplianceStatus {
    /// 合规
    Compliant,
    /// 不合规
    NonCompliant,
    /// 部分合规
    PartiallyCompliant,
    /// 待评估
    PendingAssessment,
}

/// 高级IoT安全管理器
#[allow(dead_code)]
pub struct AdvancedIoTSecurityManager {
    /// 安全事件
    security_events: Arc<RwLock<HashMap<String, SecurityEvent>>>,
    /// 零信任策略
    zero_trust_policies: Arc<RwLock<HashMap<String, ZeroTrustPolicy>>>,
    /// 量子加密配置
    quantum_encryption_configs: Arc<RwLock<HashMap<String, QuantumEncryptionConfig>>>,
    /// 安全审计记录
    audit_records: Arc<RwLock<HashMap<String, SecurityAuditRecord>>>,
    /// 统计信息
    stats: Arc<RwLock<SecurityStats>>,
    /// 配置
    config: SecurityConfig,
    /// 威胁检测引擎
    threat_detection_engine: Arc<Mutex<ThreatDetectionEngine>>,
}

/// 安全配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityConfig {
    /// 是否启用高级安全
    pub enable_advanced_security: bool,
    /// 是否启用零信任架构
    pub enable_zero_trust: bool,
    /// 是否启用量子加密
    pub enable_quantum_encryption: bool,
    /// 是否启用安全审计
    pub enable_security_audit: bool,
    /// 威胁检测阈值
    pub threat_detection_threshold: f64,
    /// 自动响应启用
    pub enable_auto_response: bool,
    /// 审计间隔
    pub audit_interval: Duration,
    /// 自定义参数
    pub custom_params: HashMap<String, String>,
}

impl Default for SecurityConfig {
    fn default() -> Self {
        Self {
            enable_advanced_security: true,
            enable_zero_trust: true,
            enable_quantum_encryption: true,
            enable_security_audit: true,
            threat_detection_threshold: 0.7,
            enable_auto_response: true,
            audit_interval: Duration::from_secs(3600), // 1小时
            custom_params: HashMap::new(),
        }
    }
}

/// 威胁检测引擎
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ThreatDetectionEngine {
    /// 检测规则
    detection_rules: Vec<DetectionRule>,
    /// 机器学习模型
    ml_models: HashMap<String, MLModel>,
    /// 检测统计
    detection_stats: DetectionStats,
}

/// 检测规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectionRule {
    /// 规则ID
    pub rule_id: String,
    /// 规则名称
    pub rule_name: String,
    /// 规则类型
    pub rule_type: DetectionRuleType,
    /// 规则条件
    pub conditions: Vec<RuleCondition>,
    /// 威胁类型
    pub threat_type: SecurityThreatType,
    /// 威胁级别
    pub threat_level: ThreatLevel,
    /// 规则状态
    pub status: RuleStatus,
}

/// 检测规则类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum DetectionRuleType {
    /// 基于规则
    RuleBased,
    /// 基于异常
    AnomalyBased,
    /// 基于签名
    SignatureBased,
    /// 基于行为
    BehaviorBased,
    /// 机器学习
    MachineLearning,
    /// 自定义类型
    Custom(String),
}

/// 机器学习模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MLModel {
    /// 模型ID
    pub model_id: String,
    /// 模型名称
    pub model_name: String,
    /// 模型类型
    pub model_type: MLModelType,
    /// 模型版本
    pub model_version: String,
    /// 模型准确率
    pub accuracy: f64,
    /// 模型状态
    pub status: ModelStatus,
    /// 最后训练时间
    pub last_trained: DateTime<Utc>,
}

/// 机器学习模型类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum MLModelType {
    /// 异常检测
    AnomalyDetection,
    /// 分类
    Classification,
    /// 聚类
    Clustering,
    /// 回归
    Regression,
    /// 深度学习
    DeepLearning,
    /// 强化学习
    ReinforcementLearning,
    /// 自定义类型
    Custom(String),
}

/// 模型状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ModelStatus {
    /// 训练中
    Training,
    /// 已训练
    Trained,
    /// 部署中
    Deploying,
    /// 已部署
    Deployed,
    /// 错误
    Error,
}

/// 检测统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectionStats {
    /// 总检测次数
    pub total_detections: u64,
    /// 真阳性
    pub true_positives: u64,
    /// 假阳性
    pub false_positives: u64,
    /// 真阴性
    pub true_negatives: u64,
    /// 假阴性
    pub false_negatives: u64,
    /// 检测准确率
    pub detection_accuracy: f64,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

/// 安全统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityStats {
    /// 总安全事件数
    pub total_security_events: u64,
    /// 活跃威胁数
    pub active_threats: u64,
    /// 已解决威胁数
    pub resolved_threats: u64,
    /// 平均响应时间
    pub avg_response_time: Duration,
    /// 零信任策略数
    pub zero_trust_policies_count: u32,
    /// 量子加密配置数
    pub quantum_encryption_configs_count: u32,
    /// 审计记录数
    pub audit_records_count: u64,
    /// 合规率
    pub compliance_rate: f64,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

impl AdvancedIoTSecurityManager {
    /// 创建新的高级IoT安全管理器
    pub fn new(config: SecurityConfig) -> Self {
        Self {
            security_events: Arc::new(RwLock::new(HashMap::new())),
            zero_trust_policies: Arc::new(RwLock::new(HashMap::new())),
            quantum_encryption_configs: Arc::new(RwLock::new(HashMap::new())),
            audit_records: Arc::new(RwLock::new(HashMap::new())),
            stats: Arc::new(RwLock::new(SecurityStats {
                total_security_events: 0,
                active_threats: 0,
                resolved_threats: 0,
                avg_response_time: Duration::ZERO,
                zero_trust_policies_count: 0,
                quantum_encryption_configs_count: 0,
                audit_records_count: 0,
                compliance_rate: 0.0,
                last_updated: Utc::now(),
            })),
            config,
            threat_detection_engine: Arc::new(Mutex::new(ThreatDetectionEngine {
                detection_rules: Vec::new(),
                ml_models: HashMap::new(),
                detection_stats: DetectionStats {
                    total_detections: 0,
                    true_positives: 0,
                    false_positives: 0,
                    true_negatives: 0,
                    false_negatives: 0,
                    detection_accuracy: 0.0,
                    last_updated: Utc::now(),
                },
            })),
        }
    }

    /// 创建安全事件
    pub async fn create_security_event(&self, event: SecurityEvent) -> Result<String, SecurityError> {
        let event_id = event.event_id.clone();
        
        // 验证事件
        self.validate_security_event(&event).await?;
        
        // 存储事件
        {
            let mut events = self.security_events.write().await;
            events.insert(event_id.clone(), event);
        }
        
        // 更新统计
        self.update_security_stats().await;
        
        // 自动响应
        if self.config.enable_auto_response {
            self.auto_respond_to_threat(&event_id).await?;
        }
        
        Ok(event_id)
    }

    /// 创建零信任策略
    pub async fn create_zero_trust_policy(&self, policy: ZeroTrustPolicy) -> Result<String, SecurityError> {
        let policy_id = policy.policy_id.clone();
        
        // 验证策略
        self.validate_zero_trust_policy(&policy).await?;
        
        // 存储策略
        {
            let mut policies = self.zero_trust_policies.write().await;
            policies.insert(policy_id.clone(), policy);
        }
        
        // 更新统计
        self.update_security_stats().await;
        
        Ok(policy_id)
    }

    /// 创建量子加密配置
    pub async fn create_quantum_encryption_config(&self, config: QuantumEncryptionConfig) -> Result<String, SecurityError> {
        let config_id = config.config_id.clone();
        
        // 验证配置
        self.validate_quantum_encryption_config(&config).await?;
        
        // 存储配置
        {
            let mut configs = self.quantum_encryption_configs.write().await;
            configs.insert(config_id.clone(), config);
        }
        
        // 更新统计
        self.update_security_stats().await;
        
        Ok(config_id)
    }

    /// 创建安全审计记录
    pub async fn create_audit_record(&self, record: SecurityAuditRecord) -> Result<String, SecurityError> {
        let record_id = record.record_id.clone();
        
        // 验证记录
        self.validate_audit_record(&record).await?;
        
        // 存储记录
        {
            let mut records = self.audit_records.write().await;
            records.insert(record_id.clone(), record);
        }
        
        // 更新统计
        self.update_security_stats().await;
        
        Ok(record_id)
    }

    /// 获取安全事件
    pub async fn get_security_event(&self, event_id: &str) -> Result<SecurityEvent, SecurityError> {
        let events = self.security_events.read().await;
        let event = events.get(event_id)
            .ok_or_else(|| SecurityError::EventNotFound(event_id.to_string()))?;
        Ok(event.clone())
    }

    /// 获取安全统计信息
    pub async fn get_security_stats(&self) -> SecurityStats {
        self.stats.read().await.clone()
    }

    /// 获取安全事件列表
    pub async fn get_security_events(&self, status_filter: Option<SecurityEventStatus>, limit: Option<usize>) -> Vec<SecurityEvent> {
        let events = self.security_events.read().await;
        let mut event_list: Vec<SecurityEvent> = events.values().cloned().collect();
        
        // 应用状态过滤
        if let Some(status) = status_filter {
            event_list.retain(|event| event.status == status);
        }
        
        // 按时间排序
        event_list.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));
        
        // 应用限制
        if let Some(limit) = limit {
            event_list.truncate(limit);
        }
        
        event_list
    }

    /// 获取零信任策略列表
    pub async fn get_zero_trust_policies(&self) -> Vec<ZeroTrustPolicy> {
        let policies = self.zero_trust_policies.read().await;
        policies.values().cloned().collect()
    }

    /// 获取量子加密配置列表
    pub async fn get_quantum_encryption_configs(&self) -> Vec<QuantumEncryptionConfig> {
        let configs = self.quantum_encryption_configs.read().await;
        configs.values().cloned().collect()
    }

    /// 获取审计记录列表
    pub async fn get_audit_records(&self, limit: Option<usize>) -> Vec<SecurityAuditRecord> {
        let records = self.audit_records.read().await;
        let mut record_list: Vec<SecurityAuditRecord> = records.values().cloned().collect();
        
        // 按时间排序
        record_list.sort_by(|a, b| b.audit_time.cmp(&a.audit_time));
        
        // 应用限制
        if let Some(limit) = limit {
            record_list.truncate(limit);
        }
        
        record_list
    }

    /// 启动威胁检测
    pub async fn start_threat_detection(self: Arc<Self>) {
        let self_clone = self.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(60));
            loop {
                interval.tick().await;
                if let Err(e) = self_clone.detect_threats().await {
                    eprintln!("威胁检测失败: {:?}", e);
                }
            }
        });
    }

    /// 检测威胁
    async fn detect_threats(&self) -> Result<(), SecurityError> {
        // 模拟威胁检测
        let threat_types = vec![
            SecurityThreatType::Malware,
            SecurityThreatType::NetworkAttack,
            SecurityThreatType::DataBreach,
            SecurityThreatType::IdentitySpoofing,
        ];
        
        for threat_type in threat_types {
            if rand::random::<f64>() < 0.1 { // 10%概率检测到威胁
                let event = SecurityEvent {
                    event_id: uuid::Uuid::new_v4().to_string(),
                    event_type: SecurityEventType::ThreatDetected,
                    threat_type: threat_type.clone(),
                    threat_level: ThreatLevel::Medium,
                    description: format!("检测到{:?}威胁", threat_type),
                    source_ip: Some("192.168.1.100".to_string()),
                    target_device: Some("device_001".to_string()),
                    timestamp: Utc::now(),
                    status: SecurityEventStatus::New,
                    event_data: HashMap::new(),
                    response_actions: Vec::new(),
                    impact_assessment: None,
                };
                
                self.create_security_event(event).await?;
            }
        }
        
        Ok(())
    }

    /// 自动响应威胁
    async fn auto_respond_to_threat(&self, event_id: &str) -> Result<(), SecurityError> {
        let mut events = self.security_events.write().await;
        if let Some(event) = events.get_mut(event_id) {
            // 根据威胁类型和级别选择响应措施
            let response = match event.threat_level {
                ThreatLevel::Critical | ThreatLevel::Emergency => {
                    SecurityResponse {
                        response_id: uuid::Uuid::new_v4().to_string(),
                        response_type: SecurityResponseType::BlockConnection,
                        description: "自动阻止可疑连接".to_string(),
                        executed_at: Utc::now(),
                        result: SecurityResponseResult::Success,
                        parameters: HashMap::new(),
                    }
                },
                ThreatLevel::High => {
                    SecurityResponse {
                        response_id: uuid::Uuid::new_v4().to_string(),
                        response_type: SecurityResponseType::SendAlert,
                        description: "发送安全告警".to_string(),
                        executed_at: Utc::now(),
                        result: SecurityResponseResult::Success,
                        parameters: HashMap::new(),
                    }
                },
                _ => {
                    SecurityResponse {
                        response_id: uuid::Uuid::new_v4().to_string(),
                        response_type: SecurityResponseType::SendAlert,
                        description: "记录安全事件".to_string(),
                        executed_at: Utc::now(),
                        result: SecurityResponseResult::Success,
                        parameters: HashMap::new(),
                    }
                }
            };
            
            event.response_actions.push(response);
            event.status = SecurityEventStatus::Mitigated;
        }
        
        Ok(())
    }

    /// 验证安全事件
    async fn validate_security_event(&self, event: &SecurityEvent) -> Result<(), SecurityError> {
        if event.event_id.is_empty() {
            return Err(SecurityError::InvalidEvent("事件ID不能为空".to_string()));
        }
        
        if event.description.is_empty() {
            return Err(SecurityError::InvalidEvent("事件描述不能为空".to_string()));
        }
        
        Ok(())
    }

    /// 验证零信任策略
    async fn validate_zero_trust_policy(&self, policy: &ZeroTrustPolicy) -> Result<(), SecurityError> {
        if policy.policy_id.is_empty() {
            return Err(SecurityError::InvalidPolicy("策略ID不能为空".to_string()));
        }
        
        if policy.policy_name.is_empty() {
            return Err(SecurityError::InvalidPolicy("策略名称不能为空".to_string()));
        }
        
        if policy.rules.is_empty() {
            return Err(SecurityError::InvalidPolicy("策略规则不能为空".to_string()));
        }
        
        Ok(())
    }

    /// 验证量子加密配置
    async fn validate_quantum_encryption_config(&self, config: &QuantumEncryptionConfig) -> Result<(), SecurityError> {
        if config.config_id.is_empty() {
            return Err(SecurityError::InvalidConfig("配置ID不能为空".to_string()));
        }
        
        if config.key_length == 0 {
            return Err(SecurityError::InvalidConfig("密钥长度不能为0".to_string()));
        }
        
        Ok(())
    }

    /// 验证审计记录
    async fn validate_audit_record(&self, record: &SecurityAuditRecord) -> Result<(), SecurityError> {
        if record.record_id.is_empty() {
            return Err(SecurityError::InvalidRecord("记录ID不能为空".to_string()));
        }
        
        if record.audit_target.is_empty() {
            return Err(SecurityError::InvalidRecord("审计对象不能为空".to_string()));
        }
        
        Ok(())
    }

    /// 更新安全统计
    async fn update_security_stats(&self) {
        let mut stats = self.stats.write().await;
        
        let events = self.security_events.read().await;
        let policies = self.zero_trust_policies.read().await;
        let configs = self.quantum_encryption_configs.read().await;
        let records = self.audit_records.read().await;
        
        stats.total_security_events = events.len() as u64;
        stats.active_threats = events.values()
            .filter(|e| e.status == SecurityEventStatus::New || e.status == SecurityEventStatus::Investigating)
            .count() as u64;
        stats.resolved_threats = events.values()
            .filter(|e| e.status == SecurityEventStatus::Resolved)
            .count() as u64;
        stats.zero_trust_policies_count = policies.len() as u32;
        stats.quantum_encryption_configs_count = configs.len() as u32;
        stats.audit_records_count = records.len() as u64;
        
        // 计算合规率
        let compliant_records = records.values()
            .filter(|r| r.compliance_status == ComplianceStatus::Compliant)
            .count();
        if records.len() > 0 {
            stats.compliance_rate = compliant_records as f64 / records.len() as f64;
        }
        
        stats.last_updated = Utc::now();
    }
}

/// 安全错误
#[derive(Debug, Error)]
pub enum SecurityError {
    #[error("安全事件未找到: {0}")]
    EventNotFound(String),
    
    #[error("无效的安全事件: {0}")]
    InvalidEvent(String),
    
    #[error("无效的策略: {0}")]
    InvalidPolicy(String),
    
    #[error("无效的配置: {0}")]
    InvalidConfig(String),
    
    #[error("无效的审计记录: {0}")]
    InvalidRecord(String),
    
    #[error("威胁检测失败: {0}")]
    ThreatDetectionFailed(String),
    
    #[error("自动响应失败: {0}")]
    AutoResponseFailed(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("内部错误: {0}")]
    InternalError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_security_manager_creation() {
        let config = SecurityConfig::default();
        let manager = AdvancedIoTSecurityManager::new(config);
        
        let stats = manager.get_security_stats().await;
        assert_eq!(stats.total_security_events, 0);
        assert_eq!(stats.active_threats, 0);
    }

    #[tokio::test]
    async fn test_security_event_creation() {
        let config = SecurityConfig::default();
        let manager = AdvancedIoTSecurityManager::new(config);
        
        let event = SecurityEvent {
            event_id: "test_event".to_string(),
            event_type: SecurityEventType::ThreatDetected,
            threat_type: SecurityThreatType::Malware,
            threat_level: ThreatLevel::High,
            description: "测试安全事件".to_string(),
            source_ip: Some("192.168.1.100".to_string()),
            target_device: Some("device_001".to_string()),
            timestamp: Utc::now(),
            status: SecurityEventStatus::New,
            event_data: HashMap::new(),
            response_actions: Vec::new(),
            impact_assessment: None,
        };
        
        let result = manager.create_security_event(event).await;
        assert!(result.is_ok());
        
        let event_id = result.unwrap();
        assert_eq!(event_id, "test_event");
    }

    #[tokio::test]
    async fn test_zero_trust_policy_creation() {
        let config = SecurityConfig::default();
        let manager = AdvancedIoTSecurityManager::new(config);
        
        let policy = ZeroTrustPolicy {
            policy_id: "test_policy".to_string(),
            policy_name: "测试策略".to_string(),
            policy_type: ZeroTrustPolicyType::AuthenticationPolicy,
            rules: vec![
                ZeroTrustRule {
                    rule_id: "rule1".to_string(),
                    rule_name: "测试规则".to_string(),
                    conditions: vec![
                        RuleCondition {
                            condition_type: ConditionType::UserIdentity,
                            field: "user_id".to_string(),
                            operator: ConditionOperator::Equals,
                            value: "admin".to_string(),
                        }
                    ],
                    actions: vec![
                        RuleAction {
                            action_type: ActionType::Allow,
                            parameters: HashMap::new(),
                        }
                    ],
                    priority: 1,
                    status: RuleStatus::Enabled,
                }
            ],
            status: PolicyStatus::Active,
            created_at: Utc::now(),
            updated_at: Utc::now(),
            description: "测试零信任策略".to_string(),
        };
        
        let result = manager.create_zero_trust_policy(policy).await;
        assert!(result.is_ok());
        
        let policy_id = result.unwrap();
        assert_eq!(policy_id, "test_policy");
    }

    #[tokio::test]
    async fn test_quantum_encryption_config_creation() {
        let config = SecurityConfig::default();
        let manager = AdvancedIoTSecurityManager::new(config);
        
        let quantum_config = QuantumEncryptionConfig {
            config_id: "test_quantum_config".to_string(),
            algorithm: QuantumEncryptionAlgorithm::BB84,
            key_length: 256,
            qkd_protocol: QKDProtocol::BB84,
            security_parameters: HashMap::new(),
            status: EncryptionStatus::Active,
            created_at: Utc::now(),
        };
        
        let result = manager.create_quantum_encryption_config(quantum_config).await;
        assert!(result.is_ok());
        
        let config_id = result.unwrap();
        assert_eq!(config_id, "test_quantum_config");
    }

    #[tokio::test]
    async fn test_audit_record_creation() {
        let config = SecurityConfig::default();
        let manager = AdvancedIoTSecurityManager::new(config);
        
        let record = SecurityAuditRecord {
            record_id: "test_audit".to_string(),
            audit_type: AuditType::SecurityConfigurationAudit,
            audit_target: "system_config".to_string(),
            audit_result: AuditResult::Pass,
            audit_time: Utc::now(),
            auditor: "security_auditor".to_string(),
            audit_details: HashMap::new(),
            compliance_status: ComplianceStatus::Compliant,
            recommendations: vec!["保持当前配置".to_string()],
        };
        
        let result = manager.create_audit_record(record).await;
        assert!(result.is_ok());
        
        let record_id = result.unwrap();
        assert_eq!(record_id, "test_audit");
    }
}
