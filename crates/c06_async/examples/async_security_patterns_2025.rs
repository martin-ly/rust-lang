use anyhow::Result;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tracing::{info, warn, debug, error};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

/// 2025年异步安全编程模式演示
/// 展示最新的异步安全编程技术和最佳实践

/// 1. 异步访问控制管理器
pub struct AsyncAccessControlManager {
    permissions: Arc<RwLock<HashMap<String, Vec<String>>>>,
    rate_limits: Arc<RwLock<HashMap<String, RateLimit>>>,
    audit_log: Arc<RwLock<Vec<AuditEntry>>>,
}

#[derive(Debug, Clone)]
pub struct RateLimit {
    pub max_requests: u32,
    pub time_window: Duration,
    pub current_requests: u32,
    pub window_start: Instant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditEntry {
    pub timestamp: u64,
    pub user_id: String,
    pub action: String,
    pub resource: String,
    pub success: bool,
    pub ip_address: Option<String>,
}

impl AsyncAccessControlManager {
    pub fn new() -> Self {
        Self {
            permissions: Arc::new(RwLock::new(HashMap::new())),
            rate_limits: Arc::new(RwLock::new(HashMap::new())),
            audit_log: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn grant_permission(&self, user_id: String, resource: String) {
        let mut permissions = self.permissions.write().await;
        permissions.entry(user_id).or_insert_with(Vec::new).push(resource);
    }

    pub async fn revoke_permission(&self, user_id: String, resource: String) {
        let mut permissions = self.permissions.write().await;
        if let Some(user_permissions) = permissions.get_mut(&user_id) {
            user_permissions.retain(|r| r != &resource);
        }
    }

    pub async fn check_permission(&self, user_id: &str, resource: &str) -> bool {
        let permissions = self.permissions.read().await;
        permissions
            .get(user_id)
            .map_or(false, |user_permissions| user_permissions.contains(&resource.to_string()))
    }

    pub async fn set_rate_limit(&self, user_id: String, max_requests: u32, time_window: Duration) {
        let rate_limit = RateLimit {
            max_requests,
            time_window,
            current_requests: 0,
            window_start: Instant::now(),
        };
        self.rate_limits.write().await.insert(user_id, rate_limit);
    }

    pub async fn check_rate_limit(&self, user_id: &str) -> bool {
        let mut rate_limits = self.rate_limits.write().await;
        
        if let Some(rate_limit) = rate_limits.get_mut(user_id) {
            // 检查时间窗口是否已过期
            if rate_limit.window_start.elapsed() >= rate_limit.time_window {
                rate_limit.current_requests = 0;
                rate_limit.window_start = Instant::now();
            }

            if rate_limit.current_requests >= rate_limit.max_requests {
                return false;
            }

            rate_limit.current_requests += 1;
            true
        } else {
            // 没有设置速率限制，默认允许
            true
        }
    }

    pub async fn log_access(&self, user_id: String, action: String, resource: String, success: bool, ip_address: Option<String>) {
        let entry = AuditEntry {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            user_id,
            action,
            resource,
            success,
            ip_address,
        };

        self.audit_log.write().await.push(entry);
    }

    pub async fn secure_access(&self, user_id: String, action: String, resource: String, ip_address: Option<String>) -> Result<bool> {
        // 检查权限
        if !self.check_permission(&user_id, &resource).await {
            self.log_access(user_id.clone(), action.clone(), resource.clone(), false, ip_address.clone()).await;
            return Err(anyhow::anyhow!("访问被拒绝：权限不足"));
        }

        // 检查速率限制
        if !self.check_rate_limit(&user_id).await {
            self.log_access(user_id.clone(), action.clone(), resource.clone(), false, ip_address.clone()).await;
            return Err(anyhow::anyhow!("访问被拒绝：超出速率限制"));
        }

        // 记录成功访问
        self.log_access(user_id, action, resource, true, ip_address).await;
        Ok(true)
    }

    pub async fn get_audit_log(&self) -> Vec<AuditEntry> {
        self.audit_log.read().await.clone()
    }
}

/// 2. 异步加密服务
pub struct AsyncEncryptionService {
    encryption_key: Arc<RwLock<Vec<u8>>>,
    encryption_history: Arc<RwLock<Vec<EncryptionRecord>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptionRecord {
    pub timestamp: u64,
    pub operation: String,
    pub data_size: usize,
    pub algorithm: String,
}

impl AsyncEncryptionService {
    pub fn new(key: Vec<u8>) -> Self {
        Self {
            encryption_key: Arc::new(RwLock::new(key)),
            encryption_history: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn encrypt(&self, data: &str) -> Result<String> {
        let start_time = Instant::now();
        let key = self.encryption_key.read().await;

        // 简化的加密实现（实际应用中应使用专业加密库）
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        key.hash(&mut hasher);
        let hash = hasher.finish();

        let encrypted = format!("{:x}", hash);
        
        // 记录加密操作
        let record = EncryptionRecord {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            operation: "encrypt".to_string(),
            data_size: data.len(),
            algorithm: "hash_based".to_string(),
        };
        self.encryption_history.write().await.push(record);

        debug!("数据加密完成，耗时: {:?}", start_time.elapsed());
        Ok(encrypted)
    }

    pub async fn decrypt(&self, encrypted_data: &str, original_data: &str) -> Result<bool> {
        let start_time = Instant::now();
        let encrypted = self.encrypt(original_data).await?;
        
        let is_valid = encrypted == encrypted_data;
        
        // 记录解密操作
        let record = EncryptionRecord {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            operation: "decrypt".to_string(),
            data_size: encrypted_data.len(),
            algorithm: "hash_based".to_string(),
        };
        self.encryption_history.write().await.push(record);

        debug!("数据解密完成，耗时: {:?}", start_time.elapsed());
        Ok(is_valid)
    }

    pub async fn get_encryption_history(&self) -> Vec<EncryptionRecord> {
        self.encryption_history.read().await.clone()
    }

    pub async fn rotate_key(&self, new_key: Vec<u8>) {
        *self.encryption_key.write().await = new_key;
        info!("加密密钥已轮换");
    }
}

/// 3. 异步输入验证器
pub struct AsyncInputValidator {
    validation_rules: Arc<RwLock<HashMap<String, Vec<ValidationRule>>>>,
    validation_history: Arc<RwLock<Vec<ValidationRecord>>>,
}

#[derive(Debug, Clone)]
pub struct ValidationRule {
    pub name: String,
    pub pattern: String,
    pub min_length: Option<usize>,
    pub max_length: Option<usize>,
    pub required: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationRecord {
    pub timestamp: u64,
    pub field_name: String,
    pub value: String,
    pub success: bool,
    pub error_message: Option<String>,
}

impl AsyncInputValidator {
    pub fn new() -> Self {
        Self {
            validation_rules: Arc::new(RwLock::new(HashMap::new())),
            validation_history: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn add_rule(&self, field_name: String, rule: ValidationRule) {
        self.validation_rules.write().await
            .entry(field_name)
            .or_insert_with(Vec::new)
            .push(rule);
    }

    pub async fn validate_field(&self, field_name: &str, value: &str) -> Result<()> {
        let rules = self.validation_rules.read().await;
        
        if let Some(field_rules) = rules.get(field_name) {
            for rule in field_rules {
                if rule.required && value.is_empty() {
                    self.log_validation(field_name, value, false, Some("字段是必需的".to_string())).await;
                    return Err(anyhow::anyhow!("字段 '{}' 是必需的", field_name));
                }

                if let Some(min_len) = rule.min_length {
                    if value.len() < min_len {
                        self.log_validation(field_name, value, false, Some(format!("最小长度应为 {}", min_len))).await;
                        return Err(anyhow::anyhow!("字段 '{}' 长度不能少于 {}", field_name, min_len));
                    }
                }

                if let Some(max_len) = rule.max_length {
                    if value.len() > max_len {
                        self.log_validation(field_name, value, false, Some(format!("最大长度应为 {}", max_len))).await;
                        return Err(anyhow::anyhow!("字段 '{}' 长度不能超过 {}", field_name, max_len));
                    }
                }

                // 简化的正则表达式验证
                if !rule.pattern.is_empty() && !value.contains(&rule.pattern) {
                    self.log_validation(field_name, value, false, Some(format!("格式不符合要求: {}", rule.pattern))).await;
                    return Err(anyhow::anyhow!("字段 '{}' 格式不正确", field_name));
                }
            }
        }

        self.log_validation(field_name, value, true, None).await;
        Ok(())
    }

    pub async fn validate_data(&self, data: &HashMap<String, String>) -> Result<()> {
        for (field_name, value) in data {
            self.validate_field(field_name, value).await?;
        }
        Ok(())
    }

    async fn log_validation(&self, field_name: &str, value: &str, success: bool, error_message: Option<String>) {
        let record = ValidationRecord {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            field_name: field_name.to_string(),
            value: value.to_string(),
            success,
            error_message,
        };
        self.validation_history.write().await.push(record);
    }

    pub async fn get_validation_history(&self) -> Vec<ValidationRecord> {
        self.validation_history.read().await.clone()
    }
}

/// 4. 异步安全会话管理器
pub struct AsyncSecureSessionManager {
    sessions: Arc<RwLock<HashMap<String, SecureSession>>>,
    session_timeout: Duration,
    max_sessions_per_user: usize,
}

#[derive(Debug, Clone)]
pub struct SecureSession {
    pub session_id: String,
    pub user_id: String,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub ip_address: String,
    pub user_agent: String,
    pub is_active: bool,
}

impl AsyncSecureSessionManager {
    pub fn new(session_timeout: Duration, max_sessions_per_user: usize) -> Self {
        Self {
            sessions: Arc::new(RwLock::new(HashMap::new())),
            session_timeout,
            max_sessions_per_user,
        }
    }

    pub async fn create_session(&self, user_id: String, ip_address: String, user_agent: String) -> Result<String> {
        // 清理过期会话
        self.cleanup_expired_sessions().await;

        // 检查用户会话数量限制
        let user_sessions = self.get_user_sessions(&user_id).await;
        if user_sessions.len() >= self.max_sessions_per_user {
            // 删除最旧的会话
            if let Some(oldest_session) = user_sessions.iter().min_by_key(|s| s.created_at) {
                self.invalidate_session(&oldest_session.session_id).await;
            }
        }

        let session_id = format!("session_{}_{}", user_id, std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs());

        let session = SecureSession {
            session_id: session_id.clone(),
            user_id: user_id.clone(),
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            ip_address,
            user_agent,
            is_active: true,
        };

        self.sessions.write().await.insert(session_id.clone(), session);
        info!("为用户 '{}' 创建新会话: {}", user_id, session_id);
        
        Ok(session_id)
    }

    pub async fn validate_session(&self, session_id: &str, ip_address: &str) -> Result<String> {
        let mut sessions = self.sessions.write().await;
        
        if let Some(session) = sessions.get_mut(session_id) {
            // 检查会话是否过期
            if session.last_accessed.elapsed() > self.session_timeout {
                session.is_active = false;
                return Err(anyhow::anyhow!("会话已过期"));
            }

            // 检查IP地址是否匹配（可选的安全检查）
            if session.ip_address != ip_address {
                warn!("会话 '{}' IP地址不匹配", session_id);
                // 可以选择是否允许IP地址不匹配的会话
            }

            session.last_accessed = Instant::now();
            Ok(session.user_id.clone())
        } else {
            Err(anyhow::anyhow!("无效的会话ID"))
        }
    }

    pub async fn invalidate_session(&self, session_id: &str) {
        if let Some(session) = self.sessions.write().await.get_mut(session_id) {
            session.is_active = false;
            info!("会话 '{}' 已失效", session_id);
        }
    }

    pub async fn invalidate_user_sessions(&self, user_id: &str) {
        let mut sessions = self.sessions.write().await;
        for session in sessions.values_mut() {
            if session.user_id == user_id {
                session.is_active = false;
            }
        }
        info!("用户 '{}' 的所有会话已失效", user_id);
    }

    pub async fn get_user_sessions(&self, user_id: &str) -> Vec<SecureSession> {
        self.sessions.read().await
            .values()
            .filter(|s| s.user_id == user_id)
            .cloned()
            .collect()
    }

    async fn cleanup_expired_sessions(&self) {
        let mut sessions = self.sessions.write().await;
        let _now = Instant::now();
        
        sessions.retain(|_, session| {
            session.last_accessed.elapsed() <= self.session_timeout && session.is_active
        });
    }

    pub async fn get_active_sessions_count(&self) -> usize {
        self.sessions.read().await
            .values()
            .filter(|s| s.is_active && s.last_accessed.elapsed() <= self.session_timeout)
            .count()
    }
}

/// 5. 异步安全日志记录器
pub struct AsyncSecureLogger {
    log_entries: Arc<RwLock<Vec<SecurityLogEntry>>>,
    log_levels: Arc<RwLock<HashMap<String, LogLevel>>>,
    max_log_entries: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityLogEntry {
    pub timestamp: u64,
    pub level: LogLevel,
    pub component: String,
    pub message: String,
    pub user_id: Option<String>,
    pub ip_address: Option<String>,
    pub severity: SeverityLevel,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogLevel {
    Debug,
    Info,
    Warning,
    Error,
    Critical,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SeverityLevel {
    Low,
    Medium,
    High,
    Critical,
}

impl AsyncSecureLogger {
    pub fn new(max_log_entries: usize) -> Self {
        Self {
            log_entries: Arc::new(RwLock::new(Vec::new())),
            log_levels: Arc::new(RwLock::new(HashMap::new())),
            max_log_entries,
        }
    }

    pub async fn set_component_log_level(&self, component: String, level: LogLevel) {
        self.log_levels.write().await.insert(component, level);
    }

    pub async fn log_security_event(
        &self,
        level: LogLevel,
        component: String,
        message: String,
        user_id: Option<String>,
        ip_address: Option<String>,
        severity: SeverityLevel,
    ) {
        let entry = SecurityLogEntry {
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            level: level.clone(),
            component: component.clone(),
            message: message.clone(),
            user_id,
            ip_address,
            severity: severity.clone(),
        };

        // 检查组件日志级别
        let should_log = if let Some(component_level) = self.log_levels.read().await.get(&component) {
            self.should_log_level(&level, component_level)
        } else {
            true // 默认记录所有级别
        };

        if should_log {
            let mut entries = self.log_entries.write().await;
            entries.push(entry.clone());

            // 限制日志条目数量
            let current_len = entries.len();
            if current_len > self.max_log_entries {
                let remove_count = current_len - self.max_log_entries;
                entries.drain(0..remove_count);
            }

            // 根据严重程度记录到不同的日志级别
            match severity {
                SeverityLevel::Critical => error!("[SECURITY-CRITICAL] {}: {}", component, message),
                SeverityLevel::High => error!("[SECURITY-HIGH] {}: {}", component, message),
                SeverityLevel::Medium => warn!("[SECURITY-MEDIUM] {}: {}", component, message),
                SeverityLevel::Low => info!("[SECURITY-LOW] {}: {}", component, message),
            }
        }
    }

    fn should_log_level(&self, entry_level: &LogLevel, component_level: &LogLevel) -> bool {
        match (entry_level, component_level) {
            (LogLevel::Debug, _) => true,
            (LogLevel::Info, LogLevel::Debug | LogLevel::Info) => true,
            (LogLevel::Warning, LogLevel::Debug | LogLevel::Info | LogLevel::Warning) => true,
            (LogLevel::Error, LogLevel::Debug | LogLevel::Info | LogLevel::Warning | LogLevel::Error) => true,
            (LogLevel::Critical, _) => true,
            _ => false,
        }
    }

    pub async fn get_security_logs(&self, component: Option<String>, level: Option<LogLevel>) -> Vec<SecurityLogEntry> {
        let entries = self.log_entries.read().await;
        
        entries.iter()
            .filter(|entry| {
                let component_match = component.as_ref().map_or(true, |c| entry.component == *c);
                let level_match = level.as_ref().map_or(true, |l| std::mem::discriminant(&entry.level) == std::mem::discriminant(l));
                component_match && level_match
            })
            .cloned()
            .collect()
    }

    pub async fn get_critical_security_events(&self) -> Vec<SecurityLogEntry> {
        let entries = self.log_entries.read().await;
        
        entries.iter()
            .filter(|entry| matches!(entry.severity, SeverityLevel::Critical | SeverityLevel::High))
            .cloned()
            .collect()
    }
}

/// 演示异步安全编程模式
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    info!("🚀 开始 2025 年异步安全编程模式演示");

    // 1. 异步访问控制演示
    demo_async_access_control().await?;

    // 2. 异步加密服务演示
    demo_async_encryption_service().await?;

    // 3. 异步输入验证演示
    demo_async_input_validation().await?;

    // 4. 异步安全会话管理演示
    demo_async_secure_session_management().await?;

    // 5. 异步安全日志记录演示
    demo_async_secure_logging().await?;

    info!("✅ 2025 年异步安全编程模式演示完成!");
    Ok(())
}

async fn demo_async_access_control() -> Result<()> {
    info!("🔐 演示异步访问控制");

    let access_control = AsyncAccessControlManager::new();

    // 设置权限
    access_control.grant_permission("user1".to_string(), "read_data".to_string()).await;
    access_control.grant_permission("user1".to_string(), "write_data".to_string()).await;
    access_control.grant_permission("user2".to_string(), "read_data".to_string()).await;

    // 设置速率限制
    access_control.set_rate_limit("user1".to_string(), 5, Duration::from_secs(10)).await;
    access_control.set_rate_limit("user2".to_string(), 3, Duration::from_secs(10)).await;

    // 测试访问控制
    let result1 = access_control.secure_access(
        "user1".to_string(),
        "read".to_string(),
        "read_data".to_string(),
        Some("192.168.1.1".to_string()),
    ).await?;
    info!("用户1读取数据: {}", result1);

    let result2 = access_control.secure_access(
        "user2".to_string(),
        "write".to_string(),
        "write_data".to_string(),
        Some("192.168.1.2".to_string()),
    ).await;
    match result2 {
        Ok(_) => info!("用户2写入数据成功"),
        Err(e) => warn!("用户2写入数据失败: {}", e),
    }

    // 查看审计日志
    let audit_log = access_control.get_audit_log().await;
    info!("审计日志条目数: {}", audit_log.len());

    Ok(())
}

async fn demo_async_encryption_service() -> Result<()> {
    info!("🔒 演示异步加密服务");

    let encryption_service = AsyncEncryptionService::new(b"secret_key_2025".to_vec());

    let original_data = "敏感数据：用户密码和信用卡信息";
    
    // 加密数据
    let encrypted = encryption_service.encrypt(original_data).await?;
    info!("加密后的数据: {}", encrypted);

    // 验证解密
    let is_valid = encryption_service.decrypt(&encrypted, original_data).await?;
    info!("解密验证结果: {}", is_valid);

    // 查看加密历史
    let history = encryption_service.get_encryption_history().await;
    info!("加密操作历史: {} 条记录", history.len());

    // 轮换密钥
    encryption_service.rotate_key(b"new_secret_key_2025".to_vec()).await;
    info!("加密密钥已轮换");

    Ok(())
}

async fn demo_async_input_validation() -> Result<()> {
    info!("✅ 演示异步输入验证");

    let validator = AsyncInputValidator::new();

    // 添加验证规则
    validator.add_rule("username".to_string(), ValidationRule {
        name: "username_rule".to_string(),
        pattern: "user".to_string(),
        min_length: Some(3),
        max_length: Some(20),
        required: true,
    }).await;

    validator.add_rule("email".to_string(), ValidationRule {
        name: "email_rule".to_string(),
        pattern: "@".to_string(),
        min_length: Some(5),
        max_length: Some(100),
        required: true,
    }).await;

    // 验证数据
    let mut data = HashMap::new();
    data.insert("username".to_string(), "user123".to_string());
    data.insert("email".to_string(), "user@example.com".to_string());

    let validation_result = validator.validate_data(&data).await;
    match validation_result {
        Ok(_) => info!("数据验证通过"),
        Err(e) => warn!("数据验证失败: {}", e),
    }

    // 测试无效数据
    let mut invalid_data = HashMap::new();
    invalid_data.insert("username".to_string(), "ab".to_string()); // 太短
    invalid_data.insert("email".to_string(), "invalid_email".to_string()); // 缺少@

    let invalid_result = validator.validate_data(&invalid_data).await;
    match invalid_result {
        Ok(_) => info!("无效数据验证通过"),
        Err(e) => warn!("无效数据验证失败: {}", e),
    }

    // 查看验证历史
    let history = validator.get_validation_history().await;
    info!("验证历史: {} 条记录", history.len());

    Ok(())
}

async fn demo_async_secure_session_management() -> Result<()> {
    info!("🔑 演示异步安全会话管理");

    let session_manager = AsyncSecureSessionManager::new(
        Duration::from_secs(300), // 5分钟超时
        3, // 每个用户最多3个会话
    );

    // 创建会话
    let session_id1 = session_manager.create_session(
        "user1".to_string(),
        "192.168.1.1".to_string(),
        "Mozilla/5.0".to_string(),
    ).await?;
    info!("创建会话1: {}", session_id1);

    let session_id2 = session_manager.create_session(
        "user1".to_string(),
        "192.168.1.2".to_string(),
        "Chrome/91.0".to_string(),
    ).await?;
    info!("创建会话2: {}", session_id2);

    // 验证会话
    let user_id = session_manager.validate_session(&session_id1, "192.168.1.1").await?;
    info!("会话验证成功，用户ID: {}", user_id);

    // 查看用户会话
    let user_sessions = session_manager.get_user_sessions("user1").await;
    info!("用户1的会话数: {}", user_sessions.len());

    // 查看活跃会话数
    let active_sessions = session_manager.get_active_sessions_count().await;
    info!("活跃会话数: {}", active_sessions);

    Ok(())
}

async fn demo_async_secure_logging() -> Result<()> {
    info!("📝 演示异步安全日志记录");

    let secure_logger = AsyncSecureLogger::new(1000);

    // 设置组件日志级别
    secure_logger.set_component_log_level("auth".to_string(), LogLevel::Info).await;
    secure_logger.set_component_log_level("payment".to_string(), LogLevel::Warning).await;

    // 记录安全事件
    secure_logger.log_security_event(
        LogLevel::Info,
        "auth".to_string(),
        "用户登录成功".to_string(),
        Some("user1".to_string()),
        Some("192.168.1.1".to_string()),
        SeverityLevel::Low,
    ).await;

    secure_logger.log_security_event(
        LogLevel::Warning,
        "payment".to_string(),
        "异常支付尝试".to_string(),
        Some("user2".to_string()),
        Some("192.168.1.100".to_string()),
        SeverityLevel::High,
    ).await;

    secure_logger.log_security_event(
        LogLevel::Error,
        "auth".to_string(),
        "多次登录失败".to_string(),
        Some("user3".to_string()),
        Some("192.168.1.200".to_string()),
        SeverityLevel::Critical,
    ).await;

    // 查看关键安全事件
    let critical_events = secure_logger.get_critical_security_events().await;
    info!("关键安全事件数: {}", critical_events.len());

    // 查看特定组件的日志
    let auth_logs = secure_logger.get_security_logs(Some("auth".to_string()), None).await;
    info!("认证组件日志数: {}", auth_logs.len());

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_access_control() {
        let access_control = AsyncAccessControlManager::new();
        access_control.grant_permission("user1".to_string(), "resource1".to_string()).await;
        
        assert!(access_control.check_permission("user1", "resource1").await);
        assert!(!access_control.check_permission("user1", "resource2").await);
    }

    #[tokio::test]
    async fn test_async_encryption_service() {
        let encryption_service = AsyncEncryptionService::new(b"test_key".to_vec());
        let data = "test data";
        
        let encrypted = encryption_service.encrypt(data).await.unwrap();
        let is_valid = encryption_service.decrypt(&encrypted, data).await.unwrap();
        
        assert!(is_valid);
    }

    #[tokio::test]
    async fn test_async_input_validation() {
        let validator = AsyncInputValidator::new();
        validator.add_rule("test_field".to_string(), ValidationRule {
            name: "test_rule".to_string(),
            pattern: "".to_string(),
            min_length: Some(3),
            max_length: Some(10),
            required: true,
        }).await;
        
        assert!(validator.validate_field("test_field", "valid").await.is_ok());
        assert!(validator.validate_field("test_field", "ab").await.is_err());
    }

    #[tokio::test]
    async fn test_async_secure_session_management() {
        let session_manager = AsyncSecureSessionManager::new(Duration::from_secs(60), 5);
        
        let session_id = session_manager.create_session(
            "user1".to_string(),
            "127.0.0.1".to_string(),
            "test".to_string(),
        ).await.unwrap();
        
        let user_id = session_manager.validate_session(&session_id, "127.0.0.1").await.unwrap();
        assert_eq!(user_id, "user1");
    }

    #[tokio::test]
    async fn test_async_secure_logger() {
        let logger = AsyncSecureLogger::new(100);
        
        logger.log_security_event(
            LogLevel::Info,
            "test".to_string(),
            "test message".to_string(),
            None,
            None,
            SeverityLevel::Low,
        ).await;
        
        let logs = logger.get_security_logs(None, None).await;
        assert_eq!(logs.len(), 1);
    }
}
