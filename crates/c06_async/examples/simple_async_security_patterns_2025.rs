use anyhow::Result;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tracing::{info, warn, error};
use std::collections::HashMap;

/// 2025年简化异步安全编程模式演示
/// 展示实用的异步安全编程最佳实践

/// 1. 简化异步访问控制
#[derive(Debug, Clone, PartialEq)]
pub enum Permission {
    Read,
    Write,
    Admin,
}

#[derive(Debug, Clone)]
pub struct User {
    pub id: String,
    pub permissions: Vec<Permission>,
}

pub struct SimpleAsyncAccessControl {
    users: Arc<RwLock<HashMap<String, User>>>,
    audit_log: Arc<RwLock<Vec<String>>>,
}

impl SimpleAsyncAccessControl {
    pub fn new() -> Self {
        Self {
            users: Arc::new(RwLock::new(HashMap::new())),
            audit_log: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn add_user(&self, user: User) {
        self.users.write().await.insert(user.id.clone(), user);
    }

    pub async fn check_permission(&self, user_id: &str, required_permission: &Permission) -> bool {
        let users = self.users.read().await;
        if let Some(user) = users.get(user_id) {
            let has_permission = user.permissions.contains(required_permission);
            
            // 记录审计日志
            let log_entry = format!(
                "用户 {} 请求权限 {:?}: {}",
                user_id,
                required_permission,
                if has_permission { "允许" } else { "拒绝" }
            );
            self.audit_log.write().await.push(log_entry);
            
            has_permission
        } else {
            self.audit_log.write().await.push(format!("用户 {} 不存在", user_id));
            false
        }
    }

    pub async fn get_audit_log(&self) -> Vec<String> {
        self.audit_log.read().await.clone()
    }
}

/// 2. 简化异步加密服务
pub struct SimpleAsyncEncryption {
    key: Arc<RwLock<String>>,
    operation_count: Arc<RwLock<u32>>,
}

impl SimpleAsyncEncryption {
    pub fn new() -> Self {
        Self {
            key: Arc::new(RwLock::new("default_key_2025".to_string())),
            operation_count: Arc::new(RwLock::new(0)),
        }
    }

    pub async fn encrypt(&self, data: &str) -> String {
        let key = self.key.read().await;
        let mut count = self.operation_count.write().await;
        *count += 1;
        
        // 简单的XOR加密（仅用于演示）
        let encrypted: String = data
            .chars()
            .zip(key.chars().cycle())
            .map(|(c, k)| ((c as u8) ^ (k as u8)) as char)
            .collect();
        
        format!("{:x}", encrypted.as_bytes().iter().fold(0u64, |acc, &b| acc.wrapping_mul(31).wrapping_add(b as u64)))
    }

    pub async fn decrypt(&self, encrypted: &str, original: &str) -> bool {
        let decrypted = self.encrypt(original).await;
        decrypted == encrypted
    }

    pub async fn rotate_key(&self) {
        let mut key = self.key.write().await;
        *key = format!("new_key_{}", Instant::now().elapsed().as_millis());
        info!("加密密钥已轮换");
    }

    pub async fn get_operation_count(&self) -> u32 {
        *self.operation_count.read().await
    }
}

/// 3. 简化异步输入验证
#[derive(Debug, Clone)]
pub struct ValidationRule {
    pub field: String,
    pub required: bool,
    pub max_length: Option<usize>,
    pub pattern: Option<String>,
}

pub struct SimpleAsyncValidator {
    rules: Arc<RwLock<HashMap<String, Vec<ValidationRule>>>>,
    validation_history: Arc<RwLock<Vec<String>>>,
}

impl SimpleAsyncValidator {
    pub fn new() -> Self {
        Self {
            rules: Arc::new(RwLock::new(HashMap::new())),
            validation_history: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn add_validation_rules(&self, entity_type: String, rules: Vec<ValidationRule>) {
        self.rules.write().await.insert(entity_type, rules);
    }

    pub async fn validate(&self, entity_type: &str, data: &HashMap<String, String>) -> Result<()> {
        let rules = self.rules.read().await;
        if let Some(entity_rules) = rules.get(entity_type) {
            for rule in entity_rules {
                if let Some(value) = data.get(&rule.field) {
                    // 检查必填字段
                    if rule.required && value.trim().is_empty() {
                        let error = format!("字段 '{}' 是必填的", rule.field);
                        self.validation_history.write().await.push(error.clone());
                        return Err(anyhow::anyhow!(error));
                    }

                    // 检查最大长度
                    if let Some(max_len) = rule.max_length {
                        if value.len() > max_len {
                            let error = format!("字段 '{}' 长度超过限制 ({} 字符)", rule.field, max_len);
                            self.validation_history.write().await.push(error.clone());
                            return Err(anyhow::anyhow!(error));
                        }
                    }

                    // 简单的邮箱格式检查
                    if rule.field == "email" && !value.contains("@") {
                        let error = format!("字段 '{}' 格式不正确", rule.field);
                        self.validation_history.write().await.push(error.clone());
                        return Err(anyhow::anyhow!(error));
                    }
                } else if rule.required {
                    let error = format!("字段 '{}' 是必填的", rule.field);
                    self.validation_history.write().await.push(error.clone());
                    return Err(anyhow::anyhow!(error));
                }
            }
        }

        self.validation_history.write().await.push(format!("{} 验证通过", entity_type));
        Ok(())
    }

    pub async fn get_validation_history(&self) -> Vec<String> {
        self.validation_history.read().await.clone()
    }
}

/// 4. 简化异步会话管理
#[derive(Debug, Clone)]
pub struct Session {
    pub id: String,
    pub user_id: String,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub ip_address: Option<String>,
    pub is_active: bool,
}

pub struct SimpleAsyncSessionManager {
    sessions: Arc<RwLock<HashMap<String, Session>>>,
    session_timeout: Duration,
}

impl SimpleAsyncSessionManager {
    pub fn new(session_timeout: Duration) -> Self {
        Self {
            sessions: Arc::new(RwLock::new(HashMap::new())),
            session_timeout,
        }
    }

    pub async fn create_session(&self, user_id: String, ip_address: Option<String>) -> String {
        let session_id = format!("session_{}_{}", user_id, Instant::now().elapsed().as_secs());
        let session = Session {
            id: session_id.clone(),
            user_id,
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            ip_address,
            is_active: true,
        };

        self.sessions.write().await.insert(session_id.clone(), session);
        session_id
    }

    pub async fn validate_session(&self, session_id: &str, ip_address: Option<String>) -> Result<String> {
        let mut sessions = self.sessions.write().await;
        if let Some(session) = sessions.get_mut(session_id) {
            // 检查会话是否过期
            if session.last_accessed.elapsed() > self.session_timeout {
                session.is_active = false;
                return Err(anyhow::anyhow!("会话已过期"));
            }

            // 检查IP地址（如果提供）
            if let Some(ref current_ip) = ip_address {
                if let Some(ref session_ip) = session.ip_address {
                    if current_ip != session_ip {
                        warn!("会话 '{}' IP地址不匹配", session_id);
                    }
                }
            }

            session.last_accessed = Instant::now();
            Ok(session.user_id.clone())
        } else {
            Err(anyhow::anyhow!("会话不存在"))
        }
    }

    pub async fn get_active_sessions(&self) -> Vec<Session> {
        let sessions = self.sessions.read().await;
        sessions.values()
            .filter(|session| session.is_active && session.last_accessed.elapsed() <= self.session_timeout)
            .cloned()
            .collect()
    }

    pub async fn cleanup_expired_sessions(&self) {
        let mut sessions = self.sessions.write().await;
        sessions.retain(|_, session| {
            session.last_accessed.elapsed() <= self.session_timeout && session.is_active
        });
    }
}

/// 5. 简化异步安全日志
#[derive(Debug, Clone, PartialEq)]
pub enum SecurityLevel {
    Low,
    Medium,
    High,
    Critical,
}

pub struct SimpleAsyncSecurityLogger {
    logs: Arc<RwLock<Vec<(SecurityLevel, String, String)>>>,
    max_entries: usize,
}

impl SimpleAsyncSecurityLogger {
    pub fn new(max_entries: usize) -> Self {
        Self {
            logs: Arc::new(RwLock::new(Vec::new())),
            max_entries,
        }
    }

    pub async fn log(&self, level: SecurityLevel, component: String, message: String) {
        let mut logs = self.logs.write().await;
        logs.push((level.clone(), component.clone(), message.clone()));

        // 限制日志条目数量
        if logs.len() > self.max_entries {
            logs.remove(0);
        }

        // 根据级别记录
        match level {
            SecurityLevel::Low => info!("[SECURITY-LOW] {}: {}", component, message),
            SecurityLevel::Medium => warn!("[SECURITY-MEDIUM] {}: {}", component, message),
            SecurityLevel::High => error!("[SECURITY-HIGH] {}: {}", component, message),
            SecurityLevel::Critical => error!("[SECURITY-CRITICAL] {}: {}", component, message),
        }
    }

    pub async fn get_logs(&self) -> Vec<(SecurityLevel, String, String)> {
        self.logs.read().await.clone()
    }

    pub async fn get_critical_logs(&self) -> Vec<(SecurityLevel, String, String)> {
        let logs = self.logs.read().await;
        logs.iter()
            .filter(|(level, _, _)| *level == SecurityLevel::Critical)
            .cloned()
            .collect()
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    
    info!("🚀 开始 2025 年简化异步安全编程模式演示");

    // 1. 演示简化异步访问控制
    info!("🔐 演示简化异步访问控制");
    let access_control = SimpleAsyncAccessControl::new();
    
    access_control.add_user(User {
        id: "user1".to_string(),
        permissions: vec![Permission::Read, Permission::Write],
    }).await;

    access_control.add_user(User {
        id: "user2".to_string(),
        permissions: vec![Permission::Read],
    }).await;

    let can_read = access_control.check_permission("user1", &Permission::Read).await;
    info!("用户1读取权限: {}", can_read);

    let can_write = access_control.check_permission("user2", &Permission::Write).await;
    info!("用户2写入权限: {}", can_write);

    let audit_log = access_control.get_audit_log().await;
    info!("审计日志条目数: {}", audit_log.len());

    // 2. 演示简化异步加密服务
    info!("🔒 演示简化异步加密服务");
    let encryption = SimpleAsyncEncryption::new();
    
    let encrypted = encryption.encrypt("sensitive_data").await;
    info!("加密后的数据: {}", encrypted);

    let is_valid = encryption.decrypt(&encrypted, "sensitive_data").await;
    info!("解密验证结果: {}", is_valid);

    let operation_count = encryption.get_operation_count().await;
    info!("加密操作次数: {}", operation_count);

    encryption.rotate_key().await;
    encryption.rotate_key().await;

    // 3. 演示简化异步输入验证
    info!("✅ 演示简化异步输入验证");
    let validator = SimpleAsyncValidator::new();
    
    validator.add_validation_rules("user".to_string(), vec![
        ValidationRule {
            field: "name".to_string(),
            required: true,
            max_length: Some(50),
            pattern: None,
        },
        ValidationRule {
            field: "email".to_string(),
            required: true,
            max_length: Some(100),
            pattern: Some("@".to_string()),
        },
    ]).await;

    let mut valid_data = HashMap::new();
    valid_data.insert("name".to_string(), "John Doe".to_string());
    valid_data.insert("email".to_string(), "john@example.com".to_string());
    
    let validation_result = validator.validate("user", &valid_data).await;
    info!("数据验证结果: {:?}", validation_result.is_ok());

    let mut invalid_data = HashMap::new();
    invalid_data.insert("name".to_string(), "Jane".to_string());
    invalid_data.insert("email".to_string(), "invalid-email".to_string());
    
    let invalid_result = validator.validate("user", &invalid_data).await;
    info!("无效数据验证结果: {:?}", invalid_result.is_err());

    let validation_history = validator.get_validation_history().await;
    info!("验证历史条目数: {}", validation_history.len());

    // 4. 演示简化异步会话管理
    info!("🔑 演示简化异步会话管理");
    let session_manager = SimpleAsyncSessionManager::new(Duration::from_secs(3600));
    
    let session_id1 = session_manager.create_session("user1".to_string(), Some("192.168.1.1".to_string())).await;
    info!("创建会话1: {}", session_id1);

    let session_id2 = session_manager.create_session("user1".to_string(), Some("192.168.1.2".to_string())).await;
    info!("创建会话2: {}", session_id2);

    let validation_result = session_manager.validate_session(&session_id1, Some("192.168.1.1".to_string())).await;
    info!("会话验证结果: {:?}", validation_result);

    let active_sessions = session_manager.get_active_sessions().await;
    info!("活跃会话数: {}", active_sessions.len());

    session_manager.cleanup_expired_sessions().await;

    // 5. 演示简化异步安全日志
    info!("📝 演示简化异步安全日志");
    let security_logger = SimpleAsyncSecurityLogger::new(1000);
    
    security_logger.log(SecurityLevel::Low, "auth".to_string(), "用户登录成功".to_string()).await;
    security_logger.log(SecurityLevel::High, "payment".to_string(), "异常支付尝试".to_string()).await;
    security_logger.log(SecurityLevel::Critical, "auth".to_string(), "多次登录失败".to_string()).await;

    let critical_logs = security_logger.get_critical_logs().await;
    info!("关键安全事件数: {}", critical_logs.len());

    let all_logs = security_logger.get_logs().await;
    info!("总日志条目数: {}", all_logs.len());

    info!("✅ 2025 年简化异步安全编程模式演示完成!");
    
    Ok(())
}
