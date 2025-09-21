//! 设备认证模块
//! 
//! 提供设备认证和授权功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use chrono::{DateTime, Utc};
use super::SecurityError;

/// 设备认证器
pub struct DeviceAuthenticator {
    /// 受信任的证书映射
    trusted_certificates: HashMap<String, DeviceCertificate>,
    /// 活跃令牌映射
    active_tokens: HashMap<String, AuthToken>,
    /// 认证配置
    config: AuthenticationConfig,
    /// 访问控制策略
    access_policies: HashMap<String, AccessPolicy>,
    /// 审计日志
    audit_logs: Vec<AuditLogEntry>,
    /// 会话管理
    active_sessions: HashMap<String, Session>,
    /// 多因素认证配置
    mfa_config: MFAConfig,
}

/// 访问控制策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessPolicy {
    pub id: String,
    pub name: String,
    pub description: String,
    pub rules: Vec<AccessRule>,
    pub priority: u32,
    pub enabled: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 访问规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessRule {
    pub resource: String,
    pub action: String,
    pub effect: AccessEffect,
    pub conditions: Vec<AccessCondition>,
}

/// 访问效果
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AccessEffect {
    Allow,
    Deny,
}

/// 访问条件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessCondition {
    pub field: String,
    pub operator: String,
    pub value: serde_json::Value,
}

/// 审计日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditLogEntry {
    pub id: String,
    pub timestamp: DateTime<Utc>,
    pub event_type: AuditEventType,
    pub device_id: String,
    pub user_id: Option<String>,
    pub resource: String,
    pub action: String,
    pub result: AuditResult,
    pub details: HashMap<String, String>,
    pub ip_address: Option<String>,
    pub user_agent: Option<String>,
}

/// 审计事件类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AuditEventType {
    Authentication,
    Authorization,
    DataAccess,
    ConfigurationChange,
    SecurityEvent,
    SystemEvent,
}

/// 审计结果
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AuditResult {
    Success,
    Failure,
    Warning,
}

/// 会话信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Session {
    pub id: String,
    pub device_id: String,
    pub user_id: Option<String>,
    pub created_at: DateTime<Utc>,
    pub last_activity: DateTime<Utc>,
    pub expires_at: DateTime<Utc>,
    pub ip_address: Option<String>,
    pub user_agent: Option<String>,
    pub is_active: bool,
}

/// 多因素认证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MFAConfig {
    pub enabled: bool,
    pub methods: Vec<MFAMethod>,
    pub backup_codes: Vec<String>,
    pub grace_period_minutes: u32,
}

/// 多因素认证方法
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum MFAMethod {
    TOTP,
    SMS,
    Email,
    HardwareToken,
    Biometric,
}

/// 安全统计信息
#[derive(Debug, Clone)]
pub struct SecurityStats {
    pub total_authentications: u64,
    pub successful_authentications: u64,
    pub failed_authentications: u64,
    pub active_sessions: usize,
    pub active_tokens: usize,
    pub security_events: u64,
    pub last_security_event: Option<DateTime<Utc>>,
}

/// 认证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthenticationConfig {
    /// 令牌过期时间 (小时)
    pub token_expiry_hours: u32,
    /// 最大活跃令牌数
    pub max_active_tokens: usize,
    /// 是否启用令牌刷新
    pub enable_token_refresh: bool,
    /// 刷新令牌过期时间 (天)
    pub refresh_token_expiry_days: u32,
    /// 是否启用多因素认证
    pub enable_mfa: bool,
}

impl Default for AuthenticationConfig {
    fn default() -> Self {
        Self {
            token_expiry_hours: 24,
            max_active_tokens: 1000,
            enable_token_refresh: true,
            refresh_token_expiry_days: 30,
            enable_mfa: false,
        }
    }
}

/// 设备证书
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceCertificate {
    /// 设备ID
    pub device_id: String,
    /// 公钥
    pub public_key: Vec<u8>,
    /// 颁发时间
    pub issued_at: DateTime<Utc>,
    /// 过期时间
    pub expires_at: DateTime<Utc>,
    /// 颁发者
    pub issuer: String,
    /// 证书签名
    pub signature: Vec<u8>,
    /// 证书链
    pub certificate_chain: Vec<Vec<u8>>,
    /// 证书扩展
    pub extensions: HashMap<String, String>,
}

impl DeviceCertificate {
    /// 创建新的设备证书
    pub fn new(
        device_id: String,
        public_key: Vec<u8>,
        issuer: String,
        validity_days: u32,
    ) -> Self {
        let now = Utc::now();
        let expires_at = now + chrono::Duration::days(validity_days as i64);
        
        Self {
            device_id,
            public_key,
            issued_at: now,
            expires_at,
            issuer,
            signature: Vec::new(),
            certificate_chain: Vec::new(),
            extensions: HashMap::new(),
        }
    }

    /// 检查证书是否过期
    pub fn is_expired(&self) -> bool {
        self.expires_at < Utc::now()
    }

    /// 检查证书是否有效
    pub fn is_valid(&self) -> bool {
        !self.is_expired() && !self.public_key.is_empty()
    }

    /// 检查证书是否即将过期
    pub fn is_expiring_soon(&self, days: u32) -> bool {
        let threshold = Utc::now() + chrono::Duration::days(days as i64);
        self.expires_at < threshold
    }

    /// 获取证书剩余有效天数
    pub fn get_remaining_days(&self) -> i64 {
        let now = Utc::now();
        if self.expires_at > now {
            (self.expires_at - now).num_days()
        } else {
            0
        }
    }

    /// 添加证书扩展
    pub fn add_extension(&mut self, key: String, value: String) {
        self.extensions.insert(key, value);
    }

    /// 获取证书扩展
    pub fn get_extension(&self, key: &str) -> Option<&String> {
        self.extensions.get(key)
    }
}

/// 设备凭证
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceCredentials {
    /// 设备ID
    pub device_id: String,
    /// 私钥
    pub private_key: Vec<u8>,
    /// 设备证书
    pub certificate: DeviceCertificate,
    /// 设备密钥对类型
    pub key_type: KeyType,
    /// 创建时间
    pub created_at: DateTime<Utc>,
}

/// 密钥类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum KeyType {
    /// RSA密钥
    RSA { key_size: u32 },
    /// ECDSA密钥
    ECDSA { curve: String },
    /// Ed25519密钥
    Ed25519,
}

impl KeyType {
    /// 获取密钥类型描述
    pub fn description(&self) -> &'static str {
        match self {
            KeyType::RSA { .. } => "RSA密钥",
            KeyType::ECDSA { .. } => "ECDSA密钥",
            KeyType::Ed25519 => "Ed25519密钥",
        }
    }
}

/// 认证令牌
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthToken {
    /// 令牌ID
    pub token_id: String,
    /// 设备ID
    pub device_id: String,
    /// 颁发时间
    pub issued_at: DateTime<Utc>,
    /// 过期时间
    pub expires_at: DateTime<Utc>,
    /// 权限列表
    pub permissions: Vec<Permission>,
    /// 令牌类型
    pub token_type: TokenType,
    /// 令牌签名
    pub signature: Vec<u8>,
    /// 刷新令牌
    pub refresh_token: Option<String>,
    /// 令牌元数据
    pub metadata: HashMap<String, String>,
}

/// 令牌类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum TokenType {
    /// 访问令牌
    Access,
    /// 刷新令牌
    Refresh,
    /// 设备令牌
    Device,
    /// 服务令牌
    Service,
}

/// 权限
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Permission {
    /// 读取权限
    Read,
    /// 写入权限
    Write,
    /// 执行权限
    Execute,
    /// 管理权限
    Admin,
    /// 自定义权限
    Custom(String),
}

impl Permission {
    /// 获取权限描述
    pub fn description(&self) -> String {
        match self {
            Permission::Read => "读取权限".to_string(),
            Permission::Write => "写入权限".to_string(),
            Permission::Execute => "执行权限".to_string(),
            Permission::Admin => "管理权限".to_string(),
            Permission::Custom(name) => format!("自定义权限: {}", name),
        }
    }
}

impl AuthToken {
    /// 创建新的认证令牌
    pub fn new(
        token_id: String,
        device_id: String,
        permissions: Vec<Permission>,
        token_type: TokenType,
        expiry_hours: u32,
    ) -> Self {
        let now = Utc::now();
        let expires_at = now + chrono::Duration::hours(expiry_hours as i64);
        
        Self {
            token_id,
            device_id,
            issued_at: now,
            expires_at,
            permissions,
            token_type,
            signature: Vec::new(),
            refresh_token: None,
            metadata: HashMap::new(),
        }
    }

    /// 检查令牌是否过期
    pub fn is_expired(&self) -> bool {
        self.expires_at < Utc::now()
    }

    /// 检查令牌是否即将过期
    pub fn is_expiring_soon(&self, hours: u32) -> bool {
        let threshold = Utc::now() + chrono::Duration::hours(hours as i64);
        self.expires_at < threshold
    }

    /// 检查是否有指定权限
    pub fn has_permission(&self, permission: &Permission) -> bool {
        self.permissions.contains(permission)
    }

    /// 检查是否有任意权限
    pub fn has_any_permission(&self, permissions: &[Permission]) -> bool {
        permissions.iter().any(|p| self.has_permission(p))
    }

    /// 检查是否有所有权限
    pub fn has_all_permissions(&self, permissions: &[Permission]) -> bool {
        permissions.iter().all(|p| self.has_permission(p))
    }

    /// 添加元数据
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    /// 获取元数据
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }

    /// 设置刷新令牌
    pub fn set_refresh_token(&mut self, refresh_token: String) {
        self.refresh_token = Some(refresh_token);
    }
}

/// 认证结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthenticationResult {
    /// 是否认证成功
    pub success: bool,
    /// 认证令牌
    pub token: Option<AuthToken>,
    /// 错误信息
    pub error: Option<String>,
    /// 认证时间
    pub authenticated_at: DateTime<Utc>,
    /// 客户端信息
    pub client_info: Option<ClientInfo>,
}

/// 客户端信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClientInfo {
    /// 客户端IP地址
    pub ip_address: String,
    /// 用户代理
    pub user_agent: Option<String>,
    /// 客户端类型
    pub client_type: ClientType,
    /// 地理位置
    pub location: Option<Location>,
}

/// 客户端类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ClientType {
    /// 移动设备
    Mobile,
    /// 桌面设备
    Desktop,
    /// 服务器
    Server,
    /// 物联网设备
    IoTDevice,
    /// 未知
    Unknown,
}

/// 地理位置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Location {
    /// 国家
    pub country: Option<String>,
    /// 城市
    pub city: Option<String>,
    /// 经度
    pub longitude: Option<f64>,
    /// 纬度
    pub latitude: Option<f64>,
}

impl DeviceAuthenticator {
    /// 创建新的设备认证器
    pub fn new(config: AuthenticationConfig) -> Self {
        Self {
            trusted_certificates: HashMap::new(),
            active_tokens: HashMap::new(),
            config,
            access_policies: HashMap::new(),
            audit_logs: Vec::new(),
            active_sessions: HashMap::new(),
            mfa_config: MFAConfig {
                enabled: false,
                methods: Vec::new(),
                backup_codes: Vec::new(),
                grace_period_minutes: 30,
            },
        }
    }

    /// 添加受信任的证书
    pub fn add_trusted_certificate(&mut self, certificate: DeviceCertificate) -> Result<(), SecurityError> {
        if certificate.is_expired() {
            return Err(SecurityError::CertificateError("证书已过期".to_string()));
        }
        
        self.trusted_certificates.insert(certificate.device_id.clone(), certificate);
        Ok(())
    }

    /// 移除受信任的证书
    pub fn remove_trusted_certificate(&mut self, device_id: &str) -> bool {
        self.trusted_certificates.remove(device_id).is_some()
    }

    /// 验证设备证书
    pub fn verify_device_certificate(&self, certificate: &DeviceCertificate) -> Result<bool, SecurityError> {
        // 检查证书是否过期
        if certificate.is_expired() {
            return Err(SecurityError::CertificateError("证书已过期".to_string()));
        }

        // 检查证书是否在受信任列表中
        if !self.trusted_certificates.contains_key(&certificate.device_id) {
            return Err(SecurityError::CertificateError("证书不在受信任列表中".to_string()));
        }

        // 这里应该验证证书签名，简化实现
        Ok(true)
    }

    /// 生成认证令牌
    pub fn generate_auth_token(
        &mut self,
        device_id: &str,
        permissions: Vec<Permission>,
        token_type: TokenType,
    ) -> Result<AuthToken, SecurityError> {
        // 检查设备证书
        if !self.trusted_certificates.contains_key(device_id) {
            return Err(SecurityError::AuthenticationFailed(
                format!("设备 {} 未认证", device_id)
            ));
        }

        // 检查活跃令牌数量限制
        if self.active_tokens.len() >= self.config.max_active_tokens {
            return Err(SecurityError::AuthenticationFailed(
                "活跃令牌数量已达上限".to_string()
            ));
        }

        let token_id = uuid::Uuid::new_v4().to_string();
        let token = AuthToken::new(
            token_id.clone(),
            device_id.to_string(),
            permissions,
            token_type,
            self.config.token_expiry_hours,
        );

        // 生成刷新令牌
        if self.config.enable_token_refresh {
            let _refresh_token = uuid::Uuid::new_v4().to_string();
            // 注意：这里需要可变引用，但token是不可变的
            // 在实际实现中，可能需要重新设计
        }

        self.active_tokens.insert(token_id, token.clone());
        Ok(token)
    }

    /// 验证认证令牌
    pub fn verify_auth_token(&self, token: &AuthToken) -> Result<bool, SecurityError> {
        // 检查令牌是否过期
        if token.is_expired() {
            return Err(SecurityError::AuthenticationFailed("令牌已过期".to_string()));
        }

        // 检查令牌是否在活跃列表中
        if !self.active_tokens.contains_key(&token.token_id) {
            return Err(SecurityError::AuthenticationFailed("令牌无效".to_string()));
        }

        // 检查设备证书
        if !self.trusted_certificates.contains_key(&token.device_id) {
            return Err(SecurityError::AuthenticationFailed(
                format!("设备 {} 证书无效", token.device_id)
            ));
        }

        Ok(true)
    }

    /// 撤销认证令牌
    pub fn revoke_auth_token(&mut self, token_id: &str) -> bool {
        self.active_tokens.remove(token_id).is_some()
    }

    /// 撤销设备的所有令牌
    pub fn revoke_device_tokens(&mut self, device_id: &str) -> usize {
        let mut removed_count = 0;
        self.active_tokens.retain(|_, token| {
            if token.device_id == device_id {
                removed_count += 1;
                false
            } else {
                true
            }
        });
        removed_count
    }

    /// 清理过期的令牌
    pub fn cleanup_expired_tokens(&mut self) -> usize {
        let mut removed_count = 0;
        self.active_tokens.retain(|_, token| {
            if token.is_expired() {
                removed_count += 1;
                false
            } else {
                true
            }
        });
        removed_count
    }

    /// 获取活跃令牌数量
    pub fn get_active_token_count(&self) -> usize {
        self.active_tokens.len()
    }

    /// 获取设备令牌数量
    pub fn get_device_token_count(&self, device_id: &str) -> usize {
        self.active_tokens.values()
            .filter(|token| token.device_id == device_id)
            .count()
    }

    /// 获取认证统计信息
    pub fn get_authentication_statistics(&self) -> AuthenticationStatistics {
        let mut device_token_counts = HashMap::new();
        let mut token_type_counts = HashMap::new();
        let mut expired_tokens = 0;

        for token in self.active_tokens.values() {
            // 统计设备令牌数量
            *device_token_counts.entry(token.device_id.clone()).or_insert(0) += 1;
            
            // 统计令牌类型
            let type_name = match token.token_type {
                TokenType::Access => "访问令牌",
                TokenType::Refresh => "刷新令牌",
                TokenType::Device => "设备令牌",
                TokenType::Service => "服务令牌",
            };
            *token_type_counts.entry(type_name.to_string()).or_insert(0) += 1;
            
            // 统计过期令牌
            if token.is_expired() {
                expired_tokens += 1;
            }
        }

        AuthenticationStatistics {
            total_certificates: self.trusted_certificates.len(),
            total_active_tokens: self.active_tokens.len(),
            expired_tokens,
            device_token_counts,
            token_type_counts,
        }
    }
}

/// 认证统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthenticationStatistics {
    /// 总证书数
    pub total_certificates: usize,
    /// 总活跃令牌数
    pub total_active_tokens: usize,
    /// 过期令牌数
    pub expired_tokens: usize,
    /// 设备令牌数量分布
    pub device_token_counts: HashMap<String, usize>,
    /// 令牌类型分布
    pub token_type_counts: HashMap<String, usize>,
}

impl DeviceAuthenticator {
    /// 添加访问控制策略
    pub fn add_access_policy(&mut self, policy: AccessPolicy) -> Result<(), SecurityError> {
        self.access_policies.insert(policy.id.clone(), policy);
        self.log_audit_event(
            AuditEventType::ConfigurationChange,
            "system".to_string(),
            None,
            "access_policy".to_string(),
            "add".to_string(),
            AuditResult::Success,
            HashMap::new(),
        );
        Ok(())
    }

    /// 设备认证
    pub fn authenticate_device(&mut self, device_id: &str, _credentials: &str) -> Result<AuthToken, SecurityError> {
        // 验证设备证书
        if let Some(certificate) = self.trusted_certificates.get(device_id) {
            if certificate.is_valid() {
                // 创建认证令牌
                let token = AuthToken::new(
                    format!("token_{}", device_id),
                    device_id.to_string(),
                    vec![Permission::Read, Permission::Write],
                    TokenType::Device,
                    self.config.token_expiry_hours,
                );
                
                self.active_tokens.insert(token.token_id.clone(), token.clone());
                
                self.log_audit_event(
                    AuditEventType::Authentication,
                    device_id.to_string(),
                    Some(token.token_id.clone()),
                    "device".to_string(),
                    "authenticate".to_string(),
                    AuditResult::Success,
                    HashMap::new(),
                );
                
                return Ok(token);
            }
        }
        
        self.log_audit_event(
            AuditEventType::Authentication,
            device_id.to_string(),
            None,
            "device".to_string(),
            "authenticate".to_string(),
            AuditResult::Failure,
            HashMap::new(),
        );
        
        Err(SecurityError::AuthenticationFailed("设备认证失败".to_string()))
    }

    /// 验证令牌
    pub fn verify_token(&mut self, token_id: &str) -> Result<AuthToken, SecurityError> {
        if let Some(token) = self.active_tokens.get(token_id) {
            if !token.is_expired() {
                return Ok(token.clone());
            } else {
                // 令牌过期，移除
                self.active_tokens.remove(token_id);
            }
        }
        Err(SecurityError::InvalidToken)
    }

    /// 刷新令牌
    pub fn refresh_token(&mut self, refresh_token: &str) -> Result<AuthToken, SecurityError> {
        // 查找对应的令牌
        let mut found_token_id = None;
        let mut token_data = None;
        
        for (token_id, token) in &self.active_tokens {
            if let Some(refresh) = &token.refresh_token {
                if refresh == refresh_token {
                    found_token_id = Some(token_id.clone());
                    token_data = Some(token.clone());
                    break;
                }
            }
        }
        
        if let (Some(token_id), Some(token)) = (found_token_id, token_data) {
            // 创建新令牌
            let new_token = AuthToken::new(
                format!("token_{}", token.device_id),
                token.device_id.clone(),
                token.permissions.clone(),
                token.token_type.clone(),
                self.config.token_expiry_hours,
            );
            
            // 移除旧令牌，添加新令牌
            self.active_tokens.remove(&token_id);
            self.active_tokens.insert(new_token.token_id.clone(), new_token.clone());
            
            Ok(new_token)
        } else {
            Err(SecurityError::InvalidToken)
        }
    }

    /// 移除访问控制策略
    pub fn remove_access_policy(&mut self, policy_id: &str) -> Option<AccessPolicy> {
        let policy = self.access_policies.remove(policy_id);
        if policy.is_some() {
            self.log_audit_event(
                AuditEventType::ConfigurationChange,
                "system".to_string(),
                None,
                "access_policy".to_string(),
                "remove".to_string(),
                AuditResult::Success,
                HashMap::new(),
            );
        }
        policy
    }

    /// 检查访问权限
    pub fn check_access(&self, _device_id: &str, resource: &str, action: &str) -> bool {
        // 简化实现，实际应该根据访问控制策略进行复杂判断
        for policy in self.access_policies.values() {
            if !policy.enabled {
                continue;
            }
            
            for rule in &policy.rules {
                if rule.resource == resource && rule.action == action {
                    match rule.effect {
                        AccessEffect::Allow => return true,
                        AccessEffect::Deny => return false,
                    }
                }
            }
        }
        
        // 默认拒绝
        false
    }

    /// 创建会话
    pub fn create_session(&mut self, device_id: String, user_id: Option<String>, ip_address: Option<String>, user_agent: Option<String>) -> Session {
        let session_id = uuid::Uuid::new_v4().to_string();
        let now = Utc::now();
        let expires_at = now + chrono::Duration::hours(self.config.token_expiry_hours as i64);
        
        let session = Session {
            id: session_id.clone(),
            device_id: device_id.clone(),
            user_id,
            created_at: now,
            last_activity: now,
            expires_at,
            ip_address,
            user_agent,
            is_active: true,
        };
        
        self.active_sessions.insert(session_id, session.clone());
        
        self.log_audit_event(
            AuditEventType::Authentication,
            device_id,
            session.user_id.clone(),
            "session".to_string(),
            "create".to_string(),
            AuditResult::Success,
            HashMap::new(),
        );
        
        session
    }

    /// 更新会话活动
    pub fn update_session_activity(&mut self, session_id: &str) -> Result<(), SecurityError> {
        if let Some(session) = self.active_sessions.get_mut(session_id) {
            session.last_activity = Utc::now();
            Ok(())
        } else {
            Err(SecurityError::SessionError("会话不存在".to_string()))
        }
    }

    /// 终止会话
    pub fn terminate_session(&mut self, session_id: &str) -> Option<Session> {
        if let Some(session) = self.active_sessions.remove(session_id) {
            self.log_audit_event(
                AuditEventType::Authentication,
                session.device_id.clone(),
                session.user_id.clone(),
                "session".to_string(),
                "terminate".to_string(),
                AuditResult::Success,
                HashMap::new(),
            );
            Some(session)
        } else {
            None
        }
    }

    /// 清理过期会话
    pub fn cleanup_expired_sessions(&mut self) -> usize {
        let now = Utc::now();
        let mut removed_count = 0;
        
        self.active_sessions.retain(|_, session| {
            if session.expires_at < now {
                removed_count += 1;
                false
            } else {
                true
            }
        });
        
        removed_count
    }

    /// 启用多因素认证
    pub fn enable_mfa(&mut self, methods: Vec<MFAMethod>) {
        self.mfa_config.enabled = true;
        self.mfa_config.methods = methods;
        
        self.log_audit_event(
            AuditEventType::ConfigurationChange,
            "system".to_string(),
            None,
            "mfa".to_string(),
            "enable".to_string(),
            AuditResult::Success,
            HashMap::new(),
        );
    }

    /// 禁用多因素认证
    pub fn disable_mfa(&mut self) {
        self.mfa_config.enabled = false;
        self.mfa_config.methods.clear();
        
        self.log_audit_event(
            AuditEventType::ConfigurationChange,
            "system".to_string(),
            None,
            "mfa".to_string(),
            "disable".to_string(),
            AuditResult::Success,
            HashMap::new(),
        );
    }

    /// 验证多因素认证
    pub fn verify_mfa(&self, _device_id: &str, method: &MFAMethod, _code: &str) -> bool {
        if !self.mfa_config.enabled {
            return true; // MFA未启用，直接通过
        }
        
        if !self.mfa_config.methods.contains(method) {
            return false; // 方法未启用
        }
        
        // 这里应该实现具体的MFA验证逻辑
        // 简化实现，总是返回true
        true
    }

    /// 记录审计事件
    pub fn log_audit_event(&mut self, event_type: AuditEventType, device_id: String, user_id: Option<String>, resource: String, action: String, result: AuditResult, details: HashMap<String, String>) {
        let log_entry = AuditLogEntry {
            id: uuid::Uuid::new_v4().to_string(),
            timestamp: Utc::now(),
            event_type,
            device_id,
            user_id,
            resource,
            action,
            result,
            details,
            ip_address: None,
            user_agent: None,
        };
        
        self.audit_logs.push(log_entry);
        
        // 限制审计日志大小
        if self.audit_logs.len() > 10000 {
            self.audit_logs.remove(0);
        }
    }

    /// 获取审计日志
    pub fn get_audit_logs(&self, limit: Option<usize>) -> Vec<AuditLogEntry> {
        let logs = &self.audit_logs;
        if let Some(limit) = limit {
            logs.iter().rev().take(limit).cloned().collect()
        } else {
            logs.clone()
        }
    }

    /// 获取安全统计信息
    pub fn get_security_stats(&self) -> SecurityStats {
        let total_auth = self.audit_logs.iter().filter(|log| log.event_type == AuditEventType::Authentication).count() as u64;
        let successful_auth = self.audit_logs.iter().filter(|log| log.event_type == AuditEventType::Authentication && log.result == AuditResult::Success).count() as u64;
        let failed_auth = total_auth - successful_auth;
        let security_events = self.audit_logs.iter().filter(|log| log.event_type == AuditEventType::SecurityEvent).count() as u64;
        let last_security_event = self.audit_logs.iter().filter(|log| log.event_type == AuditEventType::SecurityEvent).last().map(|log| log.timestamp);
        
        SecurityStats {
            total_authentications: total_auth,
            successful_authentications: successful_auth,
            failed_authentications: failed_auth,
            active_sessions: self.active_sessions.len(),
            active_tokens: self.active_tokens.len(),
            security_events,
            last_security_event,
        }
    }

    /// 导出安全配置
    pub fn export_security_config(&self) -> Result<Vec<u8>, SecurityError> {
        let config = serde_json::json!({
            "authentication_config": self.config,
            "access_policies": self.access_policies,
            "mfa_config": self.mfa_config,
        });
        
        serde_json::to_vec(&config)
            .map_err(|e| SecurityError::SerializationError(e.to_string()))
    }

    /// 导入安全配置
    pub fn import_security_config(&mut self, data: &[u8]) -> Result<(), SecurityError> {
        let config: serde_json::Value = serde_json::from_slice(data)
            .map_err(|e| SecurityError::DeserializationError(e.to_string()))?;
        
        if let Some(auth_config) = config.get("authentication_config") {
            self.config = serde_json::from_value(auth_config.clone())
                .map_err(|e| SecurityError::DeserializationError(e.to_string()))?;
        }
        
        if let Some(policies) = config.get("access_policies") {
            self.access_policies = serde_json::from_value(policies.clone())
                .map_err(|e| SecurityError::DeserializationError(e.to_string()))?;
        }
        
        if let Some(mfa_config) = config.get("mfa_config") {
            self.mfa_config = serde_json::from_value(mfa_config.clone())
                .map_err(|e| SecurityError::DeserializationError(e.to_string()))?;
        }
        
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_device_certificate_creation() {
        let certificate = DeviceCertificate::new(
            "device_001".to_string(),
            vec![1, 2, 3, 4],
            "ca_001".to_string(),
            365,
        );

        assert_eq!(certificate.device_id, "device_001");
        assert_eq!(certificate.issuer, "ca_001");
        assert!(!certificate.is_expired());
        assert!(certificate.get_remaining_days() > 0);
    }

    #[test]
    fn test_auth_token_creation() {
        let token = AuthToken::new(
            "token_001".to_string(),
            "device_001".to_string(),
            vec![Permission::Read, Permission::Write],
            TokenType::Access,
            24,
        );

        assert_eq!(token.token_id, "token_001");
        assert_eq!(token.device_id, "device_001");
        assert!(!token.is_expired());
        assert!(token.has_permission(&Permission::Read));
        assert!(token.has_permission(&Permission::Write));
        assert!(!token.has_permission(&Permission::Admin));
    }

    #[test]
    fn test_device_authenticator() {
        let config = AuthenticationConfig::default();
        let mut authenticator = DeviceAuthenticator::new(config);

        let certificate = DeviceCertificate::new(
            "device_001".to_string(),
            vec![1, 2, 3, 4],
            "ca_001".to_string(),
            365,
        );

        assert!(authenticator.add_trusted_certificate(certificate).is_ok());
        assert_eq!(authenticator.trusted_certificates.len(), 1);
    }

    #[test]
    fn test_permission_checking() {
        let token = AuthToken::new(
            "token_001".to_string(),
            "device_001".to_string(),
            vec![Permission::Read, Permission::Write],
            TokenType::Access,
            24,
        );

        assert!(token.has_any_permission(&[Permission::Read, Permission::Admin]));
        assert!(token.has_all_permissions(&[Permission::Read, Permission::Write]));
        assert!(!token.has_all_permissions(&[Permission::Read, Permission::Admin]));
    }
}
