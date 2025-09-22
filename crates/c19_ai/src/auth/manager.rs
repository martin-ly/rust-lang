//! 认证管理器
//! 
//! 提供统一的认证和授权管理功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use uuid::Uuid;
use chrono::{DateTime, Utc};
use std::time::Duration;

use super::user::User;
use super::role::Role;
use super::permission::Permission;
use super::session::Session;
use super::jwt::JwtManager;

/// 认证管理器
#[derive(Debug)]
pub struct AuthManager {
    users: Arc<RwLock<HashMap<String, User>>>,
    roles: Arc<RwLock<HashMap<String, Role>>>,
    permissions: Arc<RwLock<HashMap<String, Permission>>>,
    sessions: Arc<RwLock<HashMap<String, Session>>>,
    jwt_manager: Arc<JwtManager>,
    config: AuthConfig,
}

/// 认证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthConfig {
    pub jwt_secret: String,
    pub jwt_expiry: Duration,
    pub session_timeout: Duration,
    pub max_login_attempts: u32,
    pub lockout_duration: Duration,
    pub password_min_length: usize,
    pub password_require_uppercase: bool,
    pub password_require_lowercase: bool,
    pub password_require_numbers: bool,
    pub password_require_special: bool,
    pub two_factor_enabled: bool,
    pub oauth_enabled: bool,
    pub ldap_enabled: bool,
}

impl Default for AuthConfig {
    fn default() -> Self {
        Self {
            jwt_secret: "your-secret-key".to_string(),
            jwt_expiry: Duration::from_secs(3600), // 1 hour
            session_timeout: Duration::from_secs(1800), // 30 minutes
            max_login_attempts: 5,
            lockout_duration: Duration::from_secs(900), // 15 minutes
            password_min_length: 8,
            password_require_uppercase: true,
            password_require_lowercase: true,
            password_require_numbers: true,
            password_require_special: true,
            two_factor_enabled: false,
            oauth_enabled: false,
            ldap_enabled: false,
        }
    }
}

/// 登录请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoginRequest {
    pub username: String,
    pub password: String,
    pub remember_me: bool,
    pub two_factor_code: Option<String>,
    pub client_info: Option<ClientInfo>,
}

/// 登录响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoginResponse {
    pub success: bool,
    pub token: Option<String>,
    pub refresh_token: Option<String>,
    pub user: Option<UserInfo>,
    pub expires_at: Option<DateTime<Utc>>,
    pub message: String,
    pub requires_two_factor: bool,
}

/// 用户信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserInfo {
    pub id: String,
    pub username: String,
    pub email: String,
    pub display_name: String,
    pub roles: Vec<String>,
    pub permissions: Vec<String>,
    pub is_active: bool,
    pub last_login: Option<DateTime<Utc>>,
    pub created_at: DateTime<Utc>,
}

/// 客户端信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ClientInfo {
    pub ip_address: String,
    pub user_agent: String,
    pub device_type: String,
    pub browser: String,
    pub os: String,
}

impl std::fmt::Display for ClientInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ClientInfo{{ip: {}, ua: {}, device: {}, browser: {}, os: {}}}", 
               self.ip_address, self.user_agent, self.device_type, self.browser, self.os)
    }
}

/// 权限检查请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionCheck {
    pub user_id: String,
    pub resource: String,
    pub action: String,
    pub context: Option<HashMap<String, String>>,
}

/// 权限检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionResult {
    pub allowed: bool,
    pub reason: Option<String>,
    pub required_permissions: Vec<String>,
    pub user_permissions: Vec<String>,
}

/// 用户统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserStats {
    pub total_users: u32,
    pub active_users: u32,
    pub inactive_users: u32,
    pub locked_users: u32,
    pub online_users: u32,
    pub total_sessions: u32,
    pub active_sessions: u32,
}

impl AuthManager {
    /// 创建新的认证管理器
    pub fn new(config: AuthConfig) -> Self {
        let jwt_manager = Arc::new(JwtManager::new(config.jwt_secret.clone()));
        
        Self {
            users: Arc::new(RwLock::new(HashMap::new())),
            roles: Arc::new(RwLock::new(HashMap::new())),
            permissions: Arc::new(RwLock::new(HashMap::new())),
            sessions: Arc::new(RwLock::new(HashMap::new())),
            jwt_manager,
            config,
        }
    }

    /// 用户注册
    pub async fn register_user(&self, username: String, email: String, password: String, display_name: String) -> Result<User> {
        // 验证用户名和邮箱是否已存在
        {
            let users = self.users.read().await;
            if users.values().any(|u| u.username == username) {
                return Err(anyhow::anyhow!("Username already exists"));
            }
            if users.values().any(|u| u.email == email) {
                return Err(anyhow::anyhow!("Email already exists"));
            }
        }

        // 验证密码强度
        self.validate_password(&password)?;

        // 创建新用户
        let user = User {
            id: Uuid::new_v4(),
            username: username.clone(),
            email,
            display_name,
            password_hash: self.hash_password(&password)?,
            is_active: true,
            is_verified: false,
            is_locked: false,
            failed_login_attempts: 0,
            locked_until: None,
            roles: vec!["user".to_string()], // 默认角色
            permissions: Vec::new(),
            two_factor_enabled: false,
            two_factor_secret: None,
            last_login: None,
            created_at: Utc::now(),
            updated_at: Utc::now(),
            metadata: HashMap::new(),
        };

        // 保存用户
        {
            let mut users = self.users.write().await;
            users.insert(user.id.to_string(), user.clone());
        }

        Ok(user)
    }

    /// 用户登录
    pub async fn login(&self, request: LoginRequest) -> Result<LoginResponse> {
        // 获取用户
        let user = self.get_user_by_username(&request.username).await?;

        // 检查用户是否被锁定
        if user.is_locked {
            if let Some(locked_until) = user.locked_until {
                if Utc::now() < locked_until {
                    return Ok(LoginResponse {
                        success: false,
                        token: None,
                        refresh_token: None,
                        user: None,
                        expires_at: None,
                        message: "Account is locked".to_string(),
                        requires_two_factor: false,
                    });
                }
            }
        }

        // 验证密码
        if !self.verify_password(&request.password, &user.password_hash)? {
            self.increment_failed_login(&user.id.to_string()).await?;
            return Ok(LoginResponse {
                success: false,
                token: None,
                refresh_token: None,
                user: None,
                expires_at: None,
                message: "Invalid credentials".to_string(),
                requires_two_factor: false,
            });
        }

        // 检查是否需要双因素认证
        if user.two_factor_enabled && request.two_factor_code.is_none() {
            return Ok(LoginResponse {
                success: false,
                token: None,
                refresh_token: None,
                user: None,
                expires_at: None,
                message: "Two-factor authentication required".to_string(),
                requires_two_factor: true,
            });
        }

        // 验证双因素认证码
        if user.two_factor_enabled {
            if let Some(code) = request.two_factor_code {
                if !self.verify_two_factor_code(&user, &code)? {
                    return Ok(LoginResponse {
                        success: false,
                        token: None,
                        refresh_token: None,
                        user: None,
                        expires_at: None,
                        message: "Invalid two-factor code".to_string(),
                        requires_two_factor: true,
                    });
                }
            }
        }

        // 重置失败登录次数
        self.reset_failed_login(&user.id.to_string()).await?;

        // 生成JWT令牌
        let token = self.jwt_manager.generate_token(&user.id, &user.username, &user.roles)?;
        let refresh_token = self.jwt_manager.generate_refresh_token(&user.id)?;

        // 创建会话
        let session = Session {
            id: Uuid::new_v4(),
            user_id: user.id.clone(),
            token: token.clone(),
            refresh_token: refresh_token.clone(),
            expires_at: Utc::now() + chrono::Duration::from_std(self.config.jwt_expiry).unwrap_or_default(),
            ip_address: None,
            user_agent: None,
            client_info: request.client_info.map(|c| c.to_string()),
            created_at: Utc::now(),
            last_accessed: Utc::now(),
            is_active: true,
        };

        {
            let mut sessions = self.sessions.write().await;
            sessions.insert(session.id.to_string(), session);
        }

        // 更新用户最后登录时间
        self.update_last_login(&user.id.to_string()).await?;

        // 构建用户信息
        let user_info = UserInfo {
            id: user.id.to_string(),
            username: user.username.clone(),
            email: user.email.clone(),
            display_name: user.display_name.clone(),
            roles: user.roles.clone(),
            permissions: user.permissions.clone(),
            is_active: user.is_active,
            last_login: user.last_login,
            created_at: user.created_at,
        };

        Ok(LoginResponse {
            success: true,
            token: Some(token),
            refresh_token: Some(refresh_token),
            user: Some(user_info),
            expires_at: Some(Utc::now() + chrono::Duration::from_std(self.config.jwt_expiry).unwrap_or_default()),
            message: "Login successful".to_string(),
            requires_two_factor: false,
        })
    }

    /// 用户登出
    pub async fn logout(&self, token: &str) -> Result<()> {
        // 查找并删除会话
        {
            let mut sessions = self.sessions.write().await;
            sessions.retain(|_, session| session.token != token);
        }

        Ok(())
    }

    /// 验证令牌
    pub async fn validate_token(&self, token: &str) -> Result<UserInfo> {
        // 验证JWT令牌
        let claims = self.jwt_manager.validate_token(token)?;

        // 检查会话是否存在且有效
        {
            let sessions = self.sessions.read().await;
            if let Some(session) = sessions.values().find(|s| s.token == token) {
                if !session.is_active || session.expires_at < Utc::now() {
                    return Err(anyhow::anyhow!("Session expired"));
                }
            } else {
                return Err(anyhow::anyhow!("Invalid session"));
            }
        }

        // 获取用户信息
        let user = self.get_user(&claims.sub.to_string()).await?;
        
        Ok(UserInfo {
            id: user.id.to_string(),
            username: user.username,
            email: user.email,
            display_name: user.display_name,
            roles: user.roles,
            permissions: user.permissions,
            is_active: user.is_active,
            last_login: user.last_login,
            created_at: user.created_at,
        })
    }

    /// 刷新令牌
    pub async fn refresh_token(&self, refresh_token: &str) -> Result<LoginResponse> {
        // 验证刷新令牌
        let _claims = self.jwt_manager.validate_refresh_token(refresh_token)?;

        // 查找会话
        let session = {
            let sessions = self.sessions.read().await;
            sessions.values()
                .find(|s| s.refresh_token == refresh_token)
                .cloned()
        };

        if let Some(session) = session {
            if !session.is_active || session.expires_at < Utc::now() {
                return Err(anyhow::anyhow!("Session expired"));
            }

            // 获取用户
            let user = self.get_user(&session.user_id.to_string()).await?;

            // 生成新令牌
            let new_token = self.jwt_manager.generate_token(&user.id, &user.username, &user.roles)?;
            let new_refresh_token = self.jwt_manager.generate_refresh_token(&user.id)?;

            // 更新会话
            {
                let mut sessions = self.sessions.write().await;
                if let Some(session) = sessions.get_mut(&session.id.to_string()) {
                    session.token = new_token.clone();
                    session.refresh_token = new_refresh_token.clone();
                    session.expires_at = Utc::now() + chrono::Duration::from_std(self.config.jwt_expiry).unwrap_or_default();
                    session.last_accessed = Utc::now();
                }
            }

            // 构建用户信息
            let user_info = UserInfo {
                id: user.id.to_string(),
                username: user.username,
                email: user.email,
                display_name: user.display_name,
                roles: user.roles,
                permissions: user.permissions,
                is_active: user.is_active,
                last_login: user.last_login,
                created_at: user.created_at,
            };

            Ok(LoginResponse {
                success: true,
                token: Some(new_token),
                refresh_token: Some(new_refresh_token),
                user: Some(user_info),
                expires_at: Some(Utc::now() + chrono::Duration::from_std(self.config.jwt_expiry).unwrap_or_default()),
                message: "Token refreshed successfully".to_string(),
                requires_two_factor: false,
            })
        } else {
            Err(anyhow::anyhow!("Invalid refresh token"))
        }
    }

    /// 检查权限
    pub async fn check_permission(&self, check: PermissionCheck) -> Result<PermissionResult> {
        let user = self.get_user(&check.user_id).await?;
        
        // 获取用户的所有权限
        let user_permissions = self.get_user_permissions(&user).await;
        
        // 检查是否有特定权限
        let required_permission = format!("{}:{}", check.resource, check.action);
        let allowed = user_permissions.contains(&required_permission);

        Ok(PermissionResult {
            allowed,
            reason: if allowed { None } else { Some("Insufficient permissions".to_string()) },
            required_permissions: vec![required_permission],
            user_permissions,
        })
    }

    /// 创建角色
    pub async fn create_role(&self, name: String, description: String, permissions: Vec<String>) -> Result<Role> {
        let role = Role {
            id: Uuid::new_v4(),
            name: name.clone(),
            description,
            permissions,
            is_system: false,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        {
            let mut roles = self.roles.write().await;
            roles.insert(name, role.clone());
        }

        Ok(role)
    }

    /// 创建权限
    pub async fn create_permission(&self, name: String, description: String, resource: String, action: String, category: String) -> Result<Permission> {
        let permission = Permission {
            id: Uuid::new_v4(),
            name: name.clone(),
            description,
            resource,
            action,
            category,
            is_system: false,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };

        {
            let mut permissions = self.permissions.write().await;
            permissions.insert(name, permission.clone());
        }

        Ok(permission)
    }

    /// 分配角色给用户
    pub async fn assign_role(&self, user_id: &str, role_name: &str) -> Result<()> {
        let mut user = self.get_user(user_id).await?;
        
        if !user.roles.contains(&role_name.to_string()) {
            user.roles.push(role_name.to_string());
            user.updated_at = Utc::now();
            
            {
                let mut users = self.users.write().await;
                users.insert(user_id.to_string(), user);
            }
        }

        Ok(())
    }

    /// 移除用户角色
    pub async fn remove_role(&self, user_id: &str, role_name: &str) -> Result<()> {
        let mut user = self.get_user(user_id).await?;
        
        user.roles.retain(|r| r != role_name);
        user.updated_at = Utc::now();
        
        {
            let mut users = self.users.write().await;
            users.insert(user_id.to_string(), user);
        }

        Ok(())
    }

    /// 获取用户
    async fn get_user(&self, user_id: &str) -> Result<User> {
        let users = self.users.read().await;
        users.get(user_id)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("User not found: {}", user_id))
    }

    /// 根据用户名获取用户
    async fn get_user_by_username(&self, username: &str) -> Result<User> {
        let users = self.users.read().await;
        users.values()
            .find(|u| u.username == username)
            .cloned()
            .ok_or_else(|| anyhow::anyhow!("User not found: {}", username))
    }

    /// 获取用户权限
    async fn get_user_permissions(&self, user: &User) -> Vec<String> {
        let mut permissions = user.permissions.clone();
        
        // 从角色获取权限
        let roles = self.roles.read().await;
        for role_name in &user.roles {
            if let Some(role) = roles.get(role_name) {
                permissions.extend(role.permissions.clone());
            }
        }
        
        permissions.sort();
        permissions.dedup();
        permissions
    }

    /// 验证密码强度
    fn validate_password(&self, password: &str) -> Result<()> {
        if password.len() < self.config.password_min_length {
            return Err(anyhow::anyhow!("Password too short"));
        }

        if self.config.password_require_uppercase && !password.chars().any(|c| c.is_uppercase()) {
            return Err(anyhow::anyhow!("Password must contain uppercase letter"));
        }

        if self.config.password_require_lowercase && !password.chars().any(|c| c.is_lowercase()) {
            return Err(anyhow::anyhow!("Password must contain lowercase letter"));
        }

        if self.config.password_require_numbers && !password.chars().any(|c| c.is_numeric()) {
            return Err(anyhow::anyhow!("Password must contain number"));
        }

        if self.config.password_require_special && !password.chars().any(|c| "!@#$%^&*()_+-=[]{}|;:,.<>?".contains(c)) {
            return Err(anyhow::anyhow!("Password must contain special character"));
        }

        Ok(())
    }

    /// 哈希密码
    fn hash_password(&self, password: &str) -> Result<String> {
        use argon2::{Argon2, PasswordHasher};
        use argon2::password_hash::SaltString;
        use argon2::password_hash::rand_core::OsRng;

        let salt = SaltString::generate(&mut OsRng);
        let argon2 = Argon2::default();
        let password_hash = argon2.hash_password(password.as_bytes(), &salt)
            .map_err(|e| anyhow::anyhow!("Password hashing failed: {}", e))?;
        Ok(password_hash.to_string())
    }

    /// 验证密码
    fn verify_password(&self, password: &str, hash: &str) -> Result<bool> {
        use argon2::{Argon2, PasswordVerifier};
        use argon2::password_hash::PasswordHash;

        let parsed_hash = PasswordHash::new(hash)
            .map_err(|e| anyhow::anyhow!("Password hash parsing failed: {}", e))?;
        let argon2 = Argon2::default();
        Ok(argon2.verify_password(password.as_bytes(), &parsed_hash).is_ok())
    }

    /// 增加失败登录次数
    async fn increment_failed_login(&self, user_id: &str) -> Result<()> {
        let mut user = self.get_user(user_id).await?;
        user.failed_login_attempts += 1;

        if user.failed_login_attempts >= self.config.max_login_attempts {
            user.is_locked = true;
            user.locked_until = Some(Utc::now() + chrono::Duration::from_std(self.config.lockout_duration).unwrap_or_default());
        }

        user.updated_at = Utc::now();

        {
            let mut users = self.users.write().await;
            users.insert(user_id.to_string(), user);
        }

        Ok(())
    }

    /// 重置失败登录次数
    async fn reset_failed_login(&self, user_id: &str) -> Result<()> {
        let mut user = self.get_user(user_id).await?;
        user.failed_login_attempts = 0;
        user.is_locked = false;
        user.locked_until = None;
        user.updated_at = Utc::now();

        {
            let mut users = self.users.write().await;
            users.insert(user_id.to_string(), user);
        }

        Ok(())
    }

    /// 更新最后登录时间
    async fn update_last_login(&self, user_id: &str) -> Result<()> {
        let mut user = self.get_user(user_id).await?;
        user.last_login = Some(Utc::now());
        user.updated_at = Utc::now();

        {
            let mut users = self.users.write().await;
            users.insert(user_id.to_string(), user);
        }

        Ok(())
    }

    /// 验证双因素认证码
    fn verify_two_factor_code(&self, _user: &User, _code: &str) -> Result<bool> {
        // TODO: 实现TOTP验证
        Ok(true)
    }

    /// 获取用户统计
    pub async fn get_user_stats(&self) -> UserStats {
        let users = self.users.read().await;
        let sessions = self.sessions.read().await;

        let total_users = users.len() as u32;
        let active_users = users.values().filter(|u| u.is_active).count() as u32;
        let inactive_users = total_users - active_users;
        let locked_users = users.values().filter(|u| u.is_locked).count() as u32;
        let online_users = sessions.values().filter(|s| s.is_active).count() as u32;
        let total_sessions = sessions.len() as u32;
        let active_sessions = sessions.values().filter(|s| s.is_active).count() as u32;

        UserStats {
            total_users,
            active_users,
            inactive_users,
            locked_users,
            online_users,
            total_sessions,
            active_sessions,
        }
    }

    /// 清理过期会话
    pub async fn cleanup_expired_sessions(&self) -> Result<u32> {
        let mut sessions = self.sessions.write().await;
        let initial_count = sessions.len();
        
        sessions.retain(|_, session| {
            session.is_active && session.expires_at > Utc::now()
        });

        Ok((initial_count - sessions.len()) as u32)
    }
}
