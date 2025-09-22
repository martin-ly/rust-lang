//! 用户管理模块
//! 
//! 提供用户实体和相关的管理功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 用户实体
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub username: String,
    pub email: String,
    pub display_name: String,
    pub password_hash: String,
    pub is_active: bool,
    pub is_verified: bool,
    pub is_locked: bool,
    pub failed_login_attempts: u32,
    pub locked_until: Option<DateTime<Utc>>,
    pub roles: Vec<String>,
    pub permissions: Vec<String>,
    pub two_factor_enabled: bool,
    pub two_factor_secret: Option<String>,
    pub last_login: Option<DateTime<Utc>>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub metadata: HashMap<String, String>,
}

impl User {
    /// 创建新用户
    pub fn new(
        username: String,
        email: String,
        display_name: String,
        password_hash: String,
    ) -> Self {
        Self {
            id: Uuid::new_v4(),
            username,
            email,
            display_name,
            password_hash,
            is_active: true,
            is_verified: false,
            is_locked: false,
            failed_login_attempts: 0,
            locked_until: None,
            roles: vec!["user".to_string()],
            permissions: Vec::new(),
            two_factor_enabled: false,
            two_factor_secret: None,
            last_login: None,
            created_at: Utc::now(),
            updated_at: Utc::now(),
            metadata: HashMap::new(),
        }
    }

    /// 更新用户信息
    pub fn update(&mut self, username: Option<String>, email: Option<String>, display_name: Option<String>) {
        if let Some(username) = username {
            self.username = username;
        }
        if let Some(email) = email {
            self.email = email;
        }
        if let Some(display_name) = display_name {
            self.display_name = display_name;
        }
        self.updated_at = Utc::now();
    }

    /// 更改密码
    pub fn change_password(&mut self, new_password_hash: String) {
        self.password_hash = new_password_hash;
        self.updated_at = Utc::now();
    }

    /// 激活用户
    pub fn activate(&mut self) {
        self.is_active = true;
        self.updated_at = Utc::now();
    }

    /// 停用用户
    pub fn deactivate(&mut self) {
        self.is_active = false;
        self.updated_at = Utc::now();
    }

    /// 验证用户邮箱
    pub fn verify(&mut self) {
        self.is_verified = true;
        self.updated_at = Utc::now();
    }

    /// 锁定用户
    pub fn lock(&mut self, until: Option<DateTime<Utc>>) {
        self.is_locked = true;
        self.locked_until = until;
        self.updated_at = Utc::now();
    }

    /// 解锁用户
    pub fn unlock(&mut self) {
        self.is_locked = false;
        self.locked_until = None;
        self.failed_login_attempts = 0;
        self.updated_at = Utc::now();
    }

    /// 增加失败登录次数
    pub fn increment_failed_login(&mut self) {
        self.failed_login_attempts += 1;
        self.updated_at = Utc::now();
    }

    /// 重置失败登录次数
    pub fn reset_failed_login(&mut self) {
        self.failed_login_attempts = 0;
        self.updated_at = Utc::now();
    }

    /// 更新最后登录时间
    pub fn update_last_login(&mut self) {
        self.last_login = Some(Utc::now());
        self.updated_at = Utc::now();
    }

    /// 添加角色
    pub fn add_role(&mut self, role: String) {
        if !self.roles.contains(&role) {
            self.roles.push(role);
            self.updated_at = Utc::now();
        }
    }

    /// 移除角色
    pub fn remove_role(&mut self, role: &str) {
        self.roles.retain(|r| r != role);
        self.updated_at = Utc::now();
    }

    /// 添加权限
    pub fn add_permission(&mut self, permission: String) {
        if !self.permissions.contains(&permission) {
            self.permissions.push(permission);
            self.updated_at = Utc::now();
        }
    }

    /// 移除权限
    pub fn remove_permission(&mut self, permission: &str) {
        self.permissions.retain(|p| p != permission);
        self.updated_at = Utc::now();
    }

    /// 启用双因素认证
    pub fn enable_two_factor(&mut self, secret: String) {
        self.two_factor_enabled = true;
        self.two_factor_secret = Some(secret);
        self.updated_at = Utc::now();
    }

    /// 禁用双因素认证
    pub fn disable_two_factor(&mut self) {
        self.two_factor_enabled = false;
        self.two_factor_secret = None;
        self.updated_at = Utc::now();
    }

    /// 设置元数据
    pub fn set_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
        self.updated_at = Utc::now();
    }

    /// 获取元数据
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }

    /// 移除元数据
    pub fn remove_metadata(&mut self, key: &str) {
        self.metadata.remove(key);
        self.updated_at = Utc::now();
    }

    /// 检查用户是否有特定角色
    pub fn has_role(&self, role: &str) -> bool {
        self.roles.contains(&role.to_string())
    }

    /// 检查用户是否有特定权限
    pub fn has_permission(&self, permission: &str) -> bool {
        self.permissions.contains(&permission.to_string())
    }

    /// 检查用户是否被锁定
    pub fn is_locked_now(&self) -> bool {
        if !self.is_locked {
            return false;
        }

        if let Some(locked_until) = self.locked_until {
            Utc::now() < locked_until
        } else {
            true
        }
    }

    /// 检查用户是否可以登录
    pub fn can_login(&self) -> bool {
        self.is_active && !self.is_locked_now()
    }

    /// 获取用户显示名称
    pub fn get_display_name(&self) -> &str {
        if !self.display_name.is_empty() {
            &self.display_name
        } else {
            &self.username
        }
    }

    /// 转换为用户信息
    pub fn to_user_info(&self) -> UserInfo {
        UserInfo {
            id: self.id.to_string(),
            username: self.username.clone(),
            email: self.email.clone(),
            display_name: self.display_name.clone(),
            roles: self.roles.clone(),
            permissions: self.permissions.clone(),
            is_active: self.is_active,
            last_login: self.last_login,
            created_at: self.created_at,
        }
    }
}

/// 用户信息（用于API响应）
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

/// 用户创建请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateUserRequest {
    pub username: String,
    pub email: String,
    pub display_name: String,
    pub password: String,
    pub roles: Option<Vec<String>>,
    pub metadata: Option<HashMap<String, String>>,
}

/// 用户更新请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdateUserRequest {
    pub username: Option<String>,
    pub email: Option<String>,
    pub display_name: Option<String>,
    pub is_active: Option<bool>,
    pub roles: Option<Vec<String>>,
    pub permissions: Option<Vec<String>>,
    pub metadata: Option<HashMap<String, String>>,
}

/// 用户搜索参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserSearchParams {
    pub query: Option<String>,
    pub roles: Option<Vec<String>>,
    pub is_active: Option<bool>,
    pub is_verified: Option<bool>,
    pub is_locked: Option<bool>,
    pub created_after: Option<DateTime<Utc>>,
    pub created_before: Option<DateTime<Utc>>,
    pub last_login_after: Option<DateTime<Utc>>,
    pub last_login_before: Option<DateTime<Utc>>,
    pub limit: Option<usize>,
    pub offset: Option<usize>,
    pub sort_by: Option<String>,
    pub sort_order: Option<SortOrder>,
}

/// 排序顺序
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SortOrder {
    Asc,
    Desc,
}

/// 用户统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserStatistics {
    pub total_users: u32,
    pub active_users: u32,
    pub inactive_users: u32,
    pub verified_users: u32,
    pub unverified_users: u32,
    pub locked_users: u32,
    pub users_by_role: HashMap<String, u32>,
    pub recent_registrations: u32, // 最近7天注册的用户数
    pub recent_logins: u32, // 最近7天登录的用户数
}

/// 用户活动记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserActivity {
    pub id: Uuid,
    pub user_id: Uuid,
    pub activity_type: ActivityType,
    pub description: String,
    pub ip_address: Option<String>,
    pub user_agent: Option<String>,
    pub metadata: HashMap<String, String>,
    pub created_at: DateTime<Utc>,
}

/// 活动类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ActivityType {
    Login,
    Logout,
    PasswordChange,
    ProfileUpdate,
    RoleChange,
    PermissionChange,
    TwoFactorEnable,
    TwoFactorDisable,
    AccountLock,
    AccountUnlock,
    EmailVerification,
    PasswordReset,
    Other(String),
}

impl UserActivity {
    /// 创建新的用户活动记录
    pub fn new(
        user_id: Uuid,
        activity_type: ActivityType,
        description: String,
        ip_address: Option<String>,
        user_agent: Option<String>,
    ) -> Self {
        Self {
            id: Uuid::new_v4(),
            user_id,
            activity_type,
            description,
            ip_address,
            user_agent,
            metadata: HashMap::new(),
            created_at: Utc::now(),
        }
    }

    /// 添加元数据
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }
}

/// 用户偏好设置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserPreferences {
    pub id: Uuid,
    pub user_id: Uuid,
    pub theme: String,
    pub language: String,
    pub timezone: String,
    pub notifications: NotificationSettings,
    pub privacy: PrivacySettings,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 通知设置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NotificationSettings {
    pub email_notifications: bool,
    pub push_notifications: bool,
    pub sms_notifications: bool,
    pub marketing_emails: bool,
    pub security_alerts: bool,
    pub system_updates: bool,
}

/// 隐私设置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrivacySettings {
    pub profile_visibility: ProfileVisibility,
    pub show_email: bool,
    pub show_last_login: bool,
    pub allow_search: bool,
    pub data_retention_days: Option<u32>,
}

/// 个人资料可见性
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ProfileVisibility {
    Public,
    Private,
    Friends,
    Custom(Vec<String>),
}

impl Default for UserPreferences {
    fn default() -> Self {
        Self {
            id: Uuid::new_v4(),
            user_id: Uuid::new_v4(), // 这应该在实际使用时设置
            theme: "light".to_string(),
            language: "en".to_string(),
            timezone: "UTC".to_string(),
            notifications: NotificationSettings {
                email_notifications: true,
                push_notifications: true,
                sms_notifications: false,
                marketing_emails: false,
                security_alerts: true,
                system_updates: true,
            },
            privacy: PrivacySettings {
                profile_visibility: ProfileVisibility::Private,
                show_email: false,
                show_last_login: false,
                allow_search: true,
                data_retention_days: Some(365),
            },
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }
}