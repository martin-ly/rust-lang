//! 权限管理模块
//! 
//! 提供权限实体和相关的管理功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 权限实体
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Permission {
    pub id: Uuid,
    pub name: String,
    pub description: String,
    pub resource: String,
    pub action: String,
    pub category: String,
    pub is_system: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

impl Permission {
    /// 创建新权限
    pub fn new(name: String, description: String, resource: String, action: String, category: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            description,
            resource,
            action,
            category,
            is_system: false,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建系统权限
    pub fn new_system(name: String, description: String, resource: String, action: String, category: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            description,
            resource,
            action,
            category,
            is_system: true,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 更新权限信息
    pub fn update(&mut self, name: Option<String>, description: Option<String>, category: Option<String>) {
        if let Some(name) = name {
            self.name = name;
        }
        if let Some(description) = description {
            self.description = description;
        }
        if let Some(category) = category {
            self.category = category;
        }
        self.updated_at = Utc::now();
    }

    /// 获取完整权限字符串
    pub fn get_full_permission(&self) -> String {
        format!("{}:{}", self.resource, self.action)
    }

    /// 检查是否可以修改（系统权限不能修改）
    pub fn can_modify(&self) -> bool {
        !self.is_system
    }
}

/// 权限创建请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreatePermissionRequest {
    pub name: String,
    pub description: String,
    pub resource: String,
    pub action: String,
    pub category: String,
}

/// 权限更新请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdatePermissionRequest {
    pub name: Option<String>,
    pub description: Option<String>,
    pub category: Option<String>,
}

/// 权限搜索参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionSearchParams {
    pub query: Option<String>,
    pub resource: Option<String>,
    pub action: Option<String>,
    pub category: Option<String>,
    pub is_system: Option<bool>,
    pub created_after: Option<DateTime<Utc>>,
    pub created_before: Option<DateTime<Utc>>,
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

/// 权限统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionStatistics {
    pub total_permissions: u32,
    pub system_permissions: u32,
    pub custom_permissions: u32,
    pub permissions_by_resource: HashMap<String, u32>,
    pub permissions_by_action: HashMap<String, u32>,
    pub permissions_by_category: HashMap<String, u32>,
}

/// 权限组
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionGroup {
    pub id: Uuid,
    pub name: String,
    pub description: String,
    pub permissions: Vec<String>,
    pub is_system: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

impl PermissionGroup {
    /// 创建新权限组
    pub fn new(name: String, description: String, permissions: Vec<String>) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            description,
            permissions,
            is_system: false,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建系统权限组
    pub fn new_system(name: String, description: String, permissions: Vec<String>) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            description,
            permissions,
            is_system: true,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
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

    /// 检查是否包含特定权限
    pub fn has_permission(&self, permission: &str) -> bool {
        self.permissions.contains(&permission.to_string())
    }
}

/// 预定义权限
pub struct PredefinedPermissions;

impl PredefinedPermissions {
    /// 获取所有预定义权限
    pub fn get_all() -> Vec<Permission> {
        vec![
            // 系统权限
            Permission::new_system(
                "system:read".to_string(),
                "查看系统信息".to_string(),
                "system".to_string(),
                "read".to_string(),
                "system".to_string(),
            ),
            Permission::new_system(
                "system:write".to_string(),
                "修改系统配置".to_string(),
                "system".to_string(),
                "write".to_string(),
                "system".to_string(),
            ),
            Permission::new_system(
                "system:admin".to_string(),
                "系统管理权限".to_string(),
                "system".to_string(),
                "admin".to_string(),
                "system".to_string(),
            ),

            // 用户权限
            Permission::new_system(
                "user:read".to_string(),
                "查看用户信息".to_string(),
                "user".to_string(),
                "read".to_string(),
                "user".to_string(),
            ),
            Permission::new_system(
                "user:write".to_string(),
                "创建和修改用户".to_string(),
                "user".to_string(),
                "write".to_string(),
                "user".to_string(),
            ),
            Permission::new_system(
                "user:delete".to_string(),
                "删除用户".to_string(),
                "user".to_string(),
                "delete".to_string(),
                "user".to_string(),
            ),
            Permission::new_system(
                "user:admin".to_string(),
                "用户管理权限".to_string(),
                "user".to_string(),
                "admin".to_string(),
                "user".to_string(),
            ),

            // 模型权限
            Permission::new_system(
                "model:read".to_string(),
                "查看模型信息".to_string(),
                "model".to_string(),
                "read".to_string(),
                "model".to_string(),
            ),
            Permission::new_system(
                "model:write".to_string(),
                "创建和修改模型".to_string(),
                "model".to_string(),
                "write".to_string(),
                "model".to_string(),
            ),
            Permission::new_system(
                "model:delete".to_string(),
                "删除模型".to_string(),
                "model".to_string(),
                "delete".to_string(),
                "model".to_string(),
            ),
            Permission::new_system(
                "model:use".to_string(),
                "使用模型进行推理".to_string(),
                "model".to_string(),
                "use".to_string(),
                "model".to_string(),
            ),
            Permission::new_system(
                "model:deploy".to_string(),
                "部署模型".to_string(),
                "model".to_string(),
                "deploy".to_string(),
                "model".to_string(),
            ),

            // 训练权限
            Permission::new_system(
                "training:read".to_string(),
                "查看训练任务".to_string(),
                "training".to_string(),
                "read".to_string(),
                "training".to_string(),
            ),
            Permission::new_system(
                "training:write".to_string(),
                "创建和修改训练任务".to_string(),
                "training".to_string(),
                "write".to_string(),
                "training".to_string(),
            ),
            Permission::new_system(
                "training:delete".to_string(),
                "删除训练任务".to_string(),
                "training".to_string(),
                "delete".to_string(),
                "training".to_string(),
            ),
            Permission::new_system(
                "training:start".to_string(),
                "启动训练任务".to_string(),
                "training".to_string(),
                "start".to_string(),
                "training".to_string(),
            ),
            Permission::new_system(
                "training:stop".to_string(),
                "停止训练任务".to_string(),
                "training".to_string(),
                "stop".to_string(),
                "training".to_string(),
            ),

            // 推理权限
            Permission::new_system(
                "inference:read".to_string(),
                "查看推理请求".to_string(),
                "inference".to_string(),
                "read".to_string(),
                "inference".to_string(),
            ),
            Permission::new_system(
                "inference:create".to_string(),
                "创建推理请求".to_string(),
                "inference".to_string(),
                "create".to_string(),
                "inference".to_string(),
            ),
            Permission::new_system(
                "inference:delete".to_string(),
                "删除推理请求".to_string(),
                "inference".to_string(),
                "delete".to_string(),
                "inference".to_string(),
            ),

            // 数据集权限
            Permission::new_system(
                "dataset:read".to_string(),
                "查看数据集".to_string(),
                "dataset".to_string(),
                "read".to_string(),
                "dataset".to_string(),
            ),
            Permission::new_system(
                "dataset:write".to_string(),
                "创建和修改数据集".to_string(),
                "dataset".to_string(),
                "write".to_string(),
                "dataset".to_string(),
            ),
            Permission::new_system(
                "dataset:delete".to_string(),
                "删除数据集".to_string(),
                "dataset".to_string(),
                "delete".to_string(),
                "dataset".to_string(),
            ),
            Permission::new_system(
                "dataset:download".to_string(),
                "下载数据集".to_string(),
                "dataset".to_string(),
                "download".to_string(),
                "dataset".to_string(),
            ),

            // 存储权限
            Permission::new_system(
                "storage:read".to_string(),
                "查看存储内容".to_string(),
                "storage".to_string(),
                "read".to_string(),
                "storage".to_string(),
            ),
            Permission::new_system(
                "storage:write".to_string(),
                "写入存储".to_string(),
                "storage".to_string(),
                "write".to_string(),
                "storage".to_string(),
            ),
            Permission::new_system(
                "storage:delete".to_string(),
                "删除存储内容".to_string(),
                "storage".to_string(),
                "delete".to_string(),
                "storage".to_string(),
            ),

            // 缓存权限
            Permission::new_system(
                "cache:read".to_string(),
                "查看缓存".to_string(),
                "cache".to_string(),
                "read".to_string(),
                "cache".to_string(),
            ),
            Permission::new_system(
                "cache:write".to_string(),
                "写入缓存".to_string(),
                "cache".to_string(),
                "write".to_string(),
                "cache".to_string(),
            ),
            Permission::new_system(
                "cache:delete".to_string(),
                "删除缓存".to_string(),
                "cache".to_string(),
                "delete".to_string(),
                "cache".to_string(),
            ),

            // 消息队列权限
            Permission::new_system(
                "messaging:read".to_string(),
                "查看消息队列".to_string(),
                "messaging".to_string(),
                "read".to_string(),
                "messaging".to_string(),
            ),
            Permission::new_system(
                "messaging:write".to_string(),
                "发送消息".to_string(),
                "messaging".to_string(),
                "write".to_string(),
                "messaging".to_string(),
            ),
            Permission::new_system(
                "messaging:consume".to_string(),
                "消费消息".to_string(),
                "messaging".to_string(),
                "consume".to_string(),
                "messaging".to_string(),
            ),

            // WebSocket权限
            Permission::new_system(
                "websocket:connect".to_string(),
                "连接WebSocket".to_string(),
                "websocket".to_string(),
                "connect".to_string(),
                "websocket".to_string(),
            ),
            Permission::new_system(
                "websocket:send".to_string(),
                "发送WebSocket消息".to_string(),
                "websocket".to_string(),
                "send".to_string(),
                "websocket".to_string(),
            ),
            Permission::new_system(
                "websocket:receive".to_string(),
                "接收WebSocket消息".to_string(),
                "websocket".to_string(),
                "receive".to_string(),
                "websocket".to_string(),
            ),

            // API权限
            Permission::new_system(
                "api:read".to_string(),
                "调用只读API".to_string(),
                "api".to_string(),
                "read".to_string(),
                "api".to_string(),
            ),
            Permission::new_system(
                "api:write".to_string(),
                "调用写入API".to_string(),
                "api".to_string(),
                "write".to_string(),
                "api".to_string(),
            ),
            Permission::new_system(
                "api:admin".to_string(),
                "调用管理API".to_string(),
                "api".to_string(),
                "admin".to_string(),
                "api".to_string(),
            ),

            // 监控权限
            Permission::new_system(
                "monitoring:read".to_string(),
                "查看监控数据".to_string(),
                "monitoring".to_string(),
                "read".to_string(),
                "monitoring".to_string(),
            ),
            Permission::new_system(
                "monitoring:write".to_string(),
                "修改监控配置".to_string(),
                "monitoring".to_string(),
                "write".to_string(),
                "monitoring".to_string(),
            ),

            // 配置权限
            Permission::new_system(
                "config:read".to_string(),
                "查看配置".to_string(),
                "config".to_string(),
                "read".to_string(),
                "config".to_string(),
            ),
            Permission::new_system(
                "config:write".to_string(),
                "修改配置".to_string(),
                "config".to_string(),
                "write".to_string(),
                "config".to_string(),
            ),
        ]
    }

    /// 根据资源获取权限
    pub fn get_by_resource(resource: &str) -> Vec<Permission> {
        Self::get_all()
            .into_iter()
            .filter(|permission| permission.resource == resource)
            .collect()
    }

    /// 根据动作获取权限
    pub fn get_by_action(action: &str) -> Vec<Permission> {
        Self::get_all()
            .into_iter()
            .filter(|permission| permission.action == action)
            .collect()
    }

    /// 根据类别获取权限
    pub fn get_by_category(category: &str) -> Vec<Permission> {
        Self::get_all()
            .into_iter()
            .filter(|permission| permission.category == category)
            .collect()
    }

    /// 根据名称获取权限
    pub fn get_by_name(name: &str) -> Option<Permission> {
        Self::get_all()
            .into_iter()
            .find(|permission| permission.name == name)
    }
}