//! 角色管理模块
//! 
//! 提供角色实体和相关的管理功能

use serde::{Deserialize, Serialize};
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 角色实体
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Role {
    pub id: Uuid,
    pub name: String,
    pub description: String,
    pub permissions: Vec<String>,
    pub is_system: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

impl Role {
    /// 创建新角色
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

    /// 创建系统角色
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

    /// 更新角色信息
    pub fn update(&mut self, name: Option<String>, description: Option<String>) {
        if let Some(name) = name {
            self.name = name;
        }
        if let Some(description) = description {
            self.description = description;
        }
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

    /// 批量设置权限
    pub fn set_permissions(&mut self, permissions: Vec<String>) {
        self.permissions = permissions;
        self.updated_at = Utc::now();
    }

    /// 检查是否有特定权限
    pub fn has_permission(&self, permission: &str) -> bool {
        self.permissions.contains(&permission.to_string())
    }

    /// 检查是否可以修改（系统角色不能修改）
    pub fn can_modify(&self) -> bool {
        !self.is_system
    }
}

/// 角色创建请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreateRoleRequest {
    pub name: String,
    pub description: String,
    pub permissions: Vec<String>,
}

/// 角色更新请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdateRoleRequest {
    pub name: Option<String>,
    pub description: Option<String>,
    pub permissions: Option<Vec<String>>,
}

/// 角色搜索参数
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoleSearchParams {
    pub query: Option<String>,
    pub is_system: Option<bool>,
    pub has_permission: Option<String>,
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

/// 角色统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoleStatistics {
    pub total_roles: u32,
    pub system_roles: u32,
    pub custom_roles: u32,
    pub roles_with_permissions: u32,
    pub roles_without_permissions: u32,
    pub most_used_permissions: Vec<PermissionUsage>,
}

/// 权限使用统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionUsage {
    pub permission: String,
    pub usage_count: u32,
    pub roles: Vec<String>,
}

/// 角色层次结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoleHierarchy {
    pub id: Uuid,
    pub parent_role: String,
    pub child_role: String,
    pub created_at: DateTime<Utc>,
}

impl RoleHierarchy {
    /// 创建新的角色层次关系
    pub fn new(parent_role: String, child_role: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            parent_role,
            child_role,
            created_at: Utc::now(),
        }
    }
}

/// 角色模板
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoleTemplate {
    pub id: Uuid,
    pub name: String,
    pub description: String,
    pub category: String,
    pub permissions: Vec<String>,
    pub is_predefined: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

impl RoleTemplate {
    /// 创建新角色模板
    pub fn new(name: String, description: String, category: String, permissions: Vec<String>) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            description,
            category,
            permissions,
            is_predefined: false,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 创建预定义角色模板
    pub fn new_predefined(name: String, description: String, category: String, permissions: Vec<String>) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            description,
            category,
            permissions,
            is_predefined: true,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 从模板创建角色
    pub fn create_role_from_template(&self) -> Role {
        Role::new(
            self.name.clone(),
            self.description.clone(),
            self.permissions.clone(),
        )
    }
}

/// 预定义角色模板
pub struct PredefinedRoles;

impl PredefinedRoles {
    /// 获取所有预定义角色模板
    pub fn get_all() -> Vec<RoleTemplate> {
        vec![
            // 管理员角色
            RoleTemplate::new_predefined(
                "admin".to_string(),
                "系统管理员，拥有所有权限".to_string(),
                "system".to_string(),
                vec![
                    "system:*".to_string(),
                    "user:*".to_string(),
                    "model:*".to_string(),
                    "training:*".to_string(),
                    "inference:*".to_string(),
                    "dataset:*".to_string(),
                    "storage:*".to_string(),
                    "cache:*".to_string(),
                    "messaging:*".to_string(),
                    "websocket:*".to_string(),
                    "api:*".to_string(),
                    "monitoring:*".to_string(),
                    "config:*".to_string(),
                ],
            ),
            // 用户角色
            RoleTemplate::new_predefined(
                "user".to_string(),
                "普通用户，拥有基本权限".to_string(),
                "user".to_string(),
                vec![
                    "user:read".to_string(),
                    "user:update".to_string(),
                    "model:read".to_string(),
                    "model:use".to_string(),
                    "inference:create".to_string(),
                    "inference:read".to_string(),
                    "dataset:read".to_string(),
                    "dataset:create".to_string(),
                    "dataset:update".to_string(),
                    "dataset:delete".to_string(),
                ],
            ),
            // 数据科学家角色
            RoleTemplate::new_predefined(
                "data_scientist".to_string(),
                "数据科学家，拥有模型训练和数据分析权限".to_string(),
                "data".to_string(),
                vec![
                    "user:read".to_string(),
                    "user:update".to_string(),
                    "model:*".to_string(),
                    "training:*".to_string(),
                    "inference:*".to_string(),
                    "dataset:*".to_string(),
                    "storage:read".to_string(),
                    "storage:write".to_string(),
                    "cache:read".to_string(),
                    "cache:write".to_string(),
                ],
            ),
            // 模型工程师角色
            RoleTemplate::new_predefined(
                "model_engineer".to_string(),
                "模型工程师，专注于模型开发和部署".to_string(),
                "engineering".to_string(),
                vec![
                    "user:read".to_string(),
                    "model:*".to_string(),
                    "training:read".to_string(),
                    "training:create".to_string(),
                    "training:update".to_string(),
                    "inference:*".to_string(),
                    "dataset:read".to_string(),
                    "dataset:create".to_string(),
                    "storage:read".to_string(),
                    "storage:write".to_string(),
                    "deployment:*".to_string(),
                ],
            ),
            // 运维工程师角色
            RoleTemplate::new_predefined(
                "devops".to_string(),
                "运维工程师，负责系统运维和监控".to_string(),
                "operations".to_string(),
                vec![
                    "system:*".to_string(),
                    "monitoring:*".to_string(),
                    "config:*".to_string(),
                    "storage:*".to_string(),
                    "cache:*".to_string(),
                    "messaging:*".to_string(),
                    "websocket:*".to_string(),
                    "api:*".to_string(),
                    "user:read".to_string(),
                    "model:read".to_string(),
                    "training:read".to_string(),
                    "inference:read".to_string(),
                    "dataset:read".to_string(),
                ],
            ),
            // 只读用户角色
            RoleTemplate::new_predefined(
                "readonly".to_string(),
                "只读用户，只能查看数据".to_string(),
                "readonly".to_string(),
                vec![
                    "user:read".to_string(),
                    "model:read".to_string(),
                    "training:read".to_string(),
                    "inference:read".to_string(),
                    "dataset:read".to_string(),
                    "storage:read".to_string(),
                    "cache:read".to_string(),
                    "monitoring:read".to_string(),
                ],
            ),
            // 访客角色
            RoleTemplate::new_predefined(
                "guest".to_string(),
                "访客用户，拥有最少的权限".to_string(),
                "guest".to_string(),
                vec![
                    "user:read".to_string(),
                    "model:read".to_string(),
                    "inference:create".to_string(),
                ],
            ),
        ]
    }

    /// 根据类别获取角色模板
    pub fn get_by_category(category: &str) -> Vec<RoleTemplate> {
        Self::get_all()
            .into_iter()
            .filter(|template| template.category == category)
            .collect()
    }

    /// 根据名称获取角色模板
    pub fn get_by_name(name: &str) -> Option<RoleTemplate> {
        Self::get_all()
            .into_iter()
            .find(|template| template.name == name)
    }
}

/// 角色权限映射
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RolePermissionMapping {
    pub id: Uuid,
    pub role_name: String,
    pub permission: String,
    pub granted: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

impl RolePermissionMapping {
    /// 创建新的角色权限映射
    pub fn new(role_name: String, permission: String, granted: bool) -> Self {
        Self {
            id: Uuid::new_v4(),
            role_name,
            permission,
            granted,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        }
    }

    /// 更新权限状态
    pub fn update_granted(&mut self, granted: bool) {
        self.granted = granted;
        self.updated_at = Utc::now();
    }
}

/// 角色继承关系
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RoleInheritance {
    pub id: Uuid,
    pub parent_role: String,
    pub child_role: String,
    pub inheritance_type: InheritanceType,
    pub created_at: DateTime<Utc>,
}

/// 继承类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum InheritanceType {
    /// 完全继承：子角色继承父角色的所有权限
    Full,
    /// 部分继承：子角色只继承父角色的部分权限
    Partial,
    /// 排除继承：子角色继承父角色的权限，但排除某些权限
    Exclusion,
}

impl RoleInheritance {
    /// 创建新的角色继承关系
    pub fn new(parent_role: String, child_role: String, inheritance_type: InheritanceType) -> Self {
        Self {
            id: Uuid::new_v4(),
            parent_role,
            child_role,
            inheritance_type,
            created_at: Utc::now(),
        }
    }
}