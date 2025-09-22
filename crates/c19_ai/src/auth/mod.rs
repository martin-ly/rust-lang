//! 认证和授权模块
//! 
//! 提供用户管理、权限控制和身份验证功能

pub mod user;
pub mod role;
pub mod permission;
pub mod session;
pub mod jwt;
pub mod oauth;
pub mod manager;

pub use user::{User, UserInfo, UserActivity, UserPreferences, ActivityType, NotificationSettings, PrivacySettings, ProfileVisibility};
pub use role::{Role, RoleTemplate, RoleHierarchy, RoleInheritance, InheritanceType, PredefinedRoles};
pub use permission::{Permission, PermissionGroup, PredefinedPermissions};
pub use session::*;
pub use jwt::*;
pub use oauth::*;
pub use manager::*;
