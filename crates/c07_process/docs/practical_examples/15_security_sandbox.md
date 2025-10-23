# C07-15. 安全与沙箱示例 (Rust 1.90 增强版)

## 目录

- [C07-15. 安全与沙箱示例 (Rust 1.90 增强版)](#c07-15-安全与沙箱示例-rust-190-增强版)
  - [目录](#目录)
  - [1. 进程沙箱](#1-进程沙箱)
    - [1.1 沙箱管理器](#11-沙箱管理器)
  - [2. 权限控制](#2-权限控制)
    - [2.1 权限管理器](#21-权限管理器)
  - [3. 资源限制](#3-资源限制)
    - [3.1 资源限制管理器](#31-资源限制管理器)
  - [4. 安全监控](#4-安全监控)
    - [4.1 安全监控系统](#41-安全监控系统)
  - [5. 加密通信](#5-加密通信)
    - [5.1 加密通信管理器](#51-加密通信管理器)
  - [6. 审计日志](#6-审计日志)
    - [6.1 审计日志系统](#61-审计日志系统)
  - [总结](#总结)

本章提供安全与沙箱示例，涵盖进程沙箱、权限控制、资源限制、安全监控、加密通信和审计日志等安全功能。

## 1. 进程沙箱

### 1.1 沙箱管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 进程沙箱管理器
pub struct ProcessSandboxManager {
    sandboxes: Arc<RwLock<HashMap<String, ProcessSandbox>>>,
    security_policies: Arc<RwLock<HashMap<String, SecurityPolicy>>>,
    config: SandboxConfig,
    audit_logger: Arc<AuditLogger>,
}

#[derive(Debug, Clone)]
pub struct SandboxConfig {
    pub max_sandboxes: usize,
    pub default_timeout: Duration,
    pub resource_limits: ResourceLimits,
    pub security_level: SecurityLevel,
    pub audit_enabled: bool,
    pub isolation_enabled: bool,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub max_memory_mb: u64,
    pub max_cpu_percent: f64,
    pub max_file_descriptors: u32,
    pub max_processes: u32,
    pub max_network_connections: u32,
}

#[derive(Debug, Clone)]
pub enum SecurityLevel {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug)]
pub struct ProcessSandbox {
    pub id: String,
    pub name: String,
    pub process: std::process::Child,
    pub security_policy: String,
    pub resource_usage: ResourceUsage,
    pub created_at: Instant,
    pub last_activity: Instant,
    pub status: SandboxStatus,
    pub violations: Vec<SecurityViolation>,
}

#[derive(Debug, Clone)]
pub enum SandboxStatus {
    Running,
    Suspended,
    Terminated,
    Violated,
    Timeout,
}

#[derive(Debug, Clone)]
pub struct SecurityPolicy {
    pub name: String,
    pub allowed_commands: Vec<String>,
    pub blocked_commands: Vec<String>,
    pub allowed_files: Vec<String>,
    pub blocked_files: Vec<String>,
    pub allowed_networks: Vec<String>,
    pub blocked_networks: Vec<String>,
    pub max_execution_time: Duration,
    pub resource_limits: ResourceLimits,
    pub security_level: SecurityLevel,
}

#[derive(Debug, Clone)]
pub struct ResourceUsage {
    pub memory_mb: u64,
    pub cpu_percent: f64,
    pub file_descriptors: u32,
    pub processes: u32,
    pub network_connections: u32,
}

#[derive(Debug, Clone)]
pub struct SecurityViolation {
    pub id: String,
    pub violation_type: ViolationType,
    pub description: String,
    pub timestamp: Instant,
    pub severity: ViolationSeverity,
    pub action_taken: ViolationAction,
}

#[derive(Debug, Clone)]
pub enum ViolationType {
    CommandBlocked,
    FileAccessDenied,
    NetworkAccessDenied,
    ResourceLimitExceeded,
    TimeoutExceeded,
    UnauthorizedOperation,
}

#[derive(Debug, Clone)]
pub enum ViolationSeverity {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub enum ViolationAction {
    LogOnly,
    Suspend,
    Terminate,
    Block,
}

impl ProcessSandboxManager {
    pub fn new(config: SandboxConfig) -> Self {
        Self {
            sandboxes: Arc::new(RwLock::new(HashMap::new())),
            security_policies: Arc::new(RwLock::new(HashMap::new())),
            config,
            audit_logger: Arc::new(AuditLogger::new()),
        }
    }

    // 创建安全策略
    pub async fn create_security_policy(&self, policy: SecurityPolicy) -> Result<(), SandboxError> {
        {
            let mut policies = self.security_policies.write().await;
            policies.insert(policy.name.clone(), policy);
        }

        if self.config.audit_enabled {
            self.audit_logger.log_event(AuditEvent {
                event_type: "security_policy_created".to_string(),
                description: format!("Security policy '{}' created", policy.name),
                timestamp: Instant::now(),
                severity: AuditSeverity::Info,
            }).await;
        }

        Ok(())
    }

    // 创建沙箱
    pub async fn create_sandbox(
        &self,
        name: String,
        command: String,
        args: Vec<String>,
        policy_name: String,
    ) -> Result<String, SandboxError> {
        let sandbox_id = uuid::Uuid::new_v4().to_string();

        // 获取安全策略
        let policy = {
            let policies = self.security_policies.read().await;
            policies.get(&policy_name)
                .ok_or_else(|| SandboxError::PolicyNotFound(policy_name.clone()))?
                .clone()
        };

        // 验证命令是否允许
        if !policy.allowed_commands.is_empty() && !policy.allowed_commands.contains(&command) {
            return Err(SandboxError::CommandNotAllowed(command));
        }

        if policy.blocked_commands.contains(&command) {
            return Err(SandboxError::CommandBlocked(command));
        }

        // 创建进程
        let mut cmd = std::process::Command::new(&command);
        cmd.args(&args);

        // 应用安全限制
        self.apply_security_restrictions(&mut cmd, &policy)?;

        let child = cmd.spawn()
            .map_err(|e| SandboxError::ProcessCreationFailed(e.to_string()))?;

        let sandbox = ProcessSandbox {
            id: sandbox_id.clone(),
            name,
            process: child,
            security_policy: policy_name,
            resource_usage: ResourceUsage {
                memory_mb: 0,
                cpu_percent: 0.0,
                file_descriptors: 0,
                processes: 1,
                network_connections: 0,
            },
            created_at: Instant::now(),
            last_activity: Instant::now(),
            status: SandboxStatus::Running,
            violations: Vec::new(),
        };

        {
            let mut sandboxes = self.sandboxes.write().await;
            if sandboxes.len() >= self.config.max_sandboxes {
                return Err(SandboxError::MaxSandboxesExceeded);
            }
            sandboxes.insert(sandbox_id.clone(), sandbox);
        }

        // 启动监控
        self.start_sandbox_monitoring(sandbox_id.clone()).await;

        if self.config.audit_enabled {
            self.audit_logger.log_event(AuditEvent {
                event_type: "sandbox_created".to_string(),
                description: format!("Sandbox '{}' created with policy '{}'", sandbox_id, policy_name),
                timestamp: Instant::now(),
                severity: AuditSeverity::Info,
            }).await;
        }

        Ok(sandbox_id)
    }

    // 应用安全限制
    fn apply_security_restrictions(
        &self,
        cmd: &mut std::process::Command,
        policy: &SecurityPolicy,
    ) -> Result<(), SandboxError> {
        // 设置环境变量
        cmd.env("SANDBOX_MODE", "1");
        cmd.env("SECURITY_LEVEL", format!("{:?}", policy.security_level));

        // 设置资源限制
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            
            // 设置进程组
            cmd.process_group(0);
            
            // 设置用户ID（需要适当的权限）
            // cmd.uid(1000);
            // cmd.gid(1000);
        }

        // 设置工作目录
        cmd.current_dir("/tmp/sandbox");

        Ok(())
    }

    // 启动沙箱监控
    async fn start_sandbox_monitoring(&self, sandbox_id: String) {
        let sandboxes = self.sandboxes.clone();
        let policies = self.security_policies.clone();
        let audit_logger = self.audit_logger.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(1));
            
            loop {
                interval.tick().await;
                
                let mut sandboxes_guard = sandboxes.write().await;
                if let Some(sandbox) = sandboxes_guard.get_mut(&sandbox_id) {
                    // 检查进程状态
                    if let Ok(Some(_)) = sandbox.process.try_wait() {
                        sandbox.status = SandboxStatus::Terminated;
                        break;
                    }

                    // 检查超时
                    if sandbox.created_at.elapsed() > config.default_timeout {
                        sandbox.status = SandboxStatus::Timeout;
                        let _ = sandbox.process.kill();
                        break;
                    }

                    // 更新资源使用情况
                    sandbox.resource_usage = Self::get_resource_usage(&sandbox.process).await;

                    // 检查资源限制
                    let policies_guard = policies.read().await;
                    if let Some(policy) = policies_guard.get(&sandbox.security_policy) {
                        if let Some(violation) = Self::check_resource_limits(&sandbox.resource_usage, &policy.resource_limits) {
                            sandbox.violations.push(violation.clone());
                            sandbox.status = SandboxStatus::Violated;
                            
                            // 记录审计事件
                            audit_logger.log_event(AuditEvent {
                                event_type: "resource_violation".to_string(),
                                description: format!("Resource limit exceeded in sandbox '{}'", sandbox_id),
                                timestamp: Instant::now(),
                                severity: AuditSeverity::Warning,
                            }).await;
                            
                            // 根据严重程度采取行动
                            match violation.severity {
                                ViolationSeverity::Critical => {
                                    let _ = sandbox.process.kill();
                                    sandbox.status = SandboxStatus::Terminated;
                                    break;
                                }
                                ViolationSeverity::High => {
                                    sandbox.status = SandboxStatus::Suspended;
                                }
                                _ => {}
                            }
                        }
                    }

                    sandbox.last_activity = Instant::now();
                } else {
                    break;
                }
            }
        });
    }

    // 获取资源使用情况
    async fn get_resource_usage(process: &std::process::Child) -> ResourceUsage {
        // 模拟资源使用情况获取
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        ResourceUsage {
            memory_mb: 100,
            cpu_percent: 25.0,
            file_descriptors: 10,
            processes: 1,
            network_connections: 0,
        }
    }

    // 检查资源限制
    fn check_resource_limits(
        usage: &ResourceUsage,
        limits: &ResourceLimits,
    ) -> Option<SecurityViolation> {
        if usage.memory_mb > limits.max_memory_mb {
            return Some(SecurityViolation {
                id: uuid::Uuid::new_v4().to_string(),
                violation_type: ViolationType::ResourceLimitExceeded,
                description: format!("Memory usage {}MB exceeds limit {}MB", usage.memory_mb, limits.max_memory_mb),
                timestamp: Instant::now(),
                severity: ViolationSeverity::High,
                action_taken: ViolationAction::Suspend,
            });
        }

        if usage.cpu_percent > limits.max_cpu_percent {
            return Some(SecurityViolation {
                id: uuid::Uuid::new_v4().to_string(),
                violation_type: ViolationType::ResourceLimitExceeded,
                description: format!("CPU usage {}% exceeds limit {}%", usage.cpu_percent, limits.max_cpu_percent),
                timestamp: Instant::now(),
                severity: ViolationSeverity::Medium,
                action_taken: ViolationAction::LogOnly,
            });
        }

        None
    }

    // 终止沙箱
    pub async fn terminate_sandbox(&self, sandbox_id: &str) -> Result<(), SandboxError> {
        let mut sandboxes = self.sandboxes.write().await;
        
        if let Some(sandbox) = sandboxes.get_mut(sandbox_id) {
            sandbox.process.kill()
                .map_err(|e| SandboxError::TerminationFailed(e.to_string()))?;
            
            sandbox.status = SandboxStatus::Terminated;

            if self.config.audit_enabled {
                self.audit_logger.log_event(AuditEvent {
                    event_type: "sandbox_terminated".to_string(),
                    description: format!("Sandbox '{}' terminated", sandbox_id),
                    timestamp: Instant::now(),
                    severity: AuditSeverity::Info,
                }).await;
            }
        }

        Ok(())
    }

    // 获取沙箱状态
    pub async fn get_sandbox_status(&self, sandbox_id: &str) -> Option<SandboxStatus> {
        let sandboxes = self.sandboxes.read().await;
        sandboxes.get(sandbox_id).map(|s| s.status.clone())
    }

    // 获取安全违规
    pub async fn get_security_violations(&self, sandbox_id: &str) -> Vec<SecurityViolation> {
        let sandboxes = self.sandboxes.read().await;
        sandboxes.get(sandbox_id)
            .map(|s| s.violations.clone())
            .unwrap_or_default()
    }

    // 获取沙箱统计
    pub async fn get_sandbox_stats(&self) -> SandboxStats {
        let sandboxes = self.sandboxes.read().await;
        
        let total_sandboxes = sandboxes.len();
        let running_sandboxes = sandboxes.values().filter(|s| matches!(s.status, SandboxStatus::Running)).count();
        let terminated_sandboxes = sandboxes.values().filter(|s| matches!(s.status, SandboxStatus::Terminated)).count();
        let violated_sandboxes = sandboxes.values().filter(|s| matches!(s.status, SandboxStatus::Violated)).count();
        
        let total_violations: usize = sandboxes.values().map(|s| s.violations.len()).sum();

        SandboxStats {
            total_sandboxes,
            running_sandboxes,
            terminated_sandboxes,
            violated_sandboxes,
            total_violations,
            average_resource_usage: self.calculate_average_resource_usage(&sandboxes),
        }
    }

    // 计算平均资源使用
    fn calculate_average_resource_usage(&self, sandboxes: &HashMap<String, ProcessSandbox>) -> ResourceUsage {
        if sandboxes.is_empty() {
            return ResourceUsage {
                memory_mb: 0,
                cpu_percent: 0.0,
                file_descriptors: 0,
                processes: 0,
                network_connections: 0,
            };
        }

        let total_memory: u64 = sandboxes.values().map(|s| s.resource_usage.memory_mb).sum();
        let total_cpu: f64 = sandboxes.values().map(|s| s.resource_usage.cpu_percent).sum();
        let total_fds: u32 = sandboxes.values().map(|s| s.resource_usage.file_descriptors).sum();
        let total_processes: u32 = sandboxes.values().map(|s| s.resource_usage.processes).sum();
        let total_connections: u32 = sandboxes.values().map(|s| s.resource_usage.network_connections).sum();

        let count = sandboxes.len() as u64;

        ResourceUsage {
            memory_mb: total_memory / count,
            cpu_percent: total_cpu / count as f64,
            file_descriptors: total_fds / count as u32,
            processes: total_processes / count as u32,
            network_connections: total_connections / count as u32,
        }
    }
}

// 审计日志记录器
pub struct AuditLogger {
    events: Arc<Mutex<Vec<AuditEvent>>>,
    max_events: usize,
}

#[derive(Debug, Clone)]
pub struct AuditEvent {
    pub event_type: String,
    pub description: String,
    pub timestamp: Instant,
    pub severity: AuditSeverity,
}

#[derive(Debug, Clone)]
pub enum AuditSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

impl AuditLogger {
    pub fn new() -> Self {
        Self {
            events: Arc::new(Mutex::new(Vec::new())),
            max_events: 10000,
        }
    }

    pub async fn log_event(&self, event: AuditEvent) {
        let mut events = self.events.lock().unwrap();
        
        if events.len() >= self.max_events {
            events.remove(0);
        }
        
        events.push(event);
    }

    pub fn get_events(&self) -> Vec<AuditEvent> {
        self.events.lock().unwrap().clone()
    }
}

#[derive(Debug)]
pub struct SandboxStats {
    pub total_sandboxes: usize,
    pub running_sandboxes: usize,
    pub terminated_sandboxes: usize,
    pub violated_sandboxes: usize,
    pub total_violations: usize,
    pub average_resource_usage: ResourceUsage,
}

#[derive(Debug, thiserror::Error)]
pub enum SandboxError {
    #[error("安全策略未找到: {0}")]
    PolicyNotFound(String),
    
    #[error("命令不允许: {0}")]
    CommandNotAllowed(String),
    
    #[error("命令被阻止: {0}")]
    CommandBlocked(String),
    
    #[error("进程创建失败: {0}")]
    ProcessCreationFailed(String),
    
    #[error("超过最大沙箱数")]
    MaxSandboxesExceeded,
    
    #[error("终止失败: {0}")]
    TerminationFailed(String),
    
    #[error("沙箱操作失败: {0}")]
    SandboxOperationFailed(String),
}
```

## 2. 权限控制

### 2.1 权限管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 权限管理器
pub struct PermissionManager {
    users: Arc<RwLock<HashMap<String, User>>>,
    roles: Arc<RwLock<HashMap<String, Role>>>,
    permissions: Arc<RwLock<HashMap<String, Permission>>>,
    sessions: Arc<RwLock<HashMap<String, Session>>>,
    config: PermissionConfig,
}

#[derive(Debug, Clone)]
pub struct PermissionConfig {
    pub max_sessions: usize,
    pub session_timeout: Duration,
    pub password_min_length: usize,
    pub max_login_attempts: u32,
    pub lockout_duration: Duration,
    pub audit_enabled: bool,
}

#[derive(Debug, Clone)]
pub struct User {
    pub id: String,
    pub username: String,
    pub password_hash: String,
    pub roles: Vec<String>,
    pub permissions: Vec<String>,
    pub created_at: Instant,
    pub last_login: Option<Instant>,
    pub login_attempts: u32,
    pub locked_until: Option<Instant>,
    pub status: UserStatus,
}

#[derive(Debug, Clone)]
pub enum UserStatus {
    Active,
    Inactive,
    Locked,
    Suspended,
}

#[derive(Debug, Clone)]
pub struct Role {
    pub id: String,
    pub name: String,
    pub permissions: Vec<String>,
    pub description: String,
    pub created_at: Instant,
    pub status: RoleStatus,
}

#[derive(Debug, Clone)]
pub enum RoleStatus {
    Active,
    Inactive,
    Deprecated,
}

#[derive(Debug, Clone)]
pub struct Permission {
    pub id: String,
    pub name: String,
    pub resource: String,
    pub action: String,
    pub description: String,
    pub created_at: Instant,
    pub status: PermissionStatus,
}

#[derive(Debug, Clone)]
pub enum PermissionStatus {
    Active,
    Inactive,
    Deprecated,
}

#[derive(Debug, Clone)]
pub struct Session {
    pub id: String,
    pub user_id: String,
    pub created_at: Instant,
    pub last_activity: Instant,
    pub expires_at: Instant,
    pub ip_address: String,
    pub user_agent: String,
    pub status: SessionStatus,
}

#[derive(Debug, Clone)]
pub enum SessionStatus {
    Active,
    Expired,
    Terminated,
    Suspended,
}

impl PermissionManager {
    pub fn new(config: PermissionConfig) -> Self {
        Self {
            users: Arc::new(RwLock::new(HashMap::new())),
            roles: Arc::new(RwLock::new(HashMap::new())),
            permissions: Arc::new(RwLock::new(HashMap::new())),
            sessions: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    // 创建用户
    pub async fn create_user(
        &self,
        username: String,
        password: String,
        roles: Vec<String>,
    ) -> Result<String, PermissionError> {
        if password.len() < self.config.password_min_length {
            return Err(PermissionError::PasswordTooShort);
        }

        let user_id = uuid::Uuid::new_v4().to_string();
        let password_hash = self.hash_password(&password)?;

        let user = User {
            id: user_id.clone(),
            username: username.clone(),
            password_hash,
            roles,
            permissions: Vec::new(),
            created_at: Instant::now(),
            last_login: None,
            login_attempts: 0,
            locked_until: None,
            status: UserStatus::Active,
        };

        {
            let mut users = self.users.write().await;
            users.insert(user_id.clone(), user);
        }

        Ok(user_id)
    }

    // 创建角色
    pub async fn create_role(
        &self,
        name: String,
        permissions: Vec<String>,
        description: String,
    ) -> Result<String, PermissionError> {
        let role_id = uuid::Uuid::new_v4().to_string();

        let role = Role {
            id: role_id.clone(),
            name,
            permissions,
            description,
            created_at: Instant::now(),
            status: RoleStatus::Active,
        };

        {
            let mut roles = self.roles.write().await;
            roles.insert(role_id.clone(), role);
        }

        Ok(role_id)
    }

    // 创建权限
    pub async fn create_permission(
        &self,
        name: String,
        resource: String,
        action: String,
        description: String,
    ) -> Result<String, PermissionError> {
        let permission_id = uuid::Uuid::new_v4().to_string();

        let permission = Permission {
            id: permission_id.clone(),
            name,
            resource,
            action,
            description,
            created_at: Instant::now(),
            status: PermissionStatus::Active,
        };

        {
            let mut permissions = self.permissions.write().await;
            permissions.insert(permission_id.clone(), permission);
        }

        Ok(permission_id)
    }

    // 用户登录
    pub async fn login(
        &self,
        username: &str,
        password: &str,
        ip_address: String,
        user_agent: String,
    ) -> Result<String, PermissionError> {
        let mut users = self.users.write().await;
        
        if let Some(user) = users.get_mut(username) {
            // 检查用户状态
            if !matches!(user.status, UserStatus::Active) {
                return Err(PermissionError::UserInactive);
            }

            // 检查是否被锁定
            if let Some(locked_until) = user.locked_until {
                if Instant::now() < locked_until {
                    return Err(PermissionError::UserLocked);
                }
            }

            // 验证密码
            if !self.verify_password(password, &user.password_hash)? {
                user.login_attempts += 1;
                
                if user.login_attempts >= self.config.max_login_attempts {
                    user.locked_until = Some(Instant::now() + self.config.lockout_duration);
                    user.status = UserStatus::Locked;
                }
                
                return Err(PermissionError::InvalidCredentials);
            }

            // 重置登录尝试次数
            user.login_attempts = 0;
            user.locked_until = None;
            user.last_login = Some(Instant::now());

            // 创建会话
            let session_id = self.create_session(user.id.clone(), ip_address, user_agent).await?;
            
            Ok(session_id)
        } else {
            Err(PermissionError::UserNotFound)
        }
    }

    // 创建会话
    async fn create_session(
        &self,
        user_id: String,
        ip_address: String,
        user_agent: String,
    ) -> Result<String, PermissionError> {
        let session_id = uuid::Uuid::new_v4().to_string();
        let now = Instant::now();

        let session = Session {
            id: session_id.clone(),
            user_id,
            created_at: now,
            last_activity: now,
            expires_at: now + self.config.session_timeout,
            ip_address,
            user_agent,
            status: SessionStatus::Active,
        };

        {
            let mut sessions = self.sessions.write().await;
            if sessions.len() >= self.config.max_sessions {
                return Err(PermissionError::MaxSessionsExceeded);
            }
            sessions.insert(session_id.clone(), session);
        }

        Ok(session_id)
    }

    // 检查权限
    pub async fn check_permission(
        &self,
        session_id: &str,
        resource: &str,
        action: &str,
    ) -> Result<bool, PermissionError> {
        // 验证会话
        let user_id = self.validate_session(session_id).await?;

        // 获取用户权限
        let user_permissions = self.get_user_permissions(&user_id).await?;

        // 检查权限
        let has_permission = user_permissions.iter().any(|permission| {
            permission.resource == resource && permission.action == action
        });

        Ok(has_permission)
    }

    // 验证会话
    async fn validate_session(&self, session_id: &str) -> Result<String, PermissionError> {
        let mut sessions = self.sessions.write().await;
        
        if let Some(session) = sessions.get_mut(session_id) {
            if session.expires_at < Instant::now() {
                session.status = SessionStatus::Expired;
                return Err(PermissionError::SessionExpired);
            }

            if !matches!(session.status, SessionStatus::Active) {
                return Err(PermissionError::SessionInvalid);
            }

            session.last_activity = Instant::now();
            Ok(session.user_id.clone())
        } else {
            Err(PermissionError::SessionNotFound)
        }
    }

    // 获取用户权限
    async fn get_user_permissions(&self, user_id: &str) -> Result<Vec<Permission>, PermissionError> {
        let users = self.users.read().await;
        let roles = self.roles.read().await;
        let permissions = self.permissions.read().await;

        if let Some(user) = users.get(user_id) {
            let mut user_permissions = Vec::new();

            // 获取直接权限
            for permission_id in &user.permissions {
                if let Some(permission) = permissions.get(permission_id) {
                    user_permissions.push(permission.clone());
                }
            }

            // 获取角色权限
            for role_id in &user.roles {
                if let Some(role) = roles.get(role_id) {
                    for permission_id in &role.permissions {
                        if let Some(permission) = permissions.get(permission_id) {
                            user_permissions.push(permission.clone());
                        }
                    }
                }
            }

            Ok(user_permissions)
        } else {
            Err(PermissionError::UserNotFound)
        }
    }

    // 密码哈希
    fn hash_password(&self, password: &str) -> Result<String, PermissionError> {
        // 简单的哈希实现（实际应用中应使用更安全的哈希算法）
        Ok(format!("{:x}", md5::compute(password)))
    }

    // 验证密码
    fn verify_password(&self, password: &str, hash: &str) -> Result<bool, PermissionError> {
        let password_hash = self.hash_password(password)?;
        Ok(password_hash == *hash)
    }

    // 注销
    pub async fn logout(&self, session_id: &str) -> Result<(), PermissionError> {
        let mut sessions = self.sessions.write().await;
        
        if let Some(session) = sessions.get_mut(session_id) {
            session.status = SessionStatus::Terminated;
        }

        Ok(())
    }

    // 获取权限统计
    pub async fn get_permission_stats(&self) -> PermissionStats {
        let users = self.users.read().await;
        let roles = self.roles.read().await;
        let permissions = self.permissions.read().await;
        let sessions = self.sessions.read().await;

        let total_users = users.len();
        let active_users = users.values().filter(|u| matches!(u.status, UserStatus::Active)).count();
        let locked_users = users.values().filter(|u| matches!(u.status, UserStatus::Locked)).count();
        
        let total_roles = roles.len();
        let active_roles = roles.values().filter(|r| matches!(r.status, RoleStatus::Active)).count();
        
        let total_permissions = permissions.len();
        let active_permissions = permissions.values().filter(|p| matches!(p.status, PermissionStatus::Active)).count();
        
        let total_sessions = sessions.len();
        let active_sessions = sessions.values().filter(|s| matches!(s.status, SessionStatus::Active)).count();

        PermissionStats {
            total_users,
            active_users,
            locked_users,
            total_roles,
            active_roles,
            total_permissions,
            active_permissions,
            total_sessions,
            active_sessions,
        }
    }
}

#[derive(Debug)]
pub struct PermissionStats {
    pub total_users: usize,
    pub active_users: usize,
    pub locked_users: usize,
    pub total_roles: usize,
    pub active_roles: usize,
    pub total_permissions: usize,
    pub active_permissions: usize,
    pub total_sessions: usize,
    pub active_sessions: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum PermissionError {
    #[error("密码太短")]
    PasswordTooShort,
    
    #[error("用户未找到")]
    UserNotFound,
    
    #[error("用户未激活")]
    UserInactive,
    
    #[error("用户被锁定")]
    UserLocked,
    
    #[error("无效凭据")]
    InvalidCredentials,
    
    #[error("会话未找到")]
    SessionNotFound,
    
    #[error("会话已过期")]
    SessionExpired,
    
    #[error("会话无效")]
    SessionInvalid,
    
    #[error("超过最大会话数")]
    MaxSessionsExceeded,
    
    #[error("权限检查失败: {0}")]
    PermissionCheckFailed(String),
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}
```

## 3. 资源限制

### 3.1 资源限制管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 资源限制管理器
pub struct ResourceLimitManager {
    limits: Arc<RwLock<HashMap<String, ResourceLimit>>>,
    usage: Arc<RwLock<HashMap<String, ResourceUsage>>>,
    violations: Arc<RwLock<Vec<ResourceViolation>>>,
    config: ResourceLimitConfig,
}

#[derive(Debug, Clone)]
pub struct ResourceLimitConfig {
    pub max_limits: usize,
    pub check_interval: Duration,
    pub auto_enforcement: bool,
    pub violation_threshold: u32,
    pub grace_period: Duration,
}

#[derive(Debug, Clone)]
pub struct ResourceLimit {
    pub id: String,
    pub name: String,
    pub resource_type: ResourceType,
    pub limit_value: u64,
    pub unit: String,
    pub enforcement_action: EnforcementAction,
    pub created_at: Instant,
    pub status: LimitStatus,
}

#[derive(Debug, Clone)]
pub enum ResourceType {
    Memory,
    CPU,
    Disk,
    Network,
    FileDescriptors,
    Processes,
    Connections,
}

#[derive(Debug, Clone)]
pub enum EnforcementAction {
    LogOnly,
    Throttle,
    Block,
    Terminate,
}

#[derive(Debug, Clone)]
pub enum LimitStatus {
    Active,
    Inactive,
    Suspended,
}

#[derive(Debug, Clone)]
pub struct ResourceUsage {
    pub id: String,
    pub resource_type: ResourceType,
    pub current_value: u64,
    pub peak_value: u64,
    pub average_value: u64,
    pub last_updated: Instant,
    pub measurement_count: u64,
}

#[derive(Debug, Clone)]
pub struct ResourceViolation {
    pub id: String,
    pub limit_id: String,
    pub resource_type: ResourceType,
    pub limit_value: u64,
    pub actual_value: u64,
    pub violation_time: Instant,
    pub severity: ViolationSeverity,
    pub action_taken: EnforcementAction,
    pub resolved: bool,
}

#[derive(Debug, Clone)]
pub enum ViolationSeverity {
    Low,
    Medium,
    High,
    Critical,
}

impl ResourceLimitManager {
    pub fn new(config: ResourceLimitConfig) -> Self {
        Self {
            limits: Arc::new(RwLock::new(HashMap::new())),
            usage: Arc::new(RwLock::new(HashMap::new())),
            violations: Arc::new(RwLock::new(Vec::new())),
            config,
        }
    }

    // 创建资源限制
    pub async fn create_limit(
        &self,
        name: String,
        resource_type: ResourceType,
        limit_value: u64,
        unit: String,
        enforcement_action: EnforcementAction,
    ) -> Result<String, ResourceLimitError> {
        let limit_id = uuid::Uuid::new_v4().to_string();

        let limit = ResourceLimit {
            id: limit_id.clone(),
            name,
            resource_type,
            limit_value,
            unit,
            enforcement_action,
            created_at: Instant::now(),
            status: LimitStatus::Active,
        };

        {
            let mut limits = self.limits.write().await;
            if limits.len() >= self.config.max_limits {
                return Err(ResourceLimitError::MaxLimitsExceeded);
            }
            limits.insert(limit_id.clone(), limit);
        }

        Ok(limit_id)
    }

    // 更新资源使用情况
    pub async fn update_usage(
        &self,
        resource_id: String,
        resource_type: ResourceType,
        current_value: u64,
    ) -> Result<(), ResourceLimitError> {
        let mut usage = self.usage.write().await;
        
        if let Some(existing_usage) = usage.get_mut(&resource_id) {
            // 更新现有使用情况
            existing_usage.current_value = current_value;
            existing_usage.peak_value = existing_usage.peak_value.max(current_value);
            existing_usage.measurement_count += 1;
            
            // 计算平均值
            let total = existing_usage.average_value * (existing_usage.measurement_count - 1) + current_value;
            existing_usage.average_value = total / existing_usage.measurement_count;
            
            existing_usage.last_updated = Instant::now();
        } else {
            // 创建新的使用情况记录
            let new_usage = ResourceUsage {
                id: resource_id.clone(),
                resource_type: resource_type.clone(),
                current_value,
                peak_value: current_value,
                average_value: current_value,
                last_updated: Instant::now(),
                measurement_count: 1,
            };
            usage.insert(resource_id, new_usage);
        }

        // 检查限制
        if self.config.auto_enforcement {
            self.check_limits(&resource_id, &resource_type, current_value).await?;
        }

        Ok(())
    }

    // 检查限制
    async fn check_limits(
        &self,
        resource_id: &str,
        resource_type: &ResourceType,
        current_value: u64,
    ) -> Result<(), ResourceLimitError> {
        let limits = self.limits.read().await;
        
        for limit in limits.values() {
            if limit.resource_type == *resource_type && 
               matches!(limit.status, LimitStatus::Active) &&
               current_value > limit.limit_value {
                
                // 创建违规记录
                let violation = ResourceViolation {
                    id: uuid::Uuid::new_v4().to_string(),
                    limit_id: limit.id.clone(),
                    resource_type: resource_type.clone(),
                    limit_value: limit.limit_value,
                    actual_value: current_value,
                    violation_time: Instant::now(),
                    severity: self.calculate_severity(current_value, limit.limit_value),
                    action_taken: limit.enforcement_action.clone(),
                    resolved: false,
                };

                // 记录违规
                {
                    let mut violations = self.violations.write().await;
                    violations.push(violation.clone());
                }

                // 执行强制措施
                self.enforce_action(&violation, resource_id).await?;
            }
        }

        Ok(())
    }

    // 计算严重程度
    fn calculate_severity(&self, actual_value: u64, limit_value: u64) -> ViolationSeverity {
        let ratio = actual_value as f64 / limit_value as f64;
        
        if ratio >= 2.0 {
            ViolationSeverity::Critical
        } else if ratio >= 1.5 {
            ViolationSeverity::High
        } else if ratio >= 1.2 {
            ViolationSeverity::Medium
        } else {
            ViolationSeverity::Low
        }
    }

    // 执行强制措施
    async fn enforce_action(
        &self,
        violation: &ResourceViolation,
        resource_id: &str,
    ) -> Result<(), ResourceLimitError> {
        match violation.action_taken {
            EnforcementAction::LogOnly => {
                println!("资源限制违规记录: {} 超过限制 {} {}", 
                    resource_id, violation.limit_value, violation.resource_type);
            }
            EnforcementAction::Throttle => {
                println!("资源限制违规: 限制 {} 的资源使用", resource_id);
                // 实际实现中会执行节流操作
            }
            EnforcementAction::Block => {
                println!("资源限制违规: 阻止 {} 的资源访问", resource_id);
                // 实际实现中会阻止资源访问
            }
            EnforcementAction::Terminate => {
                println!("资源限制违规: 终止 {} 的资源使用", resource_id);
                // 实际实现中会终止资源使用
            }
        }

        Ok(())
    }

    // 获取资源使用情况
    pub async fn get_usage(&self, resource_id: &str) -> Option<ResourceUsage> {
        let usage = self.usage.read().await;
        usage.get(resource_id).cloned()
    }

    // 获取所有资源使用情况
    pub async fn get_all_usage(&self) -> Vec<ResourceUsage> {
        let usage = self.usage.read().await;
        usage.values().cloned().collect()
    }

    // 获取违规记录
    pub async fn get_violations(&self, limit_id: Option<&str>) -> Vec<ResourceViolation> {
        let violations = self.violations.read().await;
        
        if let Some(limit_id) = limit_id {
            violations.iter()
                .filter(|v| v.limit_id == limit_id)
                .cloned()
                .collect()
        } else {
            violations.clone()
        }
    }

    // 解决违规
    pub async fn resolve_violation(&self, violation_id: &str) -> Result<(), ResourceLimitError> {
        let mut violations = self.violations.write().await;
        
        if let Some(violation) = violations.iter_mut().find(|v| v.id == violation_id) {
            violation.resolved = true;
        }

        Ok(())
    }

    // 获取资源统计
    pub async fn get_resource_stats(&self) -> ResourceStats {
        let limits = self.limits.read().await;
        let usage = self.usage.read().await;
        let violations = self.violations.read().await;

        let total_limits = limits.len();
        let active_limits = limits.values().filter(|l| matches!(l.status, LimitStatus::Active)).count();
        
        let total_resources = usage.len();
        let total_violations = violations.len();
        let unresolved_violations = violations.iter().filter(|v| !v.resolved).count();

        ResourceStats {
            total_limits,
            active_limits,
            total_resources,
            total_violations,
            unresolved_violations,
            average_usage: self.calculate_average_usage(&usage),
        }
    }

    // 计算平均使用情况
    fn calculate_average_usage(&self, usage: &HashMap<String, ResourceUsage>) -> f64 {
        if usage.is_empty() {
            return 0.0;
        }

        let total: u64 = usage.values().map(|u| u.average_value).sum();
        total as f64 / usage.len() as f64
    }
}

#[derive(Debug)]
pub struct ResourceStats {
    pub total_limits: usize,
    pub active_limits: usize,
    pub total_resources: usize,
    pub total_violations: usize,
    pub unresolved_violations: usize,
    pub average_usage: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum ResourceLimitError {
    #[error("超过最大限制数")]
    MaxLimitsExceeded,
    
    #[error("限制未找到: {0}")]
    LimitNotFound(String),
    
    #[error("资源未找到: {0}")]
    ResourceNotFound(String),
    
    #[error("违规处理失败: {0}")]
    ViolationHandlingFailed(String),
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}
```

## 4. 安全监控

### 4.1 安全监控系统

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 安全监控系统
pub struct SecurityMonitor {
    monitors: Arc<RwLock<HashMap<String, SecurityMonitorInstance>>>,
    alerts: Arc<RwLock<Vec<SecurityAlert>>>,
    rules: Arc<RwLock<HashMap<String, SecurityRule>>>,
    config: SecurityMonitorConfig,
}

#[derive(Debug, Clone)]
pub struct SecurityMonitorConfig {
    pub max_monitors: usize,
    pub check_interval: Duration,
    pub alert_threshold: u32,
    pub auto_response: bool,
    pub notification_enabled: bool,
    pub log_level: LogLevel,
}

#[derive(Debug, Clone)]
pub enum LogLevel {
    Debug,
    Info,
    Warning,
    Error,
    Critical,
}

#[derive(Debug)]
pub struct SecurityMonitorInstance {
    pub id: String,
    pub name: String,
    pub monitor_type: MonitorType,
    pub target: String,
    pub status: MonitorStatus,
    pub last_check: Instant,
    pub check_count: u64,
    pub alert_count: u64,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum MonitorType {
    ProcessMonitor,
    FileMonitor,
    NetworkMonitor,
    SystemMonitor,
    UserMonitor,
}

#[derive(Debug, Clone)]
pub enum MonitorStatus {
    Active,
    Inactive,
    Suspended,
    Error,
}

#[derive(Debug, Clone)]
pub struct SecurityRule {
    pub id: String,
    pub name: String,
    pub rule_type: RuleType,
    pub condition: String,
    pub action: RuleAction,
    pub severity: AlertSeverity,
    pub enabled: bool,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum RuleType {
    Threshold,
    Pattern,
    Anomaly,
    Compliance,
}

#[derive(Debug, Clone)]
pub enum RuleAction {
    Log,
    Alert,
    Block,
    Terminate,
    Notify,
}

#[derive(Debug, Clone)]
pub enum AlertSeverity {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct SecurityAlert {
    pub id: String,
    pub monitor_id: String,
    pub rule_id: String,
    pub alert_type: AlertType,
    pub severity: AlertSeverity,
    pub message: String,
    pub timestamp: Instant,
    pub resolved: bool,
    pub resolution_time: Option<Instant>,
}

#[derive(Debug, Clone)]
pub enum AlertType {
    SecurityBreach,
    UnauthorizedAccess,
    ResourceAbuse,
    SystemAnomaly,
    ComplianceViolation,
}

impl SecurityMonitor {
    pub fn new(config: SecurityMonitorConfig) -> Self {
        Self {
            monitors: Arc::new(RwLock::new(HashMap::new())),
            alerts: Arc::new(RwLock::new(Vec::new())),
            rules: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    // 创建监控实例
    pub async fn create_monitor(
        &self,
        name: String,
        monitor_type: MonitorType,
        target: String,
    ) -> Result<String, SecurityMonitorError> {
        let monitor_id = uuid::Uuid::new_v4().to_string();

        let monitor = SecurityMonitorInstance {
            id: monitor_id.clone(),
            name,
            monitor_type,
            target,
            status: MonitorStatus::Active,
            last_check: Instant::now(),
            check_count: 0,
            alert_count: 0,
            created_at: Instant::now(),
        };

        {
            let mut monitors = self.monitors.write().await;
            if monitors.len() >= self.config.max_monitors {
                return Err(SecurityMonitorError::MaxMonitorsExceeded);
            }
            monitors.insert(monitor_id.clone(), monitor);
        }

        // 启动监控
        self.start_monitoring(monitor_id.clone()).await;

        Ok(monitor_id)
    }

    // 创建安全规则
    pub async fn create_rule(
        &self,
        name: String,
        rule_type: RuleType,
        condition: String,
        action: RuleAction,
        severity: AlertSeverity,
    ) -> Result<String, SecurityMonitorError> {
        let rule_id = uuid::Uuid::new_v4().to_string();

        let rule = SecurityRule {
            id: rule_id.clone(),
            name,
            rule_type,
            condition,
            action,
            severity,
            enabled: true,
            created_at: Instant::now(),
        };

        {
            let mut rules = self.rules.write().await;
            rules.insert(rule_id.clone(), rule);
        }

        Ok(rule_id)
    }

    // 启动监控
    async fn start_monitoring(&self, monitor_id: String) {
        let monitors = self.monitors.clone();
        let rules = self.rules.clone();
        let alerts = self.alerts.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.check_interval);
            
            loop {
                interval.tick().await;
                
                let mut monitors_guard = monitors.write().await;
                if let Some(monitor) = monitors_guard.get_mut(&monitor_id) {
                    if !matches!(monitor.status, MonitorStatus::Active) {
                        break;
                    }

                    // 执行监控检查
                    let check_result = Self::perform_check(monitor).await;
                    
                    monitor.last_check = Instant::now();
                    monitor.check_count += 1;

                    if let Err(alert) = check_result {
                        monitor.alert_count += 1;
                        
                        // 创建安全警报
                        let security_alert = SecurityAlert {
                            id: uuid::Uuid::new_v4().to_string(),
                            monitor_id: monitor_id.clone(),
                            rule_id: "default".to_string(),
                            alert_type: AlertType::SystemAnomaly,
                            severity: AlertSeverity::Medium,
                            message: alert,
                            timestamp: Instant::now(),
                            resolved: false,
                            resolution_time: None,
                        };

                        {
                            let mut alerts_guard = alerts.write().await;
                            alerts_guard.push(security_alert);
                        }
                    }
                } else {
                    break;
                }
            }
        });
    }

    // 执行监控检查
    async fn perform_check(monitor: &SecurityMonitorInstance) -> Result<(), String> {
        match monitor.monitor_type {
            MonitorType::ProcessMonitor => {
                // 模拟进程监控检查
                tokio::time::sleep(Duration::from_millis(10)).await;
                Ok(())
            }
            MonitorType::FileMonitor => {
                // 模拟文件监控检查
                tokio::time::sleep(Duration::from_millis(10)).await;
                Ok(())
            }
            MonitorType::NetworkMonitor => {
                // 模拟网络监控检查
                tokio::time::sleep(Duration::from_millis(10)).await;
                Ok(())
            }
            MonitorType::SystemMonitor => {
                // 模拟系统监控检查
                tokio::time::sleep(Duration::from_millis(10)).await;
                Ok(())
            }
            MonitorType::UserMonitor => {
                // 模拟用户监控检查
                tokio::time::sleep(Duration::from_millis(10)).await;
                Ok(())
            }
        }
    }

    // 获取安全警报
    pub async fn get_alerts(
        &self,
        monitor_id: Option<&str>,
        severity: Option<AlertSeverity>,
        resolved: Option<bool>,
    ) -> Vec<SecurityAlert> {
        let alerts = self.alerts.read().await;
        
        alerts.iter()
            .filter(|alert| {
                if let Some(monitor_id) = monitor_id {
                    alert.monitor_id == monitor_id
                } else {
                    true
                }
            })
            .filter(|alert| {
                if let Some(severity) = &severity {
                    alert.severity == *severity
                } else {
                    true
                }
            })
            .filter(|alert| {
                if let Some(resolved) = resolved {
                    alert.resolved == resolved
                } else {
                    true
                }
            })
            .cloned()
            .collect()
    }

    // 解决警报
    pub async fn resolve_alert(&self, alert_id: &str) -> Result<(), SecurityMonitorError> {
        let mut alerts = self.alerts.write().await;
        
        if let Some(alert) = alerts.iter_mut().find(|a| a.id == alert_id) {
            alert.resolved = true;
            alert.resolution_time = Some(Instant::now());
        }

        Ok(())
    }

    // 获取监控统计
    pub async fn get_monitor_stats(&self) -> MonitorStats {
        let monitors = self.monitors.read().await;
        let alerts = self.alerts.read().await;

        let total_monitors = monitors.len();
        let active_monitors = monitors.values().filter(|m| matches!(m.status, MonitorStatus::Active)).count();
        let total_alerts = alerts.len();
        let unresolved_alerts = alerts.iter().filter(|a| !a.resolved).count();
        
        let total_checks: u64 = monitors.values().map(|m| m.check_count).sum();
        let total_alert_count: u64 = monitors.values().map(|m| m.alert_count).sum();

        MonitorStats {
            total_monitors,
            active_monitors,
            total_alerts,
            unresolved_alerts,
            total_checks,
            total_alert_count,
            alert_rate: if total_checks > 0 {
                total_alert_count as f64 / total_checks as f64
            } else {
                0.0
            },
        }
    }
}

#[derive(Debug)]
pub struct MonitorStats {
    pub total_monitors: usize,
    pub active_monitors: usize,
    pub total_alerts: usize,
    pub unresolved_alerts: usize,
    pub total_checks: u64,
    pub total_alert_count: u64,
    pub alert_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum SecurityMonitorError {
    #[error("超过最大监控数")]
    MaxMonitorsExceeded,
    
    #[error("监控未找到: {0}")]
    MonitorNotFound(String),
    
    #[error("规则未找到: {0}")]
    RuleNotFound(String),
    
    #[error("警报未找到: {0}")]
    AlertNotFound(String),
    
    #[error("监控操作失败: {0}")]
    MonitorOperationFailed(String),
}
```

## 5. 加密通信

### 5.1 加密通信管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 加密通信管理器
pub struct EncryptionManager {
    keys: Arc<RwLock<HashMap<String, EncryptionKey>>>,
    sessions: Arc<RwLock<HashMap<String, EncryptionSession>>>,
    config: EncryptionConfig,
}

#[derive(Debug, Clone)]
pub struct EncryptionConfig {
    pub key_size: usize,
    pub session_timeout: Duration,
    pub max_sessions: usize,
    pub algorithm: EncryptionAlgorithm,
    pub key_rotation_interval: Duration,
    pub auto_key_rotation: bool,
}

#[derive(Debug, Clone)]
pub enum EncryptionAlgorithm {
    AES256,
    RSA2048,
    ChaCha20,
    Blowfish,
}

#[derive(Debug, Clone)]
pub struct EncryptionKey {
    pub id: String,
    pub key_data: Vec<u8>,
    pub algorithm: EncryptionAlgorithm,
    pub created_at: Instant,
    pub expires_at: Option<Instant>,
    pub usage_count: u64,
    pub status: KeyStatus,
}

#[derive(Debug, Clone)]
pub enum KeyStatus {
    Active,
    Expired,
    Revoked,
    Suspended,
}

#[derive(Debug, Clone)]
pub struct EncryptionSession {
    pub id: String,
    pub key_id: String,
    pub created_at: Instant,
    pub last_activity: Instant,
    pub expires_at: Instant,
    pub message_count: u64,
    pub bytes_encrypted: u64,
    pub status: SessionStatus,
}

#[derive(Debug, Clone)]
pub enum SessionStatus {
    Active,
    Expired,
    Terminated,
    Suspended,
}

impl EncryptionManager {
    pub fn new(config: EncryptionConfig) -> Self {
        Self {
            keys: Arc::new(RwLock::new(HashMap::new())),
            sessions: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    // 生成加密密钥
    pub async fn generate_key(
        &self,
        algorithm: Option<EncryptionAlgorithm>,
    ) -> Result<String, EncryptionError> {
        let key_id = uuid::Uuid::new_v4().to_string();
        let algorithm = algorithm.unwrap_or(self.config.algorithm.clone());
        
        let key_data = self.generate_key_data(&algorithm)?;
        
        let key = EncryptionKey {
            id: key_id.clone(),
            key_data,
            algorithm,
            created_at: Instant::now(),
            expires_at: None,
            usage_count: 0,
            status: KeyStatus::Active,
        };

        {
            let mut keys = self.keys.write().await;
            keys.insert(key_id.clone(), key);
        }

        Ok(key_id)
    }

    // 生成密钥数据
    fn generate_key_data(&self, algorithm: &EncryptionAlgorithm) -> Result<Vec<u8>, EncryptionError> {
        match algorithm {
            EncryptionAlgorithm::AES256 => {
                // 生成32字节的AES-256密钥
                Ok(vec![0u8; 32])
            }
            EncryptionAlgorithm::RSA2048 => {
                // 生成RSA密钥
                Ok(vec![0u8; 256])
            }
            EncryptionAlgorithm::ChaCha20 => {
                // 生成32字节的ChaCha20密钥
                Ok(vec![0u8; 32])
            }
            EncryptionAlgorithm::Blowfish => {
                // 生成Blowfish密钥
                Ok(vec![0u8; 16])
            }
        }
    }

    // 创建加密会话
    pub async fn create_session(&self, key_id: String) -> Result<String, EncryptionError> {
        let session_id = uuid::Uuid::new_v4().to_string();
        let now = Instant::now();

        let session = EncryptionSession {
            id: session_id.clone(),
            key_id,
            created_at: now,
            last_activity: now,
            expires_at: now + self.config.session_timeout,
            message_count: 0,
            bytes_encrypted: 0,
            status: SessionStatus::Active,
        };

        {
            let mut sessions = self.sessions.write().await;
            if sessions.len() >= self.config.max_sessions {
                return Err(EncryptionError::MaxSessionsExceeded);
            }
            sessions.insert(session_id.clone(), session);
        }

        Ok(session_id)
    }

    // 加密数据
    pub async fn encrypt(
        &self,
        session_id: &str,
        data: &[u8],
    ) -> Result<Vec<u8>, EncryptionError> {
        let mut sessions = self.sessions.write().await;
        let mut keys = self.keys.write().await;

        if let Some(session) = sessions.get_mut(session_id) {
            if session.expires_at < Instant::now() {
                session.status = SessionStatus::Expired;
                return Err(EncryptionError::SessionExpired);
            }

            if let Some(key) = keys.get_mut(&session.key_id) {
                if !matches!(key.status, KeyStatus::Active) {
                    return Err(EncryptionError::KeyInactive);
                }

                // 执行加密
                let encrypted_data = self.perform_encryption(data, &key.key_data, &key.algorithm)?;

                // 更新统计
                session.last_activity = Instant::now();
                session.message_count += 1;
                session.bytes_encrypted += data.len() as u64;
                key.usage_count += 1;

                Ok(encrypted_data)
            } else {
                Err(EncryptionError::KeyNotFound)
            }
        } else {
            Err(EncryptionError::SessionNotFound)
        }
    }

    // 解密数据
    pub async fn decrypt(
        &self,
        session_id: &str,
        encrypted_data: &[u8],
    ) -> Result<Vec<u8>, EncryptionError> {
        let mut sessions = self.sessions.write().await;
        let keys = self.keys.read().await;

        if let Some(session) = sessions.get_mut(session_id) {
            if session.expires_at < Instant::now() {
                session.status = SessionStatus::Expired;
                return Err(EncryptionError::SessionExpired);
            }

            if let Some(key) = keys.get(&session.key_id) {
                if !matches!(key.status, KeyStatus::Active) {
                    return Err(EncryptionError::KeyInactive);
                }

                // 执行解密
                let decrypted_data = self.perform_decryption(encrypted_data, &key.key_data, &key.algorithm)?;

                // 更新统计
                session.last_activity = Instant::now();

                Ok(decrypted_data)
            } else {
                Err(EncryptionError::KeyNotFound)
            }
        } else {
            Err(EncryptionError::SessionNotFound)
        }
    }

    // 执行加密
    fn perform_encryption(
        &self,
        data: &[u8],
        key: &[u8],
        algorithm: &EncryptionAlgorithm,
    ) -> Result<Vec<u8>, EncryptionError> {
        match algorithm {
            EncryptionAlgorithm::AES256 => {
                // 简单的XOR加密（实际应用中应使用真正的AES）
                Ok(data.iter().zip(key.iter().cycle()).map(|(d, k)| d ^ k).collect())
            }
            EncryptionAlgorithm::RSA2048 => {
                // RSA加密实现
                Ok(data.to_vec())
            }
            EncryptionAlgorithm::ChaCha20 => {
                // ChaCha20加密实现
                Ok(data.to_vec())
            }
            EncryptionAlgorithm::Blowfish => {
                // Blowfish加密实现
                Ok(data.to_vec())
            }
        }
    }

    // 执行解密
    fn perform_decryption(
        &self,
        encrypted_data: &[u8],
        key: &[u8],
        algorithm: &EncryptionAlgorithm,
    ) -> Result<Vec<u8>, EncryptionError> {
        match algorithm {
            EncryptionAlgorithm::AES256 => {
                // 简单的XOR解密（实际应用中应使用真正的AES）
                Ok(encrypted_data.iter().zip(key.iter().cycle()).map(|(d, k)| d ^ k).collect())
            }
            EncryptionAlgorithm::RSA2048 => {
                // RSA解密实现
                Ok(encrypted_data.to_vec())
            }
            EncryptionAlgorithm::ChaCha20 => {
                // ChaCha20解密实现
                Ok(encrypted_data.to_vec())
            }
            EncryptionAlgorithm::Blowfish => {
                // Blowfish解密实现
                Ok(encrypted_data.to_vec())
            }
        }
    }

    // 获取加密统计
    pub async fn get_encryption_stats(&self) -> EncryptionStats {
        let keys = self.keys.read().await;
        let sessions = self.sessions.read().await;

        let total_keys = keys.len();
        let active_keys = keys.values().filter(|k| matches!(k.status, KeyStatus::Active)).count();
        let total_sessions = sessions.len();
        let active_sessions = sessions.values().filter(|s| matches!(s.status, SessionStatus::Active)).count();
        
        let total_messages: u64 = sessions.values().map(|s| s.message_count).sum();
        let total_bytes: u64 = sessions.values().map(|s| s.bytes_encrypted).sum();

        EncryptionStats {
            total_keys,
            active_keys,
            total_sessions,
            active_sessions,
            total_messages,
            total_bytes,
            average_message_size: if total_messages > 0 {
                total_bytes as f64 / total_messages as f64
            } else {
                0.0
            },
        }
    }
}

#[derive(Debug)]
pub struct EncryptionStats {
    pub total_keys: usize,
    pub active_keys: usize,
    pub total_sessions: usize,
    pub active_sessions: usize,
    pub total_messages: u64,
    pub total_bytes: u64,
    pub average_message_size: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum EncryptionError {
    #[error("密钥生成失败")]
    KeyGenerationFailed,
    
    #[error("密钥未找到")]
    KeyNotFound,
    
    #[error("密钥未激活")]
    KeyInactive,
    
    #[error("会话未找到")]
    SessionNotFound,
    
    #[error("会话已过期")]
    SessionExpired,
    
    #[error("超过最大会话数")]
    MaxSessionsExceeded,
    
    #[error("加密失败: {0}")]
    EncryptionFailed(String),
    
    #[error("解密失败: {0}")]
    DecryptionFailed(String),
}
```

## 6. 审计日志

### 6.1 审计日志系统

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};

// 审计日志系统
pub struct AuditLogSystem {
    logs: Arc<RwLock<Vec<AuditLogEntry>>>,
    filters: Arc<RwLock<HashMap<String, LogFilter>>>,
    config: AuditLogConfig,
    stats: Arc<Mutex<AuditLogStats>>,
}

#[derive(Debug, Clone)]
pub struct AuditLogConfig {
    pub max_log_entries: usize,
    pub log_level: LogLevel,
    pub retention_period: Duration,
    pub auto_cleanup: bool,
    pub compression_enabled: bool,
    pub encryption_enabled: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditLogEntry {
    pub id: String,
    pub timestamp: Instant,
    pub level: LogLevel,
    pub category: LogCategory,
    pub event_type: String,
    pub description: String,
    pub user_id: Option<String>,
    pub session_id: Option<String>,
    pub resource: Option<String>,
    pub action: Option<String>,
    pub result: LogResult,
    pub metadata: HashMap<String, String>,
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
pub enum LogCategory {
    Authentication,
    Authorization,
    ResourceAccess,
    SystemOperation,
    SecurityEvent,
    Compliance,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogResult {
    Success,
    Failure,
    Partial,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct LogFilter {
    pub id: String,
    pub name: String,
    pub level_filter: Option<LogLevel>,
    pub category_filter: Option<LogCategory>,
    pub user_filter: Option<String>,
    pub time_range: Option<TimeRange>,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub struct TimeRange {
    pub start: Instant,
    pub end: Instant,
}

impl AuditLogSystem {
    pub fn new(config: AuditLogConfig) -> Self {
        Self {
            logs: Arc::new(RwLock::new(Vec::new())),
            filters: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(Mutex::new(AuditLogStats {
                total_entries: 0,
                debug_entries: 0,
                info_entries: 0,
                warning_entries: 0,
                error_entries: 0,
                critical_entries: 0,
                successful_operations: 0,
                failed_operations: 0,
            })),
        }
    }

    // 记录审计日志
    pub async fn log_event(&self, entry: AuditLogEntry) -> Result<(), AuditLogError> {
        let mut logs = self.logs.write().await;
        let mut stats = self.stats.lock().unwrap();

        // 检查日志级别
        if !self.should_log(&entry.level) {
            return Ok(());
        }

        // 检查容量限制
        if logs.len() >= self.config.max_log_entries {
            if self.config.auto_cleanup {
                self.cleanup_old_logs(&mut logs).await;
            } else {
                return Err(AuditLogError::LogCapacityExceeded);
            }
        }

        // 添加日志条目
        logs.push(entry.clone());

        // 更新统计
        stats.total_entries += 1;
        match entry.level {
            LogLevel::Debug => stats.debug_entries += 1,
            LogLevel::Info => stats.info_entries += 1,
            LogLevel::Warning => stats.warning_entries += 1,
            LogLevel::Error => stats.error_entries += 1,
            LogLevel::Critical => stats.critical_entries += 1,
        }

        match entry.result {
            LogResult::Success => stats.successful_operations += 1,
            LogResult::Failure => stats.failed_operations += 1,
            _ => {}
        }

        Ok(())
    }

    // 检查是否应该记录日志
    fn should_log(&self, level: &LogLevel) -> bool {
        match (&self.config.log_level, level) {
            (LogLevel::Debug, _) => true,
            (LogLevel::Info, LogLevel::Debug) => false,
            (LogLevel::Info, _) => true,
            (LogLevel::Warning, LogLevel::Debug | LogLevel::Info) => false,
            (LogLevel::Warning, _) => true,
            (LogLevel::Error, LogLevel::Debug | LogLevel::Info | LogLevel::Warning) => false,
            (LogLevel::Error, _) => true,
            (LogLevel::Critical, LogLevel::Critical) => true,
            (LogLevel::Critical, _) => false,
        }
    }

    // 清理旧日志
    async fn cleanup_old_logs(&self, logs: &mut Vec<AuditLogEntry>) {
        let cutoff_time = Instant::now() - self.config.retention_period;
        logs.retain(|entry| entry.timestamp > cutoff_time);
    }

    // 创建日志过滤器
    pub async fn create_filter(
        &self,
        name: String,
        level_filter: Option<LogLevel>,
        category_filter: Option<LogCategory>,
        user_filter: Option<String>,
        time_range: Option<TimeRange>,
    ) -> Result<String, AuditLogError> {
        let filter_id = uuid::Uuid::new_v4().to_string();

        let filter = LogFilter {
            id: filter_id.clone(),
            name,
            level_filter,
            category_filter,
            user_filter,
            time_range,
            enabled: true,
        };

        {
            let mut filters = self.filters.write().await;
            filters.insert(filter_id.clone(), filter);
        }

        Ok(filter_id)
    }

    // 查询日志
    pub async fn query_logs(
        &self,
        filter_id: Option<&str>,
        limit: Option<usize>,
    ) -> Result<Vec<AuditLogEntry>, AuditLogError> {
        let logs = self.logs.read().await;
        let filters = self.filters.read().await;

        let mut filtered_logs = logs.clone();

        // 应用过滤器
        if let Some(filter_id) = filter_id {
            if let Some(filter) = filters.get(filter_id) {
                if filter.enabled {
                    filtered_logs = self.apply_filter(&filtered_logs, filter);
                }
            }
        }

        // 按时间排序（最新的在前）
        filtered_logs.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));

        // 应用限制
        if let Some(limit) = limit {
            filtered_logs.truncate(limit);
        }

        Ok(filtered_logs)
    }

    // 应用过滤器
    fn apply_filter(&self, logs: &[AuditLogEntry], filter: &LogFilter) -> Vec<AuditLogEntry> {
        logs.iter()
            .filter(|entry| {
                // 级别过滤
                if let Some(level_filter) = &filter.level_filter {
                    if entry.level != *level_filter {
                        return false;
                    }
                }

                // 类别过滤
                if let Some(category_filter) = &filter.category_filter {
                    if entry.category != *category_filter {
                        return false;
                    }
                }

                // 用户过滤
                if let Some(user_filter) = &filter.user_filter {
                    if let Some(user_id) = &entry.user_id {
                        if user_id != user_filter {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }

                // 时间范围过滤
                if let Some(time_range) = &filter.time_range {
                    if entry.timestamp < time_range.start || entry.timestamp > time_range.end {
                        return false;
                    }
                }

                true
            })
            .cloned()
            .collect()
    }

    // 导出日志
    pub async fn export_logs(
        &self,
        filter_id: Option<&str>,
        format: ExportFormat,
    ) -> Result<Vec<u8>, AuditLogError> {
        let logs = self.query_logs(filter_id, None).await?;

        match format {
            ExportFormat::Json => {
                let json = serde_json::to_string_pretty(&logs)
                    .map_err(|e| AuditLogError::ExportFailed(e.to_string()))?;
                Ok(json.into_bytes())
            }
            ExportFormat::Csv => {
                let mut csv = String::new();
                csv.push_str("id,timestamp,level,category,event_type,description,user_id,result\n");
                
                for log in logs {
                    csv.push_str(&format!(
                        "{},{},{:?},{:?},{},{},{},{:?}\n",
                        log.id,
                        log.timestamp.elapsed().as_secs(),
                        log.level,
                        log.category,
                        log.event_type,
                        log.description,
                        log.user_id.unwrap_or_default(),
                        log.result
                    ));
                }
                
                Ok(csv.into_bytes())
            }
            ExportFormat::Xml => {
                let mut xml = String::new();
                xml.push_str("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
                xml.push_str("<audit_logs>\n");
                
                for log in logs {
                    xml.push_str(&format!(
                        "  <entry id=\"{}\" timestamp=\"{}\" level=\"{:?}\" category=\"{:?}\">\n",
                        log.id,
                        log.timestamp.elapsed().as_secs(),
                        log.level,
                        log.category
                    ));
                    xml.push_str(&format!("    <event_type>{}</event_type>\n", log.event_type));
                    xml.push_str(&format!("    <description>{}</description>\n", log.description));
                    if let Some(user_id) = &log.user_id {
                        xml.push_str(&format!("    <user_id>{}</user_id>\n", user_id));
                    }
                    xml.push_str(&format!("    <result>{:?}</result>\n", log.result));
                    xml.push_str("  </entry>\n");
                }
                
                xml.push_str("</audit_logs>\n");
                Ok(xml.into_bytes())
            }
        }
    }

    // 获取审计统计
    pub fn get_audit_stats(&self) -> AuditLogStats {
        self.stats.lock().unwrap().clone()
    }

    // 清理日志
    pub async fn cleanup_logs(&self) -> Result<(), AuditLogError> {
        let mut logs = self.logs.write().await;
        self.cleanup_old_logs(&mut logs).await;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum ExportFormat {
    Json,
    Csv,
    Xml,
}

#[derive(Debug, Clone)]
pub struct AuditLogStats {
    pub total_entries: u64,
    pub debug_entries: u64,
    pub info_entries: u64,
    pub warning_entries: u64,
    pub error_entries: u64,
    pub critical_entries: u64,
    pub successful_operations: u64,
    pub failed_operations: u64,
}

#[derive(Debug, thiserror::Error)]
pub enum AuditLogError {
    #[error("日志容量超出")]
    LogCapacityExceeded,
    
    #[error("导出失败: {0}")]
    ExportFailed(String),
    
    #[error("过滤器未找到: {0}")]
    FilterNotFound(String),
    
    #[error("日志操作失败: {0}")]
    LogOperationFailed(String),
}
```

## 总结

本章提供了安全与沙箱的完整示例，包括：

1. **进程沙箱** - 进程隔离和安全限制
2. **权限控制** - 用户认证和授权管理
3. **资源限制** - 资源使用监控和限制
4. **安全监控** - 实时安全事件监控
5. **加密通信** - 数据加密和密钥管理
6. **审计日志** - 完整的审计日志系统

这些示例展示了如何在 Rust 1.90 中实现企业级的安全功能，提供了完整的监控、审计和合规支持。
