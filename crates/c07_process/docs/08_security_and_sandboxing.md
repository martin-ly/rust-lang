# C07-08. 安全与沙箱 (Rust 1.92.0 增强版)

> **文档定位**: Tier 4 高级主题
> **最后更新**: 2025-12-25
> **Rust版本**: 1.92.0+ (Edition 2024)
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

## 📋 目录

- [C07-08. 安全与沙箱 (Rust 1.92.0 增强版)](#c07-08-安全与沙箱-rust-1920-增强版)
  - [📋 目录](#-目录)
  - [1. Rust 1.92.0 安全特性（自 Rust 1.90 引入）](#1-rust-1920-安全特性自-rust-190-引入)
    - [1.1 异步安全闭包](#11-异步安全闭包)
    - [1.2 改进的错误处理](#12-改进的错误处理)
    - [1.3 内存安全增强](#13-内存安全增强)
    - [1.4 并发安全特性](#14-并发安全特性)
  - [2. 权限控制](#2-权限控制)
    - [1.1 用户权限管理](#11-用户权限管理)
    - [1.2 资源限制](#12-资源限制)
  - [2. 沙箱执行](#2-沙箱执行)
    - [2.1 进程沙箱](#21-进程沙箱)
    - [2.2 容器化执行](#22-容器化执行)
  - [3. 安全审计](#3-安全审计)
    - [3.1 安全事件监控](#31-安全事件监控)
  - [4. 威胁防护](#4-威胁防护)
    - [4.1 入侵检测](#41-入侵检测)
  - [6. 现代安全库集成](#6-现代安全库集成)
    - [6.1 Tokio 安全特性](#61-tokio-安全特性)
    - [6.2 Async-Std 安全增强](#62-async-std-安全增强)
    - [6.3 第三方安全库](#63-第三方安全库)
  - [7. 企业级安全实践](#7-企业级安全实践)
    - [7.1 安全策略管理](#71-安全策略管理)
    - [7.2 安全监控与告警](#72-安全监控与告警)
    - [7.3 事件响应](#73-事件响应)
  - [8. 总结](#8-总结)

本章深入探讨 Rust 1.92.0 进程管理中的安全机制（兼容 Rust 1.90+ 特性），包括最新的语言安全特性、权限控制、沙箱执行、资源限制、安全审计和威胁防护，以及现代安全库的集成和企业级安全实践。

## 1. Rust 1.92.0 安全特性（自 Rust 1.90 引入）

### 1.1 异步安全闭包

Rust 1.92.0 引入了异步闭包（自 Rust 1.90 引入），为进程安全提供了新的可能性：

```rust
use std::process::{Command, Stdio};
use std::time::Duration;
use tokio::time::timeout;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};

// 异步安全进程执行器
pub struct AsyncSecureProcessExecutor {
    security_context: SecurityContext,
    audit_logger: Arc<Mutex<AuditLogger>>,
}

#[derive(Debug, Clone)]
pub struct SecurityContext {
    pub user_id: String,
    pub permissions: Vec<Permission>,
    pub resource_limits: ResourceLimits,
    pub execution_timeout: Duration,
    pub allowed_commands: Vec<String>,
    pub denied_commands: Vec<String>,
}

impl AsyncSecureProcessExecutor {
    pub fn new(security_context: SecurityContext) -> Self {
        Self {
            security_context,
            audit_logger: Arc::new(Mutex::new(AuditLogger::new())),
        }
    }

    // 使用异步闭包执行安全进程
    pub async fn execute_secure<F, Fut>(
        &self,
        command: String,
        args: Vec<String>,
        security_check: F,
    ) -> Result<ProcessResult, SecurityError>
    where
        F: FnOnce(&SecurityContext, &str, &[String]) -> Fut,
        Fut: Future<Output = Result<(), SecurityError>>,
    {
        // 执行安全检查
        security_check(&self.security_context, &command, &args).await?;

        // 记录审计日志
        self.audit_logger.lock().await.log_execution(
            &self.security_context.user_id,
            &command,
            &args,
        ).await;

        // 创建安全进程
        let mut child = Command::new(&command)
            .args(&args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| SecurityError::ProcessSpawnFailed(e.to_string()))?;

        // 设置超时
        let timeout_duration = self.security_context.execution_timeout;
        let result = timeout(timeout_duration, async {
            let output = child.wait_with_output().await
                .map_err(|e| SecurityError::ProcessExecutionFailed(e.to_string()))?;

            Ok(ProcessResult {
                exit_code: output.status.code().unwrap_or(-1),
                stdout: String::from_utf8_lossy(&output.stdout).to_string(),
                stderr: String::from_utf8_lossy(&output.stderr).to_string(),
                execution_time: Duration::from_millis(0), // 实际实现中计算执行时间
            })
        }).await;

        match result {
            Ok(Ok(process_result)) => {
                self.audit_logger.lock().await.log_success(
                    &self.security_context.user_id,
                    &command,
                    &process_result,
                ).await;
                Ok(process_result)
            }
            Ok(Err(e)) => {
                self.audit_logger.lock().await.log_failure(
                    &self.security_context.user_id,
                    &command,
                    &e,
                ).await;
                Err(e)
            }
            Err(_) => {
                let timeout_error = SecurityError::ExecutionTimeout;
                self.audit_logger.lock().await.log_failure(
                    &self.security_context.user_id,
                    &command,
                    &timeout_error,
                ).await;
                Err(timeout_error)
            }
        }
    }
}

#[derive(Debug)]
pub struct ProcessResult {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
    pub execution_time: Duration,
}

#[derive(Debug, thiserror::Error)]
pub enum SecurityError {
    #[error("进程启动失败: {0}")]
    ProcessSpawnFailed(String),
    #[error("进程执行失败: {0}")]
    ProcessExecutionFailed(String),
    #[error("执行超时")]
    ExecutionTimeout,
    #[error("权限不足")]
    InsufficientPermissions,
    #[error("命令被禁止")]
    CommandForbidden,
    #[error("资源限制违规")]
    ResourceLimitViolation,
}

// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let security_context = SecurityContext {
        user_id: "user123".to_string(),
        permissions: vec![Permission::ExecuteCommand("ls".to_string())],
        resource_limits: ResourceLimits {
            max_memory_mb: 512,
            max_cpu_percent: 50.0,
            max_file_descriptors: 100,
            max_disk_usage_mb: 1024,
            max_network_bandwidth_mbps: 10.0,
        },
        execution_timeout: Duration::from_secs(30),
        allowed_commands: vec!["ls".to_string(), "cat".to_string()],
        denied_commands: vec!["rm".to_string(), "sudo".to_string()],
    };

    let executor = AsyncSecureProcessExecutor::new(security_context);

    // 使用异步闭包进行安全检查
    let result = executor.execute_secure(
        "ls".to_string(),
        vec!["-la".to_string()],
        |context, command, args| async move {
            // 检查命令是否被允许
            if context.denied_commands.contains(command) {
                return Err(SecurityError::CommandForbidden);
            }

            if !context.allowed_commands.is_empty() && !context.allowed_commands.contains(command) {
                return Err(SecurityError::InsufficientPermissions);
            }

            // 检查参数安全性
            for arg in args {
                if arg.contains("..") || arg.contains("/") {
                    return Err(SecurityError::CommandForbidden);
                }
            }

            Ok(())
        },
    ).await?;

    println!("命令执行结果: {:?}", result);
    Ok(())
}
```

### 1.2 改进的错误处理

Rust 1.92.0 改进了错误处理（自 Rust 1.90 引入），使安全相关的错误更加清晰：

```rust
use thiserror::Error;
use std::fmt;

// 安全错误类型定义
#[derive(Error, Debug)]
pub enum ProcessSecurityError {
    #[error("权限验证失败: {user_id} 尝试执行 {command}")]
    PermissionDenied {
        user_id: String,
        command: String,
        required_permission: String,
    },

    #[error("资源限制违规: {resource} 超出限制 {limit}")]
    ResourceLimitExceeded {
        resource: String,
        current: u64,
        limit: u64,
    },

    #[error("安全策略违规: {policy}")]
    SecurityPolicyViolation {
        policy: String,
        details: String,
    },

    #[error("沙箱执行失败: {reason}")]
    SandboxExecutionFailed {
        reason: String,
        sandbox_id: String,
    },

    #[error("审计日志记录失败: {0}")]
    AuditLoggingFailed(String),
}

// 安全进程管理器
pub struct SecureProcessManager {
    security_policies: Arc<Mutex<Vec<SecurityPolicy>>>,
    audit_logger: Arc<Mutex<AuditLogger>>,
    resource_monitor: Arc<Mutex<ResourceMonitor>>,
}

impl SecureProcessManager {
    pub async fn execute_with_security_check(
        &self,
        user_id: &str,
        command: &str,
        args: &[String],
    ) -> Result<ProcessResult, ProcessSecurityError> {
        // 权限检查
        self.check_permissions(user_id, command)
            .await
            .map_err(|e| ProcessSecurityError::PermissionDenied {
                user_id: user_id.to_string(),
                command: command.to_string(),
                required_permission: e.to_string(),
            })?;

        // 资源检查
        self.check_resource_limits(user_id)
            .await
            .map_err(|e| ProcessSecurityError::ResourceLimitExceeded {
                resource: "memory".to_string(),
                current: 0, // 实际实现中获取当前使用量
                limit: 512,
            })?;

        // 安全策略检查
        self.check_security_policies(user_id, command, args)
            .await
            .map_err(|policy| ProcessSecurityError::SecurityPolicyViolation {
                policy: policy.clone(),
                details: "策略违规".to_string(),
            })?;

        // 执行进程
        self.execute_process(command, args).await
    }

    async fn check_permissions(
        &self,
        user_id: &str,
        command: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 权限检查逻辑
        Ok(())
    }

    async fn check_resource_limits(
        &self,
        user_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 资源限制检查逻辑
        Ok(())
    }

    async fn check_security_policies(
        &self,
        user_id: &str,
        command: &str,
        args: &[String],
    ) -> Result<(), String> {
        // 安全策略检查逻辑
        Ok(())
    }

    async fn execute_process(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<ProcessResult, ProcessSecurityError> {
        // 进程执行逻辑
        Ok(ProcessResult {
            exit_code: 0,
            stdout: "".to_string(),
            stderr: "".to_string(),
            execution_time: Duration::from_millis(0),
        })
    }
}
```

### 1.3 内存安全增强

Rust 1.92.0 增强了内存安全特性（自 Rust 1.90 引入），特别是在进程间通信中：

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::collections::HashMap;

// 内存安全进程管理器
pub struct MemorySafeProcessManager {
    process_memory_map: Arc<Mutex<HashMap<String, ProcessMemoryInfo>>>,
    memory_limits: Arc<Mutex<HashMap<String, MemoryLimits>>>,
    leak_detector: Arc<Mutex<MemoryLeakDetector>>,
}

#[derive(Debug, Clone)]
pub struct ProcessMemoryInfo {
    pub process_id: String,
    pub allocated_memory: u64,
    pub peak_memory: u64,
    pub memory_regions: Vec<MemoryRegion>,
    pub last_accessed: std::time::Instant,
}

#[derive(Debug, Clone)]
pub struct MemoryRegion {
    pub start_address: u64,
    pub size: u64,
    pub permissions: MemoryPermissions,
    pub region_type: MemoryRegionType,
}

#[derive(Debug, Clone)]
pub enum MemoryPermissions {
    ReadOnly,
    WriteOnly,
    ReadWrite,
    Execute,
    ReadExecute,
    WriteExecute,
    ReadWriteExecute,
}

#[derive(Debug, Clone)]
pub enum MemoryRegionType {
    Stack,
    Heap,
    Code,
    Data,
    Shared,
    Mapped,
}

#[derive(Debug, Clone)]
pub struct MemoryLimits {
    pub max_heap_size: u64,
    pub max_stack_size: u64,
    pub max_total_memory: u64,
    pub max_memory_regions: usize,
}

impl MemorySafeProcessManager {
    pub fn new() -> Self {
        Self {
            process_memory_map: Arc::new(Mutex::new(HashMap::new())),
            memory_limits: Arc::new(Mutex::new(HashMap::new())),
            leak_detector: Arc::new(Mutex::new(MemoryLeakDetector::new())),
        }
    }

    // 安全内存分配
    pub async fn allocate_memory(
        &self,
        process_id: &str,
        size: u64,
        permissions: MemoryPermissions,
    ) -> Result<MemoryRegion, MemoryError> {
        // 检查内存限制
        let limits = self.memory_limits.lock().await;
        if let Some(limit) = limits.get(process_id) {
            if size > limit.max_heap_size {
                return Err(MemoryError::LimitExceeded);
            }
        }

        // 分配内存区域
        let region = MemoryRegion {
            start_address: 0x1000, // 实际实现中分配真实地址
            size,
            permissions,
            region_type: MemoryRegionType::Heap,
        };

        // 更新进程内存信息
        let mut memory_map = self.process_memory_map.lock().await;
        if let Some(info) = memory_map.get_mut(process_id) {
            info.allocated_memory += size;
            info.memory_regions.push(region.clone());
            info.last_accessed = std::time::Instant::now();
        }

        Ok(region)
    }

    // 内存泄漏检测
    pub async fn detect_memory_leaks(&self) -> Vec<MemoryLeak> {
        let mut detector = self.leak_detector.lock().await;
        detector.detect_leaks().await
    }

    // 内存使用监控
    pub async fn monitor_memory_usage(&self, process_id: &str) -> ProcessMemoryInfo {
        let memory_map = self.process_memory_map.lock().await;
        memory_map.get(process_id)
            .cloned()
            .unwrap_or_else(|| ProcessMemoryInfo {
                process_id: process_id.to_string(),
                allocated_memory: 0,
                peak_memory: 0,
                memory_regions: Vec::new(),
                last_accessed: std::time::Instant::now(),
            })
    }
}

#[derive(Debug, thiserror::Error)]
pub enum MemoryError {
    #[error("内存限制超出")]
    LimitExceeded,
    #[error("内存分配失败")]
    AllocationFailed,
    #[error("内存区域无效")]
    InvalidRegion,
    #[error("权限不足")]
    InsufficientPermissions,
}

// 内存泄漏检测器
pub struct MemoryLeakDetector {
    allocated_regions: HashMap<String, Vec<MemoryRegion>>,
    freed_regions: HashMap<String, Vec<MemoryRegion>>,
}

impl MemoryLeakDetector {
    pub fn new() -> Self {
        Self {
            allocated_regions: HashMap::new(),
            freed_regions: HashMap::new(),
        }
    }

    pub async fn detect_leaks(&mut self) -> Vec<MemoryLeak> {
        let mut leaks = Vec::new();

        for (process_id, allocated) in &self.allocated_regions {
            let freed = self.freed_regions.get(process_id).unwrap_or(&Vec::new());

            for region in allocated {
                if !freed.contains(region) {
                    leaks.push(MemoryLeak {
                        process_id: process_id.clone(),
                        region: region.clone(),
                        leak_size: region.size,
                        detected_at: std::time::Instant::now(),
                    });
                }
            }
        }

        leaks
    }
}

#[derive(Debug, Clone)]
pub struct MemoryLeak {
    pub process_id: String,
    pub region: MemoryRegion,
    pub leak_size: u64,
    pub detected_at: std::time::Instant,
}
```

### 1.4 并发安全特性

Rust 1.92.0 改进了并发安全特性（自 Rust 1.90 引入），特别是在多进程环境中的安全控制：

```rust
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock, Semaphore};
use std::collections::HashMap;
use std::time::{Duration, Instant};

// 并发安全进程管理器
pub struct ConcurrentSecureProcessManager {
    active_processes: Arc<RwLock<HashMap<String, SecureProcess>>>,
    process_semaphore: Arc<Semaphore>,
    security_contexts: Arc<RwLock<HashMap<String, SecurityContext>>>,
    audit_logger: Arc<Mutex<AuditLogger>>,
}

#[derive(Debug, Clone)]
pub struct SecureProcess {
    pub id: String,
    pub user_id: String,
    pub command: String,
    pub args: Vec<String>,
    pub status: ProcessStatus,
    pub security_level: SecurityLevel,
    pub created_at: Instant,
    pub resource_usage: ResourceUsage,
    pub security_violations: Vec<SecurityViolation>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ProcessStatus {
    Starting,
    Running,
    Suspended,
    Terminated,
    Failed,
    Quarantined,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SecurityLevel {
    Low,
    Medium,
    High,
    Critical,
}

impl ConcurrentSecureProcessManager {
    pub fn new(max_concurrent_processes: usize) -> Self {
        Self {
            active_processes: Arc::new(RwLock::new(HashMap::new())),
            process_semaphore: Arc::new(Semaphore::new(max_concurrent_processes)),
            security_contexts: Arc::new(RwLock::new(HashMap::new())),
            audit_logger: Arc::new(Mutex::new(AuditLogger::new())),
        }
    }

    // 并发安全进程创建
    pub async fn create_secure_process(
        &self,
        user_id: String,
        command: String,
        args: Vec<String>,
        security_level: SecurityLevel,
    ) -> Result<String, ProcessSecurityError> {
        // 获取信号量许可
        let _permit = self.process_semaphore.acquire().await
            .map_err(|_| ProcessSecurityError::ResourceLimitExceeded {
                resource: "concurrent_processes".to_string(),
                current: 0,
                limit: 0,
            })?;

        // 检查安全上下文
        let security_contexts = self.security_contexts.read().await;
        let context = security_contexts.get(&user_id)
            .ok_or_else(|| ProcessSecurityError::PermissionDenied {
                user_id: user_id.clone(),
                command: command.clone(),
                required_permission: "valid_user".to_string(),
            })?;

        // 验证命令权限
        if !self.is_command_allowed(context, &command).await {
            return Err(ProcessSecurityError::PermissionDenied {
                user_id,
                command,
                required_permission: "command_execution".to_string(),
            });
        }

        // 创建安全进程
        let process_id = uuid::Uuid::new_v4().to_string();
        let secure_process = SecureProcess {
            id: process_id.clone(),
            user_id: user_id.clone(),
            command: command.clone(),
            args: args.clone(),
            status: ProcessStatus::Starting,
            security_level: security_level.clone(),
            created_at: Instant::now(),
            resource_usage: ResourceUsage {
                memory_mb: 0,
                cpu_percent: 0.0,
                file_descriptors: 0,
                disk_usage_mb: 0,
                network_bandwidth_mbps: 0.0,
                last_updated: Instant::now(),
            },
            security_violations: Vec::new(),
        };

        // 添加到活跃进程列表
        let mut active_processes = self.active_processes.write().await;
        active_processes.insert(process_id.clone(), secure_process);

        // 记录审计日志
        self.audit_logger.lock().await.log_process_creation(
            &user_id,
            &process_id,
            &command,
            &args,
            &security_level,
        ).await;

        Ok(process_id)
    }

    // 并发安全进程监控
    pub async fn monitor_processes(&self) -> Result<(), ProcessSecurityError> {
        let mut interval = tokio::time::interval(Duration::from_millis(100));

        loop {
            interval.tick().await;

            let mut active_processes = self.active_processes.write().await;
            let mut processes_to_remove = Vec::new();

            for (process_id, process) in active_processes.iter_mut() {
                // 检查进程状态
                match process.status {
                    ProcessStatus::Running => {
                        // 监控资源使用
                        if let Err(e) = self.check_resource_limits(process).await {
                            self.handle_security_violation(
                                process_id,
                                SecurityViolationType::ResourceLimitExceeded,
                                e.to_string(),
                            ).await;
                        }

                        // 检查安全策略
                        if let Err(e) = self.check_security_policies(process).await {
                            self.handle_security_violation(
                                process_id,
                                SecurityViolationType::PolicyViolation,
                                e.to_string(),
                            ).await;
                        }
                    }
                    ProcessStatus::Terminated | ProcessStatus::Failed | ProcessStatus::Quarantined => {
                        processes_to_remove.push(process_id.clone());
                    }
                    _ => {}
                }
            }

            // 清理已终止的进程
            for process_id in processes_to_remove {
                if let Some(process) = active_processes.remove(&process_id) {
                    self.audit_logger.lock().await.log_process_termination(
                        &process.user_id,
                        &process_id,
                        &process.status,
                    ).await;
                }
            }
        }
    }

    async fn is_command_allowed(
        &self,
        context: &SecurityContext,
        command: &str,
    ) -> bool {
        // 检查命令是否在允许列表中
        if !context.allowed_commands.is_empty() {
            return context.allowed_commands.contains(&command.to_string());
        }

        // 检查命令是否在拒绝列表中
        !context.denied_commands.contains(&command.to_string())
    }

    async fn check_resource_limits(
        &self,
        process: &SecureProcess,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 资源限制检查逻辑
        Ok(())
    }

    async fn check_security_policies(
        &self,
        process: &SecureProcess,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 安全策略检查逻辑
        Ok(())
    }

    async fn handle_security_violation(
        &self,
        process_id: &str,
        violation_type: SecurityViolationType,
        description: String,
    ) {
        let violation = SecurityViolation {
            id: uuid::Uuid::new_v4().to_string(),
            violation_type,
            description,
            severity: ViolationSeverity::Medium,
            timestamp: Instant::now(),
            action_taken: None,
        };

        let mut active_processes = self.active_processes.write().await;
        if let Some(process) = active_processes.get_mut(process_id) {
            process.security_violations.push(violation);

            // 根据严重程度采取行动
            if process.security_violations.len() > 5 {
                process.status = ProcessStatus::Quarantined;
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum SecurityViolationType {
    ResourceLimitExceeded,
    PolicyViolation,
    UnauthorizedAccess,
    SuspiciousActivity,
}

#[derive(Debug, Clone)]
pub struct SecurityViolation {
    pub id: String,
    pub violation_type: SecurityViolationType,
    pub description: String,
    pub severity: ViolationSeverity,
    pub timestamp: Instant,
    pub action_taken: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ViolationSeverity {
    Low,
    Medium,
    High,
    Critical,
}

// 审计日志记录器
pub struct AuditLogger {
    logs: Vec<AuditLogEntry>,
}

impl AuditLogger {
    pub fn new() -> Self {
        Self {
            logs: Vec::new(),
        }
    }

    pub async fn log_process_creation(
        &mut self,
        user_id: &str,
        process_id: &str,
        command: &str,
        args: &[String],
        security_level: &SecurityLevel,
    ) {
        let entry = AuditLogEntry {
            id: uuid::Uuid::new_v4().to_string(),
            user_id: user_id.to_string(),
            action: AuditAction::ProcessCreation,
            resource: process_id.to_string(),
            details: format!("Command: {}, Args: {:?}, Security Level: {:?}", command, args, security_level),
            timestamp: Instant::now(),
            result: AuditResult::Success,
        };

        self.logs.push(entry);
    }

    pub async fn log_process_termination(
        &mut self,
        user_id: &str,
        process_id: &str,
        status: &ProcessStatus,
    ) {
        let entry = AuditLogEntry {
            id: uuid::Uuid::new_v4().to_string(),
            user_id: user_id.to_string(),
            action: AuditAction::ProcessTermination,
            resource: process_id.to_string(),
            details: format!("Status: {:?}", status),
            timestamp: Instant::now(),
            result: AuditResult::Success,
        };

        self.logs.push(entry);
    }

    pub async fn log_execution(
        &mut self,
        user_id: &str,
        command: &str,
        args: &[String],
    ) {
        let entry = AuditLogEntry {
            id: uuid::Uuid::new_v4().to_string(),
            user_id: user_id.to_string(),
            action: AuditAction::CommandExecution,
            resource: command.to_string(),
            details: format!("Args: {:?}", args),
            timestamp: Instant::now(),
            result: AuditResult::Success,
        };

        self.logs.push(entry);
    }

    pub async fn log_success(
        &mut self,
        user_id: &str,
        command: &str,
        result: &ProcessResult,
    ) {
        let entry = AuditLogEntry {
            id: uuid::Uuid::new_v4().to_string(),
            user_id: user_id.to_string(),
            action: AuditAction::CommandExecution,
            resource: command.to_string(),
            details: format!("Exit code: {}, Execution time: {:?}", result.exit_code, result.execution_time),
            timestamp: Instant::now(),
            result: AuditResult::Success,
        };

        self.logs.push(entry);
    }

    pub async fn log_failure(
        &mut self,
        user_id: &str,
        command: &str,
        error: &SecurityError,
    ) {
        let entry = AuditLogEntry {
            id: uuid::Uuid::new_v4().to_string(),
            user_id: user_id.to_string(),
            action: AuditAction::CommandExecution,
            resource: command.to_string(),
            details: format!("Error: {:?}", error),
            timestamp: Instant::now(),
            result: AuditResult::Failure,
        };

        self.logs.push(entry);
    }
}

#[derive(Debug, Clone)]
pub struct AuditLogEntry {
    pub id: String,
    pub user_id: String,
    pub action: AuditAction,
    pub resource: String,
    pub details: String,
    pub timestamp: Instant,
    pub result: AuditResult,
}

#[derive(Debug, Clone)]
pub enum AuditAction {
    ProcessCreation,
    ProcessTermination,
    CommandExecution,
    PermissionCheck,
    ResourceCheck,
    SecurityViolation,
}

#[derive(Debug, Clone)]
pub enum AuditResult {
    Success,
    Failure,
    Denied,
    Timeout,
}
```

## 2. 权限控制

### 1.1 用户权限管理

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub struct PermissionManager {
    users: Arc<Mutex<HashMap<String, UserPermissions>>>,
    groups: Arc<Mutex<HashMap<String, GroupPermissions>>>,
    audit_log: Arc<Mutex<Vec<AuditEntry>>>,
}

#[derive(Debug, Clone)]
pub struct UserPermissions {
    pub user_id: String,
    pub username: String,
    pub allowed_commands: Vec<String>,
    pub denied_commands: Vec<String>,
    pub resource_limits: ResourceLimits,
    pub execution_time_limit: Duration,
    pub max_concurrent_processes: usize,
    pub allowed_directories: Vec<String>,
    pub denied_directories: Vec<String>,
    pub created_at: Instant,
    pub last_accessed: Instant,
}

#[derive(Debug, Clone)]
pub struct GroupPermissions {
    pub group_id: String,
    pub group_name: String,
    pub members: Vec<String>,
    pub permissions: Vec<Permission>,
    pub resource_limits: ResourceLimits,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum Permission {
    ExecuteCommand(String),
    AccessDirectory(String),
    CreateProcess,
    KillProcess,
    ModifyPermissions,
    ViewLogs,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub max_memory_mb: u64,
    pub max_cpu_percent: f64,
    pub max_file_descriptors: u32,
    pub max_disk_usage_mb: u64,
    pub max_network_bandwidth_mbps: f64,
}

#[derive(Debug, Clone)]
pub struct AuditEntry {
    pub id: String,
    pub user_id: String,
    pub action: AuditAction,
    pub resource: String,
    pub result: AuditResult,
    pub timestamp: Instant,
    pub ip_address: Option<String>,
    pub user_agent: Option<String>,
}

#[derive(Debug, Clone)]
pub enum AuditAction {
    ExecuteCommand,
    AccessFile,
    CreateProcess,
    KillProcess,
    ModifyPermissions,
    Login,
    Logout,
}

#[derive(Debug, Clone)]
pub enum AuditResult {
    Success,
    Failure,
    Denied,
    Timeout,
}

impl PermissionManager {
    pub fn new() -> Self {
        Self {
            users: Arc::new(Mutex::new(HashMap::new())),
            groups: Arc::new(Mutex::new(HashMap::new())),
            audit_log: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn create_user(
        &self,
        user_id: String,
        username: String,
        permissions: UserPermissions,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut users = self.users.lock().await;

        if users.contains_key(&user_id) {
            return Err("用户已存在".into());
        }

        users.insert(user_id.clone(), permissions);

        // 记录审计日志
        self.log_audit_event(AuditEntry {
            id: uuid::Uuid::new_v4().to_string(),
            user_id: user_id.clone(),
            action: AuditAction::ModifyPermissions,
            resource: "user_creation".to_string(),
            result: AuditResult::Success,
            timestamp: Instant::now(),
            ip_address: None,
            user_agent: None,
        }).await;

        Ok(())
    }

    pub async fn check_command_permission(
        &self,
        user_id: &str,
        command: &str,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let users = self.users.lock().await;
        let user = users.get(user_id).ok_or("用户未找到")?;

        // 检查是否在拒绝列表中
        if user.denied_commands.contains(&command.to_string()) {
            self.log_audit_event(AuditEntry {
                id: uuid::Uuid::new_v4().to_string(),
                user_id: user_id.to_string(),
                action: AuditAction::ExecuteCommand,
                resource: command.to_string(),
                result: AuditResult::Denied,
                timestamp: Instant::now(),
                ip_address: None,
                user_agent: None,
            }).await;

            return Ok(false);
        }

        // 检查是否在允许列表中
        let allowed = user.allowed_commands.is_empty() || user.allowed_commands.contains(&command.to_string());

        self.log_audit_event(AuditEntry {
            id: uuid::Uuid::new_v4().to_string(),
            user_id: user_id.to_string(),
            action: AuditAction::ExecuteCommand,
            resource: command.to_string(),
            result: if allowed { AuditResult::Success } else { AuditResult::Denied },
            timestamp: Instant::now(),
            ip_address: None,
            user_agent: None,
        }).await;

        Ok(allowed)
    }

    pub async fn check_directory_permission(
        &self,
        user_id: &str,
        directory: &str,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        let users = self.users.lock().await;
        let user = users.get(user_id).ok_or("用户未找到")?;

        // 检查是否在拒绝列表中
        if user.denied_directories.iter().any(|d| directory.starts_with(d)) {
            return Ok(false);
        }

        // 检查是否在允许列表中
        let allowed = user.allowed_directories.is_empty() ||
            user.allowed_directories.iter().any(|d| directory.starts_with(d));

        Ok(allowed)
    }

    pub async fn get_user_permissions(&self, user_id: &str) -> Option<UserPermissions> {
        let users = self.users.lock().await;
        users.get(user_id).cloned()
    }

    pub async fn update_user_permissions(
        &self,
        user_id: &str,
        new_permissions: UserPermissions,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut users = self.users.lock().await;

        if let Some(user) = users.get_mut(user_id) {
            *user = new_permissions;
            user.last_accessed = Instant::now();

            // 记录审计日志
            self.log_audit_event(AuditEntry {
                id: uuid::Uuid::new_v4().to_string(),
                user_id: user_id.to_string(),
                action: AuditAction::ModifyPermissions,
                resource: "user_permissions".to_string(),
                result: AuditResult::Success,
                timestamp: Instant::now(),
                ip_address: None,
                user_agent: None,
            }).await;

            Ok(())
        } else {
            Err("用户未找到".into())
        }
    }

    pub async fn delete_user(&self, user_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut users = self.users.lock().await;

        if users.remove(user_id).is_some() {
            // 记录审计日志
            self.log_audit_event(AuditEntry {
                id: uuid::Uuid::new_v4().to_string(),
                user_id: user_id.to_string(),
                action: AuditAction::ModifyPermissions,
                resource: "user_deletion".to_string(),
                result: AuditResult::Success,
                timestamp: Instant::now(),
                ip_address: None,
                user_agent: None,
            }).await;

            Ok(())
        } else {
            Err("用户未找到".into())
        }
    }

    async fn log_audit_event(&self, entry: AuditEntry) {
        let mut audit_log = self.audit_log.lock().await;
        audit_log.push(entry);

        // 保持审计日志大小限制
        if audit_log.len() > 10000 {
            audit_log.remove(0);
        }
    }

    pub async fn get_audit_log(&self, limit: Option<usize>) -> Vec<AuditEntry> {
        let audit_log = self.audit_log.lock().await;

        if let Some(limit) = limit {
            audit_log.iter().rev().take(limit).cloned().collect()
        } else {
            audit_log.clone()
        }
    }

    pub async fn search_audit_log(
        &self,
        user_id: Option<&str>,
        action: Option<&AuditAction>,
        result: Option<&AuditResult>,
    ) -> Vec<AuditEntry> {
        let audit_log = self.audit_log.lock().await;

        audit_log.iter()
            .filter(|entry| {
                if let Some(uid) = user_id {
                    if entry.user_id != uid {
                        return false;
                    }
                }

                if let Some(act) = action {
                    if !std::mem::discriminant(&entry.action).eq(&std::mem::discriminant(act)) {
                        return false;
                    }
                }

                if let Some(res) = result {
                    if !std::mem::discriminant(&entry.result).eq(&std::mem::discriminant(res)) {
                        return false;
                    }
                }

                true
            })
            .cloned()
            .collect()
    }
}
```

### 1.2 资源限制

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::time::{Duration, Instant};
use std::collections::HashMap;

pub struct ResourceLimiter {
    limits: Arc<Mutex<HashMap<String, ResourceLimits>>>,
    current_usage: Arc<Mutex<HashMap<String, ResourceUsage>>>,
    enforcement_policies: Arc<Mutex<Vec<EnforcementPolicy>>>,
}

#[derive(Debug, Clone)]
pub struct ResourceUsage {
    pub memory_mb: u64,
    pub cpu_percent: f64,
    pub file_descriptors: u32,
    pub disk_usage_mb: u64,
    pub network_bandwidth_mbps: f64,
    pub last_updated: Instant,
}

#[derive(Debug, Clone)]
pub struct EnforcementPolicy {
    pub id: String,
    pub name: String,
    pub condition: EnforcementCondition,
    pub action: EnforcementAction,
    pub severity: PolicySeverity,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum EnforcementCondition {
    MemoryUsageExceeds(u64),
    CpuUsageExceeds(f64),
    FileDescriptorExceeds(u32),
    DiskUsageExceeds(u64),
    NetworkBandwidthExceeds(f64),
    ExecutionTimeExceeds(Duration),
}

#[derive(Debug, Clone)]
pub enum EnforcementAction {
    TerminateProcess,
    SuspendProcess,
    ReducePriority,
    LogWarning,
    NotifyAdmin,
    ScaleDown,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PolicySeverity {
    Low,
    Medium,
    High,
    Critical,
}

impl ResourceLimiter {
    pub fn new() -> Self {
        Self {
            limits: Arc::new(Mutex::new(HashMap::new())),
            current_usage: Arc::new(Mutex::new(HashMap::new())),
            enforcement_policies: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn set_resource_limits(
        &self,
        process_id: &str,
        limits: ResourceLimits,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut limits_map = self.limits.lock().await;
        limits_map.insert(process_id.to_string(), limits);

        Ok(())
    }

    pub async fn update_resource_usage(
        &self,
        process_id: &str,
        usage: ResourceUsage,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut usage_map = self.current_usage.lock().await;
        usage_map.insert(process_id.to_string(), usage);

        // 检查是否违反限制
        self.check_violations(process_id).await?;

        Ok(())
    }

    async fn check_violations(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let limits_map = self.limits.lock().await;
        let usage_map = self.current_usage.lock().await;
        let policies = self.enforcement_policies.lock().await;

        let limits = limits_map.get(process_id);
        let usage = usage_map.get(process_id);

        if let (Some(limits), Some(usage)) = (limits, usage) {
            // 检查内存使用
            if usage.memory_mb > limits.max_memory_mb {
                self.enforce_policy(process_id, &EnforcementCondition::MemoryUsageExceeds(usage.memory_mb), &policies).await?;
            }

            // 检查 CPU 使用
            if usage.cpu_percent > limits.max_cpu_percent {
                self.enforce_policy(process_id, &EnforcementCondition::CpuUsageExceeds(usage.cpu_percent), &policies).await?;
            }

            // 检查文件描述符
            if usage.file_descriptors > limits.max_file_descriptors {
                self.enforce_policy(process_id, &EnforcementCondition::FileDescriptorExceeds(usage.file_descriptors), &policies).await?;
            }

            // 检查磁盘使用
            if usage.disk_usage_mb > limits.max_disk_usage_mb {
                self.enforce_policy(process_id, &EnforcementCondition::DiskUsageExceeds(usage.disk_usage_mb), &policies).await?;
            }

            // 检查网络带宽
            if usage.network_bandwidth_mbps > limits.max_network_bandwidth_mbps {
                self.enforce_policy(process_id, &EnforcementCondition::NetworkBandwidthExceeds(usage.network_bandwidth_mbps), &policies).await?;
            }
        }

        Ok(())
    }

    async fn enforce_policy(
        &self,
        process_id: &str,
        condition: &EnforcementCondition,
        policies: &[EnforcementPolicy],
    ) -> Result<(), Box<dyn std::error::Error>> {
        for policy in policies {
            if self.condition_matches(condition, &policy.condition) {
                self.execute_action(process_id, &policy.action).await?;
            }
        }

        Ok(())
    }

    fn condition_matches(&self, condition: &EnforcementCondition, policy_condition: &EnforcementCondition) -> bool {
        match (condition, policy_condition) {
            (EnforcementCondition::MemoryUsageExceeds(usage), EnforcementCondition::MemoryUsageExceeds(limit)) => {
                usage >= limit
            }
            (EnforcementCondition::CpuUsageExceeds(usage), EnforcementCondition::CpuUsageExceeds(limit)) => {
                usage >= limit
            }
            (EnforcementCondition::FileDescriptorExceeds(usage), EnforcementCondition::FileDescriptorExceeds(limit)) => {
                usage >= limit
            }
            (EnforcementCondition::DiskUsageExceeds(usage), EnforcementCondition::DiskUsageExceeds(limit)) => {
                usage >= limit
            }
            (EnforcementCondition::NetworkBandwidthExceeds(usage), EnforcementCondition::NetworkBandwidthExceeds(limit)) => {
                usage >= limit
            }
            _ => false,
        }
    }

    async fn execute_action(
        &self,
        process_id: &str,
        action: &EnforcementAction,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match action {
            EnforcementAction::TerminateProcess => {
                println!("终止进程 {}", process_id);
                // 实际实现中应该终止进程
            }
            EnforcementAction::SuspendProcess => {
                println!("暂停进程 {}", process_id);
                // 实际实现中应该暂停进程
            }
            EnforcementAction::ReducePriority => {
                println!("降低进程 {} 的优先级", process_id);
                // 实际实现中应该降低进程优先级
            }
            EnforcementAction::LogWarning => {
                println!("警告: 进程 {} 违反资源限制", process_id);
            }
            EnforcementAction::NotifyAdmin => {
                println!("通知管理员: 进程 {} 违反资源限制", process_id);
            }
            EnforcementAction::ScaleDown => {
                println!("缩减进程 {} 的资源分配", process_id);
                // 实际实现中应该缩减资源分配
            }
        }

        Ok(())
    }

    pub async fn add_enforcement_policy(
        &self,
        policy: EnforcementPolicy,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut policies = self.enforcement_policies.lock().await;
        policies.push(policy);
        Ok(())
    }

    pub async fn get_resource_usage(&self, process_id: &str) -> Option<ResourceUsage> {
        let usage_map = self.current_usage.lock().await;
        usage_map.get(process_id).cloned()
    }

    pub async fn get_resource_limits(&self, process_id: &str) -> Option<ResourceLimits> {
        let limits_map = self.limits.lock().await;
        limits_map.get(process_id).cloned()
    }
}
```

## 2. 沙箱执行

### 2.1 进程沙箱

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub struct ProcessSandbox {
    sandboxes: Arc<Mutex<HashMap<String, SandboxConfig>>>,
    active_processes: Arc<Mutex<HashMap<String, SandboxedProcess>>>,
    security_policies: Arc<Mutex<Vec<SecurityPolicy>>>,
}

#[derive(Debug, Clone)]
pub struct SandboxConfig {
    pub id: String,
    pub name: String,
    pub isolation_level: IsolationLevel,
    pub allowed_system_calls: Vec<String>,
    pub denied_system_calls: Vec<String>,
    pub allowed_files: Vec<String>,
    pub denied_files: Vec<String>,
    pub allowed_network_hosts: Vec<String>,
    pub denied_network_hosts: Vec<String>,
    pub resource_limits: ResourceLimits,
    pub execution_timeout: Duration,
    pub max_processes: usize,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum IsolationLevel {
    None,
    Basic,
    Enhanced,
    Maximum,
}

#[derive(Debug, Clone)]
pub struct SandboxedProcess {
    pub id: String,
    pub sandbox_id: String,
    pub process_id: u32,
    pub command: String,
    pub args: Vec<String>,
    pub start_time: Instant,
    pub status: ProcessStatus,
    pub resource_usage: ResourceUsage,
    pub security_violations: Vec<SecurityViolation>,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Starting,
    Running,
    Suspended,
    Terminated,
    Failed,
}

#[derive(Debug, Clone)]
pub struct SecurityViolation {
    pub id: String,
    pub violation_type: ViolationType,
    pub description: String,
    pub severity: ViolationSeverity,
    pub timestamp: Instant,
    pub action_taken: Option<String>,
}

#[derive(Debug, Clone)]
pub enum ViolationType {
    UnauthorizedSystemCall,
    FileAccessViolation,
    NetworkAccessViolation,
    ResourceLimitExceeded,
    ExecutionTimeout,
    PrivilegeEscalation,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ViolationSeverity {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct SecurityPolicy {
    pub id: String,
    pub name: String,
    pub condition: SecurityCondition,
    pub action: SecurityAction,
    pub severity: PolicySeverity,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum SecurityCondition {
    SystemCallViolation,
    FileAccessViolation,
    NetworkAccessViolation,
    ResourceViolation,
    TimeoutViolation,
}

#[derive(Debug, Clone)]
pub enum SecurityAction {
    TerminateProcess,
    SuspendProcess,
    LogViolation,
    NotifySecurity,
    QuarantineProcess,
    BlockAccess,
}

impl ProcessSandbox {
    pub fn new() -> Self {
        Self {
            sandboxes: Arc::new(Mutex::new(HashMap::new())),
            active_processes: Arc::new(Mutex::new(HashMap::new())),
            security_policies: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn create_sandbox(
        &self,
        config: SandboxConfig,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut sandboxes = self.sandboxes.lock().await;

        if sandboxes.contains_key(&config.id) {
            return Err("沙箱已存在".into());
        }

        sandboxes.insert(config.id.clone(), config);

        Ok(())
    }

    pub async fn execute_in_sandbox(
        &self,
        sandbox_id: &str,
        command: String,
        args: Vec<String>,
    ) -> Result<String, Box<dyn std::error::Error>> {
        let sandboxes = self.sandboxes.lock().await;
        let sandbox = sandboxes.get(sandbox_id).ok_or("沙箱未找到")?;

        // 验证命令是否被允许
        if !self.is_command_allowed(sandbox, &command).await? {
            return Err("命令不被允许".into());
        }

        // 创建沙箱化进程
        let process_id = uuid::Uuid::new_v4().to_string();
        let sandboxed_process = SandboxedProcess {
            id: process_id.clone(),
            sandbox_id: sandbox_id.to_string(),
            process_id: 0, // 实际实现中应该获取真实的进程 ID
            command: command.clone(),
            args: args.clone(),
            start_time: Instant::now(),
            status: ProcessStatus::Starting,
            resource_usage: ResourceUsage {
                memory_mb: 0,
                cpu_percent: 0.0,
                file_descriptors: 0,
                disk_usage_mb: 0,
                network_bandwidth_mbps: 0.0,
                last_updated: Instant::now(),
            },
            security_violations: Vec::new(),
        };

        let mut active_processes = self.active_processes.lock().await;
        active_processes.insert(process_id.clone(), sandboxed_process);

        // 启动进程监控
        self.start_process_monitoring(&process_id).await?;

        Ok(process_id)
    }

    async fn is_command_allowed(
        &self,
        sandbox: &SandboxConfig,
        command: &str,
    ) -> Result<bool, Box<dyn std::error::Error>> {
        // 检查命令是否在允许列表中
        let allowed = sandbox.allowed_system_calls.is_empty() ||
            sandbox.allowed_system_calls.contains(&command.to_string());

        // 检查命令是否在拒绝列表中
        let denied = sandbox.denied_system_calls.contains(&command.to_string());

        Ok(allowed && !denied)
    }

    async fn start_process_monitoring(
        &self,
        process_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let process_id_clone = process_id.to_string();
        let sandbox_clone = self.clone();

        tokio::spawn(async move {
            if let Err(e) = sandbox_clone.monitor_process(&process_id_clone).await {
                eprintln!("进程监控失败: {}", e);
            }
        });

        Ok(())
    }

    async fn monitor_process(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut interval = tokio::time::interval(Duration::from_millis(100));

        loop {
            interval.tick().await;

            let mut active_processes = self.active_processes.lock().await;
            let process = active_processes.get_mut(process_id);

            if let Some(process) = process {
                // 检查执行超时
                if process.start_time.elapsed() > self.get_sandbox_config(&process.sandbox_id).await?.execution_timeout {
                    self.handle_security_violation(
                        process_id,
                        ViolationType::ExecutionTimeout,
                        "进程执行超时".to_string(),
                        ViolationSeverity::High,
                    ).await?;

                    process.status = ProcessStatus::Terminated;
                    break;
                }

                // 检查资源使用
                if let Err(e) = self.check_resource_limits(process).await {
                    self.handle_security_violation(
                        process_id,
                        ViolationType::ResourceLimitExceeded,
                        e.to_string(),
                        ViolationSeverity::Medium,
                    ).await?;
                }

                // 检查安全策略
                if let Err(e) = self.check_security_policies(process).await {
                    self.handle_security_violation(
                        process_id,
                        ViolationType::UnauthorizedSystemCall,
                        e.to_string(),
                        ViolationSeverity::Critical,
                    ).await?;
                }

                // 如果进程已终止，停止监控
                if matches!(process.status, ProcessStatus::Terminated | ProcessStatus::Failed) {
                    break;
                }
            } else {
                break;
            }
        }

        Ok(())
    }

    async fn get_sandbox_config(&self, sandbox_id: &str) -> Result<SandboxConfig, Box<dyn std::error::Error>> {
        let sandboxes = self.sandboxes.lock().await;
        sandboxes.get(sandbox_id).cloned().ok_or("沙箱未找到".into())
    }

    async fn check_resource_limits(
        &self,
        process: &mut SandboxedProcess,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let sandbox = self.get_sandbox_config(&process.sandbox_id).await?;

        if process.resource_usage.memory_mb > sandbox.resource_limits.max_memory_mb {
            return Err("内存使用超限".into());
        }

        if process.resource_usage.cpu_percent > sandbox.resource_limits.max_cpu_percent {
            return Err("CPU 使用超限".into());
        }

        if process.resource_usage.file_descriptors > sandbox.resource_limits.max_file_descriptors {
            return Err("文件描述符超限".into());
        }

        Ok(())
    }

    async fn check_security_policies(
        &self,
        process: &mut SandboxedProcess,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let policies = self.security_policies.lock().await;

        for policy in policies.iter() {
            if self.policy_condition_matches(process, &policy.condition) {
                self.execute_security_action(process, &policy.action).await?;
            }
        }

        Ok(())
    }

    fn policy_condition_matches(
        &self,
        process: &SandboxedProcess,
        condition: &SecurityCondition,
    ) -> bool {
        match condition {
            SecurityCondition::SystemCallViolation => {
                process.security_violations.iter().any(|v| matches!(v.violation_type, ViolationType::UnauthorizedSystemCall))
            }
            SecurityCondition::FileAccessViolation => {
                process.security_violations.iter().any(|v| matches!(v.violation_type, ViolationType::FileAccessViolation))
            }
            SecurityCondition::NetworkAccessViolation => {
                process.security_violations.iter().any(|v| matches!(v.violation_type, ViolationType::NetworkAccessViolation))
            }
            SecurityCondition::ResourceViolation => {
                process.security_violations.iter().any(|v| matches!(v.violation_type, ViolationType::ResourceLimitExceeded))
            }
            SecurityCondition::TimeoutViolation => {
                process.security_violations.iter().any(|v| matches!(v.violation_type, ViolationType::ExecutionTimeout))
            }
        }
    }

    async fn execute_security_action(
        &self,
        process: &mut SandboxedProcess,
        action: &SecurityAction,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match action {
            SecurityAction::TerminateProcess => {
                process.status = ProcessStatus::Terminated;
                println!("终止进程 {}", process.id);
            }
            SecurityAction::SuspendProcess => {
                process.status = ProcessStatus::Suspended;
                println!("暂停进程 {}", process.id);
            }
            SecurityAction::LogViolation => {
                println!("记录安全违规: 进程 {}", process.id);
            }
            SecurityAction::NotifySecurity => {
                println!("通知安全团队: 进程 {} 违规", process.id);
            }
            SecurityAction::QuarantineProcess => {
                println!("隔离进程 {}", process.id);
            }
            SecurityAction::BlockAccess => {
                println!("阻止进程 {} 的访问", process.id);
            }
        }

        Ok(())
    }

    async fn handle_security_violation(
        &self,
        process_id: &str,
        violation_type: ViolationType,
        description: String,
        severity: ViolationSeverity,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let violation = SecurityViolation {
            id: uuid::Uuid::new_v4().to_string(),
            violation_type,
            description,
            severity,
            timestamp: Instant::now(),
            action_taken: None,
        };

        let mut active_processes = self.active_processes.lock().await;
        if let Some(process) = active_processes.get_mut(process_id) {
            process.security_violations.push(violation);
        }

        Ok(())
    }

    pub async fn add_security_policy(
        &self,
        policy: SecurityPolicy,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut policies = self.security_policies.lock().await;
        policies.push(policy);
        Ok(())
    }

    pub async fn get_sandboxed_process(&self, process_id: &str) -> Option<SandboxedProcess> {
        let active_processes = self.active_processes.lock().await;
        active_processes.get(process_id).cloned()
    }

    pub async fn get_security_violations(&self, process_id: &str) -> Vec<SecurityViolation> {
        let active_processes = self.active_processes.lock().await;
        active_processes.get(process_id)
            .map(|p| p.security_violations.clone())
            .unwrap_or_default()
    }
}

impl Clone for ProcessSandbox {
    fn clone(&self) -> Self {
        Self {
            sandboxes: self.sandboxes.clone(),
            active_processes: self.active_processes.clone(),
            security_policies: self.security_policies.clone(),
        }
    }
}
```

### 2.2 容器化执行

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub struct ContainerManager {
    containers: Arc<Mutex<HashMap<String, Container>>>,
    images: Arc<Mutex<HashMap<String, ContainerImage>>>,
    networks: Arc<Mutex<HashMap<String, ContainerNetwork>>>,
}

#[derive(Debug, Clone)]
pub struct Container {
    pub id: String,
    pub name: String,
    pub image_id: String,
    pub status: ContainerStatus,
    pub config: ContainerConfig,
    pub resource_usage: ResourceUsage,
    pub created_at: Instant,
    pub started_at: Option<Instant>,
    pub stopped_at: Option<Instant>,
}

#[derive(Debug, Clone)]
pub enum ContainerStatus {
    Created,
    Running,
    Paused,
    Stopped,
    Failed,
    Removing,
}

#[derive(Debug, Clone)]
pub struct ContainerConfig {
    pub image: String,
    pub command: Vec<String>,
    pub env_vars: HashMap<String, String>,
    pub working_dir: String,
    pub user: String,
    pub resource_limits: ResourceLimits,
    pub network_mode: NetworkMode,
    pub volumes: Vec<VolumeMount>,
    pub ports: Vec<PortMapping>,
    pub security_context: SecurityContext,
}

#[derive(Debug, Clone)]
pub enum NetworkMode {
    Bridge,
    Host,
    None,
    Custom(String),
}

#[derive(Debug, Clone)]
pub struct VolumeMount {
    pub source: String,
    pub destination: String,
    pub read_only: bool,
}

#[derive(Debug, Clone)]
pub struct PortMapping {
    pub container_port: u16,
    pub host_port: u16,
    pub protocol: String,
}

#[derive(Debug, Clone)]
pub struct SecurityContext {
    pub run_as_user: Option<u32>,
    pub run_as_group: Option<u32>,
    pub read_only_root_filesystem: bool,
    pub allow_privilege_escalation: bool,
    pub capabilities: Vec<String>,
    pub seccomp_profile: Option<String>,
}

#[derive(Debug, Clone)]
pub struct ContainerImage {
    pub id: String,
    pub name: String,
    pub tag: String,
    pub size: u64,
    pub layers: Vec<String>,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub struct ContainerNetwork {
    pub id: String,
    pub name: String,
    pub driver: String,
    pub subnet: String,
    pub gateway: String,
    pub containers: Vec<String>,
}

impl ContainerManager {
    pub fn new() -> Self {
        Self {
            containers: Arc::new(Mutex::new(HashMap::new())),
            images: Arc::new(Mutex::new(HashMap::new())),
            networks: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub async fn create_container(
        &self,
        name: String,
        config: ContainerConfig,
    ) -> Result<String, Box<dyn std::error::Error>> {
        let container_id = uuid::Uuid::new_v4().to_string();

        let container = Container {
            id: container_id.clone(),
            name: name.clone(),
            image_id: config.image.clone(),
            status: ContainerStatus::Created,
            config,
            resource_usage: ResourceUsage {
                memory_mb: 0,
                cpu_percent: 0.0,
                file_descriptors: 0,
                disk_usage_mb: 0,
                network_bandwidth_mbps: 0.0,
                last_updated: Instant::now(),
            },
            created_at: Instant::now(),
            started_at: None,
            stopped_at: None,
        };

        let mut containers = self.containers.lock().await;
        containers.insert(container_id.clone(), container);

        Ok(container_id)
    }

    pub async fn start_container(
        &self,
        container_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut containers = self.containers.lock().await;
        let container = containers.get_mut(container_id).ok_or("容器未找到")?;

        if !matches!(container.status, ContainerStatus::Created | ContainerStatus::Stopped) {
            return Err("容器状态不允许启动".into());
        }

        container.status = ContainerStatus::Running;
        container.started_at = Some(Instant::now());

        // 启动容器监控
        self.start_container_monitoring(container_id).await?;

        Ok(())
    }

    pub async fn stop_container(
        &self,
        container_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut containers = self.containers.lock().await;
        let container = containers.get_mut(container_id).ok_or("容器未找到")?;

        if !matches!(container.status, ContainerStatus::Running | ContainerStatus::Paused) {
            return Err("容器状态不允许停止".into());
        }

        container.status = ContainerStatus::Stopped;
        container.stopped_at = Some(Instant::now());

        Ok(())
    }

    pub async fn pause_container(
        &self,
        container_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut containers = self.containers.lock().await;
        let container = containers.get_mut(container_id).ok_or("容器未找到")?;

        if !matches!(container.status, ContainerStatus::Running) {
            return Err("容器状态不允许暂停".into());
        }

        container.status = ContainerStatus::Paused;

        Ok(())
    }

    pub async fn unpause_container(
        &self,
        container_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut containers = self.containers.lock().await;
        let container = containers.get_mut(container_id).ok_or("容器未找到")?;

        if !matches!(container.status, ContainerStatus::Paused) {
            return Err("容器状态不允许恢复".into());
        }

        container.status = ContainerStatus::Running;

        Ok(())
    }

    pub async fn remove_container(
        &self,
        container_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut containers = self.containers.lock().await;
        let container = containers.get_mut(container_id).ok_or("容器未找到")?;

        if matches!(container.status, ContainerStatus::Running) {
            return Err("运行中的容器不能删除".into());
        }

        container.status = ContainerStatus::Removing;
        containers.remove(container_id);

        Ok(())
    }

    async fn start_container_monitoring(
        &self,
        container_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let container_id_clone = container_id.to_string();
        let manager_clone = self.clone();

        tokio::spawn(async move {
            if let Err(e) = manager_clone.monitor_container(&container_id_clone).await {
                eprintln!("容器监控失败: {}", e);
            }
        });

        Ok(())
    }

    async fn monitor_container(&self, container_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut interval = tokio::time::interval(Duration::from_secs(1));

        loop {
            interval.tick().await;

            let mut containers = self.containers.lock().await;
            let container = containers.get_mut(container_id);

            if let Some(container) = container {
                // 更新资源使用情况
                self.update_container_resource_usage(container).await?;

                // 检查资源限制
                if let Err(e) = self.check_container_resource_limits(container).await {
                    println!("容器 {} 资源限制违规: {}", container_id, e);
                    container.status = ContainerStatus::Failed;
                    break;
                }

                // 如果容器已停止，停止监控
                if matches!(container.status, ContainerStatus::Stopped | ContainerStatus::Failed | ContainerStatus::Removing) {
                    break;
                }
            } else {
                break;
            }
        }

        Ok(())
    }

    async fn update_container_resource_usage(
        &self,
        container: &mut Container,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 实际实现中应该读取容器的真实资源使用情况
        // 这里使用模拟数据
        container.resource_usage.memory_mb = rand::random::<u64>() % 1000;
        container.resource_usage.cpu_percent = rand::random::<f64>() * 100.0;
        container.resource_usage.last_updated = Instant::now();

        Ok(())
    }

    async fn check_container_resource_limits(
        &self,
        container: &Container,
    ) -> Result<(), Box<dyn std::error::Error>> {
        if container.resource_usage.memory_mb > container.config.resource_limits.max_memory_mb {
            return Err("内存使用超限".into());
        }

        if container.resource_usage.cpu_percent > container.config.resource_limits.max_cpu_percent {
            return Err("CPU 使用超限".into());
        }

        Ok(())
    }

    pub async fn get_container(&self, container_id: &str) -> Option<Container> {
        let containers = self.containers.lock().await;
        containers.get(container_id).cloned()
    }

    pub async fn list_containers(&self) -> Vec<Container> {
        let containers = self.containers.lock().await;
        containers.values().cloned().collect()
    }

    pub async fn get_container_stats(&self, container_id: &str) -> Option<ContainerStats> {
        let containers = self.containers.lock().await;
        let container = containers.get(container_id)?;

        Some(ContainerStats {
            id: container.id.clone(),
            name: container.name.clone(),
            status: container.status.clone(),
            resource_usage: container.resource_usage.clone(),
            uptime: container.started_at.map(|start| Instant::now().duration_since(start)).unwrap_or_default(),
            created_at: container.created_at,
        })
    }
}

#[derive(Debug)]
pub struct ContainerStats {
    pub id: String,
    pub name: String,
    pub status: ContainerStatus,
    pub resource_usage: ResourceUsage,
    pub uptime: Duration,
    pub created_at: Instant,
}

impl Clone for ContainerManager {
    fn clone(&self) -> Self {
        Self {
            containers: self.containers.clone(),
            images: self.images.clone(),
            networks: self.networks.clone(),
        }
    }
}
```

## 3. 安全审计

### 3.1 安全事件监控

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub struct SecurityEventMonitor {
    events: Arc<Mutex<Vec<SecurityEvent>>>,
    rules: Arc<Mutex<Vec<SecurityRule>>>,
    alerts: Arc<Mutex<Vec<SecurityAlert>>>,
    thresholds: Arc<Mutex<SecurityThresholds>>,
}

#[derive(Debug, Clone)]
pub struct SecurityEvent {
    pub id: String,
    pub event_type: SecurityEventType,
    pub severity: EventSeverity,
    pub source: String,
    pub target: String,
    pub description: String,
    pub metadata: HashMap<String, String>,
    pub timestamp: Instant,
    pub processed: bool,
}

#[derive(Debug, Clone)]
pub enum SecurityEventType {
    ProcessCreation,
    ProcessTermination,
    FileAccess,
    NetworkConnection,
    SystemCall,
    PrivilegeEscalation,
    ResourceViolation,
    AuthenticationFailure,
    AuthorizationFailure,
    DataExfiltration,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum EventSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

#[derive(Debug, Clone)]
pub struct SecurityRule {
    pub id: String,
    pub name: String,
    pub condition: RuleCondition,
    pub action: RuleAction,
    pub enabled: bool,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum RuleCondition {
    EventType(SecurityEventType),
    Severity(EventSeverity),
    Source(String),
    Target(String),
    Frequency(u32, Duration),
    Pattern(String),
}

#[derive(Debug, Clone)]
pub enum RuleAction {
    Log,
    Alert,
    Block,
    Quarantine,
    Notify,
    Escalate,
}

#[derive(Debug, Clone)]
pub struct SecurityAlert {
    pub id: String,
    pub rule_id: String,
    pub event_id: String,
    pub severity: AlertSeverity,
    pub title: String,
    pub description: String,
    pub timestamp: Instant,
    pub acknowledged: bool,
    pub resolved: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AlertSeverity {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct SecurityThresholds {
    pub max_events_per_minute: u32,
    pub max_failed_attempts: u32,
    pub max_resource_violations: u32,
    pub alert_cooldown: Duration,
}

impl SecurityEventMonitor {
    pub fn new() -> Self {
        Self {
            events: Arc::new(Mutex::new(Vec::new())),
            rules: Arc::new(Mutex::new(Vec::new())),
            alerts: Arc::new(Mutex::new(Vec::new())),
            thresholds: Arc::new(Mutex::new(SecurityThresholds {
                max_events_per_minute: 1000,
                max_failed_attempts: 10,
                max_resource_violations: 5,
                alert_cooldown: Duration::from_secs(300),
            })),
        }
    }

    pub async fn log_event(
        &self,
        event_type: SecurityEventType,
        severity: EventSeverity,
        source: String,
        target: String,
        description: String,
        metadata: HashMap<String, String>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let event = SecurityEvent {
            id: uuid::Uuid::new_v4().to_string(),
            event_type,
            severity,
            source,
            target,
            description,
            metadata,
            timestamp: Instant::now(),
            processed: false,
        };

        let mut events = self.events.lock().await;
        events.push(event.clone());

        // 保持事件列表大小限制
        if events.len() > 100000 {
            events.remove(0);
        }

        // 处理事件
        self.process_event(&event).await?;

        Ok(())
    }

    async fn process_event(
        &self,
        event: &SecurityEvent,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let rules = self.rules.lock().await;

        for rule in rules.iter() {
            if rule.enabled && self.rule_matches(event, rule) {
                self.execute_rule_action(event, rule).await?;
            }
        }

        Ok(())
    }

    fn rule_matches(&self, event: &SecurityEvent, rule: &SecurityRule) -> bool {
        match &rule.condition {
            RuleCondition::EventType(event_type) => {
                std::mem::discriminant(&event.event_type) == std::mem::discriminant(event_type)
            }
            RuleCondition::Severity(severity) => {
                event.severity >= *severity
            }
            RuleCondition::Source(source) => {
                event.source.contains(source)
            }
            RuleCondition::Target(target) => {
                event.target.contains(target)
            }
            RuleCondition::Frequency(count, duration) => {
                self.check_frequency_condition(event, *count, *duration)
            }
            RuleCondition::Pattern(pattern) => {
                event.description.contains(pattern) || event.source.contains(pattern)
            }
        }
    }

    fn check_frequency_condition(
        &self,
        event: &SecurityEvent,
        count: u32,
        duration: Duration,
    ) -> bool {
        // 实际实现中应该检查事件频率
        // 这里使用简化实现
        false
    }

    async fn execute_rule_action(
        &self,
        event: &SecurityEvent,
        rule: &SecurityRule,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match &rule.action {
            RuleAction::Log => {
                println!("安全事件: {} - {}", event.event_type, event.description);
            }
            RuleAction::Alert => {
                self.create_alert(event, rule).await?;
            }
            RuleAction::Block => {
                println!("阻止事件: {}", event.id);
            }
            RuleAction::Quarantine => {
                println!("隔离事件: {}", event.id);
            }
            RuleAction::Notify => {
                println!("通知管理员: {}", event.description);
            }
            RuleAction::Escalate => {
                println!("升级事件: {}", event.id);
            }
        }

        Ok(())
    }

    async fn create_alert(
        &self,
        event: &SecurityEvent,
        rule: &SecurityRule,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let alert = SecurityAlert {
            id: uuid::Uuid::new_v4().to_string(),
            rule_id: rule.id.clone(),
            event_id: event.id.clone(),
            severity: match event.severity {
                EventSeverity::Info => AlertSeverity::Low,
                EventSeverity::Warning => AlertSeverity::Medium,
                EventSeverity::Error => AlertSeverity::High,
                EventSeverity::Critical => AlertSeverity::Critical,
            },
            title: format!("安全规则触发: {}", rule.name),
            description: event.description.clone(),
            timestamp: Instant::now(),
            acknowledged: false,
            resolved: false,
        };

        let mut alerts = self.alerts.lock().await;
        alerts.push(alert);

        Ok(())
    }

    pub async fn add_security_rule(
        &self,
        rule: SecurityRule,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut rules = self.rules.lock().await;
        rules.push(rule);
        Ok(())
    }

    pub async fn get_security_events(
        &self,
        limit: Option<usize>,
        filter: Option<EventFilter>,
    ) -> Vec<SecurityEvent> {
        let events = self.events.lock().await;

        let mut filtered_events: Vec<SecurityEvent> = events.iter()
            .filter(|event| {
                if let Some(filter) = &filter {
                    self.event_matches_filter(event, filter)
                } else {
                    true
                }
            })
            .cloned()
            .collect();

        filtered_events.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));

        if let Some(limit) = limit {
            filtered_events.truncate(limit);
        }

        filtered_events
    }

    fn event_matches_filter(&self, event: &SecurityEvent, filter: &EventFilter) -> bool {
        if let Some(event_type) = &filter.event_type {
            if std::mem::discriminant(&event.event_type) != std::mem::discriminant(event_type) {
                return false;
            }
        }

        if let Some(severity) = &filter.severity {
            if event.severity < *severity {
                return false;
            }
        }

        if let Some(source) = &filter.source {
            if !event.source.contains(source) {
                return false;
            }
        }

        if let Some(target) = &filter.target {
            if !event.target.contains(target) {
                return false;
            }
        }

        if let Some(start_time) = &filter.start_time {
            if event.timestamp < *start_time {
                return false;
            }
        }

        if let Some(end_time) = &filter.end_time {
            if event.timestamp > *end_time {
                return false;
            }
        }

        true
    }

    pub async fn get_security_alerts(
        &self,
        limit: Option<usize>,
    ) -> Vec<SecurityAlert> {
        let alerts = self.alerts.lock().await;

        let mut sorted_alerts = alerts.clone();
        sorted_alerts.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));

        if let Some(limit) = limit {
            sorted_alerts.truncate(limit);
        }

        sorted_alerts
    }

    pub async fn acknowledge_alert(
        &self,
        alert_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut alerts = self.alerts.lock().await;

        if let Some(alert) = alerts.iter_mut().find(|a| a.id == alert_id) {
            alert.acknowledged = true;
            Ok(())
        } else {
            Err("警报未找到".into())
        }
    }

    pub async fn resolve_alert(
        &self,
        alert_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut alerts = self.alerts.lock().await;

        if let Some(alert) = alerts.iter_mut().find(|a| a.id == alert_id) {
            alert.resolved = true;
            Ok(())
        } else {
            Err("警报未找到".into())
        }
    }
}

#[derive(Debug, Clone)]
pub struct EventFilter {
    pub event_type: Option<SecurityEventType>,
    pub severity: Option<EventSeverity>,
    pub source: Option<String>,
    pub target: Option<String>,
    pub start_time: Option<Instant>,
    pub end_time: Option<Instant>,
}
```

## 4. 威胁防护

### 4.1 入侵检测

```rust
use std::sync::Arc;
use tokio::sync::Mutex;
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub struct IntrusionDetectionSystem {
    detectors: Arc<Mutex<Vec<Box<dyn ThreatDetector + Send + Sync>>>>,
    threats: Arc<Mutex<Vec<Threat>>>,
    mitigation_strategies: Arc<Mutex<Vec<MitigationStrategy>>>,
    whitelist: Arc<Mutex<Vec<String>>>,
    blacklist: Arc<Mutex<Vec<String>>>,
}

pub trait ThreatDetector {
    fn detect(&self, event: &SecurityEvent) -> Option<Threat>;
    fn get_name(&self) -> &str;
    fn get_confidence(&self) -> f64;
}

#[derive(Debug, Clone)]
pub struct Threat {
    pub id: String,
    pub threat_type: ThreatType,
    pub severity: ThreatSeverity,
    pub confidence: f64,
    pub source: String,
    pub target: String,
    pub description: String,
    pub indicators: Vec<ThreatIndicator>,
    pub timestamp: Instant,
    pub detected_by: String,
    pub mitigated: bool,
}

#[derive(Debug, Clone)]
pub enum ThreatType {
    Malware,
    Exploit,
    DataBreach,
    PrivilegeEscalation,
    DenialOfService,
    Phishing,
    SocialEngineering,
    InsiderThreat,
    AdvancedPersistentThreat,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ThreatSeverity {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct ThreatIndicator {
    pub indicator_type: IndicatorType,
    pub value: String,
    pub confidence: f64,
    pub source: String,
}

#[derive(Debug, Clone)]
pub enum IndicatorType {
    IPAddress,
    Domain,
    FileHash,
    ProcessName,
    Command,
    RegistryKey,
    NetworkTraffic,
    UserBehavior,
}

#[derive(Debug, Clone)]
pub struct MitigationStrategy {
    pub id: String,
    pub name: String,
    pub threat_type: ThreatType,
    pub action: MitigationAction,
    pub automated: bool,
    pub effectiveness: f64,
}

#[derive(Debug, Clone)]
pub enum MitigationAction {
    BlockIP,
    QuarantineFile,
    TerminateProcess,
    DisableUser,
    IsolateNetwork,
    NotifyAdmin,
    EscalateToSecurity,
    CollectEvidence,
}

impl IntrusionDetectionSystem {
    pub fn new() -> Self {
        Self {
            detectors: Arc::new(Mutex::new(Vec::new())),
            threats: Arc::new(Mutex::new(Vec::new())),
            mitigation_strategies: Arc::new(Mutex::new(Vec::new())),
            whitelist: Arc::new(Mutex::new(Vec::new())),
            blacklist: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn add_detector(
        &self,
        detector: Box<dyn ThreatDetector + Send + Sync>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut detectors = self.detectors.lock().await;
        detectors.push(detector);
        Ok(())
    }

    pub async fn analyze_event(
        &self,
        event: &SecurityEvent,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 检查白名单
        if self.is_whitelisted(&event.source).await {
            return Ok(());
        }

        // 检查黑名单
        if self.is_blacklisted(&event.source).await {
            self.create_threat(event, ThreatType::Malware, ThreatSeverity::High).await?;
            return Ok(());
        }

        // 运行威胁检测器
        let detectors = self.detectors.lock().await;
        for detector in detectors.iter() {
            if let Some(threat) = detector.detect(event) {
                self.handle_threat(threat).await?;
            }
        }

        Ok(())
    }

    async fn is_whitelisted(&self, source: &str) -> bool {
        let whitelist = self.whitelist.lock().await;
        whitelist.contains(&source.to_string())
    }

    async fn is_blacklisted(&self, source: &str) -> bool {
        let blacklist = self.blacklist.lock().await;
        blacklist.contains(&source.to_string())
    }

    async fn create_threat(
        &self,
        event: &SecurityEvent,
        threat_type: ThreatType,
        severity: ThreatSeverity,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let threat = Threat {
            id: uuid::Uuid::new_v4().to_string(),
            threat_type,
            severity,
            confidence: 0.8,
            source: event.source.clone(),
            target: event.target.clone(),
            description: event.description.clone(),
            indicators: Vec::new(),
            timestamp: Instant::now(),
            detected_by: "IDS".to_string(),
            mitigated: false,
        };

        self.handle_threat(threat).await?;
        Ok(())
    }

    async fn handle_threat(
        &self,
        threat: Threat,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut threats = self.threats.lock().await;
        threats.push(threat.clone());

        // 保持威胁列表大小限制
        if threats.len() > 10000 {
            threats.remove(0);
        }

        // 查找缓解策略
        let strategies = self.mitigation_strategies.lock().await;
        for strategy in strategies.iter() {
            if std::mem::discriminant(&strategy.threat_type) == std::mem::discriminant(&threat.threat_type) {
                if strategy.automated {
                    self.execute_mitigation_action(&threat, &strategy.action).await?;
                } else {
                    println!("需要手动缓解威胁: {}", threat.id);
                }
            }
        }

        Ok(())
    }

    async fn execute_mitigation_action(
        &self,
        threat: &Threat,
        action: &MitigationAction,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match action {
            MitigationAction::BlockIP => {
                println!("阻止 IP: {}", threat.source);
            }
            MitigationAction::QuarantineFile => {
                println!("隔离文件: {}", threat.target);
            }
            MitigationAction::TerminateProcess => {
                println!("终止进程: {}", threat.target);
            }
            MitigationAction::DisableUser => {
                println!("禁用用户: {}", threat.source);
            }
            MitigationAction::IsolateNetwork => {
                println!("隔离网络: {}", threat.source);
            }
            MitigationAction::NotifyAdmin => {
                println!("通知管理员: 威胁 {}", threat.id);
            }
            MitigationAction::EscalateToSecurity => {
                println!("升级到安全团队: 威胁 {}", threat.id);
            }
            MitigationAction::CollectEvidence => {
                println!("收集证据: 威胁 {}", threat.id);
            }
        }

        Ok(())
    }

    pub async fn add_mitigation_strategy(
        &self,
        strategy: MitigationStrategy,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut strategies = self.mitigation_strategies.lock().await;
        strategies.push(strategy);
        Ok(())
    }

    pub async fn add_to_whitelist(&self, item: String) -> Result<(), Box<dyn std::error::Error>> {
        let mut whitelist = self.whitelist.lock().await;
        whitelist.push(item);
        Ok(())
    }

    pub async fn add_to_blacklist(&self, item: String) -> Result<(), Box<dyn std::error::Error>> {
        let mut blacklist = self.blacklist.lock().await;
        blacklist.push(item);
        Ok(())
    }

    pub async fn get_threats(
        &self,
        limit: Option<usize>,
    ) -> Vec<Threat> {
        let threats = self.threats.lock().await;

        let mut sorted_threats = threats.clone();
        sorted_threats.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));

        if let Some(limit) = limit {
            sorted_threats.truncate(limit);
        }

        sorted_threats
    }

    pub async fn get_threat_summary(&self) -> ThreatSummary {
        let threats = self.threats.lock().await;

        let mut summary = ThreatSummary {
            total_threats: threats.len(),
            threats_by_type: HashMap::new(),
            threats_by_severity: HashMap::new(),
            mitigated_threats: 0,
            active_threats: 0,
        };

        for threat in threats.iter() {
            // 按类型统计
            let type_key = format!("{:?}", threat.threat_type);
            *summary.threats_by_type.entry(type_key).or_insert(0) += 1;

            // 按严重程度统计
            let severity_key = format!("{:?}", threat.severity);
            *summary.threats_by_severity.entry(severity_key).or_insert(0) += 1;

            // 统计缓解状态
            if threat.mitigated {
                summary.mitigated_threats += 1;
            } else {
                summary.active_threats += 1;
            }
        }

        summary
    }
}

#[derive(Debug)]
pub struct ThreatSummary {
    pub total_threats: usize,
    pub threats_by_type: HashMap<String, usize>,
    pub threats_by_severity: HashMap<String, usize>,
    pub mitigated_threats: usize,
    pub active_threats: usize,
}

pub struct MalwareDetector;

impl ThreatDetector for MalwareDetector {
    fn detect(&self, event: &SecurityEvent) -> Option<Threat> {
        // 简化的恶意软件检测逻辑
        if event.description.contains("malware") || event.description.contains("virus") {
            Some(Threat {
                id: uuid::Uuid::new_v4().to_string(),
                threat_type: ThreatType::Malware,
                severity: ThreatSeverity::High,
                confidence: 0.9,
                source: event.source.clone(),
                target: event.target.clone(),
                description: event.description.clone(),
                indicators: Vec::new(),
                timestamp: Instant::now(),
                detected_by: "MalwareDetector".to_string(),
                mitigated: false,
            })
        } else {
            None
        }
    }

    fn get_name(&self) -> &str {
        "MalwareDetector"
    }

    fn get_confidence(&self) -> f64 {
        0.9
    }
}

pub struct ExploitDetector;

impl ThreatDetector for ExploitDetector {
    fn detect(&self, event: &SecurityEvent) -> Option<Threat> {
        // 简化的漏洞利用检测逻辑
        if event.description.contains("exploit") || event.description.contains("buffer overflow") {
            Some(Threat {
                id: uuid::Uuid::new_v4().to_string(),
                threat_type: ThreatType::Exploit,
                severity: ThreatSeverity::Critical,
                confidence: 0.8,
                source: event.source.clone(),
                target: event.target.clone(),
                description: event.description.clone(),
                indicators: Vec::new(),
                timestamp: Instant::now(),
                detected_by: "ExploitDetector".to_string(),
                mitigated: false,
            })
        } else {
            None
        }
    }

    fn get_name(&self) -> &str {
        "ExploitDetector"
    }

    fn get_confidence(&self) -> f64 {
        0.8
    }
}
```

## 6. 现代安全库集成

### 6.1 Tokio 安全特性

Tokio 1.0+ 提供了强大的异步安全特性：

```rust
use tokio::process::{Command, Child};
use tokio::sync::{Mutex, RwLock};
use tokio::time::{timeout, Duration};
use std::collections::HashMap;

// Tokio 安全进程管理器
pub struct TokioSecureProcessManager {
    active_processes: Arc<RwLock<HashMap<String, TokioSecureProcess>>>,
    security_policies: Arc<Mutex<Vec<SecurityPolicy>>>,
    resource_monitor: Arc<Mutex<ResourceMonitor>>,
}

#[derive(Debug, Clone)]
pub struct TokioSecureProcess {
    pub id: String,
    pub child: Option<Child>,
    pub security_context: SecurityContext,
    pub resource_limits: ResourceLimits,
    pub created_at: std::time::Instant,
    pub status: ProcessStatus,
}

impl TokioSecureProcessManager {
    pub fn new() -> Self {
        Self {
            active_processes: Arc::new(RwLock::new(HashMap::new())),
            security_policies: Arc::new(Mutex::new(Vec::new())),
            resource_monitor: Arc::new(Mutex::new(ResourceMonitor::new())),
        }
    }

    // 使用 Tokio 执行安全进程
    pub async fn execute_secure_process(
        &self,
        security_context: SecurityContext,
        command: String,
        args: Vec<String>,
    ) -> Result<String, SecurityError> {
        // 安全检查
        self.validate_security_context(&security_context).await?;
        self.validate_command(&command, &args).await?;

        // 创建 Tokio 进程
        let mut child = Command::new(&command)
            .args(&args)
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .map_err(|e| SecurityError::ProcessSpawnFailed(e.to_string()))?;

        let process_id = uuid::Uuid::new_v4().to_string();
        let secure_process = TokioSecureProcess {
            id: process_id.clone(),
            child: Some(child),
            security_context: security_context.clone(),
            resource_limits: security_context.resource_limits.clone(),
            created_at: std::time::Instant::now(),
            status: ProcessStatus::Starting,
        };

        // 添加到活跃进程列表
        let mut active_processes = self.active_processes.write().await;
        active_processes.insert(process_id.clone(), secure_process);

        // 启动监控任务
        self.start_process_monitoring(&process_id).await?;

        Ok(process_id)
    }

    // 异步进程监控
    async fn start_process_monitoring(&self, process_id: &str) -> Result<(), SecurityError> {
        let process_id = process_id.to_string();
        let manager = self.clone();

        tokio::spawn(async move {
            if let Err(e) = manager.monitor_process(&process_id).await {
                eprintln!("进程监控失败: {}", e);
            }
        });

        Ok(())
    }

    async fn monitor_process(&self, process_id: &str) -> Result<(), SecurityError> {
        let mut interval = tokio::time::interval(Duration::from_millis(100));

        loop {
            interval.tick().await;

            let mut active_processes = self.active_processes.write().await;
            let process = active_processes.get_mut(process_id);

            if let Some(process) = process {
                // 检查进程状态
                if let Some(child) = &mut process.child {
                    match child.try_wait() {
                        Ok(Some(status)) => {
                            process.status = if status.success() {
                                ProcessStatus::Terminated
                            } else {
                                ProcessStatus::Failed
                            };
                            process.child = None;
                            break;
                        }
                        Ok(None) => {
                            process.status = ProcessStatus::Running;
                        }
                        Err(e) => {
                            eprintln!("检查进程状态失败: {}", e);
                            process.status = ProcessStatus::Failed;
                            break;
                        }
                    }
                }

                // 检查资源限制
                if let Err(e) = self.check_resource_limits(process).await {
                    self.handle_resource_violation(process_id, &e).await?;
                }

                // 检查安全策略
                if let Err(e) = self.check_security_policies(process).await {
                    self.handle_security_violation(process_id, &e).await?;
                }
            } else {
                break;
            }
        }

        Ok(())
    }

    async fn validate_security_context(
        &self,
        context: &SecurityContext,
    ) -> Result<(), SecurityError> {
        // 验证用户权限
        if context.user_id.is_empty() {
            return Err(SecurityError::InsufficientPermissions);
        }

        // 验证资源限制
        if context.resource_limits.max_memory_mb == 0 {
            return Err(SecurityError::ResourceLimitViolation);
        }

        Ok(())
    }

    async fn validate_command(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<(), SecurityError> {
        // 检查命令安全性
        if command.contains("..") || command.contains("/") {
            return Err(SecurityError::CommandForbidden);
        }

        // 检查参数安全性
        for arg in args {
            if arg.contains("..") || arg.contains("rm") || arg.contains("sudo") {
                return Err(SecurityError::CommandForbidden);
            }
        }

        Ok(())
    }

    async fn check_resource_limits(
        &self,
        process: &TokioSecureProcess,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 资源限制检查逻辑
        Ok(())
    }

    async fn check_security_policies(
        &self,
        process: &TokioSecureProcess,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 安全策略检查逻辑
        Ok(())
    }

    async fn handle_resource_violation(
        &self,
        process_id: &str,
        error: &Box<dyn std::error::Error>,
    ) -> Result<(), SecurityError> {
        println!("资源违规: 进程 {} - {}", process_id, error);
        Ok(())
    }

    async fn handle_security_violation(
        &self,
        process_id: &str,
        error: &Box<dyn std::error::Error>,
    ) -> Result<(), SecurityError> {
        println!("安全违规: 进程 {} - {}", process_id, error);
        Ok(())
    }
}

impl Clone for TokioSecureProcessManager {
    fn clone(&self) -> Self {
        Self {
            active_processes: self.active_processes.clone(),
            security_policies: self.security_policies.clone(),
            resource_monitor: self.resource_monitor.clone(),
        }
    }
}
```

### 6.2 Async-Std 安全增强

Async-Std 2.0 提供了额外的安全特性：

```rust
use async_std::process::{Command, Child, Stdio};
use async_std::sync::{Mutex, RwLock};
use async_std::time::{timeout, Duration};
use std::collections::HashMap;

// Async-Std 安全进程管理器
pub struct AsyncStdSecureProcessManager {
    active_processes: Arc<RwLock<HashMap<String, AsyncStdSecureProcess>>>,
    security_contexts: Arc<Mutex<HashMap<String, SecurityContext>>>,
    audit_logger: Arc<Mutex<AuditLogger>>,
}

#[derive(Debug, Clone)]
pub struct AsyncStdSecureProcess {
    pub id: String,
    pub child: Option<Child>,
    pub security_context: SecurityContext,
    pub created_at: std::time::Instant,
    pub status: ProcessStatus,
    pub security_violations: Vec<SecurityViolation>,
}

impl AsyncStdSecureProcessManager {
    pub fn new() -> Self {
        Self {
            active_processes: Arc::new(RwLock::new(HashMap::new())),
            security_contexts: Arc::new(Mutex::new(HashMap::new())),
            audit_logger: Arc::new(Mutex::new(AuditLogger::new())),
        }
    }

    // 使用 Async-Std 执行安全进程
    pub async fn execute_secure_process(
        &self,
        user_id: String,
        command: String,
        args: Vec<String>,
    ) -> Result<String, SecurityError> {
        // 获取安全上下文
        let security_contexts = self.security_contexts.lock().await;
        let security_context = security_contexts.get(&user_id)
            .ok_or(SecurityError::InsufficientPermissions)?;

        // 验证命令权限
        if !self.is_command_allowed(security_context, &command).await {
            return Err(SecurityError::CommandForbidden);
        }

        // 创建 Async-Std 进程
        let mut child = Command::new(&command)
            .args(&args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| SecurityError::ProcessSpawnFailed(e.to_string()))?;

        let process_id = uuid::Uuid::new_v4().to_string();
        let secure_process = AsyncStdSecureProcess {
            id: process_id.clone(),
            child: Some(child),
            security_context: security_context.clone(),
            created_at: std::time::Instant::now(),
            status: ProcessStatus::Starting,
            security_violations: Vec::new(),
        };

        // 添加到活跃进程列表
        let mut active_processes = self.active_processes.write().await;
        active_processes.insert(process_id.clone(), secure_process);

        // 记录审计日志
        self.audit_logger.lock().await.log_process_creation(
            &user_id,
            &process_id,
            &command,
            &args,
        ).await;

        // 启动监控任务
        self.start_process_monitoring(&process_id).await?;

        Ok(process_id)
    }

    // 异步进程监控
    async fn start_process_monitoring(&self, process_id: &str) -> Result<(), SecurityError> {
        let process_id = process_id.to_string();
        let manager = self.clone();

        async_std::task::spawn(async move {
            if let Err(e) = manager.monitor_process(&process_id).await {
                eprintln!("进程监控失败: {}", e);
            }
        });

        Ok(())
    }

    async fn monitor_process(&self, process_id: &str) -> Result<(), SecurityError> {
        let mut interval = async_std::time::interval(Duration::from_millis(100));

        loop {
            interval.tick().await;

            let mut active_processes = self.active_processes.write().await;
            let process = active_processes.get_mut(process_id);

            if let Some(process) = process {
                // 检查进程状态
                if let Some(child) = &mut process.child {
                    match child.try_wait() {
                        Ok(Some(status)) => {
                            process.status = if status.success() {
                                ProcessStatus::Terminated
                            } else {
                                ProcessStatus::Failed
                            };
                            process.child = None;
                            break;
                        }
                        Ok(None) => {
                            process.status = ProcessStatus::Running;
                        }
                        Err(e) => {
                            eprintln!("检查进程状态失败: {}", e);
                            process.status = ProcessStatus::Failed;
                            break;
                        }
                    }
                }

                // 检查安全策略
                if let Err(e) = self.check_security_policies(process).await {
                    self.handle_security_violation(process_id, &e).await?;
                }
            } else {
                break;
            }
        }

        Ok(())
    }

    async fn is_command_allowed(
        &self,
        context: &SecurityContext,
        command: &str,
    ) -> bool {
        // 检查命令是否在允许列表中
        if !context.allowed_commands.is_empty() {
            return context.allowed_commands.contains(&command.to_string());
        }

        // 检查命令是否在拒绝列表中
        !context.denied_commands.contains(&command.to_string())
    }

    async fn check_security_policies(
        &self,
        process: &AsyncStdSecureProcess,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 安全策略检查逻辑
        Ok(())
    }

    async fn handle_security_violation(
        &self,
        process_id: &str,
        error: &Box<dyn std::error::Error>,
    ) -> Result<(), SecurityError> {
        println!("安全违规: 进程 {} - {}", process_id, error);
        Ok(())
    }
}

impl Clone for AsyncStdSecureProcessManager {
    fn clone(&self) -> Self {
        Self {
            active_processes: self.active_processes.clone(),
            security_contexts: self.security_contexts.clone(),
            audit_logger: self.audit_logger.clone(),
        }
    }
}
```

### 6.3 第三方安全库

集成现代第三方安全库：

```rust
use duct::cmd;
use subprocess::{Popen, PopenConfig, Redirection};
use std::collections::HashMap;

// 第三方安全库集成
pub struct ThirdPartySecurityManager {
    duct_executor: DuctSecureExecutor,
    subprocess_executor: SubprocessSecureExecutor,
    security_policies: Arc<Mutex<Vec<SecurityPolicy>>>,
}

// Duct 安全执行器
pub struct DuctSecureExecutor {
    allowed_commands: Vec<String>,
    denied_commands: Vec<String>,
    resource_limits: ResourceLimits,
}

impl DuctSecureExecutor {
    pub fn new(
        allowed_commands: Vec<String>,
        denied_commands: Vec<String>,
        resource_limits: ResourceLimits,
    ) -> Self {
        Self {
            allowed_commands,
            denied_commands,
            resource_limits,
        }
    }

    // 使用 Duct 执行安全命令
    pub async fn execute_secure_command(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, SecurityError> {
        // 安全检查
        if self.denied_commands.contains(&command.to_string()) {
            return Err(SecurityError::CommandForbidden);
        }

        if !self.allowed_commands.is_empty() && !self.allowed_commands.contains(&command.to_string()) {
            return Err(SecurityError::InsufficientPermissions);
        }

        // 使用 Duct 执行命令
        let result = cmd(command, args)
            .stdout_capture()
            .stderr_capture()
            .run()
            .map_err(|e| SecurityError::ProcessExecutionFailed(e.to_string()))?;

        if result.status.success() {
            Ok(String::from_utf8_lossy(&result.stdout).to_string())
        } else {
            Err(SecurityError::ProcessExecutionFailed(
                String::from_utf8_lossy(&result.stderr).to_string()
            ))
        }
    }
}

// Subprocess 安全执行器
pub struct SubprocessSecureExecutor {
    security_context: SecurityContext,
    audit_logger: Arc<Mutex<AuditLogger>>,
}

impl SubprocessSecureExecutor {
    pub fn new(security_context: SecurityContext) -> Self {
        Self {
            security_context,
            audit_logger: Arc::new(Mutex::new(AuditLogger::new())),
        }
    }

    // 使用 Subprocess 执行安全命令
    pub async fn execute_secure_command(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, SecurityError> {
        // 安全检查
        if !self.is_command_allowed(command).await {
            return Err(SecurityError::CommandForbidden);
        }

        // 记录审计日志
        self.audit_logger.lock().await.log_execution(
            &self.security_context.user_id,
            command,
            args,
        ).await;

        // 使用 Subprocess 执行命令
        let mut cmd_args = vec![command.to_string()];
        cmd_args.extend(args.iter().cloned());

        let mut process = Popen::create(
            &cmd_args,
            PopenConfig {
                stdin: Redirection::Pipe,
                stdout: Redirection::Pipe,
                stderr: Redirection::Pipe,
                ..Default::default()
            },
        ).map_err(|e| SecurityError::ProcessSpawnFailed(e.to_string()))?;

        // 等待进程完成
        let (stdout, stderr) = process.communicate(None)
            .map_err(|e| SecurityError::ProcessExecutionFailed(e.to_string()))?;

        if process.poll().is_some() {
            let exit_code = process.wait()
                .map_err(|e| SecurityError::ProcessExecutionFailed(e.to_string()))?;

            if exit_code.success() {
                Ok(stdout.unwrap_or_default())
            } else {
                Err(SecurityError::ProcessExecutionFailed(
                    stderr.unwrap_or_default()
                ))
            }
        } else {
            Err(SecurityError::ProcessExecutionFailed("进程未正常退出".to_string()))
        }
    }

    async fn is_command_allowed(&self, command: &str) -> bool {
        // 检查命令是否在允许列表中
        if !self.security_context.allowed_commands.is_empty() {
            return self.security_context.allowed_commands.contains(&command.to_string());
        }

        // 检查命令是否在拒绝列表中
        !self.security_context.denied_commands.contains(&command.to_string())
    }
}

impl ThirdPartySecurityManager {
    pub fn new(
        allowed_commands: Vec<String>,
        denied_commands: Vec<String>,
        resource_limits: ResourceLimits,
        security_context: SecurityContext,
    ) -> Self {
        Self {
            duct_executor: DuctSecureExecutor::new(allowed_commands, denied_commands, resource_limits),
            subprocess_executor: SubprocessSecureExecutor::new(security_context),
            security_policies: Arc::new(Mutex::new(Vec::new())),
        }
    }

    // 统一的安全命令执行接口
    pub async fn execute_command(
        &self,
        executor_type: ExecutorType,
        command: &str,
        args: &[String],
    ) -> Result<String, SecurityError> {
        match executor_type {
            ExecutorType::Duct => {
                self.duct_executor.execute_secure_command(command, args).await
            }
            ExecutorType::Subprocess => {
                self.subprocess_executor.execute_secure_command(command, args).await
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExecutorType {
    Duct,
    Subprocess,
}
```

## 7. 企业级安全实践

### 7.1 安全策略管理

```rust
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};
use std::collections::HashMap;
use std::time::{Duration, Instant};

// 企业级安全策略管理器
pub struct EnterpriseSecurityPolicyManager {
    policies: Arc<RwLock<HashMap<String, SecurityPolicy>>>,
    policy_groups: Arc<RwLock<HashMap<String, PolicyGroup>>>,
    compliance_rules: Arc<Mutex<Vec<ComplianceRule>>>,
    audit_logger: Arc<Mutex<AuditLogger>>,
}

#[derive(Debug, Clone)]
pub struct SecurityPolicy {
    pub id: String,
    pub name: String,
    pub description: String,
    pub policy_type: PolicyType,
    pub rules: Vec<PolicyRule>,
    pub severity: PolicySeverity,
    pub enabled: bool,
    pub created_at: Instant,
    pub updated_at: Instant,
    pub created_by: String,
    pub updated_by: String,
}

#[derive(Debug, Clone)]
pub enum PolicyType {
    AccessControl,
    ResourceLimits,
    CommandRestrictions,
    NetworkSecurity,
    DataProtection,
    Compliance,
}

#[derive(Debug, Clone)]
pub struct PolicyRule {
    pub id: String,
    pub name: String,
    pub condition: RuleCondition,
    pub action: RuleAction,
    pub priority: u32,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub enum RuleCondition {
    UserRole(String),
    CommandPattern(String),
    ResourceUsage(ResourceType, u64),
    TimeWindow(TimeWindow),
    Location(String),
    Device(String),
}

#[derive(Debug, Clone)]
pub enum RuleAction {
    Allow,
    Deny,
    Log,
    Alert,
    Quarantine,
    Escalate,
}

#[derive(Debug, Clone)]
pub enum ResourceType {
    Memory,
    CPU,
    Disk,
    Network,
    FileDescriptors,
}

#[derive(Debug, Clone)]
pub struct TimeWindow {
    pub start: u8, // 小时
    pub end: u8,   // 小时
    pub days: Vec<u8>, // 星期几
}

#[derive(Debug, Clone)]
pub struct PolicyGroup {
    pub id: String,
    pub name: String,
    pub description: String,
    pub policies: Vec<String>, // 策略 ID 列表
    pub priority: u32,
    pub enabled: bool,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub struct ComplianceRule {
    pub id: String,
    pub name: String,
    pub standard: ComplianceStandard,
    pub requirements: Vec<ComplianceRequirement>,
    pub enabled: bool,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum ComplianceStandard {
    SOX,
    HIPAA,
    PCI_DSS,
    GDPR,
    ISO27001,
    NIST,
}

#[derive(Debug, Clone)]
pub struct ComplianceRequirement {
    pub id: String,
    pub description: String,
    pub mandatory: bool,
    pub verification_method: VerificationMethod,
}

#[derive(Debug, Clone)]
pub enum VerificationMethod {
    Automated,
    Manual,
    Hybrid,
}

impl EnterpriseSecurityPolicyManager {
    pub fn new() -> Self {
        Self {
            policies: Arc::new(RwLock::new(HashMap::new())),
            policy_groups: Arc::new(RwLock::new(HashMap::new())),
            compliance_rules: Arc::new(Mutex::new(Vec::new())),
            audit_logger: Arc::new(Mutex::new(AuditLogger::new())),
        }
    }

    // 创建安全策略
    pub async fn create_policy(
        &self,
        policy: SecurityPolicy,
    ) -> Result<(), PolicyError> {
        let mut policies = self.policies.write().await;

        if policies.contains_key(&policy.id) {
            return Err(PolicyError::PolicyExists);
        }

        policies.insert(policy.id.clone(), policy.clone());

        // 记录审计日志
        self.audit_logger.lock().await.log_policy_creation(
            &policy.created_by,
            &policy.id,
            &policy.name,
        ).await;

        Ok(())
    }

    // 更新安全策略
    pub async fn update_policy(
        &self,
        policy_id: &str,
        updated_policy: SecurityPolicy,
        updated_by: &str,
    ) -> Result<(), PolicyError> {
        let mut policies = self.policies.write().await;

        if let Some(existing_policy) = policies.get_mut(policy_id) {
            *existing_policy = updated_policy;
            existing_policy.updated_at = Instant::now();
            existing_policy.updated_by = updated_by.to_string();

            // 记录审计日志
            self.audit_logger.lock().await.log_policy_update(
                updated_by,
                policy_id,
                &existing_policy.name,
            ).await;

            Ok(())
        } else {
            Err(PolicyError::PolicyNotFound)
        }
    }

    // 评估安全策略
    pub async fn evaluate_policy(
        &self,
        user_id: &str,
        command: &str,
        args: &[String],
        context: &SecurityContext,
    ) -> Result<PolicyEvaluationResult, PolicyError> {
        let policies = self.policies.read().await;
        let mut results = Vec::new();

        for (policy_id, policy) in policies.iter() {
            if !policy.enabled {
                continue;
            }

            let evaluation = self.evaluate_policy_rules(
                policy,
                user_id,
                command,
                args,
                context,
            ).await?;

            results.push(PolicyEvaluation {
                policy_id: policy_id.clone(),
                policy_name: policy.name.clone(),
                evaluation,
            });
        }

        Ok(PolicyEvaluationResult {
            user_id: user_id.to_string(),
            command: command.to_string(),
            evaluations: results,
            overall_result: self.determine_overall_result(&results),
        })
    }

    async fn evaluate_policy_rules(
        &self,
        policy: &SecurityPolicy,
        user_id: &str,
        command: &str,
        args: &[String],
        context: &SecurityContext,
    ) -> Result<RuleEvaluation, PolicyError> {
        let mut rule_results = Vec::new();
        let mut overall_action = RuleAction::Allow;

        for rule in &policy.rules {
            if !rule.enabled {
                continue;
            }

            let matches = self.evaluate_rule_condition(
                &rule.condition,
                user_id,
                command,
                args,
                context,
            ).await?;

            if matches {
                rule_results.push(RuleResult {
                    rule_id: rule.id.clone(),
                    rule_name: rule.name.clone(),
                    action: rule.action.clone(),
                    priority: rule.priority,
                });

                // 根据优先级确定最终动作
                if rule.priority > self.get_action_priority(&overall_action) {
                    overall_action = rule.action.clone();
                }
            }
        }

        Ok(RuleEvaluation {
            policy_id: policy.id.clone(),
            policy_name: policy.name.clone(),
            rule_results,
            overall_action,
        })
    }

    async fn evaluate_rule_condition(
        &self,
        condition: &RuleCondition,
        user_id: &str,
        command: &str,
        args: &[String],
        context: &SecurityContext,
    ) -> Result<bool, PolicyError> {
        match condition {
            RuleCondition::UserRole(role) => {
                // 检查用户角色
                Ok(context.user_id.contains(role))
            }
            RuleCondition::CommandPattern(pattern) => {
                // 检查命令模式
                Ok(command.contains(pattern))
            }
            RuleCondition::ResourceUsage(resource_type, limit) => {
                // 检查资源使用
                match resource_type {
                    ResourceType::Memory => {
                        Ok(context.resource_limits.max_memory_mb > *limit)
                    }
                    ResourceType::CPU => {
                        Ok(context.resource_limits.max_cpu_percent > *limit as f64)
                    }
                    _ => Ok(false),
                }
            }
            RuleCondition::TimeWindow(time_window) => {
                // 检查时间窗口
                let now = chrono::Local::now();
                let current_hour = now.hour() as u8;
                let current_day = now.weekday().num_days_from_monday() as u8;

                Ok(time_window.start <= current_hour
                    && current_hour <= time_window.end
                    && time_window.days.contains(&current_day))
            }
            RuleCondition::Location(location) => {
                // 检查位置
                Ok(context.user_id.contains(location))
            }
            RuleCondition::Device(device) => {
                // 检查设备
                Ok(context.user_id.contains(device))
            }
        }
    }

    fn get_action_priority(&self, action: &RuleAction) -> u32 {
        match action {
            RuleAction::Deny => 100,
            RuleAction::Quarantine => 90,
            RuleAction::Escalate => 80,
            RuleAction::Alert => 70,
            RuleAction::Log => 60,
            RuleAction::Allow => 50,
        }
    }

    fn determine_overall_result(&self, evaluations: &[PolicyEvaluation]) -> RuleAction {
        let mut highest_priority = 0;
        let mut overall_action = RuleAction::Allow;

        for evaluation in evaluations {
            let priority = self.get_action_priority(&evaluation.evaluation.overall_action);
            if priority > highest_priority {
                highest_priority = priority;
                overall_action = evaluation.evaluation.overall_action.clone();
            }
        }

        overall_action
    }
}

#[derive(Debug, Clone)]
pub struct PolicyEvaluationResult {
    pub user_id: String,
    pub command: String,
    pub evaluations: Vec<PolicyEvaluation>,
    pub overall_result: RuleAction,
}

#[derive(Debug, Clone)]
pub struct PolicyEvaluation {
    pub policy_id: String,
    pub policy_name: String,
    pub evaluation: RuleEvaluation,
}

#[derive(Debug, Clone)]
pub struct RuleEvaluation {
    pub policy_id: String,
    pub policy_name: String,
    pub rule_results: Vec<RuleResult>,
    pub overall_action: RuleAction,
}

#[derive(Debug, Clone)]
pub struct RuleResult {
    pub rule_id: String,
    pub rule_name: String,
    pub action: RuleAction,
    pub priority: u32,
}

#[derive(Debug, thiserror::Error)]
pub enum PolicyError {
    #[error("策略已存在")]
    PolicyExists,
    #[error("策略未找到")]
    PolicyNotFound,
    #[error("策略评估失败")]
    PolicyEvaluationFailed,
    #[error("规则条件无效")]
    InvalidRuleCondition,
    #[error("权限不足")]
    InsufficientPermissions,
}
```

### 7.2 安全监控与告警

```rust
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};
use std::collections::HashMap;
use std::time::{Duration, Instant};

// 企业级安全监控系统
pub struct EnterpriseSecurityMonitor {
    monitors: Arc<RwLock<HashMap<String, SecurityMonitor>>>,
    alert_rules: Arc<Mutex<Vec<AlertRule>>>,
    notification_channels: Arc<Mutex<Vec<NotificationChannel>>>,
    incident_manager: Arc<Mutex<IncidentManager>>,
}

#[derive(Debug, Clone)]
pub struct SecurityMonitor {
    pub id: String,
    pub name: String,
    pub monitor_type: MonitorType,
    pub configuration: MonitorConfiguration,
    pub enabled: bool,
    pub created_at: Instant,
    pub last_check: Option<Instant>,
    pub status: MonitorStatus,
}

#[derive(Debug, Clone)]
pub enum MonitorType {
    ProcessMonitor,
    ResourceMonitor,
    NetworkMonitor,
    FileSystemMonitor,
    UserActivityMonitor,
    ComplianceMonitor,
}

#[derive(Debug, Clone)]
pub struct MonitorConfiguration {
    pub check_interval: Duration,
    pub thresholds: HashMap<String, Threshold>,
    pub filters: Vec<Filter>,
    pub actions: Vec<MonitorAction>,
}

#[derive(Debug, Clone)]
pub struct Threshold {
    pub value: f64,
    pub operator: ThresholdOperator,
    pub severity: AlertSeverity,
}

#[derive(Debug, Clone)]
pub enum ThresholdOperator {
    GreaterThan,
    LessThan,
    Equal,
    NotEqual,
    GreaterThanOrEqual,
    LessThanOrEqual,
}

#[derive(Debug, Clone)]
pub struct Filter {
    pub field: String,
    pub operator: FilterOperator,
    pub value: String,
}

#[derive(Debug, Clone)]
pub enum FilterOperator {
    Equals,
    Contains,
    StartsWith,
    EndsWith,
    Regex,
}

#[derive(Debug, Clone)]
pub enum MonitorAction {
    Log,
    Alert,
    Block,
    Quarantine,
    Notify,
    Escalate,
}

#[derive(Debug, Clone, PartialEq)]
pub enum MonitorStatus {
    Healthy,
    Warning,
    Critical,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct AlertRule {
    pub id: String,
    pub name: String,
    pub condition: AlertCondition,
    pub severity: AlertSeverity,
    pub enabled: bool,
    pub cooldown: Duration,
    pub last_triggered: Option<Instant>,
    pub notification_channels: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum AlertCondition {
    ProcessCountExceeds(u32),
    ResourceUsageExceeds(ResourceType, f64),
    SecurityViolationDetected,
    ComplianceViolationDetected,
    UnauthorizedAccessAttempt,
    SuspiciousActivityDetected,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AlertSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

#[derive(Debug, Clone)]
pub struct NotificationChannel {
    pub id: String,
    pub name: String,
    pub channel_type: NotificationChannelType,
    pub configuration: NotificationConfiguration,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub enum NotificationChannelType {
    Email,
    Slack,
    Webhook,
    SMS,
    PagerDuty,
    Custom,
}

#[derive(Debug, Clone)]
pub struct NotificationConfiguration {
    pub recipients: Vec<String>,
    pub template: String,
    pub retry_count: u32,
    pub timeout: Duration,
}

#[derive(Debug, Clone)]
pub struct IncidentManager {
    pub incidents: Vec<SecurityIncident>,
    pub escalation_rules: Vec<EscalationRule>,
    pub response_teams: Vec<ResponseTeam>,
}

#[derive(Debug, Clone)]
pub struct SecurityIncident {
    pub id: String,
    pub title: String,
    pub description: String,
    pub severity: AlertSeverity,
    pub status: IncidentStatus,
    pub created_at: Instant,
    pub updated_at: Instant,
    pub assigned_to: Option<String>,
    pub resolution: Option<String>,
    pub related_alerts: Vec<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IncidentStatus {
    Open,
    InProgress,
    Resolved,
    Closed,
    Escalated,
}

#[derive(Debug, Clone)]
pub struct EscalationRule {
    pub id: String,
    pub name: String,
    pub condition: EscalationCondition,
    pub action: EscalationAction,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub enum EscalationCondition {
    TimeExceeded(Duration),
    SeverityLevel(AlertSeverity),
    UnassignedIncident,
    MultipleIncidents(u32),
}

#[derive(Debug, Clone)]
pub enum EscalationAction {
    AssignToTeam(String),
    NotifyManager(String),
    CreateTicket(String),
    EscalateToSecurity,
}

#[derive(Debug, Clone)]
pub struct ResponseTeam {
    pub id: String,
    pub name: String,
    pub members: Vec<TeamMember>,
    pub contact_info: String,
    pub availability: TeamAvailability,
}

#[derive(Debug, Clone)]
pub struct TeamMember {
    pub id: String,
    pub name: String,
    pub role: String,
    pub contact_info: String,
    pub availability: MemberAvailability,
}

#[derive(Debug, Clone)]
pub enum TeamAvailability {
    Always,
    BusinessHours,
    OnCall,
    Custom(Vec<TimeWindow>),
}

#[derive(Debug, Clone)]
pub enum MemberAvailability {
    Available,
    Busy,
    Away,
    Offline,
}

impl EnterpriseSecurityMonitor {
    pub fn new() -> Self {
        Self {
            monitors: Arc::new(RwLock::new(HashMap::new())),
            alert_rules: Arc::new(Mutex::new(Vec::new())),
            notification_channels: Arc::new(Mutex::new(Vec::new())),
            incident_manager: Arc::new(Mutex::new(IncidentManager {
                incidents: Vec::new(),
                escalation_rules: Vec::new(),
                response_teams: Vec::new(),
            })),
        }
    }

    // 启动安全监控
    pub async fn start_monitoring(&self) -> Result<(), MonitorError> {
        let monitors = self.monitors.read().await;

        for (monitor_id, monitor) in monitors.iter() {
            if monitor.enabled {
                self.start_monitor(monitor_id, monitor).await?;
            }
        }

        Ok(())
    }

    // 启动单个监控器
    async fn start_monitor(
        &self,
        monitor_id: &str,
        monitor: &SecurityMonitor,
    ) -> Result<(), MonitorError> {
        let monitor_id = monitor_id.to_string();
        let monitor_clone = monitor.clone();
        let self_clone = self.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(monitor_clone.configuration.check_interval);

            loop {
                interval.tick().await;

                if let Err(e) = self_clone.run_monitor_check(&monitor_id, &monitor_clone).await {
                    eprintln!("监控器 {} 检查失败: {}", monitor_id, e);
                }
            }
        });

        Ok(())
    }

    // 运行监控检查
    async fn run_monitor_check(
        &self,
        monitor_id: &str,
        monitor: &SecurityMonitor,
    ) -> Result<(), MonitorError> {
        let start_time = Instant::now();

        // 执行监控检查
        let check_result = match monitor.monitor_type {
            MonitorType::ProcessMonitor => {
                self.check_process_monitor(monitor).await?
            }
            MonitorType::ResourceMonitor => {
                self.check_resource_monitor(monitor).await?
            }
            MonitorType::NetworkMonitor => {
                self.check_network_monitor(monitor).await?
            }
            MonitorType::FileSystemMonitor => {
                self.check_filesystem_monitor(monitor).await?
            }
            MonitorType::UserActivityMonitor => {
                self.check_user_activity_monitor(monitor).await?
            }
            MonitorType::ComplianceMonitor => {
                self.check_compliance_monitor(monitor).await?
            }
        };

        // 更新监控状态
        self.update_monitor_status(monitor_id, &check_result).await?;

        // 检查是否需要触发告警
        if check_result.triggered_alerts {
            self.trigger_alerts(monitor_id, &check_result).await?;
        }

        Ok(())
    }

    async fn check_process_monitor(
        &self,
        monitor: &SecurityMonitor,
    ) -> Result<MonitorCheckResult, MonitorError> {
        // 进程监控检查逻辑
        Ok(MonitorCheckResult {
            monitor_id: monitor.id.clone(),
            status: MonitorStatus::Healthy,
            triggered_alerts: false,
            metrics: HashMap::new(),
            timestamp: Instant::now(),
        })
    }

    async fn check_resource_monitor(
        &self,
        monitor: &SecurityMonitor,
    ) -> Result<MonitorCheckResult, MonitorError> {
        // 资源监控检查逻辑
        Ok(MonitorCheckResult {
            monitor_id: monitor.id.clone(),
            status: MonitorStatus::Healthy,
            triggered_alerts: false,
            metrics: HashMap::new(),
            timestamp: Instant::now(),
        })
    }

    async fn check_network_monitor(
        &self,
        monitor: &SecurityMonitor,
    ) -> Result<MonitorCheckResult, MonitorError> {
        // 网络监控检查逻辑
        Ok(MonitorCheckResult {
            monitor_id: monitor.id.clone(),
            status: MonitorStatus::Healthy,
            triggered_alerts: false,
            metrics: HashMap::new(),
            timestamp: Instant::now(),
        })
    }

    async fn check_filesystem_monitor(
        &self,
        monitor: &SecurityMonitor,
    ) -> Result<MonitorCheckResult, MonitorError> {
        // 文件系统监控检查逻辑
        Ok(MonitorCheckResult {
            monitor_id: monitor.id.clone(),
            status: MonitorStatus::Healthy,
            triggered_alerts: false,
            metrics: HashMap::new(),
            timestamp: Instant::now(),
        })
    }

    async fn check_user_activity_monitor(
        &self,
        monitor: &SecurityMonitor,
    ) -> Result<MonitorCheckResult, MonitorError> {
        // 用户活动监控检查逻辑
        Ok(MonitorCheckResult {
            monitor_id: monitor.id.clone(),
            status: MonitorStatus::Healthy,
            triggered_alerts: false,
            metrics: HashMap::new(),
            timestamp: Instant::now(),
        })
    }

    async fn check_compliance_monitor(
        &self,
        monitor: &SecurityMonitor,
    ) -> Result<MonitorCheckResult, MonitorError> {
        // 合规性监控检查逻辑
        Ok(MonitorCheckResult {
            monitor_id: monitor.id.clone(),
            status: MonitorStatus::Healthy,
            triggered_alerts: false,
            metrics: HashMap::new(),
            timestamp: Instant::now(),
        })
    }

    async fn update_monitor_status(
        &self,
        monitor_id: &str,
        check_result: &MonitorCheckResult,
    ) -> Result<(), MonitorError> {
        let mut monitors = self.monitors.write().await;
        if let Some(monitor) = monitors.get_mut(monitor_id) {
            monitor.status = check_result.status.clone();
            monitor.last_check = Some(check_result.timestamp);
        }
        Ok(())
    }

    async fn trigger_alerts(
        &self,
        monitor_id: &str,
        check_result: &MonitorCheckResult,
    ) -> Result<(), MonitorError> {
        let alert_rules = self.alert_rules.lock().await;

        for rule in alert_rules.iter() {
            if !rule.enabled {
                continue;
            }

            // 检查冷却时间
            if let Some(last_triggered) = rule.last_triggered {
                if last_triggered.elapsed() < rule.cooldown {
                    continue;
                }
            }

            // 检查告警条件
            if self.evaluate_alert_condition(&rule.condition, check_result).await? {
                self.create_alert(rule, check_result).await?;
            }
        }

        Ok(())
    }

    async fn evaluate_alert_condition(
        &self,
        condition: &AlertCondition,
        check_result: &MonitorCheckResult,
    ) -> Result<bool, MonitorError> {
        match condition {
            AlertCondition::ProcessCountExceeds(limit) => {
                // 检查进程数量
                Ok(false) // 实际实现中检查进程数量
            }
            AlertCondition::ResourceUsageExceeds(resource_type, limit) => {
                // 检查资源使用
                Ok(false) // 实际实现中检查资源使用
            }
            AlertCondition::SecurityViolationDetected => {
                // 检查安全违规
                Ok(check_result.status == MonitorStatus::Critical)
            }
            AlertCondition::ComplianceViolationDetected => {
                // 检查合规性违规
                Ok(false) // 实际实现中检查合规性
            }
            AlertCondition::UnauthorizedAccessAttempt => {
                // 检查未授权访问
                Ok(false) // 实际实现中检查访问权限
            }
            AlertCondition::SuspiciousActivityDetected => {
                // 检查可疑活动
                Ok(false) // 实际实现中检查活动模式
            }
        }
    }

    async fn create_alert(
        &self,
        rule: &AlertRule,
        check_result: &MonitorCheckResult,
    ) -> Result<(), MonitorError> {
        let alert = SecurityAlert {
            id: uuid::Uuid::new_v4().to_string(),
            rule_id: rule.id.clone(),
            monitor_id: check_result.monitor_id.clone(),
            severity: rule.severity.clone(),
            title: format!("安全告警: {}", rule.name),
            description: format!("监控器 {} 检测到异常", check_result.monitor_id),
            timestamp: Instant::now(),
            acknowledged: false,
            resolved: false,
        };

        // 发送通知
        self.send_notifications(&alert, &rule.notification_channels).await?;

        // 创建事件
        self.create_incident(&alert).await?;

        Ok(())
    }

    async fn send_notifications(
        &self,
        alert: &SecurityAlert,
        channel_ids: &[String],
    ) -> Result<(), MonitorError> {
        let notification_channels = self.notification_channels.lock().await;

        for channel_id in channel_ids {
            if let Some(channel) = notification_channels.iter().find(|c| c.id == *channel_id) {
                if channel.enabled {
                    self.send_notification(channel, alert).await?;
                }
            }
        }

        Ok(())
    }

    async fn send_notification(
        &self,
        channel: &NotificationChannel,
        alert: &SecurityAlert,
    ) -> Result<(), MonitorError> {
        match channel.channel_type {
            NotificationChannelType::Email => {
                // 发送邮件通知
                println!("发送邮件通知: {}", alert.title);
            }
            NotificationChannelType::Slack => {
                // 发送 Slack 通知
                println!("发送 Slack 通知: {}", alert.title);
            }
            NotificationChannelType::Webhook => {
                // 发送 Webhook 通知
                println!("发送 Webhook 通知: {}", alert.title);
            }
            NotificationChannelType::SMS => {
                // 发送短信通知
                println!("发送短信通知: {}", alert.title);
            }
            NotificationChannelType::PagerDuty => {
                // 发送 PagerDuty 通知
                println!("发送 PagerDuty 通知: {}", alert.title);
            }
            NotificationChannelType::Custom => {
                // 发送自定义通知
                println!("发送自定义通知: {}", alert.title);
            }
        }

        Ok(())
    }

    async fn create_incident(&self, alert: &SecurityAlert) -> Result<(), MonitorError> {
        let mut incident_manager = self.incident_manager.lock().await;

        let incident = SecurityIncident {
            id: uuid::Uuid::new_v4().to_string(),
            title: alert.title.clone(),
            description: alert.description.clone(),
            severity: alert.severity.clone(),
            status: IncidentStatus::Open,
            created_at: Instant::now(),
            updated_at: Instant::now(),
            assigned_to: None,
            resolution: None,
            related_alerts: vec![alert.id.clone()],
        };

        incident_manager.incidents.push(incident);
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct MonitorCheckResult {
    pub monitor_id: String,
    pub status: MonitorStatus,
    pub triggered_alerts: bool,
    pub metrics: HashMap<String, f64>,
    pub timestamp: Instant,
}

#[derive(Debug, Clone)]
pub struct SecurityAlert {
    pub id: String,
    pub rule_id: String,
    pub monitor_id: String,
    pub severity: AlertSeverity,
    pub title: String,
    pub description: String,
    pub timestamp: Instant,
    pub acknowledged: bool,
    pub resolved: bool,
}

#[derive(Debug, thiserror::Error)]
pub enum MonitorError {
    #[error("监控器启动失败")]
    MonitorStartFailed,
    #[error("监控检查失败")]
    MonitorCheckFailed,
    #[error("告警触发失败")]
    AlertTriggerFailed,
    #[error("通知发送失败")]
    NotificationFailed,
    #[error("事件创建失败")]
    IncidentCreationFailed,
}

impl Clone for EnterpriseSecurityMonitor {
    fn clone(&self) -> Self {
        Self {
            monitors: self.monitors.clone(),
            alert_rules: self.alert_rules.clone(),
            notification_channels: self.notification_channels.clone(),
            incident_manager: self.incident_manager.clone(),
        }
    }
}
```

### 7.3 事件响应

```rust
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};
use std::collections::HashMap;
use std::time::{Duration, Instant};

// 企业级事件响应系统
pub struct EnterpriseIncidentResponseSystem {
    incident_manager: Arc<Mutex<IncidentManager>>,
    response_playbooks: Arc<RwLock<HashMap<String, ResponsePlaybook>>>,
    automation_rules: Arc<Mutex<Vec<AutomationRule>>>,
    forensics_collector: Arc<Mutex<ForensicsCollector>>,
    communication_manager: Arc<Mutex<CommunicationManager>>,
}

#[derive(Debug, Clone)]
pub struct ResponsePlaybook {
    pub id: String,
    pub name: String,
    pub description: String,
    pub incident_types: Vec<IncidentType>,
    pub severity_levels: Vec<AlertSeverity>,
    pub steps: Vec<ResponseStep>,
    pub escalation_rules: Vec<EscalationRule>,
    pub enabled: bool,
    pub created_at: Instant,
    pub updated_at: Instant,
}

#[derive(Debug, Clone)]
pub enum IncidentType {
    SecurityBreach,
    DataBreach,
    Malware,
    Phishing,
    InsiderThreat,
    SystemCompromise,
    NetworkIntrusion,
    ComplianceViolation,
}

#[derive(Debug, Clone)]
pub struct ResponseStep {
    pub id: String,
    pub name: String,
    pub description: String,
    pub step_type: StepType,
    pub actions: Vec<ResponseAction>,
    pub dependencies: Vec<String>,
    pub estimated_duration: Duration,
    pub required_skills: Vec<String>,
    pub automated: bool,
}

#[derive(Debug, Clone)]
pub enum StepType {
    Immediate,
    ShortTerm,
    MediumTerm,
    LongTerm,
    FollowUp,
}

#[derive(Debug, Clone)]
pub enum ResponseAction {
    IsolateSystems,
    PreserveEvidence,
    NotifyStakeholders,
    EngageLegal,
    ContactLawEnforcement,
    ImplementCountermeasures,
    ConductForensics,
    UpdateSecurityControls,
    CommunicateWithPublic,
    ConductPostIncidentReview,
}

#[derive(Debug, Clone)]
pub struct AutomationRule {
    pub id: String,
    pub name: String,
    pub trigger_condition: AutomationTrigger,
    pub actions: Vec<AutomatedAction>,
    pub enabled: bool,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum AutomationTrigger {
    IncidentCreated(IncidentType),
    SeverityLevel(AlertSeverity),
    TimeElapsed(Duration),
    ManualTrigger,
    CustomCondition(String),
}

#[derive(Debug, Clone)]
pub enum AutomatedAction {
    AssignIncident(String),
    SendNotification(String),
    ExecuteScript(String),
    UpdateStatus(IncidentStatus),
    EscalateIncident,
    CreateTicket(String),
    BlockIP(String),
    QuarantineSystem(String),
}

#[derive(Debug, Clone)]
pub struct ForensicsCollector {
    pub collection_rules: Vec<CollectionRule>,
    pub storage_config: StorageConfiguration,
    pub retention_policy: RetentionPolicy,
}

#[derive(Debug, Clone)]
pub struct CollectionRule {
    pub id: String,
    pub name: String,
    pub incident_types: Vec<IncidentType>,
    pub data_types: Vec<DataType>,
    pub collection_method: CollectionMethod,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub enum DataType {
    Logs,
    MemoryDumps,
    DiskImages,
    NetworkTraffic,
    RegistrySnapshots,
    ProcessList,
    FileSystemSnapshots,
    UserActivity,
}

#[derive(Debug, Clone)]
pub enum CollectionMethod {
    Automated,
    Manual,
    Hybrid,
}

#[derive(Debug, Clone)]
pub struct StorageConfiguration {
    pub storage_type: StorageType,
    pub location: String,
    pub encryption: bool,
    pub compression: bool,
    pub max_size: u64,
}

#[derive(Debug, Clone)]
pub enum StorageType {
    Local,
    Network,
    Cloud,
    Hybrid,
}

#[derive(Debug, Clone)]
pub struct RetentionPolicy {
    pub retention_period: Duration,
    pub archive_period: Duration,
    pub deletion_policy: DeletionPolicy,
}

#[derive(Debug, Clone)]
pub enum DeletionPolicy {
    Automatic,
    Manual,
    Never,
}

#[derive(Debug, Clone)]
pub struct CommunicationManager {
    pub communication_channels: Vec<CommunicationChannel>,
    pub templates: Vec<CommunicationTemplate>,
    pub escalation_matrix: EscalationMatrix,
}

#[derive(Debug, Clone)]
pub struct CommunicationChannel {
    pub id: String,
    pub name: String,
    pub channel_type: CommunicationChannelType,
    pub configuration: CommunicationConfiguration,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub enum CommunicationChannelType {
    Email,
    Phone,
    SMS,
    Slack,
    Teams,
    Webhook,
    Custom,
}

#[derive(Debug, Clone)]
pub struct CommunicationConfiguration {
    pub recipients: Vec<String>,
    pub template_id: String,
    pub priority: CommunicationPriority,
    pub retry_count: u32,
    pub timeout: Duration,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum CommunicationPriority {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct CommunicationTemplate {
    pub id: String,
    pub name: String,
    pub template_type: TemplateType,
    pub content: String,
    pub variables: Vec<String>,
    pub enabled: bool,
}

#[derive(Debug, Clone)]
pub enum TemplateType {
    IncidentNotification,
    StatusUpdate,
    EscalationNotice,
    ResolutionSummary,
    PublicStatement,
}

#[derive(Debug, Clone)]
pub struct EscalationMatrix {
    pub levels: Vec<EscalationLevel>,
    pub timeouts: Vec<EscalationTimeout>,
    pub contact_info: HashMap<String, ContactInfo>,
}

#[derive(Debug, Clone)]
pub struct EscalationLevel {
    pub level: u32,
    pub name: String,
    pub roles: Vec<String>,
    pub contact_methods: Vec<CommunicationChannelType>,
}

#[derive(Debug, Clone)]
pub struct EscalationTimeout {
    pub level: u32,
    pub timeout: Duration,
    pub action: EscalationAction,
}

#[derive(Debug, Clone)]
pub struct ContactInfo {
    pub name: String,
    pub role: String,
    pub contact_methods: HashMap<CommunicationChannelType, String>,
    pub availability: Availability,
}

#[derive(Debug, Clone)]
pub enum Availability {
    Always,
    BusinessHours,
    OnCall,
    Custom(Vec<TimeWindow>),
}

impl EnterpriseIncidentResponseSystem {
    pub fn new() -> Self {
        Self {
            incident_manager: Arc::new(Mutex::new(IncidentManager {
                incidents: Vec::new(),
                escalation_rules: Vec::new(),
                response_teams: Vec::new(),
            })),
            response_playbooks: Arc::new(RwLock::new(HashMap::new())),
            automation_rules: Arc::new(Mutex::new(Vec::new())),
            forensics_collector: Arc::new(Mutex::new(ForensicsCollector {
                collection_rules: Vec::new(),
                storage_config: StorageConfiguration {
                    storage_type: StorageType::Local,
                    location: "/tmp/forensics".to_string(),
                    encryption: true,
                    compression: true,
                    max_size: 1024 * 1024 * 1024, // 1GB
                },
                retention_policy: RetentionPolicy {
                    retention_period: Duration::from_secs(30 * 24 * 60 * 60), // 30 days
                    archive_period: Duration::from_secs(365 * 24 * 60 * 60), // 1 year
                    deletion_policy: DeletionPolicy::Manual,
                },
            })),
            communication_manager: Arc::new(Mutex::new(CommunicationManager {
                communication_channels: Vec::new(),
                templates: Vec::new(),
                escalation_matrix: EscalationMatrix {
                    levels: Vec::new(),
                    timeouts: Vec::new(),
                    contact_info: HashMap::new(),
                },
            })),
        }
    }

    // 启动事件响应
    pub async fn start_incident_response(
        &self,
        incident_id: &str,
    ) -> Result<(), ResponseError> {
        let mut incident_manager = self.incident_manager.lock().await;
        let incident = incident_manager.incidents.iter_mut()
            .find(|i| i.id == incident_id)
            .ok_or(ResponseError::IncidentNotFound)?;

        // 更新事件状态
        incident.status = IncidentStatus::InProgress;
        incident.updated_at = Instant::now();

        // 选择合适的响应手册
        let playbook = self.select_response_playbook(incident).await?;

        // 执行响应步骤
        self.execute_response_playbook(incident, &playbook).await?;

        // 启动自动化规则
        self.trigger_automation_rules(incident).await?;

        // 开始取证收集
        self.start_forensics_collection(incident).await?;

        // 发送初始通知
        self.send_initial_notifications(incident).await?;

        Ok(())
    }

    async fn select_response_playbook(
        &self,
        incident: &SecurityIncident,
    ) -> Result<ResponsePlaybook, ResponseError> {
        let playbooks = self.response_playbooks.read().await;

        // 根据事件类型和严重程度选择合适的响应手册
        for (_, playbook) in playbooks.iter() {
            if playbook.enabled {
                // 检查事件类型匹配
                // 检查严重程度匹配
                // 返回第一个匹配的手册
                return Ok(playbook.clone());
            }
        }

        Err(ResponseError::NoPlaybookFound)
    }

    async fn execute_response_playbook(
        &self,
        incident: &mut SecurityIncident,
        playbook: &ResponsePlaybook,
    ) -> Result<(), ResponseError> {
        for step in &playbook.steps {
            // 检查依赖
            if !self.check_step_dependencies(step).await? {
                continue;
            }

            // 执行步骤
            self.execute_response_step(incident, step).await?;

            // 更新事件状态
            incident.updated_at = Instant::now();
        }

        Ok(())
    }

    async fn check_step_dependencies(
        &self,
        step: &ResponseStep,
    ) -> Result<bool, ResponseError> {
        // 检查步骤依赖
        for dependency in &step.dependencies {
            // 检查依赖是否满足
            // 实际实现中检查依赖状态
        }

        Ok(true)
    }

    async fn execute_response_step(
        &self,
        incident: &mut SecurityIncident,
        step: &ResponseStep,
    ) -> Result<(), ResponseError> {
        println!("执行响应步骤: {}", step.name);

        for action in &step.actions {
            match action {
                ResponseAction::IsolateSystems => {
                    println!("隔离系统");
                }
                ResponseAction::PreserveEvidence => {
                    println!("保存证据");
                }
                ResponseAction::NotifyStakeholders => {
                    println!("通知利益相关者");
                }
                ResponseAction::EngageLegal => {
                    println!("联系法务部门");
                }
                ResponseAction::ContactLawEnforcement => {
                    println!("联系执法部门");
                }
                ResponseAction::ImplementCountermeasures => {
                    println!("实施反制措施");
                }
                ResponseAction::ConductForensics => {
                    println!("进行取证分析");
                }
                ResponseAction::UpdateSecurityControls => {
                    println!("更新安全控制");
                }
                ResponseAction::CommunicateWithPublic => {
                    println!("与公众沟通");
                }
                ResponseAction::ConductPostIncidentReview => {
                    println!("进行事后审查");
                }
            }
        }

        Ok(())
    }

    async fn trigger_automation_rules(
        &self,
        incident: &SecurityIncident,
    ) -> Result<(), ResponseError> {
        let automation_rules = self.automation_rules.lock().await;

        for rule in automation_rules.iter() {
            if !rule.enabled {
                continue;
            }

            if self.evaluate_automation_trigger(&rule.trigger_condition, incident).await? {
                self.execute_automated_actions(&rule.actions).await?;
            }
        }

        Ok(())
    }

    async fn evaluate_automation_trigger(
        &self,
        trigger: &AutomationTrigger,
        incident: &SecurityIncident,
    ) -> Result<bool, ResponseError> {
        match trigger {
            AutomationTrigger::IncidentCreated(incident_type) => {
                // 检查事件类型
                Ok(true) // 实际实现中检查事件类型
            }
            AutomationTrigger::SeverityLevel(severity) => {
                // 检查严重程度
                Ok(incident.severity >= *severity)
            }
            AutomationTrigger::TimeElapsed(duration) => {
                // 检查时间
                Ok(incident.created_at.elapsed() >= *duration)
            }
            AutomationTrigger::ManualTrigger => {
                // 手动触发
                Ok(false)
            }
            AutomationTrigger::CustomCondition(condition) => {
                // 自定义条件
                Ok(false) // 实际实现中评估自定义条件
            }
        }
    }

    async fn execute_automated_actions(
        &self,
        actions: &[AutomatedAction],
    ) -> Result<(), ResponseError> {
        for action in actions {
            match action {
                AutomatedAction::AssignIncident(assignee) => {
                    println!("自动分配事件给: {}", assignee);
                }
                AutomatedAction::SendNotification(channel) => {
                    println!("发送通知到: {}", channel);
                }
                AutomatedAction::ExecuteScript(script) => {
                    println!("执行脚本: {}", script);
                }
                AutomatedAction::UpdateStatus(status) => {
                    println!("更新状态为: {:?}", status);
                }
                AutomatedAction::EscalateIncident => {
                    println!("升级事件");
                }
                AutomatedAction::CreateTicket(system) => {
                    println!("创建工单: {}", system);
                }
                AutomatedAction::BlockIP(ip) => {
                    println!("阻止 IP: {}", ip);
                }
                AutomatedAction::QuarantineSystem(system) => {
                    println!("隔离系统: {}", system);
                }
            }
        }

        Ok(())
    }

    async fn start_forensics_collection(
        &self,
        incident: &SecurityIncident,
    ) -> Result<(), ResponseError> {
        let mut collector = self.forensics_collector.lock().await;

        for rule in &collector.collection_rules {
            if !rule.enabled {
                continue;
            }

            // 检查事件类型匹配
            // 实际实现中检查事件类型

            // 开始收集数据
            self.collect_forensic_data(rule, incident).await?;
        }

        Ok(())
    }

    async fn collect_forensic_data(
        &self,
        rule: &CollectionRule,
        incident: &SecurityIncident,
    ) -> Result<(), ResponseError> {
        println!("收集取证数据: {}", rule.name);

        for data_type in &rule.data_types {
            match data_type {
                DataType::Logs => {
                    println!("收集日志");
                }
                DataType::MemoryDumps => {
                    println!("收集内存转储");
                }
                DataType::DiskImages => {
                    println!("收集磁盘镜像");
                }
                DataType::NetworkTraffic => {
                    println!("收集网络流量");
                }
                DataType::RegistrySnapshots => {
                    println!("收集注册表快照");
                }
                DataType::ProcessList => {
                    println!("收集进程列表");
                }
                DataType::FileSystemSnapshots => {
                    println!("收集文件系统快照");
                }
                DataType::UserActivity => {
                    println!("收集用户活动");
                }
            }
        }

        Ok(())
    }

    async fn send_initial_notifications(
        &self,
        incident: &SecurityIncident,
    ) -> Result<(), ResponseError> {
        let communication_manager = self.communication_manager.lock().await;

        // 发送初始通知
        for channel in &communication_manager.communication_channels {
            if channel.enabled {
                self.send_notification(channel, incident).await?;
            }
        }

        Ok(())
    }

    async fn send_notification(
        &self,
        channel: &CommunicationChannel,
        incident: &SecurityIncident,
    ) -> Result<(), ResponseError> {
        match channel.channel_type {
            CommunicationChannelType::Email => {
                println!("发送邮件通知: {}", incident.title);
            }
            CommunicationChannelType::Phone => {
                println!("发送电话通知: {}", incident.title);
            }
            CommunicationChannelType::SMS => {
                println!("发送短信通知: {}", incident.title);
            }
            CommunicationChannelType::Slack => {
                println!("发送 Slack 通知: {}", incident.title);
            }
            CommunicationChannelType::Teams => {
                println!("发送 Teams 通知: {}", incident.title);
            }
            CommunicationChannelType::Webhook => {
                println!("发送 Webhook 通知: {}", incident.title);
            }
            CommunicationChannelType::Custom => {
                println!("发送自定义通知: {}", incident.title);
            }
        }

        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ResponseError {
    #[error("事件未找到")]
    IncidentNotFound,
    #[error("未找到响应手册")]
    NoPlaybookFound,
    #[error("步骤依赖不满足")]
    StepDependencyNotMet,
    #[error("自动化规则执行失败")]
    AutomationRuleFailed,
    #[error("取证收集失败")]
    ForensicsCollectionFailed,
    #[error("通知发送失败")]
    NotificationFailed,
}

impl Clone for EnterpriseIncidentResponseSystem {
    fn clone(&self) -> Self {
        Self {
            incident_manager: self.incident_manager.clone(),
            response_playbooks: self.response_playbooks.clone(),
            automation_rules: self.automation_rules.clone(),
            forensics_collector: self.forensics_collector.clone(),
            communication_manager: self.communication_manager.clone(),
        }
    }
}
```

## 8. 总结

本章详细介绍了 Rust 1.92.0 进程管理中的安全机制（兼容 Rust 1.90+ 特性）：

1. **Rust 1.92.0 安全特性**（兼容 Rust 1.90+ 特性）: 异步安全闭包、改进的错误处理、内存安全增强、并发安全特性
2. **权限控制**: 用户权限管理、资源限制、最小权限原则、动态权限调整
3. **沙箱执行**: 进程沙箱、容器化执行、系统调用拦截、文件系统沙箱
4. **安全审计**: 安全事件监控、行为分析、合规性检查
5. **威胁防护**: 入侵检测、恶意软件防护、零信任架构
6. **现代安全库集成**: Tokio 安全特性、Async-Std 安全增强、第三方安全库
7. **企业级安全实践**: 安全策略管理、安全监控与告警、事件响应

这些技术为构建安全的进程管理系统提供了全面的保护机制，能够有效防范各种安全威胁，确保系统的安全性和可靠性。Rust 1.92.0 的新特性（兼容 Rust 1.90+ 特性）进一步增强了安全性和性能，使进程管理更加安全、高效和可靠。
