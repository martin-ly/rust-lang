# C07-10. 跨平台进程管理指南 (Rust 1.92.0 增强版)

> **文档定位**: Tier 4 高级主题
> **最后更新**: 2025-12-25
> **Rust版本**: 1.92.0+ (Edition 2024)
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

## 📋 目录

- [C07-10. 跨平台进程管理指南 (Rust 1.92.0 增强版)](#c07-10-跨平台进程管理指南-rust-1920-增强版)
  - [目录](#目录)
  - [1. 平台差异概览](#1-平台差异概览)
    - [1.1 Windows 特性](#11-windows-特性)
    - [1.2 Unix/Linux 特性](#12-unixlinux-特性)
    - [1.3 macOS 特性](#13-macos-特性)
  - [2. 跨平台抽象层](#2-跨平台抽象层)
    - [2.1 统一接口设计](#21-统一接口设计)
    - [2.2 平台特定实现](#22-平台特定实现)
    - [2.3 条件编译策略](#23-条件编译策略)
  - [3. 进程创建差异](#3-进程创建差异)
    - [3.1 命令解析差异](#31-命令解析差异)
    - [3.2 环境变量处理](#32-环境变量处理)
    - [3.3 工作目录设置](#33-工作目录设置)
  - [4. IPC 机制差异](#4-ipc-机制差异)
    - [4.1 管道实现差异](#41-管道实现差异)
    - [4.2 信号处理差异](#42-信号处理差异)
  - [5. 权限和安全](#5-权限和安全)
    - [5.1 用户权限模型](#51-用户权限模型)
  - [6. 性能优化](#6-性能优化)
    - [6.1 平台特定优化](#61-平台特定优化)
  - [7. 测试策略](#7-测试策略)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 跨平台开发最佳实践](#81-跨平台开发最佳实践)
  - [9. 小结](#9-小结)
    - [关键差异总结](#关键差异总结)
    - [最佳实践](#最佳实践)
    - [开发建议](#开发建议)

本章提供基于 Rust 1.92.0 的全面跨平台进程管理指南（兼容 Rust 1.90+ 特性），涵盖 Windows、Unix/Linux 和 macOS 的差异处理，以及 Rust 1.92.0 新特性在跨平台开发中的应用。

## 1. 平台差异概览

### 1.1 Windows 特性

```rust
#[cfg(windows)]
mod windows_specific {
    use std::process::Command;
    use std::os::windows::process::CommandExt;

    // Windows 特定进程管理
    pub struct WindowsProcessManager {
        job_objects: std::collections::HashMap<String, windows::Win32::System::JobObjects::HANDLE>,
    }

    impl WindowsProcessManager {
        pub fn new() -> Self {
            Self {
                job_objects: std::collections::HashMap::new(),
            }
        }

        // Windows 作业对象管理
        pub fn create_job_object(&mut self, name: &str) -> Result<(), Box<dyn std::error::Error>> {
            use windows::Win32::System::JobObjects::*;

            let job_handle = CreateJobObjectW(
                None,
                &windows::core::HSTRING::from(name)
            )?;

            self.job_objects.insert(name.to_string(), job_handle);
            Ok(())
        }

        // Windows 服务管理
        pub fn install_service(&self, service_name: &str, executable_path: &str) -> Result<(), Box<dyn std::error::Error>> {
            let mut command = Command::new("sc");
            command.args(&["create", service_name, &format!("binPath= {}", executable_path)]);

            let output = command.output()?;
            if !output.status.success() {
                return Err(format!("服务安装失败: {}", String::from_utf8_lossy(&output.stderr)).into());
            }

            Ok(())
        }

        // Windows 进程优先级设置
        pub fn set_process_priority(&self, pid: u32, priority: WindowsPriority) -> Result<(), Box<dyn std::error::Error>> {
            use windows::Win32::System::Threading::*;

            let process_handle = OpenProcess(PROCESS_SET_INFORMATION, false, pid)?;
            let priority_class = match priority {
                WindowsPriority::Idle => IDLE_PRIORITY_CLASS,
                WindowsPriority::BelowNormal => BELOW_NORMAL_PRIORITY_CLASS,
                WindowsPriority::Normal => NORMAL_PRIORITY_CLASS,
                WindowsPriority::AboveNormal => ABOVE_NORMAL_PRIORITY_CLASS,
                WindowsPriority::High => HIGH_PRIORITY_CLASS,
                WindowsPriority::Realtime => REALTIME_PRIORITY_CLASS,
            };

            SetPriorityClass(process_handle, priority_class)?;
            Ok(())
        }
    }

    #[derive(Debug, Clone)]
    pub enum WindowsPriority {
        Idle,
        BelowNormal,
        Normal,
        AboveNormal,
        High,
        Realtime,
    }
}
```

### 1.2 Unix/Linux 特性

```rust
#[cfg(unix)]
mod unix_specific {
    use std::process::Command;
    use std::os::unix::process::CommandExt;
    use nix::sys::resource::{setrlimit, Resource, ResourceLimits};
    use nix::unistd::{setuid, setgid, Uid, Gid};

    // Unix 特定进程管理
    pub struct UnixProcessManager {
        process_groups: std::collections::HashMap<u32, i32>,
    }

    impl UnixProcessManager {
        pub fn new() -> Self {
            Self {
                process_groups: std::collections::HashMap::new(),
            }
        }

        // Unix 进程组管理
        pub fn create_process_group(&mut self, pgid: i32) -> Result<(), Box<dyn std::error::Error>> {
            use nix::unistd::setpgid;
            setpgid(0, pgid)?;
            self.process_groups.insert(std::process::id(), pgid);
            Ok(())
        }

        // Unix 信号处理
        pub fn setup_signal_handlers(&self) -> Result<(), Box<dyn std::error::Error>> {
            use nix::sys::signal::{signal, SigHandler, Signal};

            unsafe {
                signal(Signal::SIGTERM, SigHandler::Handler(handle_sigterm))?;
                signal(Signal::SIGINT, SigHandler::Handler(handle_sigint))?;
                signal(Signal::SIGHUP, SigHandler::Handler(handle_sighup))?;
            }

            Ok(())
        }

        // Unix 资源限制
        pub fn set_resource_limits(&self, limits: &UnixResourceLimits) -> Result<(), Box<dyn std::error::Error>> {
            // 内存限制
            setrlimit(
                Resource::RLIMIT_AS,
                ResourceLimits::new(limits.max_memory, limits.max_memory * 2)
            )?;

            // 文件描述符限制
            setrlimit(
                Resource::RLIMIT_NOFILE,
                ResourceLimits::new(limits.max_fds, limits.max_fds * 2)
            )?;

            // CPU 时间限制
            setrlimit(
                Resource::RLIMIT_CPU,
                ResourceLimits::new(limits.max_cpu_time, limits.max_cpu_time * 2)
            )?;

            Ok(())
        }

        // Unix 用户权限设置
        pub fn drop_privileges(&self, uid: u32, gid: u32) -> Result<(), Box<dyn std::error::Error>> {
            setgid(Gid::from_raw(gid))?;
            setuid(Uid::from_raw(uid))?;
            Ok(())
        }
    }

    #[derive(Debug, Clone)]
    pub struct UnixResourceLimits {
        pub max_memory: u64,
        pub max_fds: u64,
        pub max_cpu_time: u64,
    }

    extern "C" fn handle_sigterm(_signal: i32) {
        println!("收到 SIGTERM 信号，正在清理资源...");
        std::process::exit(0);
    }

    extern "C" fn handle_sigint(_signal: i32) {
        println!("收到 SIGINT 信号，正在中断...");
        std::process::exit(1);
    }

    extern "C" fn handle_sighup(_signal: i32) {
        println!("收到 SIGHUP 信号，正在重新加载配置...");
    }
}
```

### 1.3 macOS 特性

```rust
#[cfg(target_os = "macos")]
mod macos_specific {
    use std::process::Command;

    // macOS 特定进程管理
    pub struct MacOSProcessManager {
        launchd_services: std::collections::HashMap<String, String>,
    }

    impl MacOSProcessManager {
        pub fn new() -> Self {
            Self {
                launchd_services: std::collections::HashMap::new(),
            }
        }

        // macOS Launchd 服务管理
        pub fn install_launchd_service(&mut self, service_name: &str, plist_path: &str) -> Result<(), Box<dyn std::error::Error>> {
            let mut command = Command::new("launchctl");
            command.args(&["load", plist_path]);

            let output = command.output()?;
            if !output.status.success() {
                return Err(format!("Launchd 服务安装失败: {}", String::from_utf8_lossy(&output.stderr)).into());
            }

            self.launchd_services.insert(service_name.to_string(), plist_path.to_string());
            Ok(())
        }

        // macOS 进程监控
        pub fn monitor_process_with_activity_monitor(&self, pid: u32) -> Result<ProcessInfo, Box<dyn std::error::Error>> {
            let mut command = Command::new("ps");
            command.args(&["-p", &pid.to_string(), "-o", "pid,ppid,pcpu,pmem,comm"]);

            let output = command.output()?;
            let output_str = String::from_utf8_lossy(&output.stdout);

            let lines: Vec<&str> = output_str.lines().collect();
            if lines.len() < 2 {
                return Err("无法获取进程信息".into());
            }

            let parts: Vec<&str> = lines[1].split_whitespace().collect();
            if parts.len() < 5 {
                return Err("进程信息格式错误".into());
            }

            Ok(ProcessInfo {
                pid: parts[0].parse()?,
                ppid: parts[1].parse()?,
                cpu_percent: parts[2].parse()?,
                memory_percent: parts[3].parse()?,
                command: parts[4].to_string(),
            })
        }
    }

    #[derive(Debug)]
    pub struct ProcessInfo {
        pub pid: u32,
        pub ppid: u32,
        pub cpu_percent: f64,
        pub memory_percent: f64,
        pub command: String,
    }
}
```

## 2. 跨平台抽象层

### 2.1 统一接口设计

```rust
// 跨平台进程管理抽象层
pub trait CrossPlatformProcessManager {
    fn spawn_process(&self, config: ProcessConfig) -> Result<ProcessHandle, ProcessError>;
    fn terminate_process(&self, handle: &ProcessHandle) -> Result<(), ProcessError>;
    fn wait_for_process(&self, handle: &ProcessHandle) -> Result<ProcessResult, ProcessError>;
    fn get_process_info(&self, handle: &ProcessHandle) -> Result<ProcessInfo, ProcessError>;
}

#[derive(Debug, Clone)]
pub struct ProcessConfig {
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub env_vars: std::collections::HashMap<String, String>,
    pub stdin: Option<String>,
    pub stdout: Option<String>,
    pub stderr: Option<String>,
    pub priority: ProcessPriority,
    pub resource_limits: ResourceLimits,
}

#[derive(Debug, Clone)]
pub enum ProcessPriority {
    Low,
    Normal,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub max_memory_mb: u64,
    pub max_cpu_time: std::time::Duration,
    pub max_file_descriptors: u32,
}

#[derive(Debug, Clone)]
pub struct ProcessHandle {
    pub id: String,
    pub pid: u32,
    pub platform_specific: PlatformSpecificHandle,
}

#[derive(Debug, Clone)]
pub enum PlatformSpecificHandle {
    #[cfg(windows)]
    Windows {
        job_handle: windows::Win32::System::JobObjects::HANDLE,
    },
    #[cfg(unix)]
    Unix {
        process_group: i32,
    },
    #[cfg(target_os = "macos")]
    MacOS {
        launchd_service: Option<String>,
    },
}

#[derive(Debug)]
pub struct ProcessResult {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
    pub execution_time: std::time::Duration,
}

#[derive(Debug)]
pub struct ProcessInfo {
    pub pid: u32,
    pub ppid: u32,
    pub cpu_percent: f64,
    pub memory_percent: f64,
    pub command: String,
    pub status: ProcessStatus,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Running,
    Stopped,
    Terminated,
    Zombie,
}

#[derive(Debug, thiserror::Error)]
pub enum ProcessError {
    #[error("进程启动失败: {0}")]
    SpawnFailed(String),

    #[error("进程终止失败: {0}")]
    TerminateFailed(String),

    #[error("进程等待失败: {0}")]
    WaitFailed(String),

    #[error("权限不足: {0}")]
    PermissionDenied(String),

    #[error("资源不足: {0}")]
    ResourceExhausted(String),

    #[error("平台不支持: {0}")]
    PlatformNotSupported(String),
}
```

### 2.2 平台特定实现

```rust
// Windows 实现
#[cfg(windows)]
impl CrossPlatformProcessManager for windows_specific::WindowsProcessManager {
    fn spawn_process(&self, config: ProcessConfig) -> Result<ProcessHandle, ProcessError> {
        use std::process::Command;
        use std::os::windows::process::CommandExt;

        let mut command = Command::new(&config.command);
        command.args(&config.args);

        if let Some(working_dir) = &config.working_dir {
            command.current_dir(working_dir);
        }

        for (key, value) in &config.env_vars {
            command.env(key, value);
        }

        // Windows 特定设置
        command.creation_flags(windows::Win32::System::Threading::CREATE_NEW_PROCESS_GROUP);

        let child = command.spawn()
            .map_err(|e| ProcessError::SpawnFailed(e.to_string()))?;

        let pid = child.id();

        Ok(ProcessHandle {
            id: uuid::Uuid::new_v4().to_string(),
            pid,
            platform_specific: PlatformSpecificHandle::Windows {
                job_handle: windows::Win32::System::JobObjects::HANDLE::default(),
            },
        })
    }

    fn terminate_process(&self, handle: &ProcessHandle) -> Result<(), ProcessError> {
        use windows::Win32::System::Threading::*;

        let process_handle = OpenProcess(PROCESS_TERMINATE, false, handle.pid)
            .map_err(|e| ProcessError::TerminateFailed(e.to_string()))?;

        TerminateProcess(process_handle, 1)
            .map_err(|e| ProcessError::TerminateFailed(e.to_string()))?;

        Ok(())
    }

    fn wait_for_process(&self, handle: &ProcessHandle) -> Result<ProcessResult, ProcessError> {
        use windows::Win32::System::Threading::*;

        let process_handle = OpenProcess(PROCESS_QUERY_INFORMATION, false, handle.pid)
            .map_err(|e| ProcessError::WaitFailed(e.to_string()))?;

        WaitForSingleObject(process_handle, INFINITE)
            .map_err(|e| ProcessError::WaitFailed(e.to_string()))?;

        Ok(ProcessResult {
            exit_code: 0,
            stdout: String::new(),
            stderr: String::new(),
            execution_time: std::time::Duration::from_secs(0),
        })
    }

    fn get_process_info(&self, handle: &ProcessHandle) -> Result<ProcessInfo, ProcessError> {
        use windows::Win32::System::ProcessStatus::*;

        let process_handle = OpenProcess(PROCESS_QUERY_INFORMATION, false, handle.pid)
            .map_err(|e| ProcessError::WaitFailed(e.to_string()))?;

        let mut process_info = PROCESS_MEMORY_COUNTERS::default();
        GetProcessMemoryInfo(process_handle, &mut process_handle, std::mem::size_of::<PROCESS_MEMORY_COUNTERS>() as u32)
            .map_err(|e| ProcessError::WaitFailed(e.to_string()))?;

        Ok(ProcessInfo {
            pid: handle.pid,
            ppid: 0,
            cpu_percent: 0.0,
            memory_percent: 0.0,
            command: String::new(),
            status: ProcessStatus::Running,
        })
    }
}

// Unix 实现
#[cfg(unix)]
impl CrossPlatformProcessManager for unix_specific::UnixProcessManager {
    fn spawn_process(&self, config: ProcessConfig) -> Result<ProcessHandle, ProcessError> {
        use std::process::Command;
        use std::os::unix::process::CommandExt;

        let mut command = Command::new(&config.command);
        command.args(&config.args);

        if let Some(working_dir) = &config.working_dir {
            command.current_dir(working_dir);
        }

        for (key, value) in &config.env_vars {
            command.env(key, value);
        }

        // Unix 特定设置
        command.before_exec(|| {
            // 设置进程组
            use nix::unistd::setpgid;
            setpgid(0, 0)?;
            Ok(())
        });

        let child = command.spawn()
            .map_err(|e| ProcessError::SpawnFailed(e.to_string()))?;

        let pid = child.id();

        Ok(ProcessHandle {
            id: uuid::Uuid::new_v4().to_string(),
            pid,
            platform_specific: PlatformSpecificHandle::Unix {
                process_group: pid as i32,
            },
        })
    }

    fn terminate_process(&self, handle: &ProcessHandle) -> Result<(), ProcessError> {
        use nix::sys::signal::{kill, Signal};
        use nix::unistd::Pid;

        kill(Pid::from_raw(handle.pid as i32), Signal::SIGTERM)
            .map_err(|e| ProcessError::TerminateFailed(e.to_string()))?;

        Ok(())
    }

    fn wait_for_process(&self, handle: &ProcessHandle) -> Result<ProcessResult, ProcessError> {
        use nix::sys::wait::{waitpid, WaitPidFlag, WaitStatus};
        use nix::unistd::Pid;

        match waitpid(Pid::from_raw(handle.pid as i32), Some(WaitPidFlag::WUNTRACED)) {
            Ok(WaitStatus::Exited(_, exit_code)) => {
                Ok(ProcessResult {
                    exit_code,
                    stdout: String::new(),
                    stderr: String::new(),
                    execution_time: std::time::Duration::from_secs(0),
                })
            }
            Ok(WaitStatus::Signaled(_, signal, _)) => {
                Err(ProcessError::WaitFailed(format!("进程被信号终止: {:?}", signal)))
            }
            Err(e) => Err(ProcessError::WaitFailed(e.to_string())),
            _ => Err(ProcessError::WaitFailed("未知等待状态".to_string())),
        }
    }

    fn get_process_info(&self, handle: &ProcessHandle) -> Result<ProcessInfo, ProcessError> {
        use std::process::Command;

        let mut command = Command::new("ps");
        command.args(&["-p", &handle.pid.to_string(), "-o", "pid,ppid,pcpu,pmem,comm"]);

        let output = command.output()
            .map_err(|e| ProcessError::WaitFailed(e.to_string()))?;

        let output_str = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = output_str.lines().collect();

        if lines.len() < 2 {
            return Err(ProcessError::WaitFailed("无法获取进程信息".to_string()));
        }

        let parts: Vec<&str> = lines[1].split_whitespace().collect();
        if parts.len() < 5 {
            return Err(ProcessError::WaitFailed("进程信息格式错误".to_string()));
        }

        Ok(ProcessInfo {
            pid: parts[0].parse().unwrap_or(0),
            ppid: parts[1].parse().unwrap_or(0),
            cpu_percent: parts[2].parse().unwrap_or(0.0),
            memory_percent: parts[3].parse().unwrap_or(0.0),
            command: parts[4].to_string(),
            status: ProcessStatus::Running,
        })
    }
}
```

### 2.3 条件编译策略

```rust
// 条件编译宏
macro_rules! platform_specific {
    (windows => $windows_code:block, unix => $unix_code:block, macos => $macos_code:block) => {
        #[cfg(windows)]
        $windows_code

        #[cfg(all(unix, not(target_os = "macos")))]
        $unix_code

        #[cfg(target_os = "macos")]
        $macos_code
    };
}

// 使用示例
fn get_platform_specific_process_manager() -> Box<dyn CrossPlatformProcessManager> {
    platform_specific! {
        windows => {
            Box::new(windows_specific::WindowsProcessManager::new())
        },
        unix => {
            Box::new(unix_specific::UnixProcessManager::new())
        },
        macos => {
            Box::new(macos_specific::MacOSProcessManager::new())
        }
    }
}

// 平台特定功能检测
pub struct PlatformCapabilities {
    pub supports_job_objects: bool,
    pub supports_process_groups: bool,
    pub supports_signals: bool,
    pub supports_resource_limits: bool,
    pub supports_user_switching: bool,
}

impl PlatformCapabilities {
    pub fn detect() -> Self {
        Self {
            supports_job_objects: cfg!(windows),
            supports_process_groups: cfg!(unix),
            supports_signals: cfg!(unix),
            supports_resource_limits: cfg!(unix),
            supports_user_switching: cfg!(unix),
        }
    }

    pub fn can_use_feature(&self, feature: &str) -> bool {
        match feature {
            "job_objects" => self.supports_job_objects,
            "process_groups" => self.supports_process_groups,
            "signals" => self.supports_signals,
            "resource_limits" => self.supports_resource_limits,
            "user_switching" => self.supports_user_switching,
            _ => false,
        }
    }
}
```

## 3. 进程创建差异

### 3.1 命令解析差异

```rust
// 跨平台命令解析
pub struct CrossPlatformCommandParser {
    platform: Platform,
}

#[derive(Debug, Clone)]
pub enum Platform {
    Windows,
    Unix,
    MacOS,
}

impl CrossPlatformCommandParser {
    pub fn new() -> Self {
        Self {
            platform: Self::detect_platform(),
        }
    }

    fn detect_platform() -> Platform {
        if cfg!(windows) {
            Platform::Windows
        } else if cfg!(target_os = "macos") {
            Platform::MacOS
        } else {
            Platform::Unix
        }
    }

    pub fn parse_command(&self, command: &str) -> Result<ParsedCommand, CommandParseError> {
        match self.platform {
            Platform::Windows => self.parse_windows_command(command),
            Platform::Unix | Platform::MacOS => self.parse_unix_command(command),
        }
    }

    fn parse_windows_command(&self, command: &str) -> Result<ParsedCommand, CommandParseError> {
        // Windows 命令解析逻辑
        let parts: Vec<&str> = command.split_whitespace().collect();
        if parts.is_empty() {
            return Err(CommandParseError::EmptyCommand);
        }

        let executable = parts[0];
        let args = parts[1..].iter().map(|s| s.to_string()).collect();

        // Windows 特定处理
        let executable = if executable.ends_with(".exe") {
            executable.to_string()
        } else {
            format!("{}.exe", executable)
        };

        Ok(ParsedCommand {
            executable,
            args,
            shell: None,
        })
    }

    fn parse_unix_command(&self, command: &str) -> Result<ParsedCommand, CommandParseError> {
        // Unix 命令解析逻辑
        let parts: Vec<&str> = command.split_whitespace().collect();
        if parts.is_empty() {
            return Err(CommandParseError::EmptyCommand);
        }

        let executable = parts[0];
        let args = parts[1..].iter().map(|s| s.to_string()).collect();

        // Unix 特定处理
        let shell = if executable.contains(" ") {
            Some("/bin/sh".to_string())
        } else {
            None
        };

        Ok(ParsedCommand {
            executable: executable.to_string(),
            args,
            shell,
        })
    }
}

#[derive(Debug)]
pub struct ParsedCommand {
    pub executable: String,
    pub args: Vec<String>,
    pub shell: Option<String>,
}

#[derive(Debug, thiserror::Error)]
pub enum CommandParseError {
    #[error("空命令")]
    EmptyCommand,

    #[error("无效的命令格式: {0}")]
    InvalidFormat(String),

    #[error("不支持的平台: {0}")]
    UnsupportedPlatform(String),
}
```

### 3.2 环境变量处理

```rust
// 跨平台环境变量处理
pub struct CrossPlatformEnvManager {
    platform: Platform,
}

impl CrossPlatformEnvManager {
    pub fn new() -> Self {
        Self {
            platform: CrossPlatformCommandParser::detect_platform(),
        }
    }

    pub fn get_system_env(&self) -> std::collections::HashMap<String, String> {
        match self.platform {
            Platform::Windows => self.get_windows_env(),
            Platform::Unix | Platform::MacOS => self.get_unix_env(),
        }
    }

    fn get_windows_env(&self) -> std::collections::HashMap<String, String> {
        let mut env_vars = std::collections::HashMap::new();

        // Windows 特定环境变量
        env_vars.insert("OS".to_string(), "Windows_NT".to_string());
        env_vars.insert("COMSPEC".to_string(), "C:\\Windows\\System32\\cmd.exe".to_string());
        env_vars.insert("PATH".to_string(), self.get_windows_path());

        // 添加系统环境变量
        for (key, value) in std::env::vars() {
            env_vars.insert(key, value);
        }

        env_vars
    }

    fn get_unix_env(&self) -> std::collections::HashMap<String, String> {
        let mut env_vars = std::collections::HashMap::new();

        // Unix 特定环境变量
        env_vars.insert("SHELL".to_string(), "/bin/bash".to_string());
        env_vars.insert("PATH".to_string(), self.get_unix_path());
        env_vars.insert("HOME".to_string(), std::env::var("HOME").unwrap_or_default());

        // 添加系统环境变量
        for (key, value) in std::env::vars() {
            env_vars.insert(key, value);
        }

        env_vars
    }

    fn get_windows_path(&self) -> String {
        // Windows PATH 环境变量
        "C:\\Windows\\System32;C:\\Windows;C:\\Windows\\System32\\Wbem".to_string()
    }

    fn get_unix_path(&self) -> String {
        // Unix PATH 环境变量
        "/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin".to_string()
    }

    pub fn sanitize_env(&self, env_vars: &mut std::collections::HashMap<String, String>) {
        match self.platform {
            Platform::Windows => self.sanitize_windows_env(env_vars),
            Platform::Unix | Platform::MacOS => self.sanitize_unix_env(env_vars),
        }
    }

    fn sanitize_windows_env(&self, env_vars: &mut std::collections::HashMap<String, String>) {
        // Windows 环境变量清理
        let dangerous_vars = ["PATH", "SYSTEMROOT", "WINDIR"];
        for var in &dangerous_vars {
            if let Some(value) = env_vars.get(*var) {
                if value.contains("..") || value.contains(";") {
                    env_vars.remove(*var);
                }
            }
        }
    }

    fn sanitize_unix_env(&self, env_vars: &mut std::collections::HashMap<String, String>) {
        // Unix 环境变量清理
        let dangerous_vars = ["PATH", "LD_LIBRARY_PATH", "LD_PRELOAD"];
        for var in &dangerous_vars {
            if let Some(value) = env_vars.get(*var) {
                if value.contains("..") || value.contains(":") {
                    env_vars.remove(*var);
                }
            }
        }
    }
}
```

### 3.3 工作目录设置

```rust
// 跨平台工作目录处理
pub struct CrossPlatformWorkingDir {
    platform: Platform,
}

impl CrossPlatformWorkingDir {
    pub fn new() -> Self {
        Self {
            platform: CrossPlatformCommandParser::detect_platform(),
        }
    }

    pub fn validate_working_dir(&self, dir: &str) -> Result<(), WorkingDirError> {
        match self.platform {
            Platform::Windows => self.validate_windows_dir(dir),
            Platform::Unix | Platform::MacOS => self.validate_unix_dir(dir),
        }
    }

    fn validate_windows_dir(&self, dir: &str) -> Result<(), WorkingDirError> {
        // Windows 目录验证
        if dir.contains("..") || dir.contains("\\") {
            return Err(WorkingDirError::InvalidPath(dir.to_string()));
        }

        if !std::path::Path::new(dir).exists() {
            return Err(WorkingDirError::DirectoryNotFound(dir.to_string()));
        }

        Ok(())
    }

    fn validate_unix_dir(&self, dir: &str) -> Result<(), WorkingDirError> {
        // Unix 目录验证
        if dir.contains("..") || dir.starts_with("/") {
            return Err(WorkingDirError::InvalidPath(dir.to_string()));
        }

        if !std::path::Path::new(dir).exists() {
            return Err(WorkingDirError::DirectoryNotFound(dir.to_string()));
        }

        Ok(())
    }

    pub fn get_safe_working_dir(&self) -> String {
        match self.platform {
            Platform::Windows => "C:\\temp".to_string(),
            Platform::Unix | Platform::MacOS => "/tmp".to_string(),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum WorkingDirError {
    #[error("无效的路径: {0}")]
    InvalidPath(String),

    #[error("目录不存在: {0}")]
    DirectoryNotFound(String),

    #[error("权限不足: {0}")]
    PermissionDenied(String),
}
```

## 4. IPC 机制差异

### 4.1 管道实现差异

```rust
// 跨平台管道实现
pub struct CrossPlatformPipe {
    platform: Platform,
}

impl CrossPlatformPipe {
    pub fn new() -> Self {
        Self {
            platform: CrossPlatformCommandParser::detect_platform(),
        }
    }

    pub fn create_pipe(&self) -> Result<PipeHandle, PipeError> {
        match self.platform {
            Platform::Windows => self.create_windows_pipe(),
            Platform::Unix | Platform::MacOS => self.create_unix_pipe(),
        }
    }

    fn create_windows_pipe(&self) -> Result<PipeHandle, PipeError> {
        use windows::Win32::System::Pipes::*;

        let pipe_name = format!("\\\\.\\pipe\\rust_pipe_{}", uuid::Uuid::new_v4());

        let pipe_handle = CreateNamedPipeW(
            &windows::core::HSTRING::from(&pipe_name),
            PIPE_ACCESS_DUPLEX,
            PIPE_TYPE_BYTE | PIPE_WAIT,
            1,
            4096,
            4096,
            0,
            None,
        ).map_err(|e| PipeError::CreationFailed(e.to_string()))?;

        Ok(PipeHandle {
            name: pipe_name,
            handle: pipe_handle,
            platform: PlatformSpecificPipe::Windows {
                pipe_handle,
            },
        })
    }

    fn create_unix_pipe(&self) -> Result<PipeHandle, PipeError> {
        use nix::unistd::pipe;

        let (read_fd, write_fd) = pipe()
            .map_err(|e| PipeError::CreationFailed(e.to_string()))?;

        Ok(PipeHandle {
            name: format!("pipe_{}", uuid::Uuid::new_v4()),
            handle: read_fd,
            platform: PlatformSpecificPipe::Unix {
                read_fd,
                write_fd,
            },
        })
    }
}

#[derive(Debug)]
pub struct PipeHandle {
    pub name: String,
    pub handle: i32,
    pub platform: PlatformSpecificPipe,
}

#[derive(Debug)]
pub enum PlatformSpecificPipe {
    #[cfg(windows)]
    Windows {
        pipe_handle: windows::Win32::System::Pipes::HANDLE,
    },
    #[cfg(unix)]
    Unix {
        read_fd: i32,
        write_fd: i32,
    },
}

#[derive(Debug, thiserror::Error)]
pub enum PipeError {
    #[error("管道创建失败: {0}")]
    CreationFailed(String),

    #[error("管道连接失败: {0}")]
    ConnectionFailed(String),

    #[error("管道读写失败: {0}")]
    IoFailed(String),
}
```

### 4.2 信号处理差异

```rust
// 跨平台信号处理
pub struct CrossPlatformSignalHandler {
    platform: Platform,
}

impl CrossPlatformSignalHandler {
    pub fn new() -> Self {
        Self {
            platform: CrossPlatformCommandParser::detect_platform(),
        }
    }

    pub fn setup_signal_handlers(&self) -> Result<(), SignalError> {
        match self.platform {
            Platform::Windows => self.setup_windows_handlers(),
            Platform::Unix | Platform::MacOS => self.setup_unix_handlers(),
        }
    }

    fn setup_windows_handlers(&self) -> Result<(), SignalError> {
        // Windows 使用事件对象而不是信号
        use windows::Win32::System::Threading::*;

        let event_handle = CreateEventW(
            None,
            true,
            false,
            &windows::core::HSTRING::from("RustProcessEvent")
        ).map_err(|e| SignalError::SetupFailed(e.to_string()))?;

        // 设置控制台事件处理
        unsafe {
            SetConsoleCtrlHandler(Some(console_ctrl_handler), true)
                .map_err(|e| SignalError::SetupFailed(e.to_string()))?;
        }

        Ok(())
    }

    fn setup_unix_handlers(&self) -> Result<(), SignalError> {
        use nix::sys::signal::{signal, SigHandler, Signal};

        unsafe {
            signal(Signal::SIGTERM, SigHandler::Handler(handle_sigterm))
                .map_err(|e| SignalError::SetupFailed(e.to_string()))?;

            signal(Signal::SIGINT, SigHandler::Handler(handle_sigint))
                .map_err(|e| SignalError::SetupFailed(e.to_string()))?;

            signal(Signal::SIGHUP, SigHandler::Handler(handle_sighup))
                .map_err(|e| SignalError::SetupFailed(e.to_string()))?;
        }

        Ok(())
    }
}

#[cfg(windows)]
extern "system" fn console_ctrl_handler(ctrl_type: u32) -> i32 {
    match ctrl_type {
        CTRL_C_EVENT | CTRL_BREAK_EVENT | CTRL_CLOSE_EVENT => {
            println!("收到控制台事件，正在清理...");
            1
        }
        _ => 0,
    }
}

#[cfg(unix)]
extern "C" fn handle_sigterm(_signal: i32) {
    println!("收到 SIGTERM 信号，正在清理...");
    std::process::exit(0);
}

#[cfg(unix)]
extern "C" fn handle_sigint(_signal: i32) {
    println!("收到 SIGINT 信号，正在中断...");
    std::process::exit(1);
}

#[cfg(unix)]
extern "C" fn handle_sighup(_signal: i32) {
    println!("收到 SIGHUP 信号，正在重新加载配置...");
}

#[derive(Debug, thiserror::Error)]
pub enum SignalError {
    #[error("信号处理设置失败: {0}")]
    SetupFailed(String),

    #[error("信号发送失败: {0}")]
    SendFailed(String),

    #[error("不支持的信号: {0}")]
    UnsupportedSignal(String),
}
```

## 5. 权限和安全

### 5.1 用户权限模型

```rust
// 跨平台用户权限管理
pub struct CrossPlatformUserManager {
    platform: Platform,
}

impl CrossPlatformUserManager {
    pub fn new() -> Self {
        Self {
            platform: CrossPlatformCommandParser::detect_platform(),
        }
    }

    pub fn get_current_user(&self) -> Result<UserInfo, UserError> {
        match self.platform {
            Platform::Windows => self.get_windows_user(),
            Platform::Unix | Platform::MacOS => self.get_unix_user(),
        }
    }

    fn get_windows_user(&self) -> Result<UserInfo, UserError> {
        use windows::Win32::System::Threading::*;

        let process_handle = GetCurrentProcess();
        let mut token_handle = std::ptr::null_mut();

        OpenProcessToken(process_handle, TOKEN_QUERY, &mut token_handle)
            .map_err(|e| UserError::QueryFailed(e.to_string()))?;

        let mut user_info_size = 0u32;
        GetTokenInformation(token_handle, TokenUser, None, 0, &mut user_info_size)
            .map_err(|e| UserError::QueryFailed(e.to_string()))?;

        Ok(UserInfo {
            uid: 0,
            gid: 0,
            username: "windows_user".to_string(),
            groups: Vec::new(),
        })
    }

    fn get_unix_user(&self) -> Result<UserInfo, UserError> {
        use nix::unistd::{getuid, getgid, getpwuid, getgrgid};

        let uid = getuid();
        let gid = getgid();

        let username = getpwuid(uid)
            .map_err(|e| UserError::QueryFailed(e.to_string()))?
            .map(|pwd| pwd.name)
            .unwrap_or_else(|| uid.to_string());

        let groups = vec![gid.to_string()];

        Ok(UserInfo {
            uid: uid.as_raw(),
            gid: gid.as_raw(),
            username,
            groups,
        })
    }

    pub fn can_switch_user(&self, target_user: &str) -> Result<bool, UserError> {
        match self.platform {
            Platform::Windows => self.can_switch_windows_user(target_user),
            Platform::Unix | Platform::MacOS => self.can_switch_unix_user(target_user),
        }
    }

    fn can_switch_windows_user(&self, _target_user: &str) -> Result<bool, UserError> {
        // Windows 用户切换检查
        Ok(false) // 简化实现
    }

    fn can_switch_unix_user(&self, target_user: &str) -> Result<bool, UserError> {
        use nix::unistd::{getuid, getpwuid};

        let current_uid = getuid();
        if current_uid.as_raw() == 0 {
            return Ok(true); // root 可以切换到任何用户
        }

        // 检查目标用户是否存在
        let target_pwd = getpwuid(nix::unistd::Uid::from_raw(0))
            .map_err(|e| UserError::QueryFailed(e.to_string()))?;

        Ok(target_pwd.is_some())
    }
}

#[derive(Debug)]
pub struct UserInfo {
    pub uid: u32,
    pub gid: u32,
    pub username: String,
    pub groups: Vec<String>,
}

#[derive(Debug, thiserror::Error)]
pub enum UserError {
    #[error("用户查询失败: {0}")]
    QueryFailed(String),

    #[error("权限不足: {0}")]
    PermissionDenied(String),

    #[error("用户不存在: {0}")]
    UserNotFound(String),
}
```

## 6. 性能优化

### 6.1 平台特定优化

```rust
// 跨平台性能优化
pub struct CrossPlatformOptimizer {
    platform: Platform,
    capabilities: PlatformCapabilities,
}

impl CrossPlatformOptimizer {
    pub fn new() -> Self {
        Self {
            platform: CrossPlatformCommandParser::detect_platform(),
            capabilities: PlatformCapabilities::detect(),
        }
    }

    pub fn optimize_process_creation(&self, config: &mut ProcessConfig) -> Result<(), OptimizationError> {
        match self.platform {
            Platform::Windows => self.optimize_windows_process(config),
            Platform::Unix | Platform::MacOS => self.optimize_unix_process(config),
        }
    }

    fn optimize_windows_process(&self, config: &mut ProcessConfig) -> Result<(), OptimizationError> {
        // Windows 特定优化
        if self.capabilities.supports_job_objects {
            // 使用作业对象进行进程管理
            config.resource_limits.max_memory_mb = config.resource_limits.max_memory_mb.min(1024);
        }

        Ok(())
    }

    fn optimize_unix_process(&self, config: &mut ProcessConfig) -> Result<(), OptimizationError> {
        // Unix 特定优化
        if self.capabilities.supports_resource_limits {
            // 设置资源限制
            config.resource_limits.max_memory_mb = config.resource_limits.max_memory_mb.min(512);
            config.resource_limits.max_file_descriptors = config.resource_limits.max_file_descriptors.min(1024);
        }

        Ok(())
    }

    pub fn get_optimal_pool_size(&self) -> usize {
        match self.platform {
            Platform::Windows => 10, // Windows 进程创建开销较大
            Platform::Unix | Platform::MacOS => 20, // Unix 进程创建较快
        }
    }

    pub fn get_optimal_timeout(&self) -> std::time::Duration {
        match self.platform {
            Platform::Windows => std::time::Duration::from_secs(30), // Windows 较慢
            Platform::Unix | Platform::MacOS => std::time::Duration::from_secs(10), // Unix 较快
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum OptimizationError {
    #[error("优化失败: {0}")]
    OptimizationFailed(String),

    #[error("平台不支持: {0}")]
    PlatformNotSupported(String),
}
```

## 7. 测试策略

```rust
// 跨平台测试框架
pub struct CrossPlatformTestSuite {
    platform: Platform,
    test_results: std::collections::HashMap<String, TestResult>,
}

#[derive(Debug)]
pub struct TestResult {
    pub passed: bool,
    pub duration: std::time::Duration,
    pub error: Option<String>,
}

impl CrossPlatformTestSuite {
    pub fn new() -> Self {
        Self {
            platform: CrossPlatformCommandParser::detect_platform(),
            test_results: std::collections::HashMap::new(),
        }
    }

    pub async fn run_all_tests(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // 基础功能测试
        self.test_basic_process_creation().await;
        self.test_process_termination().await;
        self.test_process_waiting().await;

        // 平台特定测试
        match self.platform {
            Platform::Windows => self.test_windows_specific().await,
            Platform::Unix | Platform::MacOS => self.test_unix_specific().await,
        }

        // 性能测试
        self.test_performance().await;

        Ok(())
    }

    async fn test_basic_process_creation(&mut self) {
        let start = std::time::Instant::now();

        let result = std::process::Command::new("echo")
            .arg("test")
            .output();

        let duration = start.elapsed();

        self.test_results.insert(
            "basic_process_creation".to_string(),
            TestResult {
                passed: result.is_ok(),
                duration,
                error: result.err().map(|e| e.to_string()),
            },
        );
    }

    async fn test_windows_specific(&mut self) {
        // Windows 特定测试
        let start = std::time::Instant::now();

        let result = std::process::Command::new("cmd")
            .args(&["/C", "echo windows_test"])
            .output();

        let duration = start.elapsed();

        self.test_results.insert(
            "windows_specific".to_string(),
            TestResult {
                passed: result.is_ok(),
                duration,
                error: result.err().map(|e| e.to_string()),
            },
        );
    }

    async fn test_unix_specific(&mut self) {
        // Unix 特定测试
        let start = std::time::Instant::now();

        let result = std::process::Command::new("sh")
            .args(&["-c", "echo unix_test"])
            .output();

        let duration = start.elapsed();

        self.test_results.insert(
            "unix_specific".to_string(),
            TestResult {
                passed: result.is_ok(),
                duration,
                error: result.err().map(|e| e.to_string()),
            },
        );
    }

    async fn test_performance(&mut self) {
        // 性能测试
        let iterations = 100;
        let mut total_duration = std::time::Duration::from_secs(0);
        let mut success_count = 0;

        for _ in 0..iterations {
            let start = std::time::Instant::now();

            let result = std::process::Command::new("echo")
                .arg("performance_test")
                .output();

            let duration = start.elapsed();
            total_duration += duration;

            if result.is_ok() {
                success_count += 1;
            }
        }

        let avg_duration = total_duration / iterations;
        let success_rate = success_count as f64 / iterations as f64;

        self.test_results.insert(
            "performance".to_string(),
            TestResult {
                passed: success_rate > 0.95,
                duration: avg_duration,
                error: if success_rate <= 0.95 {
                    Some(format!("成功率过低: {:.2}%", success_rate * 100.0))
                } else {
                    None
                },
            },
        );
    }

    pub fn generate_report(&self) -> String {
        let mut report = String::new();

        report.push_str(&format!("# 跨平台测试报告 - {}\n\n", self.platform));

        for (test_name, result) in &self.test_results {
            report.push_str(&format!(
                "## {}\n- 状态: {}\n- 耗时: {:?}\n",
                test_name,
                if result.passed { "通过" } else { "失败" },
                result.duration
            ));

            if let Some(error) = &result.error {
                report.push_str(&format!("- 错误: {}\n", error));
            }

            report.push_str("\n");
        }

        report
    }
}
```

## 8. 最佳实践

### 8.1 跨平台开发最佳实践

```rust
// 跨平台开发最佳实践
pub struct CrossPlatformBestPractices {
    platform: Platform,
}

impl CrossPlatformBestPractices {
    pub fn new() -> Self {
        Self {
            platform: CrossPlatformCommandParser::detect_platform(),
        }
    }

    pub fn get_recommendations(&self) -> Vec<Recommendation> {
        let mut recommendations = Vec::new();

        // 通用建议
        recommendations.push(Recommendation {
            category: "通用".to_string(),
            priority: Priority::High,
            description: "始终使用标准库的跨平台 API".to_string(),
            example: "使用 std::process::Command 而不是平台特定的 API".to_string(),
        });

        // 平台特定建议
        match self.platform {
            Platform::Windows => {
                recommendations.push(Recommendation {
                    category: "Windows".to_string(),
                    priority: Priority::Medium,
                    description: "使用作业对象管理进程组".to_string(),
                    example: "使用 CreateJobObject 和 AssignProcessToJobObject".to_string(),
                });
            }
            Platform::Unix | Platform::MacOS => {
                recommendations.push(Recommendation {
                    category: "Unix".to_string(),
                    priority: Priority::Medium,
                    description: "正确处理信号和进程组".to_string(),
                    example: "使用 setpgid 和 signal 函数".to_string(),
                });
            }
        }

        recommendations
    }

    pub fn validate_config(&self, config: &ProcessConfig) -> Vec<ValidationIssue> {
        let mut issues = Vec::new();

        // 通用验证
        if config.command.is_empty() {
            issues.push(ValidationIssue {
                severity: Severity::Error,
                message: "命令不能为空".to_string(),
                suggestion: "提供有效的命令".to_string(),
            });
        }

        // 平台特定验证
        match self.platform {
            Platform::Windows => {
                if config.command.contains("/") && !config.command.contains("\\") {
                    issues.push(ValidationIssue {
                        severity: Severity::Warning,
                        message: "Windows 路径应使用反斜杠".to_string(),
                        suggestion: "使用 \\ 而不是 /".to_string(),
                    });
                }
            }
            Platform::Unix | Platform::MacOS => {
                if config.command.contains("\\") {
                    issues.push(ValidationIssue {
                        severity: Severity::Warning,
                        message: "Unix 路径应使用正斜杠".to_string(),
                        suggestion: "使用 / 而不是 \\".to_string(),
                    });
                }
            }
        }

        issues
    }
}

#[derive(Debug)]
pub struct Recommendation {
    pub category: String,
    pub priority: Priority,
    pub description: String,
    pub example: String,
}

#[derive(Debug)]
pub enum Priority {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug)]
pub struct ValidationIssue {
    pub severity: Severity,
    pub message: String,
    pub suggestion: String,
}

#[derive(Debug)]
pub enum Severity {
    Info,
    Warning,
    Error,
    Critical,
}
```

## 9. 小结

跨平台进程管理是 Rust 系统编程中的重要主题，需要充分考虑不同平台的差异和特性：

### 关键差异总结

1. **进程创建**：Windows 使用作业对象，Unix 使用进程组
2. **信号处理**：Windows 使用事件对象，Unix 使用信号
3. **权限模型**：Windows 使用 ACL，Unix 使用 UID/GID
4. **资源限制**：Windows 使用作业对象，Unix 使用 rlimit
5. **IPC 机制**：Windows 使用命名管道，Unix 使用匿名管道

### 最佳实践

1. **使用抽象层**：统一的接口设计
2. **条件编译**：平台特定代码分离
3. **错误处理**：完善的错误处理机制
4. **性能优化**：平台特定优化策略
5. **测试覆盖**：全面的跨平台测试

### 开发建议

1. **优先使用标准库**：`std::process` 提供跨平台支持
2. **平台特定功能**：使用条件编译处理
3. **错误处理**：统一的错误类型和处理机制
4. **性能考虑**：根据平台特性优化
5. **安全第一**：权限控制和资源限制

通过合理的抽象和平台特定处理，可以构建出既跨平台又高性能的进程管理系统。
