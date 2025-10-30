# C07-06. 跨平台进程管理

## 目录

- [C07-06. 跨平台进程管理](#c07-06-跨平台进程管理)
  - [目录](#目录)
  - [1. 平台差异概述](#1-平台差异概述)
    - [1.1 主要平台差异](#11-主要平台差异)
    - [1.2 路径处理](#12-路径处理)
  - [2. Windows 特定功能](#2-windows-特定功能)
    - [2.1 Windows 进程管理](#21-windows-进程管理)
    - [2.2 Windows 服务管理](#22-windows-服务管理)
  - [3. Unix/Linux 特定功能](#3-unixlinux-特定功能)
    - [3.1 Unix 进程管理](#31-unix-进程管理)
    - [3.2 Systemd 服务管理](#32-systemd-服务管理)
  - [4. macOS 特定功能](#4-macos-特定功能)
    - [4.1 Launchd 服务管理](#41-launchd-服务管理)
  - [5. 跨平台兼容性处理](#5-跨平台兼容性处理)
    - [5.1 统一接口抽象](#51-统一接口抽象)
    - [5.2 环境变量和路径处理](#52-环境变量和路径处理)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 跨平台测试](#61-跨平台测试)
    - [6.2 错误处理策略](#62-错误处理策略)
  - [7. 总结](#7-总结)

本章深入探讨 Rust 中的跨平台进程管理，包括 Windows、Linux、macOS 等不同平台的特性差异、兼容性处理和最佳实践。

## 1. 平台差异概述

### 1.1 主要平台差异

```rust
use std::process::{Command, Stdio};
use std::os::unix::process::CommandExt as UnixCommandExt;
use std::os::windows::process::CommandExt as WindowsCommandExt;

pub struct CrossPlatformProcessManager {
    platform: Platform,
    config: CrossPlatformConfig,
}

#[derive(Debug, Clone)]
pub enum Platform {
    Windows,
    Linux,
    MacOS,
    Unix,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct CrossPlatformConfig {
    pub default_shell: String,
    pub path_separator: char,
    pub executable_extension: String,
    pub temp_dir: String,
    pub max_command_length: usize,
    pub supports_process_groups: bool,
    pub supports_signals: bool,
    pub supports_job_control: bool,
}

impl CrossPlatformProcessManager {
    pub fn new() -> Self {
        let platform = Self::detect_platform();
        let config = Self::get_platform_config(&platform);

        Self {
            platform,
            config,
        }
    }

    fn detect_platform() -> Platform {
        if cfg!(target_os = "windows") {
            Platform::Windows
        } else if cfg!(target_os = "linux") {
            Platform::Linux
        } else if cfg!(target_os = "macos") {
            Platform::MacOS
        } else if cfg!(unix) {
            Platform::Unix
        } else {
            Platform::Unknown
        }
    }

    fn get_platform_config(platform: &Platform) -> CrossPlatformConfig {
        match platform {
            Platform::Windows => CrossPlatformConfig {
                default_shell: "cmd.exe".to_string(),
                path_separator: '\\',
                executable_extension: ".exe".to_string(),
                temp_dir: std::env::var("TEMP").unwrap_or_else(|_| "C:\\Temp".to_string()),
                max_command_length: 8191,
                supports_process_groups: false,
                supports_signals: false,
                supports_job_control: true,
            },
            Platform::Linux => CrossPlatformConfig {
                default_shell: "/bin/bash".to_string(),
                path_separator: '/',
                executable_extension: String::new(),
                temp_dir: "/tmp".to_string(),
                max_command_length: 131072,
                supports_process_groups: true,
                supports_signals: true,
                supports_job_control: true,
            },
            Platform::MacOS => CrossPlatformConfig {
                default_shell: "/bin/zsh".to_string(),
                path_separator: '/',
                executable_extension: String::new(),
                temp_dir: "/tmp".to_string(),
                max_command_length: 131072,
                supports_process_groups: true,
                supports_signals: true,
                supports_job_control: true,
            },
            Platform::Unix => CrossPlatformConfig {
                default_shell: "/bin/sh".to_string(),
                path_separator: '/',
                executable_extension: String::new(),
                temp_dir: "/tmp".to_string(),
                max_command_length: 131072,
                supports_process_groups: true,
                supports_signals: true,
                supports_job_control: true,
            },
            Platform::Unknown => CrossPlatformConfig {
                default_shell: "sh".to_string(),
                path_separator: '/',
                executable_extension: String::new(),
                temp_dir: "/tmp".to_string(),
                max_command_length: 131072,
                supports_process_groups: false,
                supports_signals: false,
                supports_job_control: false,
            },
        }
    }

    pub async fn execute_command(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<CommandResult, Box<dyn std::error::Error>> {
        let mut cmd = Command::new(command);
        cmd.args(args);

        // 平台特定的配置
        match self.platform {
            Platform::Windows => {
                // Windows 特定配置
                cmd.creation_flags(0x08000000); // CREATE_NO_WINDOW
            }
            Platform::Linux | Platform::MacOS | Platform::Unix => {
                // Unix 特定配置
                cmd.process_group(0); // 创建新的进程组
            }
            _ => {}
        }

        cmd.stdin(Stdio::piped())
           .stdout(Stdio::piped())
           .stderr(Stdio::piped());

        let output = cmd.output()?;

        Ok(CommandResult {
            exit_code: output.status.code(),
            stdout: output.stdout,
            stderr: output.stderr,
            platform: self.platform.clone(),
        })
    }
}

#[derive(Debug)]
pub struct CommandResult {
    pub exit_code: Option<i32>,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub platform: Platform,
}
```

### 1.2 路径处理

```rust
use std::path::{Path, PathBuf};

pub struct CrossPlatformPath {
    path: PathBuf,
    platform: Platform,
}

impl CrossPlatformPath {
    pub fn new(path: &str) -> Self {
        let platform = CrossPlatformProcessManager::detect_platform();
        let path = PathBuf::from(path);

        Self { path, platform }
    }

    pub fn normalize(&self) -> PathBuf {
        match self.platform {
            Platform::Windows => {
                // Windows 路径规范化
                let mut normalized = self.path.clone();

                // 转换为正斜杠
                if let Some(path_str) = normalized.to_str() {
                    let normalized_str = path_str.replace('\\', "/");
                    normalized = PathBuf::from(normalized_str);
                }

                normalized
            }
            _ => {
                // Unix 路径规范化
                self.path.canonicalize().unwrap_or(self.path.clone())
            }
        }
    }

    pub fn join(&self, other: &str) -> PathBuf {
        let other_path = PathBuf::from(other);
        self.path.join(other_path)
    }

    pub fn exists(&self) -> bool {
        self.path.exists()
    }

    pub fn is_executable(&self) -> bool {
        match self.platform {
            Platform::Windows => {
                // Windows 检查文件扩展名
                if let Some(extension) = self.path.extension() {
                    extension == "exe" || extension == "bat" || extension == "cmd"
                } else {
                    false
                }
            }
            _ => {
                // Unix 检查执行权限
                use std::os::unix::fs::PermissionsExt;
                if let Ok(metadata) = std::fs::metadata(&self.path) {
                    let permissions = metadata.permissions();
                    permissions.mode() & 0o111 != 0
                } else {
                    false
                }
            }
        }
    }

    pub fn to_string(&self) -> String {
        self.path.to_string_lossy().to_string()
    }
}
```

## 2. Windows 特定功能

### 2.1 Windows 进程管理

```rust
#[cfg(target_os = "windows")]
use std::os::windows::process::CommandExt;

#[cfg(target_os = "windows")]
pub struct WindowsProcessManager {
    job_objects: std::collections::HashMap<String, windows::Win32::System::JobObjects::HANDLE>,
}

#[cfg(target_os = "windows")]
impl WindowsProcessManager {
    pub fn new() -> Self {
        Self {
            job_objects: std::collections::HashMap::new(),
        }
    }

    pub async fn create_process_with_job(
        &mut self,
        command: &str,
        args: &[String],
        job_name: &str,
    ) -> Result<u32, Box<dyn std::error::Error>> {
        use windows::Win32::System::JobObjects::*;
        use windows::Win32::Foundation::*;
        use windows::Win32::System::Threading::*;

        // 创建作业对象
        let job_handle = CreateJobObjectW(
            None,
            &windows::core::HSTRING::from(job_name),
        )?;

        // 配置作业对象
        let mut job_limits = JOBOBJECT_EXTENDED_LIMIT_INFORMATION {
            BasicLimitInformation: JOBOBJECT_BASIC_LIMIT_INFORMATION {
                LimitFlags: JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE,
                ..Default::default()
            },
            ..Default::default()
        };

        SetInformationJobObject(
            job_handle,
            JobObjectExtendedLimitInformation,
            &job_limits as *const _ as *const _,
            std::mem::size_of::<JOBOBJECT_EXTENDED_LIMIT_INFORMATION>() as u32,
        )?;

        // 创建进程
        let mut cmd = std::process::Command::new(command);
        cmd.args(args);

        // 设置进程创建标志
        cmd.creation_flags(
            CREATE_NEW_PROCESS_GROUP |
            CREATE_NO_WINDOW |
            DETACHED_PROCESS
        );

        let mut child = cmd.spawn()?;
        let pid = child.id();

        // 将进程分配给作业对象
        AssignProcessToJobObject(job_handle, HANDLE(pid as isize))?;

        // 保存作业对象句柄
        self.job_objects.insert(job_name.to_string(), job_handle);

        Ok(pid)
    }

    pub async fn terminate_job(&mut self, job_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(job_handle) = self.job_objects.remove(job_name) {
            use windows::Win32::System::JobObjects::*;

            TerminateJobObject(job_handle, 1)?;
            CloseHandle(job_handle)?;
        }

        Ok(())
    }

    pub async fn get_job_info(&self, job_name: &str) -> Result<JobInfo, Box<dyn std::error::Error>> {
        if let Some(job_handle) = self.job_objects.get(job_name) {
            use windows::Win32::System::JobObjects::*;

            let mut job_info = JOBOBJECT_BASIC_ACCOUNTING_INFORMATION::default();
            let mut return_length = 0;

            QueryInformationJobObject(
                *job_handle,
                JobObjectBasicAccountingInformation,
                &mut job_info as *mut _ as *mut _,
                std::mem::size_of::<JOBOBJECT_BASIC_ACCOUNTING_INFORMATION>() as u32,
                &mut return_length,
            )?;

            Ok(JobInfo {
                total_processes: job_info.TotalProcesses,
                active_processes: job_info.ActiveProcesses,
                total_terminated_processes: job_info.TotalTerminatedProcesses,
            })
        } else {
            Err("作业对象未找到".into())
        }
    }
}

#[cfg(target_os = "windows")]
#[derive(Debug)]
pub struct JobInfo {
    pub total_processes: u32,
    pub active_processes: u32,
    pub total_terminated_processes: u32,
}
```

### 2.2 Windows 服务管理

```rust
#[cfg(target_os = "windows")]
pub struct WindowsServiceManager;

#[cfg(target_os = "windows")]
impl WindowsServiceManager {
    pub async fn install_service(
        &self,
        service_name: &str,
        display_name: &str,
        executable_path: &str,
        description: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        use windows::Win32::System::Services::*;

        let service_manager = OpenSCManagerW(
            None,
            None,
            SC_MANAGER_CREATE_SERVICE,
        )?;

        let service = CreateServiceW(
            service_manager,
            &windows::core::HSTRING::from(service_name),
            &windows::core::HSTRING::from(display_name),
            SERVICE_ALL_ACCESS,
            SERVICE_WIN32_OWN_PROCESS,
            SERVICE_AUTO_START,
            SERVICE_ERROR_NORMAL,
            &windows::core::HSTRING::from(executable_path),
            None,
            None,
            None,
            None,
            None,
        )?;

        // 设置服务描述
        let description = windows::core::HSTRING::from(description);
        ChangeServiceConfig2W(
            service,
            SERVICE_CONFIG_DESCRIPTION,
            &description as *const _ as *const _,
        )?;

        CloseServiceHandle(service)?;
        CloseServiceHandle(service_manager)?;

        Ok(())
    }

    pub async fn start_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        use windows::Win32::System::Services::*;

        let service_manager = OpenSCManagerW(
            None,
            None,
            SC_MANAGER_CONNECT,
        )?;

        let service = OpenServiceW(
            service_manager,
            &windows::core::HSTRING::from(service_name),
            SERVICE_START,
        )?;

        StartServiceW(service, None, None)?;

        CloseServiceHandle(service)?;
        CloseServiceHandle(service_manager)?;

        Ok(())
    }

    pub async fn stop_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        use windows::Win32::System::Services::*;

        let service_manager = OpenSCManagerW(
            None,
            None,
            SC_MANAGER_CONNECT,
        )?;

        let service = OpenServiceW(
            service_manager,
            &windows::core::HSTRING::from(service_name),
            SERVICE_STOP,
        )?;

        let mut status = SERVICE_STATUS::default();
        ControlService(service, SERVICE_CONTROL_STOP, &mut status)?;

        CloseServiceHandle(service)?;
        CloseServiceHandle(service_manager)?;

        Ok(())
    }

    pub async fn get_service_status(&self, service_name: &str) -> Result<ServiceStatus, Box<dyn std::error::Error>> {
        use windows::Win32::System::Services::*;

        let service_manager = OpenSCManagerW(
            None,
            None,
            SC_MANAGER_CONNECT,
        )?;

        let service = OpenServiceW(
            service_manager,
            &windows::core::HSTRING::from(service_name),
            SERVICE_QUERY_STATUS,
        )?;

        let mut status = SERVICE_STATUS_PROCESS::default();
        let mut bytes_needed = 0;

        QueryServiceStatusEx(
            service,
            SC_STATUS_PROCESS_INFO,
            &mut status as *mut _ as *mut _,
            std::mem::size_of::<SERVICE_STATUS_PROCESS>() as u32,
            &mut bytes_needed,
        )?;

        CloseServiceHandle(service)?;
        CloseServiceHandle(service_manager)?;

        Ok(ServiceStatus {
            state: status.dwCurrentState,
            process_id: status.dwProcessId,
            service_type: status.dwServiceType,
            controls_accepted: status.dwControlsAccepted,
        })
    }
}

#[cfg(target_os = "windows")]
#[derive(Debug)]
pub struct ServiceStatus {
    pub state: u32,
    pub process_id: u32,
    pub service_type: u32,
    pub controls_accepted: u32,
}
```

## 3. Unix/Linux 特定功能

### 3.1 Unix 进程管理

```rust
#[cfg(unix)]
use std::os::unix::process::CommandExt;

#[cfg(unix)]
pub struct UnixProcessManager {
    process_groups: std::collections::HashMap<String, i32>,
    signal_handlers: std::collections::HashMap<i32, SignalHandler>,
}

#[cfg(unix)]
pub type SignalHandler = Box<dyn Fn(i32) + Send + Sync>;

#[cfg(unix)]
impl UnixProcessManager {
    pub fn new() -> Self {
        Self {
            process_groups: std::collections::HashMap::new(),
            signal_handlers: std::collections::HashMap::new(),
        }
    }

    pub async fn create_process_group(
        &mut self,
        group_name: &str,
        command: &str,
        args: &[String],
    ) -> Result<i32, Box<dyn std::error::Error>> {
        use nix::unistd::{fork, setpgid, execvp};
        use nix::sys::wait::waitpid;
        use std::ffi::CString;

        match fork()? {
            nix::unistd::ForkResult::Parent { child } => {
                // 父进程：设置进程组
                setpgid(child, child)?;
                self.process_groups.insert(group_name.to_string(), child.as_raw());
                Ok(child.as_raw())
            }
            nix::unistd::ForkResult::Child => {
                // 子进程：执行命令
                setpgid(nix::unistd::Pid::from_raw(0), nix::unistd::Pid::from_raw(0))?;

                let cmd = CString::new(command)?;
                let args: Vec<CString> = args.iter()
                    .map(|arg| CString::new(arg.as_str()))
                    .collect::<Result<Vec<_>, _>>()?;

                execvp(&cmd, &args)?;
                unreachable!()
            }
        }
    }

    pub async fn send_signal_to_group(
        &self,
        group_name: &str,
        signal: i32,
    ) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(pid) = self.process_groups.get(group_name) {
            use nix::sys::signal::kill;
            use nix::unistd::Pid;

            kill(Pid::from_raw(*pid), nix::sys::signal::Signal::from_c_int(signal)?)?;
            Ok(())
        } else {
            Err("进程组未找到".into())
        }
    }

    pub async fn setup_signal_handler(
        &mut self,
        signal: i32,
        handler: SignalHandler,
    ) -> Result<(), Box<dyn std::error::Error>> {
        use nix::sys::signal::{signal, SigHandler, Signal};

        let signal = Signal::from_c_int(signal)?;
        let handler_ptr = Box::into_raw(handler);

        unsafe {
            signal(signal, SigHandler::Handler(handle_signal))?;
        }

        self.signal_handlers.insert(signal as i32, unsafe { Box::from_raw(handler_ptr) });

        Ok(())
    }

    pub async fn get_process_info(&self, pid: i32) -> Result<ProcessInfo, Box<dyn std::error::Error>> {
        use nix::sys::wait::waitpid;
        use nix::unistd::Pid;
        use std::fs;

        let proc_path = format!("/proc/{}/stat", pid);
        let content = fs::read_to_string(proc_path)?;

        let parts: Vec<&str> = content.split_whitespace().collect();
        if parts.len() < 24 {
            return Err("进程信息格式错误".into());
        }

        Ok(ProcessInfo {
            pid,
            ppid: parts[3].parse()?,
            state: parts[2].to_string(),
            utime: parts[13].parse()?,
            stime: parts[14].parse()?,
            cutime: parts[15].parse()?,
            cstime: parts[16].parse()?,
            priority: parts[17].parse()?,
            nice: parts[18].parse()?,
            num_threads: parts[19].parse()?,
            starttime: parts[21].parse()?,
            vsize: parts[22].parse()?,
            rss: parts[23].parse()?,
        })
    }
}

#[cfg(unix)]
extern "C" fn handle_signal(signal: i32) {
    // 信号处理函数
    println!("收到信号: {}", signal);
}

#[cfg(unix)]
#[derive(Debug)]
pub struct ProcessInfo {
    pub pid: i32,
    pub ppid: i32,
    pub state: String,
    pub utime: u64,
    pub stime: u64,
    pub cutime: u64,
    pub cstime: u64,
    pub priority: i32,
    pub nice: i32,
    pub num_threads: i32,
    pub starttime: u64,
    pub vsize: u64,
    pub rss: i64,
}
```

### 3.2 Systemd 服务管理

```rust
#[cfg(target_os = "linux")]
pub struct SystemdManager;

#[cfg(target_os = "linux")]
impl SystemdManager {
    pub async fn create_service(
        &self,
        service_name: &str,
        service_config: &SystemdServiceConfig,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let service_file_path = format!("/etc/systemd/system/{}.service", service_name);
        let service_content = self.generate_service_file(service_config);

        std::fs::write(&service_file_path, service_content)?;

        // 重新加载 systemd
        self.reload_systemd().await?;

        // 启用服务
        self.enable_service(service_name).await?;

        Ok(())
    }

    fn generate_service_file(&self, config: &SystemdServiceConfig) -> String {
        format!(
            "[Unit]
Description={}
After=network.target

[Service]
Type={}
ExecStart={}
WorkingDirectory={}
User={}
Group={}
Restart={}
RestartSec={}
Environment={}

[Install]
WantedBy=multi-user.target
",
            config.description,
            config.service_type,
            config.exec_start,
            config.working_directory,
            config.user,
            config.group,
            config.restart_policy,
            config.restart_sec,
            config.environment_vars.join(" ")
        )
    }

    pub async fn start_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = std::process::Command::new("systemctl")
            .arg("start")
            .arg(service_name)
            .output()?;

        if !output.status.success() {
            return Err(format!("启动服务失败: {}", String::from_utf8_lossy(&output.stderr)).into());
        }

        Ok(())
    }

    pub async fn stop_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = std::process::Command::new("systemctl")
            .arg("stop")
            .arg(service_name)
            .output()?;

        if !output.status.success() {
            return Err(format!("停止服务失败: {}", String::from_utf8_lossy(&output.stderr)).into());
        }

        Ok(())
    }

    pub async fn get_service_status(&self, service_name: &str) -> Result<ServiceStatus, Box<dyn std::error::Error>> {
        let output = std::process::Command::new("systemctl")
            .arg("is-active")
            .arg(service_name)
            .output()?;

        let status = String::from_utf8_lossy(&output.stdout).trim().to_string();

        Ok(ServiceStatus {
            name: service_name.to_string(),
            status,
            active: status == "active",
        })
    }

    async fn reload_systemd(&self) -> Result<(), Box<dyn std::error::Error>> {
        let output = std::process::Command::new("systemctl")
            .arg("daemon-reload")
            .output()?;

        if !output.status.success() {
            return Err(format!("重新加载 systemd 失败: {}", String::from_utf8_lossy(&output.stderr)).into());
        }

        Ok(())
    }

    async fn enable_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = std::process::Command::new("systemctl")
            .arg("enable")
            .arg(service_name)
            .output()?;

        if !output.status.success() {
            return Err(format!("启用服务失败: {}", String::from_utf8_lossy(&output.stderr)).into());
        }

        Ok(())
    }
}

#[cfg(target_os = "linux")]
#[derive(Debug, Clone)]
pub struct SystemdServiceConfig {
    pub description: String,
    pub service_type: String,
    pub exec_start: String,
    pub working_directory: String,
    pub user: String,
    pub group: String,
    pub restart_policy: String,
    pub restart_sec: u32,
    pub environment_vars: Vec<String>,
}

#[cfg(target_os = "linux")]
#[derive(Debug)]
pub struct ServiceStatus {
    pub name: String,
    pub status: String,
    pub active: bool,
}
```

## 4. macOS 特定功能

### 4.1 Launchd 服务管理

```rust
#[cfg(target_os = "macos")]
pub struct LaunchdManager;

#[cfg(target_os = "macos")]
impl LaunchdManager {
    pub async fn create_launchd_service(
        &self,
        service_name: &str,
        config: &LaunchdServiceConfig,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let plist_path = format!("~/Library/LaunchAgents/{}.plist", service_name);
        let plist_content = self.generate_plist(config);

        std::fs::write(&plist_path, plist_content)?;

        // 加载服务
        self.load_service(service_name).await?;

        Ok(())
    }

    fn generate_plist(&self, config: &LaunchdServiceConfig) -> String {
        format!(
            r#"<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0">
<dict>
    <key>Label</key>
    <string>{}</string>
    <key>ProgramArguments</key>
    <array>
        <string>{}</string>
        {}
    </array>
    <key>WorkingDirectory</key>
    <string>{}</string>
    <key>RunAtLoad</key>
    <true/>
    <key>KeepAlive</key>
    <true/>
    <key>StandardOutPath</key>
    <string>{}</string>
    <key>StandardErrorPath</key>
    <string>{}</string>
</dict>
</plist>"#,
            config.label,
            config.program,
            config.args.iter().map(|arg| format!("<string>{}</string>", arg)).collect::<Vec<_>>().join("\n        "),
            config.working_directory,
            config.stdout_path,
            config.stderr_path
        )
    }

    pub async fn load_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = std::process::Command::new("launchctl")
            .arg("load")
            .arg(&format!("~/Library/LaunchAgents/{}.plist", service_name))
            .output()?;

        if !output.status.success() {
            return Err(format!("加载服务失败: {}", String::from_utf8_lossy(&output.stderr)).into());
        }

        Ok(())
    }

    pub async fn unload_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = std::process::Command::new("launchctl")
            .arg("unload")
            .arg(&format!("~/Library/LaunchAgents/{}.plist", service_name))
            .output()?;

        if !output.status.success() {
            return Err(format!("卸载服务失败: {}", String::from_utf8_lossy(&output.stderr)).into());
        }

        Ok(())
    }

    pub async fn get_service_status(&self, service_name: &str) -> Result<ServiceStatus, Box<dyn std::error::Error>> {
        let output = std::process::Command::new("launchctl")
            .arg("list")
            .arg(service_name)
            .output()?;

        let output_str = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = output_str.lines().collect();

        if lines.len() < 2 {
            return Ok(ServiceStatus {
                name: service_name.to_string(),
                status: "not_found".to_string(),
                active: false,
            });
        }

        let parts: Vec<&str> = lines[1].split_whitespace().collect();
        if parts.len() < 3 {
            return Err("服务状态格式错误".into());
        }

        let status = if parts[0] == "-" { "stopped" } else { "running" };

        Ok(ServiceStatus {
            name: service_name.to_string(),
            status: status.to_string(),
            active: status == "running",
        })
    }
}

#[cfg(target_os = "macos")]
#[derive(Debug, Clone)]
pub struct LaunchdServiceConfig {
    pub label: String,
    pub program: String,
    pub args: Vec<String>,
    pub working_directory: String,
    pub stdout_path: String,
    pub stderr_path: String,
}

#[cfg(target_os = "macos")]
#[derive(Debug)]
pub struct ServiceStatus {
    pub name: String,
    pub status: String,
    pub active: bool,
}
```

## 5. 跨平台兼容性处理

### 5.1 统一接口抽象

```rust
pub trait PlatformProcessManager {
    async fn create_process(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<ProcessHandle, Box<dyn std::error::Error>>;

    async fn terminate_process(
        &self,
        handle: &ProcessHandle,
    ) -> Result<(), Box<dyn std::error::Error>>;

    async fn wait_for_process(
        &self,
        handle: &ProcessHandle,
    ) -> Result<ProcessResult, Box<dyn std::error::Error>>;

    async fn get_process_info(
        &self,
        handle: &ProcessHandle,
    ) -> Result<ProcessInfo, Box<dyn std::error::Error>>;
}

#[derive(Debug, Clone)]
pub struct ProcessHandle {
    pub id: String,
    pub pid: u32,
    pub platform: Platform,
}

#[derive(Debug)]
pub struct ProcessResult {
    pub exit_code: Option<i32>,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub execution_time: std::time::Duration,
}

#[derive(Debug)]
pub struct ProcessInfo {
    pub pid: u32,
    pub ppid: Option<u32>,
    pub state: String,
    pub memory_usage: u64,
    pub cpu_usage: f64,
    pub start_time: std::time::SystemTime,
}

pub struct UnifiedProcessManager {
    platform_manager: Box<dyn PlatformProcessManager + Send + Sync>,
}

impl UnifiedProcessManager {
    pub fn new() -> Self {
        let platform = CrossPlatformProcessManager::detect_platform();
        let platform_manager: Box<dyn PlatformProcessManager + Send + Sync> = match platform {
            Platform::Windows => Box::new(WindowsProcessManager::new()),
            Platform::Linux => Box::new(UnixProcessManager::new()),
            Platform::MacOS => Box::new(UnixProcessManager::new()),
            Platform::Unix => Box::new(UnixProcessManager::new()),
            _ => Box::new(GenericProcessManager::new()),
        };

        Self { platform_manager }
    }

    pub async fn create_process(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<ProcessHandle, Box<dyn std::error::Error>> {
        self.platform_manager.create_process(command, args).await
    }

    pub async fn terminate_process(
        &self,
        handle: &ProcessHandle,
    ) -> Result<(), Box<dyn std::error::Error>> {
        self.platform_manager.terminate_process(handle).await
    }

    pub async fn wait_for_process(
        &self,
        handle: &ProcessHandle,
    ) -> Result<ProcessResult, Box<dyn std::error::Error>> {
        self.platform_manager.wait_for_process(handle).await
    }

    pub async fn get_process_info(
        &self,
        handle: &ProcessHandle,
    ) -> Result<ProcessInfo, Box<dyn std::error::Error>> {
        self.platform_manager.get_process_info(handle).await
    }
}

pub struct GenericProcessManager;

impl GenericProcessManager {
    pub fn new() -> Self {
        Self
    }
}

impl PlatformProcessManager for GenericProcessManager {
    async fn create_process(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<ProcessHandle, Box<dyn std::error::Error>> {
        let mut cmd = std::process::Command::new(command);
        cmd.args(args);

        let child = cmd.spawn()?;
        let pid = child.id();

        Ok(ProcessHandle {
            id: uuid::Uuid::new_v4().to_string(),
            pid,
            platform: Platform::Unknown,
        })
    }

    async fn terminate_process(
        &self,
        handle: &ProcessHandle,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 通用终止方法
        std::process::Command::new("kill")
            .arg(handle.pid.to_string())
            .output()?;

        Ok(())
    }

    async fn wait_for_process(
        &self,
        handle: &ProcessHandle,
    ) -> Result<ProcessResult, Box<dyn std::error::Error>> {
        // 通用等待方法
        let output = std::process::Command::new("wait")
            .arg(handle.pid.to_string())
            .output()?;

        Ok(ProcessResult {
            exit_code: output.status.code(),
            stdout: output.stdout,
            stderr: output.stderr,
            execution_time: std::time::Duration::from_secs(0),
        })
    }

    async fn get_process_info(
        &self,
        handle: &ProcessHandle,
    ) -> Result<ProcessInfo, Box<dyn std::error::Error>> {
        // 通用进程信息获取
        Ok(ProcessInfo {
            pid: handle.pid,
            ppid: None,
            state: "unknown".to_string(),
            memory_usage: 0,
            cpu_usage: 0.0,
            start_time: std::time::SystemTime::now(),
        })
    }
}
```

### 5.2 环境变量和路径处理

```rust
pub struct CrossPlatformEnvironment {
    platform: Platform,
    config: CrossPlatformConfig,
}

impl CrossPlatformEnvironment {
    pub fn new() -> Self {
        let platform = CrossPlatformProcessManager::detect_platform();
        let config = CrossPlatformProcessManager::get_platform_config(&platform);

        Self { platform, config }
    }

    pub fn get_temp_dir(&self) -> String {
        self.config.temp_dir.clone()
    }

    pub fn get_shell(&self) -> String {
        self.config.default_shell.clone()
    }

    pub fn normalize_path(&self, path: &str) -> String {
        match self.platform {
            Platform::Windows => {
                // Windows 路径处理
                path.replace('/', "\\")
            }
            _ => {
                // Unix 路径处理
                path.replace('\\', "/")
            }
        }
    }

    pub fn is_executable(&self, path: &str) -> bool {
        let normalized_path = self.normalize_path(path);

        match self.platform {
            Platform::Windows => {
                // Windows 检查文件扩展名
                normalized_path.ends_with(".exe") ||
                normalized_path.ends_with(".bat") ||
                normalized_path.ends_with(".cmd")
            }
            _ => {
                // Unix 检查文件权限
                if let Ok(metadata) = std::fs::metadata(&normalized_path) {
                    use std::os::unix::fs::PermissionsExt;
                    let permissions = metadata.permissions();
                    permissions.mode() & 0o111 != 0
                } else {
                    false
                }
            }
        }
    }

    pub fn get_path_separator(&self) -> char {
        self.config.path_separator
    }

    pub fn get_executable_extension(&self) -> String {
        self.config.executable_extension.clone()
    }

    pub fn build_command(&self, base_command: &str) -> String {
        if self.is_executable(base_command) {
            base_command.to_string()
        } else {
            format!("{}{}", base_command, self.get_executable_extension())
        }
    }

    pub fn get_environment_variables(&self) -> std::collections::HashMap<String, String> {
        let mut env_vars = std::collections::HashMap::new();

        for (key, value) in std::env::vars() {
            env_vars.insert(key, value);
        }

        // 添加平台特定的环境变量
        match self.platform {
            Platform::Windows => {
                env_vars.insert("OS".to_string(), "Windows_NT".to_string());
                env_vars.insert("PATHEXT".to_string(), ".COM;.EXE;.BAT;.CMD;.VBS;.VBE;.JS;.JSE;.WSF;.WSH;.MSC".to_string());
            }
            Platform::Linux => {
                env_vars.insert("OS".to_string(), "Linux".to_string());
            }
            Platform::MacOS => {
                env_vars.insert("OS".to_string(), "macOS".to_string());
            }
            _ => {}
        }

        env_vars
    }
}
```

## 6. 最佳实践

### 6.1 跨平台测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_cross_platform_process_creation() {
        let manager = CrossPlatformProcessManager::new();

        let result = manager.execute_command("echo", &["Hello, World!".to_string()]).await;
        assert!(result.is_ok());

        let result = result.unwrap();
        assert!(result.exit_code == Some(0));
        assert!(String::from_utf8_lossy(&result.stdout).contains("Hello, World!"));
    }

    #[tokio::test]
    async fn test_path_normalization() {
        let env = CrossPlatformEnvironment::new();

        let windows_path = "C:\\Users\\Test\\file.txt";
        let unix_path = "/home/test/file.txt";

        let normalized_windows = env.normalize_path(windows_path);
        let normalized_unix = env.normalize_path(unix_path);

        match env.platform {
            Platform::Windows => {
                assert_eq!(normalized_windows, "C:\\Users\\Test\\file.txt");
                assert_eq!(normalized_unix, "\\home\\test\\file.txt");
            }
            _ => {
                assert_eq!(normalized_windows, "C:/Users/Test/file.txt");
                assert_eq!(normalized_unix, "/home/test/file.txt");
            }
        }
    }

    #[tokio::test]
    async fn test_executable_detection() {
        let env = CrossPlatformEnvironment::new();

        match env.platform {
            Platform::Windows => {
                assert!(env.is_executable("test.exe"));
                assert!(env.is_executable("test.bat"));
                assert!(!env.is_executable("test.txt"));
            }
            _ => {
                // Unix 系统需要实际的文件权限测试
                // 这里只是示例
                assert!(!env.is_executable("nonexistent"));
            }
        }
    }
}
```

### 6.2 错误处理策略

```rust
#[derive(Debug, thiserror::Error)]
pub enum CrossPlatformError {
    #[error("平台不支持: {0}")]
    PlatformNotSupported(String),

    #[error("路径错误: {0}")]
    PathError(String),

    #[error("权限错误: {0}")]
    PermissionError(String),

    #[error("进程创建失败: {0}")]
    ProcessCreationFailed(String),

    #[error("进程终止失败: {0}")]
    ProcessTerminationFailed(String),

    #[error("系统调用失败: {0}")]
    SystemCallFailed(String),
}

pub struct CrossPlatformErrorHandler;

impl CrossPlatformErrorHandler {
    pub fn handle_error(error: Box<dyn std::error::Error>) -> CrossPlatformError {
        let error_msg = error.to_string();

        if error_msg.contains("permission") || error_msg.contains("Permission") {
            CrossPlatformError::PermissionError(error_msg)
        } else if error_msg.contains("path") || error_msg.contains("Path") {
            CrossPlatformError::PathError(error_msg)
        } else if error_msg.contains("spawn") || error_msg.contains("Spawn") {
            CrossPlatformError::ProcessCreationFailed(error_msg)
        } else if error_msg.contains("kill") || error_msg.contains("Kill") {
            CrossPlatformError::ProcessTerminationFailed(error_msg)
        } else {
            CrossPlatformError::SystemCallFailed(error_msg)
        }
    }

    pub fn is_recoverable(error: &CrossPlatformError) -> bool {
        match error {
            CrossPlatformError::PermissionError(_) => true,
            CrossPlatformError::PathError(_) => true,
            CrossPlatformError::ProcessCreationFailed(_) => true,
            _ => false,
        }
    }

    pub fn get_recovery_suggestion(error: &CrossPlatformError) -> String {
        match error {
            CrossPlatformError::PermissionError(_) => {
                "检查文件权限或使用管理员权限运行".to_string()
            }
            CrossPlatformError::PathError(_) => {
                "检查路径是否存在且格式正确".to_string()
            }
            CrossPlatformError::ProcessCreationFailed(_) => {
                "检查命令是否存在且可执行".to_string()
            }
            CrossPlatformError::ProcessTerminationFailed(_) => {
                "进程可能已经终止或权限不足".to_string()
            }
            CrossPlatformError::PlatformNotSupported(_) => {
                "当前平台不支持此功能".to_string()
            }
            CrossPlatformError::SystemCallFailed(_) => {
                "系统调用失败，请检查系统状态".to_string()
            }
        }
    }
}
```

## 7. 总结

本章详细介绍了 Rust 中的跨平台进程管理：

1. **平台差异处理**: 识别和处理不同平台的特性差异
2. **Windows 特定功能**: 作业对象、服务管理等 Windows 特有功能
3. **Unix/Linux 特定功能**: 进程组、信号处理、systemd 管理等
4. **macOS 特定功能**: Launchd 服务管理
5. **统一接口抽象**: 提供跨平台的统一接口
6. **环境变量和路径处理**: 跨平台的环境变量和路径处理
7. **错误处理策略**: 完善的跨平台错误处理机制

这些技术为构建真正跨平台的进程管理系统提供了坚实的基础，能够确保在不同操作系统上的一致性和可靠性。
