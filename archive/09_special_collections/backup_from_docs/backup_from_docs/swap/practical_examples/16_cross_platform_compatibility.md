# C07-16. 跨平台兼容性示例 (Rust 1.90 增强版)

## 目录

- [C07-16. 跨平台兼容性示例 (Rust 1.90 增强版)](#c07-16-跨平台兼容性示例-rust-190-增强版)
  - [目录](#目录)
  - [1. 平台检测与适配](#1-平台检测与适配)
    - [1.1 平台检测器](#11-平台检测器)
  - [2. 条件编译](#2-条件编译)
    - [2.1 条件编译管理器](#21-条件编译管理器)
  - [3. 路径处理](#3-路径处理)
    - [3.1 跨平台路径管理器](#31-跨平台路径管理器)
  - [4. 环境变量管理](#4-环境变量管理)
    - [4.1 跨平台环境变量管理器](#41-跨平台环境变量管理器)
  - [5. 系统调用封装](#5-系统调用封装)
    - [5.1 跨平台系统调用封装器](#51-跨平台系统调用封装器)
  - [6. 平台特定功能](#6-平台特定功能)
    - [6.1 平台特定功能管理器](#61-平台特定功能管理器)
  - [总结](#总结)

本章提供跨平台兼容性示例，涵盖平台检测、条件编译、路径处理、环境变量管理、系统调用封装和平台特定功能等。

## 1. 平台检测与适配

### 1.1 平台检测器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 平台检测器
pub struct PlatformDetector {
    platform_info: Arc<RwLock<PlatformInfo>>,
    capabilities: Arc<RwLock<PlatformCapabilities>>,
    config: PlatformConfig,
}

#[derive(Debug, Clone)]
pub struct PlatformInfo {
    pub os: OperatingSystem,
    pub arch: Architecture,
    pub version: String,
    pub kernel_version: String,
    pub hostname: String,
    pub user: String,
    pub home_dir: String,
    pub temp_dir: String,
    pub detected_at: Instant,
}

#[derive(Debug, Clone)]
pub enum OperatingSystem {
    Windows,
    Linux,
    macOS,
    FreeBSD,
    OpenBSD,
    NetBSD,
    Android,
    iOS,
    Unknown,
}

#[derive(Debug, Clone)]
pub enum Architecture {
    X86,
    X86_64,
    ARM,
    ARM64,
    MIPS,
    PowerPC,
    RiscV,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct PlatformCapabilities {
    pub supports_symlinks: bool,
    pub supports_hardlinks: bool,
    pub supports_file_locking: bool,
    pub supports_process_groups: bool,
    pub supports_signals: bool,
    pub supports_mmap: bool,
    pub supports_sockets: bool,
    pub supports_threads: bool,
    pub max_path_length: usize,
    pub max_filename_length: usize,
}

#[derive(Debug, Clone)]
pub struct PlatformConfig {
    pub auto_detect: bool,
    pub cache_duration: Duration,
    pub enable_capabilities: bool,
    pub verbose_logging: bool,
}

impl PlatformDetector {
    pub fn new(config: PlatformConfig) -> Self {
        Self {
            platform_info: Arc::new(RwLock::new(PlatformInfo {
                os: OperatingSystem::Unknown,
                arch: Architecture::Unknown,
                version: String::new(),
                kernel_version: String::new(),
                hostname: String::new(),
                user: String::new(),
                home_dir: String::new(),
                temp_dir: String::new(),
                detected_at: Instant::now(),
            })),
            capabilities: Arc::new(RwLock::new(PlatformCapabilities {
                supports_symlinks: false,
                supports_hardlinks: false,
                supports_file_locking: false,
                supports_process_groups: false,
                supports_signals: false,
                supports_mmap: false,
                supports_sockets: false,
                supports_threads: false,
                max_path_length: 0,
                max_filename_length: 0,
            })),
            config,
        }
    }

    // 检测平台信息
    pub async fn detect_platform(&self) -> Result<PlatformInfo, PlatformError> {
        let mut platform_info = self.platform_info.write().await;
        
        // 检测操作系统
        platform_info.os = self.detect_os().await?;
        
        // 检测架构
        platform_info.arch = self.detect_architecture().await?;
        
        // 检测版本信息
        platform_info.version = self.detect_version().await?;
        platform_info.kernel_version = self.detect_kernel_version().await?;
        
        // 检测系统信息
        platform_info.hostname = self.detect_hostname().await?;
        platform_info.user = self.detect_user().await?;
        platform_info.home_dir = self.detect_home_dir().await?;
        platform_info.temp_dir = self.detect_temp_dir().await?;
        
        platform_info.detected_at = Instant::now();
        
        Ok(platform_info.clone())
    }

    // 检测操作系统
    async fn detect_os(&self) -> Result<OperatingSystem, PlatformError> {
        #[cfg(target_os = "windows")]
        {
            Ok(OperatingSystem::Windows)
        }
        
        #[cfg(target_os = "linux")]
        {
            Ok(OperatingSystem::Linux)
        }
        
        #[cfg(target_os = "macos")]
        {
            Ok(OperatingSystem::macOS)
        }
        
        #[cfg(target_os = "freebsd")]
        {
            Ok(OperatingSystem::FreeBSD)
        }
        
        #[cfg(target_os = "openbsd")]
        {
            Ok(OperatingSystem::OpenBSD)
        }
        
        #[cfg(target_os = "netbsd")]
        {
            Ok(OperatingSystem::NetBSD)
        }
        
        #[cfg(target_os = "android")]
        {
            Ok(OperatingSystem::Android)
        }
        
        #[cfg(target_os = "ios")]
        {
            Ok(OperatingSystem::iOS)
        }
        
        #[cfg(not(any(
            target_os = "windows",
            target_os = "linux",
            target_os = "macos",
            target_os = "freebsd",
            target_os = "openbsd",
            target_os = "netbsd",
            target_os = "android",
            target_os = "ios"
        )))]
        {
            Ok(OperatingSystem::Unknown)
        }
    }

    // 检测架构
    async fn detect_architecture(&self) -> Result<Architecture, PlatformError> {
        #[cfg(target_arch = "x86")]
        {
            Ok(Architecture::X86)
        }
        
        #[cfg(target_arch = "x86_64")]
        {
            Ok(Architecture::X86_64)
        }
        
        #[cfg(target_arch = "arm")]
        {
            Ok(Architecture::ARM)
        }
        
        #[cfg(target_arch = "aarch64")]
        {
            Ok(Architecture::ARM64)
        }
        
        #[cfg(target_arch = "mips")]
        {
            Ok(Architecture::MIPS)
        }
        
        #[cfg(target_arch = "powerpc")]
        {
            Ok(Architecture::PowerPC)
        }
        
        #[cfg(target_arch = "riscv64")]
        {
            Ok(Architecture::RiscV)
        }
        
        #[cfg(not(any(
            target_arch = "x86",
            target_arch = "x86_64",
            target_arch = "arm",
            target_arch = "aarch64",
            target_arch = "mips",
            target_arch = "powerpc",
            target_arch = "riscv64"
        )))]
        {
            Ok(Architecture::Unknown)
        }
    }

    // 检测版本信息
    async fn detect_version(&self) -> Result<String, PlatformError> {
        #[cfg(target_os = "windows")]
        {
            use std::process::Command;
            let output = Command::new("ver").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        }
        
        #[cfg(target_os = "linux")]
        {
            use std::process::Command;
            let output = Command::new("uname").arg("-r").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        }
        
        #[cfg(target_os = "macos")]
        {
            use std::process::Command;
            let output = Command::new("sw_vers").arg("-productVersion").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        }
        
        #[cfg(not(any(target_os = "windows", target_os = "linux", target_os = "macos")))]
        {
            Ok("Unknown".to_string())
        }
    }

    // 检测内核版本
    async fn detect_kernel_version(&self) -> Result<String, PlatformError> {
        #[cfg(unix)]
        {
            use std::process::Command;
            let output = Command::new("uname").arg("-r").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            let output = Command::new("ver").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok("Unknown".to_string())
        }
    }

    // 检测主机名
    async fn detect_hostname(&self) -> Result<String, PlatformError> {
        #[cfg(unix)]
        {
            use std::process::Command;
            let output = Command::new("hostname").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            let output = Command::new("hostname").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok("Unknown".to_string())
        }
    }

    // 检测用户
    async fn detect_user(&self) -> Result<String, PlatformError> {
        #[cfg(unix)]
        {
            use std::process::Command;
            let output = Command::new("whoami").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            let output = Command::new("whoami").output()
                .map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok("Unknown".to_string())
        }
    }

    // 检测主目录
    async fn detect_home_dir(&self) -> Result<String, PlatformError> {
        #[cfg(unix)]
        {
            use std::env;
            Ok(env::var("HOME")
                .map_err(|_| PlatformError::DetectionFailed("HOME environment variable not found".to_string()))?)
        }
        
        #[cfg(windows)]
        {
            use std::env;
            Ok(env::var("USERPROFILE")
                .map_err(|_| PlatformError::DetectionFailed("USERPROFILE environment variable not found".to_string()))?)
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok("/tmp".to_string())
        }
    }

    // 检测临时目录
    async fn detect_temp_dir(&self) -> Result<String, PlatformError> {
        #[cfg(unix)]
        {
            use std::env;
            Ok(env::var("TMPDIR")
                .or_else(|_| env::var("TMP"))
                .or_else(|_| env::var("TEMP"))
                .unwrap_or_else(|_| "/tmp".to_string()))
        }
        
        #[cfg(windows)]
        {
            use std::env;
            Ok(env::var("TEMP")
                .or_else(|_| env::var("TMP"))
                .unwrap_or_else(|_| "C:\\Windows\\Temp".to_string()))
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok("/tmp".to_string())
        }
    }

    // 检测平台能力
    pub async fn detect_capabilities(&self) -> Result<PlatformCapabilities, PlatformError> {
        let mut capabilities = self.capabilities.write().await;
        
        // 检测符号链接支持
        capabilities.supports_symlinks = self.test_symlink_support().await?;
        
        // 检测硬链接支持
        capabilities.supports_hardlinks = self.test_hardlink_support().await?;
        
        // 检测文件锁定支持
        capabilities.supports_file_locking = self.test_file_locking_support().await?;
        
        // 检测进程组支持
        capabilities.supports_process_groups = self.test_process_group_support().await?;
        
        // 检测信号支持
        capabilities.supports_signals = self.test_signal_support().await?;
        
        // 检测内存映射支持
        capabilities.supports_mmap = self.test_mmap_support().await?;
        
        // 检测套接字支持
        capabilities.supports_sockets = self.test_socket_support().await?;
        
        // 检测线程支持
        capabilities.supports_threads = self.test_thread_support().await?;
        
        // 检测路径长度限制
        capabilities.max_path_length = self.detect_max_path_length().await?;
        capabilities.max_filename_length = self.detect_max_filename_length().await?;
        
        Ok(capabilities.clone())
    }

    // 测试符号链接支持
    async fn test_symlink_support(&self) -> Result<bool, PlatformError> {
        #[cfg(unix)]
        {
            use std::fs;
            use std::path::Path;
            
            let temp_dir = std::env::temp_dir();
            let test_file = temp_dir.join("test_symlink");
            let test_link = temp_dir.join("test_symlink_link");
            
            // 创建测试文件
            fs::write(&test_file, "test").map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            
            // 尝试创建符号链接
            let result = std::os::unix::fs::symlink(&test_file, &test_link).is_ok();
            
            // 清理
            let _ = fs::remove_file(&test_file);
            let _ = fs::remove_file(&test_link);
            
            Ok(result)
        }
        
        #[cfg(windows)]
        {
            use std::fs;
            use std::path::Path;
            
            let temp_dir = std::env::temp_dir();
            let test_file = temp_dir.join("test_symlink");
            let test_link = temp_dir.join("test_symlink_link");
            
            // 创建测试文件
            fs::write(&test_file, "test").map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            
            // 尝试创建符号链接
            let result = std::os::windows::fs::symlink_file(&test_file, &test_link).is_ok();
            
            // 清理
            let _ = fs::remove_file(&test_file);
            let _ = fs::remove_file(&test_link);
            
            Ok(result)
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(false)
        }
    }

    // 测试硬链接支持
    async fn test_hardlink_support(&self) -> Result<bool, PlatformError> {
        #[cfg(unix)]
        {
            use std::fs;
            use std::path::Path;
            
            let temp_dir = std::env::temp_dir();
            let test_file = temp_dir.join("test_hardlink");
            let test_link = temp_dir.join("test_hardlink_link");
            
            // 创建测试文件
            fs::write(&test_file, "test").map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            
            // 尝试创建硬链接
            let result = fs::hard_link(&test_file, &test_link).is_ok();
            
            // 清理
            let _ = fs::remove_file(&test_file);
            let _ = fs::remove_file(&test_link);
            
            Ok(result)
        }
        
        #[cfg(windows)]
        {
            use std::fs;
            use std::path::Path;
            
            let temp_dir = std::env::temp_dir();
            let test_file = temp_dir.join("test_hardlink");
            let test_link = temp_dir.join("test_hardlink_link");
            
            // 创建测试文件
            fs::write(&test_file, "test").map_err(|e| PlatformError::DetectionFailed(e.to_string()))?;
            
            // 尝试创建硬链接
            let result = fs::hard_link(&test_file, &test_link).is_ok();
            
            // 清理
            let _ = fs::remove_file(&test_file);
            let _ = fs::remove_file(&test_link);
            
            Ok(result)
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(false)
        }
    }

    // 测试文件锁定支持
    async fn test_file_locking_support(&self) -> Result<bool, PlatformError> {
        #[cfg(unix)]
        {
            use std::fs::File;
            use std::os::unix::io::AsRawFd;
            
            let temp_dir = std::env::temp_dir();
            let test_file = temp_dir.join("test_lock");
            
            if let Ok(file) = File::create(&test_file) {
                let fd = file.as_raw_fd();
                let result = unsafe {
                    libc::flock(fd, libc::LOCK_EX | libc::LOCK_NB) == 0
                };
                let _ = std::fs::remove_file(&test_file);
                Ok(result)
            } else {
                Ok(false)
            }
        }
        
        #[cfg(windows)]
        {
            use std::fs::File;
            use std::os::windows::io::AsRawHandle;
            use std::os::windows::io::RawHandle;
            
            let temp_dir = std::env::temp_dir();
            let test_file = temp_dir.join("test_lock");
            
            if let Ok(file) = File::create(&test_file) {
                let handle: RawHandle = file.as_raw_handle();
                let result = unsafe {
                    windows_sys::Win32::Storage::FileSystem::LockFile(
                        handle,
                        0, 0, 1, 1
                    ) != 0
                };
                let _ = std::fs::remove_file(&test_file);
                Ok(result)
            } else {
                Ok(false)
            }
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(false)
        }
    }

    // 测试进程组支持
    async fn test_process_group_support(&self) -> Result<bool, PlatformError> {
        #[cfg(unix)]
        {
            use std::process::Command;
            let output = Command::new("ps").arg("-o").arg("pgid").arg("-p").arg("1").output();
            Ok(output.is_ok())
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            let output = Command::new("tasklist").arg("/fi").arg("PID eq 1").output();
            Ok(output.is_ok())
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(false)
        }
    }

    // 测试信号支持
    async fn test_signal_support(&self) -> Result<bool, PlatformError> {
        #[cfg(unix)]
        {
            use std::process::Command;
            let output = Command::new("kill").arg("-l").output();
            Ok(output.is_ok())
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            let output = Command::new("taskkill").arg("/?").output();
            Ok(output.is_ok())
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(false)
        }
    }

    // 测试内存映射支持
    async fn test_mmap_support(&self) -> Result<bool, PlatformError> {
        #[cfg(unix)]
        {
            use std::fs::File;
            use std::os::unix::io::AsRawFd;
            
            let temp_dir = std::env::temp_dir();
            let test_file = temp_dir.join("test_mmap");
            
            if let Ok(file) = File::create(&test_file) {
                let fd = file.as_raw_fd();
                let result = unsafe {
                    libc::mmap(
                        std::ptr::null_mut(),
                        4096,
                        libc::PROT_READ | libc::PROT_WRITE,
                        libc::MAP_PRIVATE,
                        fd,
                        0
                    ) != libc::MAP_FAILED
                };
                let _ = std::fs::remove_file(&test_file);
                Ok(result)
            } else {
                Ok(false)
            }
        }
        
        #[cfg(windows)]
        {
            use std::fs::File;
            use std::os::windows::io::AsRawHandle;
            
            let temp_dir = std::env::temp_dir();
            let test_file = temp_dir.join("test_mmap");
            
            if let Ok(file) = File::create(&test_file) {
                let handle = file.as_raw_handle();
                let result = unsafe {
                    windows_sys::Win32::System::Memory::CreateFileMappingW(
                        handle,
                        std::ptr::null_mut(),
                        windows_sys::Win32::System::Memory::PAGE_READWRITE,
                        0,
                        4096,
                        std::ptr::null()
                    ) != 0
                };
                let _ = std::fs::remove_file(&test_file);
                Ok(result)
            } else {
                Ok(false)
            }
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(false)
        }
    }

    // 测试套接字支持
    async fn test_socket_support(&self) -> Result<bool, PlatformError> {
        #[cfg(unix)]
        {
            use std::net::TcpListener;
            let result = TcpListener::bind("127.0.0.1:0").is_ok();
            Ok(result)
        }
        
        #[cfg(windows)]
        {
            use std::net::TcpListener;
            let result = TcpListener::bind("127.0.0.1:0").is_ok();
            Ok(result)
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(false)
        }
    }

    // 测试线程支持
    async fn test_thread_support(&self) -> Result<bool, PlatformError> {
        use std::thread;
        let result = thread::spawn(|| {}).join().is_ok();
        Ok(result)
    }

    // 检测最大路径长度
    async fn detect_max_path_length(&self) -> Result<usize, PlatformError> {
        #[cfg(windows)]
        {
            Ok(260) // Windows 默认路径长度限制
        }
        
        #[cfg(unix)]
        {
            Ok(4096) // Unix 系统通常支持更长的路径
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(255) // 保守估计
        }
    }

    // 检测最大文件名长度
    async fn detect_max_filename_length(&self) -> Result<usize, PlatformError> {
        #[cfg(windows)]
        {
            Ok(255) // Windows 文件名长度限制
        }
        
        #[cfg(unix)]
        {
            Ok(255) // Unix 文件名长度限制
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            Ok(255) // 保守估计
        }
    }

    // 获取平台信息
    pub async fn get_platform_info(&self) -> PlatformInfo {
        self.platform_info.read().await.clone()
    }

    // 获取平台能力
    pub async fn get_capabilities(&self) -> PlatformCapabilities {
        self.capabilities.read().await.clone()
    }

    // 检查平台兼容性
    pub async fn check_compatibility(&self, requirements: &PlatformRequirements) -> CompatibilityResult {
        let platform_info = self.get_platform_info().await;
        let capabilities = self.get_capabilities().await;
        
        let mut issues = Vec::new();
        let mut warnings = Vec::new();
        
        // 检查操作系统兼容性
        if !requirements.supported_os.contains(&platform_info.os) {
            issues.push(format!("Unsupported operating system: {:?}", platform_info.os));
        }
        
        // 检查架构兼容性
        if !requirements.supported_arch.contains(&platform_info.arch) {
            issues.push(format!("Unsupported architecture: {:?}", platform_info.arch));
        }
        
        // 检查功能兼容性
        if requirements.requires_symlinks && !capabilities.supports_symlinks {
            issues.push("Symbolic links are required but not supported".to_string());
        }
        
        if requirements.requires_hardlinks && !capabilities.supports_hardlinks {
            warnings.push("Hard links are recommended but not supported".to_string());
        }
        
        if requirements.requires_file_locking && !capabilities.supports_file_locking {
            issues.push("File locking is required but not supported".to_string());
        }
        
        if requirements.requires_process_groups && !capabilities.supports_process_groups {
            warnings.push("Process groups are recommended but not supported".to_string());
        }
        
        if requirements.requires_signals && !capabilities.supports_signals {
            issues.push("Signals are required but not supported".to_string());
        }
        
        if requirements.requires_mmap && !capabilities.supports_mmap {
            warnings.push("Memory mapping is recommended but not supported".to_string());
        }
        
        if requirements.requires_sockets && !capabilities.supports_sockets {
            issues.push("Sockets are required but not supported".to_string());
        }
        
        if requirements.requires_threads && !capabilities.supports_threads {
            issues.push("Threads are required but not supported".to_string());
        }
        
        // 检查路径长度限制
        if requirements.min_path_length > capabilities.max_path_length {
            issues.push(format!(
                "Minimum path length {} exceeds platform limit {}",
                requirements.min_path_length, capabilities.max_path_length
            ));
        }
        
        if requirements.min_filename_length > capabilities.max_filename_length {
            issues.push(format!(
                "Minimum filename length {} exceeds platform limit {}",
                requirements.min_filename_length, capabilities.max_filename_length
            ));
        }
        
        let is_compatible = issues.is_empty();
        let severity = if issues.is_empty() {
            if warnings.is_empty() {
                CompatibilitySeverity::Compatible
            } else {
                CompatibilitySeverity::CompatibleWithWarnings
            }
        } else {
            CompatibilitySeverity::Incompatible
        };
        
        CompatibilityResult {
            is_compatible,
            severity,
            issues,
            warnings,
            platform_info,
            capabilities,
        }
    }
}

// 平台要求
#[derive(Debug, Clone)]
pub struct PlatformRequirements {
    pub supported_os: Vec<OperatingSystem>,
    pub supported_arch: Vec<Architecture>,
    pub requires_symlinks: bool,
    pub requires_hardlinks: bool,
    pub requires_file_locking: bool,
    pub requires_process_groups: bool,
    pub requires_signals: bool,
    pub requires_mmap: bool,
    pub requires_sockets: bool,
    pub requires_threads: bool,
    pub min_path_length: usize,
    pub min_filename_length: usize,
}

// 兼容性结果
#[derive(Debug, Clone)]
pub struct CompatibilityResult {
    pub is_compatible: bool,
    pub severity: CompatibilitySeverity,
    pub issues: Vec<String>,
    pub warnings: Vec<String>,
    pub platform_info: PlatformInfo,
    pub capabilities: PlatformCapabilities,
}

#[derive(Debug, Clone)]
pub enum CompatibilitySeverity {
    Compatible,
    CompatibleWithWarnings,
    Incompatible,
}

#[derive(Debug, thiserror::Error)]
pub enum PlatformError {
    #[error("平台检测失败: {0}")]
    DetectionFailed(String),
    
    #[error("不支持的操作: {0}")]
    UnsupportedOperation(String),
    
    #[error("平台错误: {0}")]
    PlatformError(String),
}
```

## 2. 条件编译

### 2.1 条件编译管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 条件编译管理器
pub struct ConditionalCompilationManager {
    features: Arc<RwLock<HashMap<String, Feature>>>,
    config: ConditionalConfig,
}

#[derive(Debug, Clone)]
pub struct ConditionalConfig {
    pub enable_feature_detection: bool,
    pub auto_optimization: bool,
    pub fallback_enabled: bool,
    pub verbose_logging: bool,
}

#[derive(Debug, Clone)]
pub struct Feature {
    pub name: String,
    pub description: String,
    pub enabled: bool,
    pub dependencies: Vec<String>,
    pub conflicts: Vec<String>,
    pub platform_specific: bool,
    pub fallback_available: bool,
}

impl ConditionalCompilationManager {
    pub fn new(config: ConditionalConfig) -> Self {
        Self {
            features: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    // 注册功能
    pub async fn register_feature(&self, feature: Feature) -> Result<(), ConditionalError> {
        let mut features = self.features.write().await;
        features.insert(feature.name.clone(), feature);
        Ok(())
    }

    // 检查功能是否可用
    pub async fn is_feature_available(&self, feature_name: &str) -> bool {
        let features = self.features.read().await;
        
        if let Some(feature) = features.get(feature_name) {
            if !feature.enabled {
                return false;
            }
            
            // 检查依赖
            for dep in &feature.dependencies {
                if !self.is_feature_available_static(dep, &features) {
                    return false;
                }
            }
            
            // 检查冲突
            for conflict in &feature.conflicts {
                if self.is_feature_available_static(conflict, &features) {
                    return false;
                }
            }
            
            true
        } else {
            false
        }
    }

    // 静态检查功能可用性
    fn is_feature_available_static(feature_name: &str, features: &HashMap<String, Feature>) -> bool {
        if let Some(feature) = features.get(feature_name) {
            feature.enabled
        } else {
            false
        }
    }

    // 获取功能列表
    pub async fn get_features(&self) -> Vec<Feature> {
        let features = self.features.read().await;
        features.values().cloned().collect()
    }

    // 启用功能
    pub async fn enable_feature(&self, feature_name: &str) -> Result<(), ConditionalError> {
        let mut features = self.features.write().await;
        
        if let Some(feature) = features.get_mut(feature_name) {
            feature.enabled = true;
        }
        
        Ok(())
    }

    // 禁用功能
    pub async fn disable_feature(&self, feature_name: &str) -> Result<(), ConditionalError> {
        let mut features = self.features.write().await;
        
        if let Some(feature) = features.get_mut(feature_name) {
            feature.enabled = false;
        }
        
        Ok(())
    }
}

// 平台特定功能
pub mod platform_specific {
    use super::*;

    // Windows 特定功能
    #[cfg(target_os = "windows")]
    pub mod windows {
        use super::*;

        pub async fn register_windows_features(manager: &ConditionalCompilationManager) -> Result<(), ConditionalError> {
            let features = vec![
                Feature {
                    name: "windows_console".to_string(),
                    description: "Windows Console API support".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: true,
                },
                Feature {
                    name: "windows_registry".to_string(),
                    description: "Windows Registry access".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: false,
                },
                Feature {
                    name: "windows_services".to_string(),
                    description: "Windows Services management".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: false,
                },
            ];

            for feature in features {
                manager.register_feature(feature).await?;
            }

            Ok(())
        }
    }

    // Unix 特定功能
    #[cfg(unix)]
    pub mod unix {
        use super::*;

        pub async fn register_unix_features(manager: &ConditionalCompilationManager) -> Result<(), ConditionalError> {
            let features = vec![
                Feature {
                    name: "unix_signals".to_string(),
                    description: "Unix signal handling".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: false,
                },
                Feature {
                    name: "unix_sockets".to_string(),
                    description: "Unix domain sockets".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: true,
                },
                Feature {
                    name: "unix_permissions".to_string(),
                    description: "Unix file permissions".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: true,
                },
            ];

            for feature in features {
                manager.register_feature(feature).await?;
            }

            Ok(())
        }
    }

    // Linux 特定功能
    #[cfg(target_os = "linux")]
    pub mod linux {
        use super::*;

        pub async fn register_linux_features(manager: &ConditionalCompilationManager) -> Result<(), ConditionalError> {
            let features = vec![
                Feature {
                    name: "linux_cgroups".to_string(),
                    description: "Linux cgroups support".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: false,
                },
                Feature {
                    name: "linux_namespaces".to_string(),
                    description: "Linux namespaces support".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: false,
                },
                Feature {
                    name: "linux_systemd".to_string(),
                    description: "systemd integration".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: true,
                },
            ];

            for feature in features {
                manager.register_feature(feature).await?;
            }

            Ok(())
        }
    }

    // macOS 特定功能
    #[cfg(target_os = "macos")]
    pub mod macos {
        use super::*;

        pub async fn register_macos_features(manager: &ConditionalCompilationManager) -> Result<(), ConditionalError> {
            let features = vec![
                Feature {
                    name: "macos_launchd".to_string(),
                    description: "launchd integration".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: true,
                },
                Feature {
                    name: "macos_keychain".to_string(),
                    description: "macOS Keychain access".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: false,
                },
                Feature {
                    name: "macos_notifications".to_string(),
                    description: "macOS notifications".to_string(),
                    enabled: true,
                    dependencies: Vec::new(),
                    conflicts: Vec::new(),
                    platform_specific: true,
                    fallback_available: true,
                },
            ];

            for feature in features {
                manager.register_feature(feature).await?;
            }

            Ok(())
        }
    }
}

// 条件编译宏
#[macro_export]
macro_rules! conditional_feature {
    ($feature:expr, $code:block) => {
        #[cfg(feature = $feature)]
        $code
    };
}

#[macro_export]
macro_rules! conditional_platform {
    ($platform:expr, $code:block) => {
        #[cfg(target_os = $platform)]
        $code
    };
}

#[macro_export]
macro_rules! conditional_architecture {
    ($arch:expr, $code:block) => {
        #[cfg(target_arch = $arch)]
        $code
    };
}

#[macro_export]
macro_rules! conditional_fallback {
    ($primary:block, $fallback:block) => {
        #[cfg(feature = "fallback")]
        $fallback
        #[cfg(not(feature = "fallback"))]
        $primary
    };
}

#[derive(Debug, thiserror::Error)]
pub enum ConditionalError {
    #[error("功能未找到: {0}")]
    FeatureNotFound(String),
    
    #[error("功能冲突: {0}")]
    FeatureConflict(String),
    
    #[error("依赖未满足: {0}")]
    DependencyNotMet(String),
    
    #[error("条件编译错误: {0}")]
    ConditionalCompilationError(String),
}
```

## 3. 路径处理

### 3.1 跨平台路径管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 跨平台路径管理器
pub struct CrossPlatformPathManager {
    path_cache: Arc<RwLock<HashMap<String, PathInfo>>>,
    config: PathConfig,
}

#[derive(Debug, Clone)]
pub struct PathConfig {
    pub enable_caching: bool,
    pub cache_size: usize,
    pub normalize_paths: bool,
    pub resolve_symlinks: bool,
    pub case_sensitive: bool,
    pub max_path_length: usize,
}

#[derive(Debug, Clone)]
pub struct PathInfo {
    pub original_path: String,
    pub normalized_path: String,
    pub absolute_path: String,
    pub exists: bool,
    pub is_file: bool,
    pub is_directory: bool,
    pub is_symlink: bool,
    pub permissions: Option<PathPermissions>,
    pub size: Option<u64>,
    pub modified_time: Option<Instant>,
    pub accessed_time: Option<Instant>,
    pub created_time: Option<Instant>,
}

#[derive(Debug, Clone)]
pub struct PathPermissions {
    pub readable: bool,
    pub writable: bool,
    pub executable: bool,
    pub owner_read: bool,
    pub owner_write: bool,
    pub owner_execute: bool,
    pub group_read: bool,
    pub group_write: bool,
    pub group_execute: bool,
    pub other_read: bool,
    pub other_write: bool,
    pub other_execute: bool,
}

impl CrossPlatformPathManager {
    pub fn new(config: PathConfig) -> Self {
        Self {
            path_cache: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    // 规范化路径
    pub async fn normalize_path(&self, path: &str) -> Result<String, PathError> {
        if self.config.enable_caching {
            if let Some(cached) = self.get_cached_path(path).await {
                return Ok(cached.normalized_path);
            }
        }

        let normalized = self.normalize_path_internal(path)?;
        
        if self.config.enable_caching {
            self.cache_path(path, &normalized).await;
        }

        Ok(normalized)
    }

    // 内部路径规范化
    fn normalize_path_internal(&self, path: &str) -> Result<String, PathError> {
        use std::path::Path;
        
        let path = Path::new(path);
        
        // 处理相对路径
        let normalized = if path.is_relative() {
            std::env::current_dir()
                .map_err(|e| PathError::PathError(e.to_string()))?
                .join(path)
        } else {
            path.to_path_buf()
        };

        // 规范化分隔符
        let normalized_str = normalized.to_string_lossy().to_string();
        
        #[cfg(windows)]
        {
            // Windows 使用反斜杠
            Ok(normalized_str.replace("/", "\\"))
        }
        
        #[cfg(unix)]
        {
            // Unix 使用正斜杠
            Ok(normalized_str.replace("\\", "/"))
        }
        
        #[cfg(not(any(windows, unix)))]
        {
            Ok(normalized_str)
        }
    }

    // 解析路径信息
    pub async fn resolve_path_info(&self, path: &str) -> Result<PathInfo, PathError> {
        if self.config.enable_caching {
            if let Some(cached) = self.get_cached_path(path).await {
                return Ok(cached);
            }
        }

        let path_info = self.resolve_path_info_internal(path).await?;
        
        if self.config.enable_caching {
            self.cache_path_info(path, &path_info).await;
        }

        Ok(path_info)
    }

    // 内部路径信息解析
    async fn resolve_path_info_internal(&self, path: &str) -> Result<PathInfo, PathError> {
        use std::fs;
        use std::path::Path;
        
        let path = Path::new(path);
        let normalized_path = self.normalize_path_internal(path.to_str().unwrap())?;
        let absolute_path = path.canonicalize()
            .map_err(|_| PathError::PathNotFound(path.to_string_lossy().to_string()))?
            .to_string_lossy()
            .to_string();

        let metadata = fs::metadata(path)
            .map_err(|_| PathError::PathNotFound(path.to_string_lossy().to_string()))?;

        let permissions = self.get_path_permissions(&metadata).await;
        let size = if metadata.is_file() { Some(metadata.len()) } else { None };
        
        let modified_time = metadata.modified()
            .map_err(|_| PathError::PathError("Failed to get modified time".to_string()))?
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| Instant::now() - d)
            .ok();

        let accessed_time = metadata.accessed()
            .map_err(|_| PathError::PathError("Failed to get accessed time".to_string()))?
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| Instant::now() - d)
            .ok();

        let created_time = metadata.created()
            .map_err(|_| PathError::PathError("Failed to get created time".to_string()))?
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| Instant::now() - d)
            .ok();

        Ok(PathInfo {
            original_path: path.to_string_lossy().to_string(),
            normalized_path,
            absolute_path,
            exists: true,
            is_file: metadata.is_file(),
            is_directory: metadata.is_dir(),
            is_symlink: metadata.file_type().is_symlink(),
            permissions,
            size,
            modified_time,
            accessed_time,
            created_time,
        })
    }

    // 获取路径权限
    async fn get_path_permissions(&self, metadata: &std::fs::Metadata) -> Option<PathPermissions> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let permissions = metadata.permissions();
            let mode = permissions.mode();
            
            Some(PathPermissions {
                readable: (mode & 0o444) != 0,
                writable: (mode & 0o222) != 0,
                executable: (mode & 0o111) != 0,
                owner_read: (mode & 0o400) != 0,
                owner_write: (mode & 0o200) != 0,
                owner_execute: (mode & 0o100) != 0,
                group_read: (mode & 0o040) != 0,
                group_write: (mode & 0o020) != 0,
                group_execute: (mode & 0o010) != 0,
                other_read: (mode & 0o004) != 0,
                other_write: (mode & 0o002) != 0,
                other_execute: (mode & 0o001) != 0,
            })
        }
        
        #[cfg(windows)]
        {
            use std::os::windows::fs::MetadataExt;
            let attributes = metadata.file_attributes();
            
            Some(PathPermissions {
                readable: true, // Windows 默认可读
                writable: (attributes & 0x1) == 0, // 非只读
                executable: false, // Windows 不区分可执行
                owner_read: true,
                owner_write: (attributes & 0x1) == 0,
                owner_execute: false,
                group_read: true,
                group_write: (attributes & 0x1) == 0,
                group_execute: false,
                other_read: true,
                other_write: (attributes & 0x1) == 0,
                other_execute: false,
            })
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            None
        }
    }

    // 获取缓存的路径
    async fn get_cached_path(&self, path: &str) -> Option<PathInfo> {
        let cache = self.path_cache.read().await;
        cache.get(path).cloned()
    }

    // 缓存路径
    async fn cache_path(&self, path: &str, normalized: &str) {
        let mut cache = self.path_cache.write().await;
        
        if cache.len() >= self.config.cache_size {
            // 移除最旧的条目
            if let Some(oldest_key) = cache.keys().next().cloned() {
                cache.remove(&oldest_key);
            }
        }
        
        let path_info = PathInfo {
            original_path: path.to_string(),
            normalized_path: normalized.to_string(),
            absolute_path: String::new(),
            exists: false,
            is_file: false,
            is_directory: false,
            is_symlink: false,
            permissions: None,
            size: None,
            modified_time: None,
            accessed_time: None,
            created_time: None,
        };
        
        cache.insert(path.to_string(), path_info);
    }

    // 缓存路径信息
    async fn cache_path_info(&self, path: &str, path_info: &PathInfo) {
        let mut cache = self.path_cache.write().await;
        
        if cache.len() >= self.config.cache_size {
            // 移除最旧的条目
            if let Some(oldest_key) = cache.keys().next().cloned() {
                cache.remove(&oldest_key);
            }
        }
        
        cache.insert(path.to_string(), path_info.clone());
    }

    // 检查路径是否存在
    pub async fn path_exists(&self, path: &str) -> bool {
        if let Ok(path_info) = self.resolve_path_info(path).await {
            path_info.exists
        } else {
            false
        }
    }

    // 获取路径类型
    pub async fn get_path_type(&self, path: &str) -> Option<PathType> {
        if let Ok(path_info) = self.resolve_path_info(path).await {
            if path_info.is_file {
                Some(PathType::File)
            } else if path_info.is_directory {
                Some(PathType::Directory)
            } else if path_info.is_symlink {
                Some(PathType::Symlink)
            } else {
                Some(PathType::Other)
            }
        } else {
            None
        }
    }

    // 获取路径统计
    pub async fn get_path_stats(&self) -> PathStats {
        let cache = self.path_cache.read().await;
        
        let total_cached = cache.len();
        let existing_paths = cache.values().filter(|p| p.exists).count();
        let files = cache.values().filter(|p| p.is_file).count();
        let directories = cache.values().filter(|p| p.is_directory).count();
        let symlinks = cache.values().filter(|p| p.is_symlink).count();
        
        PathStats {
            total_cached,
            existing_paths,
            files,
            directories,
            symlinks,
            cache_hit_rate: 0.0, // 需要实际统计
        }
    }
}

// 路径类型
#[derive(Debug, Clone)]
pub enum PathType {
    File,
    Directory,
    Symlink,
    Other,
}

// 路径统计
#[derive(Debug)]
pub struct PathStats {
    pub total_cached: usize,
    pub existing_paths: usize,
    pub files: usize,
    pub directories: usize,
    pub symlinks: usize,
    pub cache_hit_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum PathError {
    #[error("路径未找到: {0}")]
    PathNotFound(String),
    
    #[error("路径错误: {0}")]
    PathError(String),
    
    #[error("权限不足: {0}")]
    PermissionDenied(String),
    
    #[error("路径过长: {0}")]
    PathTooLong(String),
    
    #[error("无效路径: {0}")]
    InvalidPath(String),
}
```

## 4. 环境变量管理

### 4.1 跨平台环境变量管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 跨平台环境变量管理器
pub struct CrossPlatformEnvManager {
    env_cache: Arc<RwLock<HashMap<String, EnvVariable>>>,
    config: EnvConfig,
}

#[derive(Debug, Clone)]
pub struct EnvConfig {
    pub enable_caching: bool,
    pub cache_duration: Duration,
    pub auto_refresh: bool,
    pub case_sensitive: bool,
    pub max_cache_size: usize,
}

#[derive(Debug, Clone)]
pub struct EnvVariable {
    pub name: String,
    pub value: String,
    pub source: EnvSource,
    pub last_updated: Instant,
    pub is_system: bool,
    pub is_user: bool,
    pub is_session: bool,
}

#[derive(Debug, Clone)]
pub enum EnvSource {
    System,
    User,
    Session,
    Process,
    Unknown,
}

impl CrossPlatformEnvManager {
    pub fn new(config: EnvConfig) -> Self {
        Self {
            env_cache: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    // 获取环境变量
    pub async fn get_env_var(&self, name: &str) -> Result<Option<String>, EnvError> {
        if self.config.enable_caching {
            if let Some(cached) = self.get_cached_env_var(name).await {
                if cached.last_updated.elapsed() < self.config.cache_duration {
                    return Ok(Some(cached.value));
                }
            }
        }

        let value = self.get_env_var_internal(name)?;
        
        if self.config.enable_caching {
            self.cache_env_var(name, &value).await;
        }

        Ok(value)
    }

    // 内部环境变量获取
    fn get_env_var_internal(&self, name: &str) -> Result<Option<String>, EnvError> {
        use std::env;
        
        let value = env::var(name);
        match value {
            Ok(v) => Ok(Some(v)),
            Err(std::env::VarError::NotPresent) => Ok(None),
            Err(e) => Err(EnvError::EnvError(e.to_string())),
        }
    }

    // 设置环境变量
    pub async fn set_env_var(&self, name: &str, value: &str) -> Result<(), EnvError> {
        use std::env;
        
        env::set_var(name, value);
        
        if self.config.enable_caching {
            self.cache_env_var(name, &Some(value.to_string())).await;
        }

        Ok(())
    }

    // 删除环境变量
    pub async fn remove_env_var(&self, name: &str) -> Result<(), EnvError> {
        use std::env;
        
        env::remove_var(name);
        
        if self.config.enable_caching {
            let mut cache = self.env_cache.write().await;
            cache.remove(name);
        }

        Ok(())
    }

    // 获取所有环境变量
    pub async fn get_all_env_vars(&self) -> Result<HashMap<String, String>, EnvError> {
        use std::env;
        
        let mut env_vars = HashMap::new();
        
        for (key, value) in env::vars() {
            env_vars.insert(key, value);
        }
        
        Ok(env_vars)
    }

    // 获取缓存的环境变量
    async fn get_cached_env_var(&self, name: &str) -> Option<EnvVariable> {
        let cache = self.env_cache.read().await;
        cache.get(name).cloned()
    }

    // 缓存环境变量
    async fn cache_env_var(&self, name: &str, value: &Option<String>) {
        let mut cache = self.env_cache.write().await;
        
        if cache.len() >= self.config.max_cache_size {
            // 移除最旧的条目
            if let Some(oldest_key) = cache.keys().next().cloned() {
                cache.remove(&oldest_key);
            }
        }
        
        if let Some(value) = value {
            let env_var = EnvVariable {
                name: name.to_string(),
                value: value.clone(),
                source: self.detect_env_source(name),
                last_updated: Instant::now(),
                is_system: self.is_system_env_var(name),
                is_user: self.is_user_env_var(name),
                is_session: self.is_session_env_var(name),
            };
            
            cache.insert(name.to_string(), env_var);
        }
    }

    // 检测环境变量来源
    fn detect_env_source(&self, name: &str) -> EnvSource {
        if self.is_system_env_var(name) {
            EnvSource::System
        } else if self.is_user_env_var(name) {
            EnvSource::User
        } else if self.is_session_env_var(name) {
            EnvSource::Session
        } else {
            EnvSource::Unknown
        }
    }

    // 检查是否为系统环境变量
    fn is_system_env_var(&self, name: &str) -> bool {
        #[cfg(windows)]
        {
            use std::process::Command;
            let output = Command::new("setx").arg(name).arg("").output();
            output.is_ok()
        }
        
        #[cfg(unix)]
        {
            // 检查 /etc/environment 或类似文件
            use std::fs;
            let system_env_files = vec![
                "/etc/environment",
                "/etc/profile",
                "/etc/bash.bashrc",
            ];
            
            for file in system_env_files {
                if let Ok(content) = fs::read_to_string(file) {
                    if content.contains(&format!("{}=", name)) {
                        return true;
                    }
                }
            }
            
            false
        }
        
        #[cfg(not(any(windows, unix)))]
        {
            false
        }
    }

    // 检查是否为用户环境变量
    fn is_user_env_var(&self, name: &str) -> bool {
        #[cfg(windows)]
        {
            use std::process::Command;
            let output = Command::new("setx").arg(name).arg("").arg("/u").output();
            output.is_ok()
        }
        
        #[cfg(unix)]
        {
            use std::fs;
            let user_env_files = vec![
                "~/.bashrc",
                "~/.profile",
                "~/.zshrc",
                "~/.fishrc",
            ];
            
            for file in user_env_files {
                if let Ok(content) = fs::read_to_string(file) {
                    if content.contains(&format!("{}=", name)) {
                        return true;
                    }
                }
            }
            
            false
        }
        
        #[cfg(not(any(windows, unix)))]
        {
            false
        }
    }

    // 检查是否为会话环境变量
    fn is_session_env_var(&self, name: &str) -> bool {
        // 会话环境变量是当前进程设置的
        use std::env;
        env::var(name).is_ok()
    }

    // 获取环境变量信息
    pub async fn get_env_var_info(&self, name: &str) -> Result<Option<EnvVariable>, EnvError> {
        if self.config.enable_caching {
            if let Some(cached) = self.get_cached_env_var(name).await {
                return Ok(Some(cached));
            }
        }

        if let Some(value) = self.get_env_var_internal(name)? {
            let env_var = EnvVariable {
                name: name.to_string(),
                value,
                source: self.detect_env_source(name),
                last_updated: Instant::now(),
                is_system: self.is_system_env_var(name),
                is_user: self.is_user_env_var(name),
                is_session: self.is_session_env_var(name),
            };
            
            if self.config.enable_caching {
                self.cache_env_var(name, &Some(env_var.value.clone())).await;
            }
            
            Ok(Some(env_var))
        } else {
            Ok(None)
        }
    }

    // 获取环境变量统计
    pub async fn get_env_stats(&self) -> EnvStats {
        let cache = self.env_cache.read().await;
        let all_env_vars = self.get_all_env_vars().await.unwrap_or_default();
        
        let total_cached = cache.len();
        let total_system = cache.values().filter(|v| v.is_system).count();
        let total_user = cache.values().filter(|v| v.is_user).count();
        let total_session = cache.values().filter(|v| v.is_session).count();
        
        EnvStats {
            total_cached,
            total_system,
            total_user,
            total_session,
            total_available: all_env_vars.len(),
            cache_hit_rate: 0.0, // 需要实际统计
        }
    }
}

// 环境变量统计
#[derive(Debug)]
pub struct EnvStats {
    pub total_cached: usize,
    pub total_system: usize,
    pub total_user: usize,
    pub total_session: usize,
    pub total_available: usize,
    pub cache_hit_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum EnvError {
    #[error("环境变量错误: {0}")]
    EnvError(String),
    
    #[error("权限不足: {0}")]
    PermissionDenied(String),
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}
```

## 5. 系统调用封装

### 5.1 跨平台系统调用封装器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 跨平台系统调用封装器
pub struct CrossPlatformSyscallWrapper {
    syscalls: Arc<RwLock<HashMap<String, SyscallInfo>>>,
    config: SyscallConfig,
}

#[derive(Debug, Clone)]
pub struct SyscallConfig {
    pub enable_logging: bool,
    pub enable_caching: bool,
    pub cache_duration: Duration,
    pub max_cache_size: usize,
    pub timeout: Duration,
    pub retry_count: u32,
}

#[derive(Debug, Clone)]
pub struct SyscallInfo {
    pub name: String,
    pub platform: Platform,
    pub available: bool,
    pub last_called: Instant,
    pub call_count: u64,
    pub success_count: u64,
    pub failure_count: u64,
    pub average_duration: Duration,
}

#[derive(Debug, Clone)]
pub enum Platform {
    Windows,
    Linux,
    macOS,
    FreeBSD,
    OpenBSD,
    NetBSD,
    Android,
    iOS,
    Unknown,
}

impl CrossPlatformSyscallWrapper {
    pub fn new(config: SyscallConfig) -> Self {
        Self {
            syscalls: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    // 执行系统调用
    pub async fn execute_syscall<T>(
        &self,
        name: &str,
        operation: impl FnOnce() -> Result<T, SyscallError>,
    ) -> Result<T, SyscallError> {
        let start_time = Instant::now();
        
        // 更新系统调用信息
        self.update_syscall_info(name, start_time).await;
        
        // 执行操作
        let result = operation();
        
        // 记录结果
        self.record_syscall_result(name, start_time, result.is_ok()).await;
        
        result
    }

    // 更新系统调用信息
    async fn update_syscall_info(&self, name: &str, start_time: Instant) {
        let mut syscalls = self.syscalls.write().await;
        
        if let Some(syscall) = syscalls.get_mut(name) {
            syscall.last_called = start_time;
            syscall.call_count += 1;
        } else {
            let syscall = SyscallInfo {
                name: name.to_string(),
                platform: self.detect_platform(),
                available: true,
                last_called: start_time,
                call_count: 1,
                success_count: 0,
                failure_count: 0,
                average_duration: Duration::ZERO,
            };
            syscalls.insert(name.to_string(), syscall);
        }
    }

    // 记录系统调用结果
    async fn record_syscall_result(&self, name: &str, start_time: Instant, success: bool) {
        let duration = start_time.elapsed();
        let mut syscalls = self.syscalls.write().await;
        
        if let Some(syscall) = syscalls.get_mut(name) {
            if success {
                syscall.success_count += 1;
            } else {
                syscall.failure_count += 1;
            }
            
            // 更新平均持续时间
            let total_calls = syscall.call_count;
            let total_duration = syscall.average_duration * (total_calls - 1) as u32 + duration;
            syscall.average_duration = Duration::from_nanos(total_duration.as_nanos() as u64 / total_calls as u64);
        }
    }

    // 检测平台
    fn detect_platform(&self) -> Platform {
        #[cfg(target_os = "windows")]
        {
            Platform::Windows
        }
        
        #[cfg(target_os = "linux")]
        {
            Platform::Linux
        }
        
        #[cfg(target_os = "macos")]
        {
            Platform::macOS
        }
        
        #[cfg(target_os = "freebsd")]
        {
            Platform::FreeBSD
        }
        
        #[cfg(target_os = "openbsd")]
        {
            Platform::OpenBSD
        }
        
        #[cfg(target_os = "netbsd")]
        {
            Platform::NetBSD
        }
        
        #[cfg(target_os = "android")]
        {
            Platform::Android
        }
        
        #[cfg(target_os = "ios")]
        {
            Platform::iOS
        }
        
        #[cfg(not(any(
            target_os = "windows",
            target_os = "linux",
            target_os = "macos",
            target_os = "freebsd",
            target_os = "openbsd",
            target_os = "netbsd",
            target_os = "android",
            target_os = "ios"
        )))]
        {
            Platform::Unknown
        }
    }

    // 获取系统调用信息
    pub async fn get_syscall_info(&self, name: &str) -> Option<SyscallInfo> {
        let syscalls = self.syscalls.read().await;
        syscalls.get(name).cloned()
    }

    // 获取所有系统调用信息
    pub async fn get_all_syscall_info(&self) -> Vec<SyscallInfo> {
        let syscalls = self.syscalls.read().await;
        syscalls.values().cloned().collect()
    }

    // 获取系统调用统计
    pub async fn get_syscall_stats(&self) -> SyscallStats {
        let syscalls = self.syscalls.read().await;
        
        let total_syscalls = syscalls.len();
        let total_calls: u64 = syscalls.values().map(|s| s.call_count).sum();
        let total_successes: u64 = syscalls.values().map(|s| s.success_count).sum();
        let total_failures: u64 = syscalls.values().map(|s| s.failure_count).sum();
        
        let average_duration: Duration = if total_calls > 0 {
            let total_duration: Duration = syscalls.values().map(|s| s.average_duration).sum();
            Duration::from_nanos(total_duration.as_nanos() as u64 / total_calls as u64)
        } else {
            Duration::ZERO
        };

        SyscallStats {
            total_syscalls,
            total_calls,
            total_successes,
            total_failures,
            average_duration,
            success_rate: if total_calls > 0 {
                total_successes as f64 / total_calls as f64
            } else {
                0.0
            },
        }
    }
}

// 系统调用统计
#[derive(Debug)]
pub struct SyscallStats {
    pub total_syscalls: usize,
    pub total_calls: u64,
    pub total_successes: u64,
    pub total_failures: u64,
    pub average_duration: Duration,
    pub success_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum SyscallError {
    #[error("系统调用失败: {0}")]
    SyscallFailed(String),
    
    #[error("权限不足: {0}")]
    PermissionDenied(String),
    
    #[error("资源不足: {0}")]
    ResourceExhausted(String),
    
    #[error("操作超时: {0}")]
    Timeout(String),
    
    #[error("不支持的操作: {0}")]
    UnsupportedOperation(String),
}
```

## 6. 平台特定功能

### 6.1 平台特定功能管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 平台特定功能管理器
pub struct PlatformSpecificFeatureManager {
    features: Arc<RwLock<HashMap<String, PlatformFeature>>>,
    config: PlatformFeatureConfig,
}

#[derive(Debug, Clone)]
pub struct PlatformFeatureConfig {
    pub enable_auto_detection: bool,
    pub enable_fallback: bool,
    pub enable_logging: bool,
    pub cache_duration: Duration,
    pub max_cache_size: usize,
}

#[derive(Debug, Clone)]
pub struct PlatformFeature {
    pub name: String,
    pub description: String,
    pub platforms: Vec<Platform>,
    pub available: bool,
    pub fallback_available: bool,
    pub last_checked: Instant,
    pub usage_count: u64,
    pub success_count: u64,
    pub failure_count: u64,
}

#[derive(Debug, Clone)]
pub enum Platform {
    Windows,
    Linux,
    macOS,
    FreeBSD,
    OpenBSD,
    NetBSD,
    Android,
    iOS,
    Unknown,
}

impl PlatformSpecificFeatureManager {
    pub fn new(config: PlatformFeatureConfig) -> Self {
        Self {
            features: Arc::new(RwLock::new(HashMap::new())),
            config,
        }
    }

    // 注册平台特定功能
    pub async fn register_feature(&self, feature: PlatformFeature) -> Result<(), PlatformFeatureError> {
        let mut features = self.features.write().await;
        features.insert(feature.name.clone(), feature);
        Ok(())
    }

    // 检查功能是否可用
    pub async fn is_feature_available(&self, name: &str) -> bool {
        let features = self.features.read().await;
        
        if let Some(feature) = features.get(name) {
            feature.available
        } else {
            false
        }
    }

    // 执行平台特定功能
    pub async fn execute_feature<T>(
        &self,
        name: &str,
        operation: impl FnOnce() -> Result<T, PlatformFeatureError>,
    ) -> Result<T, PlatformFeatureError> {
        let mut features = self.features.write().await;
        
        if let Some(feature) = features.get_mut(name) {
            if !feature.available {
                return Err(PlatformFeatureError::FeatureNotAvailable(name.to_string()));
            }
            
            feature.usage_count += 1;
            
            let result = operation();
            
            if result.is_ok() {
                feature.success_count += 1;
            } else {
                feature.failure_count += 1;
            }
            
            result
        } else {
            Err(PlatformFeatureError::FeatureNotFound(name.to_string()))
        }
    }

    // 获取功能信息
    pub async fn get_feature_info(&self, name: &str) -> Option<PlatformFeature> {
        let features = self.features.read().await;
        features.get(name).cloned()
    }

    // 获取所有功能信息
    pub async fn get_all_features(&self) -> Vec<PlatformFeature> {
        let features = self.features.read().await;
        features.values().cloned().collect()
    }

    // 获取功能统计
    pub async fn get_feature_stats(&self) -> PlatformFeatureStats {
        let features = self.features.read().await;
        
        let total_features = features.len();
        let available_features = features.values().filter(|f| f.available).count();
        let total_usage: u64 = features.values().map(|f| f.usage_count).sum();
        let total_successes: u64 = features.values().map(|f| f.success_count).sum();
        let total_failures: u64 = features.values().map(|f| f.failure_count).sum();
        
        PlatformFeatureStats {
            total_features,
            available_features,
            total_usage,
            total_successes,
            total_failures,
            success_rate: if total_usage > 0 {
                total_successes as f64 / total_usage as f64
            } else {
                0.0
            },
        }
    }
}

// 平台特定功能统计
#[derive(Debug)]
pub struct PlatformFeatureStats {
    pub total_features: usize,
    pub available_features: usize,
    pub total_usage: u64,
    pub total_successes: u64,
    pub total_failures: u64,
    pub success_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum PlatformFeatureError {
    #[error("功能未找到: {0}")]
    FeatureNotFound(String),
    
    #[error("功能不可用: {0}")]
    FeatureNotAvailable(String),
    
    #[error("平台不支持: {0}")]
    PlatformNotSupported(String),
    
    #[error("操作失败: {0}")]
    OperationFailed(String),
}
```

## 总结

本章提供了跨平台兼容性的完整示例，包括：

1. **平台检测与适配** - 自动检测操作系统、架构和平台能力
2. **条件编译** - 基于平台和功能的条件编译管理
3. **路径处理** - 跨平台路径规范化和信息获取
4. **环境变量管理** - 跨平台环境变量操作和缓存
5. **系统调用封装** - 统一的系统调用接口和统计
6. **平台特定功能** - 平台特定功能的注册和管理

这些示例展示了如何在 Rust 1.90 中实现跨平台兼容性，提供了完整的平台检测、功能管理和错误处理机制。
