//! # 运行时环境支持模块
//!
//! 本模块提供了对不同运行时环境的抽象和支持：
//! - 操作系统环境 (OS Environment)
//! - 嵌入式裸机环境 (Embedded Bare Metal)
//! - Docker容器环境 (Container Environment)
//!
//! 每种环境都有其特定的资源限制、监控能力和恢复策略。

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use crate::error_handling::UnifiedError;

/// 运行时环境类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RuntimeEnvironment {
    // === 原生执行环境 ===
    /// 操作系统环境 - 完整的操作系统支持
    OperatingSystem,
    /// 嵌入式裸机环境 - 无操作系统，直接运行在硬件上
    EmbeddedBareMetal,
    /// 实时操作系统环境 - 实时性要求高的系统
    RealTimeOS,
    /// 游戏引擎环境 - 高性能实时渲染环境
    GameEngine,
    /// 移动应用环境 - 移动设备优化环境
    Mobile,
    
    // === 虚拟化执行环境 ===
    /// 虚拟机环境 - 传统虚拟化环境
    VirtualMachine,
    /// 微虚拟机环境 - 轻量级虚拟化环境
    MicroVM,
    /// Docker容器环境 - 容器化运行环境
    Container,
    /// Kubernetes Pod环境 - K8s编排的容器环境
    KubernetesPod,
    
    // === 沙箱执行环境 ===
    /// WebAssembly环境 - 沙箱化字节码执行
    WebAssembly,
    /// 函数即服务环境 - 无服务器沙箱执行
    FunctionAsAService,
    
    // === 特殊部署环境 ===
    /// 边缘计算环境 - 边缘设备部署
    EdgeComputing,
    /// 区块链环境 - 分布式区块链网络
    Blockchain,
}

impl RuntimeEnvironment {
    /// 获取环境描述
    pub fn description(&self) -> &'static str {
        match self {
            // 原生执行环境
            RuntimeEnvironment::OperatingSystem => "完整的操作系统环境，支持多进程、多线程和丰富的系统调用",
            RuntimeEnvironment::EmbeddedBareMetal => "嵌入式裸机环境，无操作系统，直接运行在硬件上",
            RuntimeEnvironment::RealTimeOS => "实时操作系统环境，提供确定性的实时响应和低延迟",
            RuntimeEnvironment::GameEngine => "游戏引擎环境，优化高性能实时渲染和资源管理",
            RuntimeEnvironment::Mobile => "移动应用环境，针对移动设备优化的电池和网络管理",
            
            // 虚拟化执行环境
            RuntimeEnvironment::VirtualMachine => "虚拟机环境，提供完整的虚拟化层和资源隔离",
            RuntimeEnvironment::MicroVM => "微虚拟机环境，轻量级虚拟化，快速启动和安全隔离",
            RuntimeEnvironment::Container => "Docker容器环境，提供隔离的运行环境和资源限制",
            RuntimeEnvironment::KubernetesPod => "Kubernetes Pod环境，支持服务发现、配置管理和编排",
            
            // 沙箱执行环境
            RuntimeEnvironment::WebAssembly => "WebAssembly环境，沙箱化字节码执行，跨平台兼容",
            RuntimeEnvironment::FunctionAsAService => "函数即服务环境，无服务器架构，按需执行",
            
            // 特殊部署环境
            RuntimeEnvironment::EdgeComputing => "边缘计算环境，低延迟处理，资源受限，网络不稳定",
            RuntimeEnvironment::Blockchain => "区块链环境，去中心化网络，共识机制，智能合约",
        }
    }

    /// 获取环境特性
    pub fn capabilities(&self) -> EnvironmentCapabilities {
        match self {
            // 原生执行环境
            RuntimeEnvironment::OperatingSystem => EnvironmentCapabilities {
                supports_multiprocessing: true,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: true,
                supports_system_calls: true,
                supports_interrupts: true,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: true,
                memory_limit: None,
                cpu_limit: None,
                disk_limit: None,
                network_limit: None,
            },
            RuntimeEnvironment::EmbeddedBareMetal => EnvironmentCapabilities {
                supports_multiprocessing: false,
                supports_multithreading: false,
                supports_file_system: false,
                supports_network: false,
                supports_memory_management: true,
                supports_process_management: false,
                supports_system_calls: false,
                supports_interrupts: true,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: false,
                memory_limit: Some(1024 * 1024), // 1MB 默认限制
                cpu_limit: Some(100), // 100MHz 默认限制
                disk_limit: Some(1024 * 1024), // 1MB 默认限制
                network_limit: None,
            },
            RuntimeEnvironment::RealTimeOS => EnvironmentCapabilities {
                supports_multiprocessing: false,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: false,
                supports_system_calls: true,
                supports_interrupts: true,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: false,
                memory_limit: Some(16 * 1024 * 1024), // 16MB 默认限制
                cpu_limit: Some(500), // 500MHz 默认限制
                disk_limit: Some(64 * 1024 * 1024), // 64MB 默认限制
                network_limit: Some(10 * 1024 * 1024), // 10MB/s 默认限制
            },
            RuntimeEnvironment::GameEngine => EnvironmentCapabilities {
                supports_multiprocessing: true,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: true,
                supports_system_calls: true,
                supports_interrupts: true,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: true,
                memory_limit: Some(2 * 1024 * 1024 * 1024), // 2GB 默认限制
                cpu_limit: Some(3000), // 3000MHz 默认限制
                disk_limit: Some(50 * 1024 * 1024 * 1024), // 50GB 默认限制
                network_limit: Some(1000 * 1024 * 1024), // 1GB/s 默认限制
            },
            RuntimeEnvironment::Mobile => EnvironmentCapabilities {
                supports_multiprocessing: true,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: true,
                supports_system_calls: true,
                supports_interrupts: true,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: false,
                memory_limit: Some(512 * 1024 * 1024), // 512MB 默认限制
                cpu_limit: Some(2000), // 2000MHz 默认限制
                disk_limit: Some(8 * 1024 * 1024 * 1024), // 8GB 默认限制
                network_limit: Some(100 * 1024 * 1024), // 100MB/s 默认限制
            },
            
            // 虚拟化执行环境
            RuntimeEnvironment::VirtualMachine => EnvironmentCapabilities {
                supports_multiprocessing: true,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: true,
                supports_system_calls: true,
                supports_interrupts: true,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: true,
                memory_limit: Some(4 * 1024 * 1024 * 1024), // 4GB 默认限制
                cpu_limit: Some(2000), // 2000MHz 默认限制
                disk_limit: Some(100 * 1024 * 1024 * 1024), // 100GB 默认限制
                network_limit: Some(1000 * 1024 * 1024), // 1GB/s 默认限制
            },
            RuntimeEnvironment::MicroVM => EnvironmentCapabilities {
                supports_multiprocessing: true,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: true,
                supports_system_calls: true,
                supports_interrupts: false,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: true,
                memory_limit: Some(256 * 1024 * 1024), // 256MB 默认限制
                cpu_limit: Some(1000), // 1000MHz 默认限制
                disk_limit: Some(10 * 1024 * 1024 * 1024), // 10GB 默认限制
                network_limit: Some(100 * 1024 * 1024), // 100MB/s 默认限制
            },
            RuntimeEnvironment::Container => EnvironmentCapabilities {
                supports_multiprocessing: true,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: true,
                supports_system_calls: true,
                supports_interrupts: false,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: true,
                memory_limit: Some(512 * 1024 * 1024), // 512MB 默认限制
                cpu_limit: Some(1000), // 1000MHz 默认限制
                disk_limit: Some(10 * 1024 * 1024 * 1024), // 10GB 默认限制
                network_limit: Some(100 * 1024 * 1024), // 100MB/s 默认限制
            },
            RuntimeEnvironment::KubernetesPod => EnvironmentCapabilities {
                supports_multiprocessing: true,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: true,
                supports_system_calls: true,
                supports_interrupts: false,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: true,
                memory_limit: Some(512 * 1024 * 1024), // 512MB 默认限制
                cpu_limit: Some(1000), // 1000MHz 默认限制
                disk_limit: Some(10 * 1024 * 1024 * 1024), // 10GB 默认限制
                network_limit: Some(100 * 1024 * 1024), // 100MB/s 默认限制
            },
            
            // 沙箱执行环境
            RuntimeEnvironment::WebAssembly => EnvironmentCapabilities {
                supports_multiprocessing: false,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: false,
                supports_system_calls: false,
                supports_interrupts: false,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: false,
                memory_limit: Some(128 * 1024 * 1024), // 128MB 默认限制
                cpu_limit: Some(1000), // 1000MHz 默认限制
                disk_limit: Some(1024 * 1024 * 1024), // 1GB 默认限制
                network_limit: Some(10 * 1024 * 1024), // 10MB/s 默认限制
            },
            RuntimeEnvironment::FunctionAsAService => EnvironmentCapabilities {
                supports_multiprocessing: false,
                supports_multithreading: true,
                supports_file_system: false,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: false,
                supports_system_calls: false,
                supports_interrupts: false,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: false,
                memory_limit: Some(1024 * 1024 * 1024), // 1GB 默认限制
                cpu_limit: Some(1000), // 1000MHz 默认限制
                disk_limit: Some(512 * 1024 * 1024), // 512MB 默认限制
                network_limit: Some(100 * 1024 * 1024), // 100MB/s 默认限制
            },
            
            // 特殊部署环境
            RuntimeEnvironment::EdgeComputing => EnvironmentCapabilities {
                supports_multiprocessing: true,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: true,
                supports_system_calls: true,
                supports_interrupts: true,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: false,
                memory_limit: Some(256 * 1024 * 1024), // 256MB 默认限制
                cpu_limit: Some(1000), // 1000MHz 默认限制
                disk_limit: Some(4 * 1024 * 1024 * 1024), // 4GB 默认限制
                network_limit: Some(50 * 1024 * 1024), // 50MB/s 默认限制
            },
            RuntimeEnvironment::Blockchain => EnvironmentCapabilities {
                supports_multiprocessing: false,
                supports_multithreading: true,
                supports_file_system: true,
                supports_network: true,
                supports_memory_management: true,
                supports_process_management: false,
                supports_system_calls: false,
                supports_interrupts: false,
                supports_timers: true,
                supports_logging: true,
                supports_metrics: true,
                supports_health_checks: true,
                supports_auto_recovery: true,
                supports_chaos_engineering: false,
                memory_limit: Some(2 * 1024 * 1024 * 1024), // 2GB 默认限制
                cpu_limit: Some(2000), // 2000MHz 默认限制
                disk_limit: Some(100 * 1024 * 1024 * 1024), // 100GB 默认限制
                network_limit: Some(100 * 1024 * 1024), // 100MB/s 默认限制
            },
        }
    }
    
    /// 检测当前运行时环境
    pub fn detect_current() -> Self {
        // 检测容器环境
        if is_container_environment() {
            if is_kubernetes_pod() {
                return RuntimeEnvironment::KubernetesPod;
            }
            return RuntimeEnvironment::Container;
        }
        
        // 检测虚拟机环境
        if is_virtual_machine() {
            if is_micro_vm() {
                return RuntimeEnvironment::MicroVM;
            }
            return RuntimeEnvironment::VirtualMachine;
        }
        
        // 检测WebAssembly环境
        if is_webassembly_environment() {
            return RuntimeEnvironment::WebAssembly;
        }
        
        // 检测函数即服务环境
        if is_faas_environment() {
            return RuntimeEnvironment::FunctionAsAService;
        }
        
        // 检测边缘计算环境
        if is_edge_computing_environment() {
            return RuntimeEnvironment::EdgeComputing;
        }
        
        // 检测实时操作系统环境
        if is_rtos_environment() {
            return RuntimeEnvironment::RealTimeOS;
        }
        
        // 检测游戏引擎环境
        if is_game_engine_environment() {
            return RuntimeEnvironment::GameEngine;
        }
        
        // 检测区块链环境
        if is_blockchain_environment() {
            return RuntimeEnvironment::Blockchain;
        }
        
        // 检测移动应用环境
        if is_mobile_environment() {
            return RuntimeEnvironment::Mobile;
        }
        
        // 检测嵌入式环境
        if is_embedded_environment() {
            return RuntimeEnvironment::EmbeddedBareMetal;
        }
        
        // 默认操作系统环境
        RuntimeEnvironment::OperatingSystem
    }
}

/// 检测是否为容器环境
fn is_container_environment() -> bool {
    std::path::Path::new("/.dockerenv").exists() ||
    std::path::Path::new("/proc/1/cgroup").exists() ||
    std::env::var("CONTAINER").is_ok()
}

/// 检测是否为Kubernetes Pod环境
fn is_kubernetes_pod() -> bool {
    std::env::var("KUBERNETES_SERVICE_HOST").is_ok() ||
    std::path::Path::new("/var/run/secrets/kubernetes.io").exists() ||
    std::env::var("KUBERNETES_PORT").is_ok()
}

/// 检测是否为虚拟机环境
fn is_virtual_machine() -> bool {
    // 检测常见的虚拟机特征文件
    let vm_indicators = [
        "/proc/vz",
        "/proc/xen",
        "/proc/vmware",
        "/sys/class/dmi/id/product_name",
    ];
    
    for indicator in &vm_indicators {
        if std::path::Path::new(indicator).exists() {
            return true;
        }
    }
    
    // 检测虚拟机相关的环境变量
    std::env::var("VIRTUAL_ENV").is_ok() ||
    std::env::var("VMWARE_ROOT").is_ok() ||
    std::env::var("VBOX_INSTALL_PATH").is_ok()
}

/// 检测是否为微虚拟机环境
fn is_micro_vm() -> bool {
    // 检测Firecracker等微虚拟机特征
    std::env::var("FIRECRACKER_SOCKET").is_ok() ||
    std::env::var("KATA_CONTAINERS").is_ok() ||
    std::path::Path::new("/proc/1/environ").exists() && 
    std::fs::read_to_string("/proc/1/environ").map_or(false, |content| {
        content.contains("firecracker") || content.contains("kata")
    })
}

/// 检测是否为WebAssembly环境
fn is_webassembly_environment() -> bool {
    #[cfg(target_arch = "wasm32")]
    return true;
    #[cfg(not(target_arch = "wasm32"))]
    {
        // 检测WASI环境
        std::env::var("WASI_SDK_PATH").is_ok() ||
        std::env::var("WASMTIME_HOME").is_ok() ||
        std::env::var("WASMER_DIR").is_ok()
    }
}

/// 检测是否为函数即服务环境
fn is_faas_environment() -> bool {
    std::env::var("AWS_LAMBDA_FUNCTION_NAME").is_ok() ||
    std::env::var("AZURE_FUNCTIONS_ENVIRONMENT").is_ok() ||
    std::env::var("FUNCTION_NAME").is_ok() ||
    std::env::var("VERCEL").is_ok() ||
    std::env::var("NETLIFY").is_ok()
}

/// 检测是否为边缘计算环境
fn is_edge_computing_environment() -> bool {
    std::env::var("EDGE_COMPUTING").is_ok() ||
    std::env::var("EDGE_NODE").is_ok() ||
    std::env::var("K3S_NODE_NAME").is_ok() ||
    std::env::var("MICROK8S").is_ok()
}

/// 检测是否为实时操作系统环境
fn is_rtos_environment() -> bool {
    std::env::var("RTOS_ENVIRONMENT").is_ok() ||
    std::env::var("FREERTOS").is_ok() ||
    std::env::var("ZEPHYR_BASE").is_ok() ||
    std::env::var("VXWORKS").is_ok()
}

/// 检测是否为游戏引擎环境
fn is_game_engine_environment() -> bool {
    std::env::var("UNITY_EDITOR").is_ok() ||
    std::env::var("UNREAL_ENGINE").is_ok() ||
    std::env::var("GODOT").is_ok() ||
    std::env::var("GAME_ENGINE").is_ok()
}

/// 检测是否为区块链环境
fn is_blockchain_environment() -> bool {
    std::env::var("ETHEREUM_NODE").is_ok() ||
    std::env::var("POLKADOT_NODE").is_ok() ||
    std::env::var("SOLANA_VALIDATOR").is_ok() ||
    std::env::var("BLOCKCHAIN_NODE").is_ok()
}

/// 检测是否为移动应用环境
fn is_mobile_environment() -> bool {
    std::env::var("ANDROID_ROOT").is_ok() ||
    std::env::var("IOS_SIMULATOR").is_ok() ||
    std::env::var("FLUTTER_ROOT").is_ok() ||
    std::env::var("REACT_NATIVE").is_ok()
}

/// 检测是否为嵌入式环境
fn is_embedded_environment() -> bool {
    std::env::var("EMBEDDED_ENVIRONMENT").is_ok() ||
    std::env::var("NO_STD").is_ok() ||
    std::env::var("EMBEDDED_TARGET").is_ok()
}

/// 环境能力描述
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentCapabilities {
    /// 是否支持多进程
    pub supports_multiprocessing: bool,
    /// 是否支持多线程
    pub supports_multithreading: bool,
    /// 是否支持文件系统
    pub supports_file_system: bool,
    /// 是否支持网络
    pub supports_network: bool,
    /// 是否支持内存管理
    pub supports_memory_management: bool,
    /// 是否支持进程管理
    pub supports_process_management: bool,
    /// 是否支持系统调用
    pub supports_system_calls: bool,
    /// 是否支持中断
    pub supports_interrupts: bool,
    /// 是否支持定时器
    pub supports_timers: bool,
    /// 是否支持日志记录
    pub supports_logging: bool,
    /// 是否支持指标收集
    pub supports_metrics: bool,
    /// 是否支持健康检查
    pub supports_health_checks: bool,
    /// 是否支持自动恢复
    pub supports_auto_recovery: bool,
    /// 是否支持混沌工程
    pub supports_chaos_engineering: bool,
    /// 内存限制（字节）
    pub memory_limit: Option<u64>,
    /// CPU限制（MHz）
    pub cpu_limit: Option<u64>,
    /// 磁盘限制（字节）
    pub disk_limit: Option<u64>,
    /// 网络限制（字节/秒）
    pub network_limit: Option<u64>,
}

/// 运行时环境适配器接口
#[async_trait]
pub trait RuntimeEnvironmentAdapter: Send + Sync {
    /// 获取环境类型
    fn environment_type(&self) -> RuntimeEnvironment;
    
    /// 获取环境能力
    fn capabilities(&self) -> EnvironmentCapabilities;
    
    /// 初始化环境
    async fn initialize(&mut self) -> Result<(), UnifiedError>;
    
    /// 清理环境
    async fn cleanup(&mut self) -> Result<(), UnifiedError>;
    
    /// 获取系统信息
    async fn get_system_info(&self) -> Result<SystemInfo, UnifiedError>;
    
    /// 获取资源使用情况
    async fn get_resource_usage(&self) -> Result<ResourceUsage, UnifiedError>;
    
    /// 检查环境健康状态
    async fn check_health(&self) -> Result<HealthStatus, UnifiedError>;
    
    /// 执行环境特定的恢复操作
    async fn perform_recovery(&self, recovery_type: RecoveryType) -> Result<(), UnifiedError>;
}

/// 系统信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemInfo {
    /// 环境类型
    pub environment: RuntimeEnvironment,
    /// 系统名称
    pub system_name: String,
    /// 系统版本
    pub system_version: String,
    /// 架构
    pub architecture: String,
    /// 总内存（字节）
    pub total_memory: u64,
    /// 总CPU核心数
    pub total_cpu_cores: u32,
    /// 总磁盘空间（字节）
    pub total_disk_space: u64,
    /// 启动时间
    pub uptime: std::time::Duration,
    /// 环境特定的额外信息
    pub extra_info: std::collections::HashMap<String, String>,
}

/// 资源使用情况
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceUsage {
    /// CPU使用率（百分比）
    pub cpu_usage_percent: f64,
    /// 内存使用量（字节）
    pub memory_usage_bytes: u64,
    /// 内存使用率（百分比）
    pub memory_usage_percent: f64,
    /// 磁盘使用量（字节）
    pub disk_usage_bytes: u64,
    /// 磁盘使用率（百分比）
    pub disk_usage_percent: f64,
    /// 网络接收字节数
    pub network_rx_bytes: u64,
    /// 网络发送字节数
    pub network_tx_bytes: u64,
    /// 网络接收速率（字节/秒）
    pub network_rx_rate: f64,
    /// 网络发送速率（字节/秒）
    pub network_tx_rate: f64,
    /// 时间戳
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

/// 健康状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthStatus {
    /// 整体健康状态
    pub overall_health: HealthLevel,
    /// 详细状态信息
    pub details: std::collections::HashMap<String, HealthLevel>,
    /// 检查时间
    pub check_time: chrono::DateTime<chrono::Utc>,
    /// 环境特定的健康指标
    pub environment_specific: std::collections::HashMap<String, String>,
}

/// 健康级别
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum HealthLevel {
    /// 健康
    Healthy,
    /// 警告
    Warning,
    /// 错误
    Error,
    /// 严重错误
    Critical,
}

/// 恢复类型
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecoveryType {
    /// 内存清理
    MemoryCleanup,
    /// 连接重置
    ConnectionReset,
    /// 进程重启
    ProcessRestart,
    /// 服务重启
    ServiceRestart,
    /// 系统重启
    SystemRestart,
    /// 自定义恢复
    Custom(String),
}

/// 运行时环境管理器
pub struct RuntimeEnvironmentManager {
    /// 当前环境适配器
    adapter: Option<Box<dyn RuntimeEnvironmentAdapter>>,
    /// 环境类型
    environment_type: RuntimeEnvironment,
}

impl RuntimeEnvironmentManager {
    /// 创建新的运行时环境管理器
    pub fn new(environment_type: RuntimeEnvironment) -> Self {
        Self {
            adapter: None,
            environment_type,
        }
    }
    
    /// 设置环境适配器
    pub fn set_adapter(&mut self, adapter: Box<dyn RuntimeEnvironmentAdapter>) {
        self.adapter = Some(adapter);
    }

    /// 使用内置工厂为给定环境创建并设置适配器
    pub fn set_adapter_from_factory(&mut self, environment: RuntimeEnvironment) {
        self.environment_type = environment;
        let adapter = create_adapter_for(environment);
        self.set_adapter(adapter);
    }
    
    /// 获取环境类型
    pub fn environment_type(&self) -> RuntimeEnvironment {
        self.environment_type
    }
    
    /// 获取环境能力
    pub fn capabilities(&self) -> EnvironmentCapabilities {
        self.environment_type.capabilities()
    }
    
    /// 初始化环境
    pub async fn initialize(&mut self) -> Result<(), UnifiedError> {
        if let Some(adapter) = &mut self.adapter {
            adapter.initialize().await
        } else {
            Err(UnifiedError::new(
                "环境适配器未设置",
                crate::error_handling::ErrorSeverity::High,
                "runtime_environment",
                crate::error_handling::ErrorContext::new(
                    "runtime_environment",
                    "initialize",
                    file!(),
                    line!(),
                    crate::error_handling::ErrorSeverity::High,
                    "runtime_environment"
                )
            ))
        }
    }
    
    /// 清理环境
    pub async fn cleanup(&mut self) -> Result<(), UnifiedError> {
        if let Some(adapter) = &mut self.adapter {
            adapter.cleanup().await
        } else {
            Err(UnifiedError::new(
                "环境适配器未设置",
                crate::error_handling::ErrorSeverity::High,
                "runtime_environment",
                crate::error_handling::ErrorContext::new(
                    "runtime_environment",
                    "cleanup",
                    file!(),
                    line!(),
                    crate::error_handling::ErrorSeverity::High,
                    "runtime_environment"
                )
            ))
        }
    }
    
    /// 获取系统信息
    pub async fn get_system_info(&self) -> Result<SystemInfo, UnifiedError> {
        if let Some(adapter) = &self.adapter {
            adapter.get_system_info().await
        } else {
            Err(UnifiedError::new(
                "环境适配器未设置",
                crate::error_handling::ErrorSeverity::High,
                "runtime_environment",
                crate::error_handling::ErrorContext::new(
                    "runtime_environment",
                    "get_system_info",
                    file!(),
                    line!(),
                    crate::error_handling::ErrorSeverity::High,
                    "runtime_environment"
                )
            ))
        }
    }
    
    /// 获取资源使用情况
    pub async fn get_resource_usage(&self) -> Result<ResourceUsage, UnifiedError> {
        if let Some(adapter) = &self.adapter {
            adapter.get_resource_usage().await
        } else {
            Err(UnifiedError::new(
                "环境适配器未设置",
                crate::error_handling::ErrorSeverity::High,
                "runtime_environment",
                crate::error_handling::ErrorContext::new(
                    "runtime_environment",
                    "get_resource_usage",
                    file!(),
                    line!(),
                    crate::error_handling::ErrorSeverity::High,
                    "runtime_environment"
                )
            ))
        }
    }
    
    /// 检查健康状态
    pub async fn check_health(&self) -> Result<HealthStatus, UnifiedError> {
        if let Some(adapter) = &self.adapter {
            adapter.check_health().await
        } else {
            Err(UnifiedError::new(
                "环境适配器未设置",
                crate::error_handling::ErrorSeverity::High,
                "runtime_environment",
                crate::error_handling::ErrorContext::new(
                    "runtime_environment",
                    "check_health",
                    file!(),
                    line!(),
                    crate::error_handling::ErrorSeverity::High,
                    "runtime_environment"
                )
            ))
        }
    }
    
    /// 执行恢复操作
    pub async fn perform_recovery(&self, recovery_type: RecoveryType) -> Result<(), UnifiedError> {
        if let Some(adapter) = &self.adapter {
            adapter.perform_recovery(recovery_type).await
        } else {
            Err(UnifiedError::new(
                "环境适配器未设置",
                crate::error_handling::ErrorSeverity::High,
                "runtime_environment",
                crate::error_handling::ErrorContext::new(
                    "runtime_environment",
                    "perform_recovery",
                    file!(),
                    line!(),
                    crate::error_handling::ErrorSeverity::High,
                    "runtime_environment"
                )
            ))
        }
    }

    /// 动态切换到新的运行时环境
    /// 该方法会清理当前适配器（若存在），然后基于目标环境自动创建并初始化新的适配器
    pub async fn switch_environment(&mut self, new_environment: RuntimeEnvironment) -> Result<(), UnifiedError> {
        if let Some(adapter) = &mut self.adapter {
            let _ = adapter.cleanup().await;
        }
        self.set_adapter_from_factory(new_environment);
        self.initialize().await
    }
}

/// 简单适配器工厂：为给定环境创建合适的适配器实例
pub fn create_adapter_for(environment: RuntimeEnvironment) -> Box<dyn RuntimeEnvironmentAdapter> {
    match environment {
        RuntimeEnvironment::OperatingSystem => Box::new(OSEnvironmentAdapter::new()),
        RuntimeEnvironment::EmbeddedBareMetal => Box::new(EmbeddedEnvironmentAdapter::new()),
        RuntimeEnvironment::Container | RuntimeEnvironment::KubernetesPod => Box::new(ContainerEnvironmentAdapter::new()),
        RuntimeEnvironment::VirtualMachine | RuntimeEnvironment::MicroVM => Box::new(virtual_machine_environment::VirtualMachineEnvironmentAdapter::new()),
        RuntimeEnvironment::RealTimeOS => Box::new(rtos_environment::RealTimeOSEnvironmentAdapter::new()),
        RuntimeEnvironment::EdgeComputing => Box::new(edge_environment::EdgeComputingEnvironmentAdapter::new()),
        RuntimeEnvironment::WebAssembly => Box::new(webassembly_environment::WebAssemblyEnvironmentAdapter::new()),
        RuntimeEnvironment::FunctionAsAService => Box::new(faas_environment::FaaSEnvironmentAdapter::new()),
        _ => Box::new(OSEnvironmentAdapter::new()),
    }
}

// 子模块
pub mod os_environment;
pub mod embedded_environment;
pub mod container_environment;
pub mod virtual_machine_environment;
pub mod webassembly_environment;
pub mod faas_environment;
pub mod monitoring_strategies;
pub mod optimization_algorithms;
pub mod testing_framework;
pub mod simulation;
pub mod rtos_environment;
pub mod edge_environment;

// 重新导出
pub use os_environment::OSEnvironmentAdapter;
pub use embedded_environment::EmbeddedEnvironmentAdapter;
pub use container_environment::ContainerEnvironmentAdapter;
pub use virtual_machine_environment::VirtualMachineEnvironmentAdapter;
pub use webassembly_environment::WebAssemblyEnvironmentAdapter;
pub use faas_environment::FaaSEnvironmentAdapter;
pub use rtos_environment::RealTimeOSEnvironmentAdapter;
pub use edge_environment::EdgeComputingEnvironmentAdapter;
pub use monitoring_strategies::{
    MonitoringStrategy, MonitoringConfig, MonitoringStrategyFactory,
    OperatingSystemMonitoringStrategy, EmbeddedBareMetalMonitoringStrategy,
    ContainerMonitoringStrategy, WebAssemblyMonitoringStrategy, FaaSMonitoringStrategy,
};
pub use optimization_algorithms::{
    OptimizationAlgorithm, OptimizationContext, OptimizationResult, OptimizationSuggestion,
    OptimizationAlgorithmFactory, EmbeddedOptimizationAlgorithm, ContainerOptimizationAlgorithm,
    WebAssemblyOptimizationAlgorithm, ResourceUsageSnapshot, PerformanceMetrics,
    OptimizationGoal, OptimizationConstraints, SuggestionType, ImplementationCost,
    Priority, RiskAssessment, RiskLevel, ImplementationComplexity,
};
pub use testing_framework::{
    EnvironmentTestFramework, TestSuite, Test, TestType, ExpectedResult, EnvironmentRequirements,
    ResourceRequirements, TestResult, TestStatus, TestResults, TestStatistics,
    CompatibilityResult, CompatibilityIssue, IssueType, Severity, TestReport, EnvironmentInfo,
    TestFrameworkFactory, EmbeddedTestFramework, ContainerTestFramework,
};
pub use simulation::{SimulationMode, SimulationConfig, SimulatedEnvironmentAdapter};

// Cloud Native/CNCF 对齐：容器运行时与 K8s 编排抽象（按 feature 导出）
#[cfg(feature = "containers")]
pub mod container_runtime;
#[cfg(feature = "kubernetes")]
pub mod kubernetes;
pub mod orchestrator;
pub mod orchestrator_supervisor;

#[cfg(feature = "containers")]
pub use container_runtime::*;
#[cfg(feature = "kubernetes")]
pub use kubernetes::*;
pub use orchestrator::*;
pub use orchestrator_supervisor::*;