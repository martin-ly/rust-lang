//! # 运行时环境示例
//!
//! 展示如何在不同运行时环境中使用c13_reliability框架

use c13_reliability::prelude::*;
use c13_reliability::runtime_environments::{
    OSEnvironmentAdapter, EmbeddedEnvironmentAdapter, ContainerEnvironmentAdapter,
    VirtualMachineEnvironmentAdapter, WebAssemblyEnvironmentAdapter, FaaSEnvironmentAdapter,
    RealTimeOSEnvironmentAdapter, EdgeComputingEnvironmentAdapter, RuntimeEnvironmentManager,
    RuntimeEnvironment, EnvironmentCapabilities,
};
//use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    println!("=== Rust 统一可靠性框架 - 运行时环境示例 ===");
    
    // 示例1: 操作系统环境
    println!("\n1. 操作系统环境示例");
    demonstrate_os_environment().await?;
    
    // 示例2: 嵌入式裸机环境
    println!("\n2. 嵌入式裸机环境示例");
    demonstrate_embedded_environment().await?;
    
    // 示例3: Docker容器环境
    println!("\n3. Docker容器环境示例");
    demonstrate_container_environment().await?;
    
    // 示例4: 环境自适应使用
    println!("\n4. 环境自适应使用示例");
    demonstrate_adaptive_usage().await?;
    
    Ok(())
}

/// 演示操作系统环境的使用
async fn demonstrate_os_environment() -> Result<(), UnifiedError> {
    println!("创建操作系统环境适配器...");
    
    let mut adapter = OSEnvironmentAdapter::new();
    adapter.initialize().await?;
    
    // 获取系统信息
    let system_info = adapter.get_system_info().await?;
    println!("系统信息:");
    println!("  环境类型: {:?}", system_info.environment);
    println!("  系统名称: {}", system_info.system_name);
    println!("  系统版本: {}", system_info.system_version);
    println!("  架构: {}", system_info.architecture);
    println!("  总内存: {} bytes", system_info.total_memory);
    println!("  CPU核心数: {}", system_info.total_cpu_cores);
    println!("  运行时间: {:?}", system_info.uptime);
    
    // 获取资源使用情况
    let resource_usage = adapter.get_resource_usage().await?;
    println!("资源使用情况:");
    println!("  CPU使用率: {:.1}%", resource_usage.cpu_usage_percent);
    println!("  内存使用: {} bytes ({:.1}%)", 
             resource_usage.memory_usage_bytes, 
             resource_usage.memory_usage_percent);
    println!("  磁盘使用: {} bytes ({:.1}%)", 
             resource_usage.disk_usage_bytes, 
             resource_usage.disk_usage_percent);
    
    // 检查健康状态
    let health_status = adapter.check_health().await?;
    println!("健康状态:");
    println!("  整体健康: {:?}", health_status.overall_health);
    for (component, health) in &health_status.details {
        println!("  {}: {:?}", component, health);
    }
    
    // 执行恢复操作
    println!("执行内存清理...");
    adapter.perform_recovery(RecoveryType::MemoryCleanup).await?;
    
    adapter.cleanup().await?;
    println!("操作系统环境示例完成");
    
    Ok(())
}

/// 演示嵌入式裸机环境的使用
async fn demonstrate_embedded_environment() -> Result<(), UnifiedError> {
    println!("创建嵌入式裸机环境适配器...");
    
    let mut adapter = EmbeddedEnvironmentAdapter::with_config(
        2 * 1024 * 1024, // 2MB 内存
        2, // 2个CPU核心
        1 * 1024 * 1024, // 1MB 磁盘
    );
    adapter.initialize().await?;
    
    // 获取系统信息
    let system_info = adapter.get_system_info().await?;
    println!("系统信息:");
    println!("  环境类型: {:?}", system_info.environment);
    println!("  系统名称: {}", system_info.system_name);
    println!("  总内存: {} bytes", system_info.total_memory);
    println!("  CPU核心数: {}", system_info.total_cpu_cores);
    println!("  运行时间: {:?}", system_info.uptime);
    
    // 获取资源使用情况
    let resource_usage = adapter.get_resource_usage().await?;
    println!("资源使用情况:");
    println!("  CPU使用率: {:.1}%", resource_usage.cpu_usage_percent);
    println!("  内存使用: {} bytes ({:.1}%)", 
             resource_usage.memory_usage_bytes, 
             resource_usage.memory_usage_percent);
    
    // 检查健康状态
    let health_status = adapter.check_health().await?;
    println!("健康状态:");
    println!("  整体健康: {:?}", health_status.overall_health);
    for (component, health) in &health_status.details {
        println!("  {}: {:?}", component, health);
    }
    
    // 执行恢复操作
    println!("执行内存清理...");
    adapter.perform_recovery(RecoveryType::MemoryCleanup).await?;
    
    adapter.cleanup().await?;
    println!("嵌入式裸机环境示例完成");
    
    Ok(())
}

/// 演示Docker容器环境的使用
async fn demonstrate_container_environment() -> Result<(), UnifiedError> {
    println!("创建Docker容器环境适配器...");
    
    let mut adapter = ContainerEnvironmentAdapter::new();
    adapter.initialize().await?;
    
    // 获取系统信息
    let system_info = adapter.get_system_info().await?;
    println!("系统信息:");
    println!("  环境类型: {:?}", system_info.environment);
    println!("  系统名称: {}", system_info.system_name);
    println!("  总内存: {} bytes", system_info.total_memory);
    println!("  CPU核心数: {}", system_info.total_cpu_cores);
    println!("  运行时间: {:?}", system_info.uptime);
    
    // 显示容器特定信息
    if let Some(container_id) = system_info.extra_info.get("container_id") {
        println!("  容器ID: {}", container_id);
    }
    if let Some(container_name) = system_info.extra_info.get("container_name") {
        println!("  容器名称: {}", container_name);
    }
    if let Some(image_name) = system_info.extra_info.get("image_name") {
        println!("  镜像名称: {}", image_name);
    }
    
    // 获取资源使用情况
    let resource_usage = adapter.get_resource_usage().await?;
    println!("资源使用情况:");
    println!("  CPU使用率: {:.1}%", resource_usage.cpu_usage_percent);
    println!("  内存使用: {} bytes ({:.1}%)", 
             resource_usage.memory_usage_bytes, 
             resource_usage.memory_usage_percent);
    println!("  磁盘使用: {} bytes ({:.1}%)", 
             resource_usage.disk_usage_bytes, 
             resource_usage.disk_usage_percent);
    println!("  网络接收: {} bytes", resource_usage.network_rx_bytes);
    println!("  网络发送: {} bytes", resource_usage.network_tx_bytes);
    
    // 检查健康状态
    let health_status = adapter.check_health().await?;
    println!("健康状态:");
    println!("  整体健康: {:?}", health_status.overall_health);
    for (component, health) in &health_status.details {
        println!("  {}: {:?}", component, health);
    }
    
    // 执行恢复操作
    println!("执行内存清理...");
    adapter.perform_recovery(RecoveryType::MemoryCleanup).await?;
    
    adapter.cleanup().await?;
    println!("Docker容器环境示例完成");
    
    Ok(())
}

/// 演示环境自适应使用
async fn demonstrate_adaptive_usage() -> Result<(), UnifiedError> {
    println!("演示环境自适应使用...");
    
    // 检测当前环境
    let environment = detect_current_environment();
    println!("检测到的环境: {:?}", environment);
    
    // 创建环境管理器
    let mut manager = RuntimeEnvironmentManager::new(environment);
    
    // 根据环境设置适配器
    match environment {
        RuntimeEnvironment::OperatingSystem => {
            let adapter = Box::new(OSEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::EmbeddedBareMetal => {
            let adapter = Box::new(EmbeddedEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::Container => {
            let adapter = Box::new(ContainerEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::RealTimeOS => {
            let adapter = Box::new(RealTimeOSEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::GameEngine => {
            // 游戏引擎环境使用操作系统适配器
            let adapter = Box::new(OSEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::Mobile => {
            // 移动环境使用操作系统适配器
            let adapter = Box::new(OSEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::VirtualMachine => {
            let adapter = Box::new(VirtualMachineEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::MicroVM => {
            let adapter = Box::new(VirtualMachineEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::KubernetesPod => {
            let adapter = Box::new(ContainerEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::WebAssembly => {
            let adapter = Box::new(WebAssemblyEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::FunctionAsAService => {
            let adapter = Box::new(FaaSEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::EdgeComputing => {
            let adapter = Box::new(EdgeComputingEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::Blockchain => {
            // 区块链环境使用操作系统适配器
            let adapter = Box::new(OSEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
    }
    
    // 初始化环境
    manager.initialize().await?;
    
    // 获取环境能力
    let capabilities = manager.capabilities();
    println!("环境能力:");
    println!("  支持多进程: {}", capabilities.supports_multiprocessing);
    println!("  支持多线程: {}", capabilities.supports_multithreading);
    println!("  支持文件系统: {}", capabilities.supports_file_system);
    println!("  支持网络: {}", capabilities.supports_network);
    println!("  支持内存管理: {}", capabilities.supports_memory_management);
    println!("  支持进程管理: {}", capabilities.supports_process_management);
    println!("  支持系统调用: {}", capabilities.supports_system_calls);
    println!("  支持中断: {}", capabilities.supports_interrupts);
    println!("  支持定时器: {}", capabilities.supports_timers);
    println!("  支持日志记录: {}", capabilities.supports_logging);
    println!("  支持指标收集: {}", capabilities.supports_metrics);
    println!("  支持健康检查: {}", capabilities.supports_health_checks);
    println!("  支持自动恢复: {}", capabilities.supports_auto_recovery);
    println!("  支持混沌工程: {}", capabilities.supports_chaos_engineering);
    
    if let Some(limit) = capabilities.memory_limit {
        println!("  内存限制: {} bytes", limit);
    }
    if let Some(limit) = capabilities.cpu_limit {
        println!("  CPU限制: {} MHz", limit);
    }
    if let Some(limit) = capabilities.disk_limit {
        println!("  磁盘限制: {} bytes", limit);
    }
    if let Some(limit) = capabilities.network_limit {
        println!("  网络限制: {} bytes/s", limit);
    }
    
    // 根据环境能力调整可靠性策略
    adjust_reliability_strategy(&capabilities).await?;
    
    // 清理环境
    manager.cleanup().await?;
    println!("环境自适应使用示例完成");
    
    Ok(())
}

/// 检测当前运行环境
fn detect_current_environment() -> RuntimeEnvironment {
    // 检查是否在Docker容器中
    if std::path::Path::new("/.dockerenv").exists() {
        return RuntimeEnvironment::Container;
    }
    
    // 检查是否在cgroup中（容器环境）
    if std::path::Path::new("/proc/1/cgroup").exists() {
        if let Ok(content) = std::fs::read_to_string("/proc/1/cgroup") {
            if content.contains("docker") || content.contains("containerd") {
                return RuntimeEnvironment::Container;
            }
        }
    }
    
    // 检查是否在嵌入式环境中（简化检测）
    if std::env::var("EMBEDDED_ENVIRONMENT").is_ok() {
        return RuntimeEnvironment::EmbeddedBareMetal;
    }
    
    // 默认认为是操作系统环境
    RuntimeEnvironment::OperatingSystem
}

/// 根据环境能力调整可靠性策略
async fn adjust_reliability_strategy(capabilities: &EnvironmentCapabilities) -> Result<(), UnifiedError> {
    println!("根据环境能力调整可靠性策略...");
    
    // 创建容错配置
    let mut config = FaultToleranceConfig::default();
    
    // 根据环境能力调整配置
    if capabilities.supports_multiprocessing {
        println!("  启用多进程容错策略");
        config.circuit_breaker.failure_threshold = 10;
    } else {
        println!("  使用单进程容错策略");
        config.circuit_breaker.failure_threshold = 5;
    }
    
    if capabilities.supports_network {
        println!("  启用网络容错策略");
        config.retry.max_attempts = 3;
    } else {
        println!("  禁用网络相关容错策略");
        config.retry.max_attempts = 1;
    }
    
    if capabilities.supports_chaos_engineering {
        println!("  启用混沌工程测试");
    } else {
        println!("  禁用混沌工程测试（环境不支持）");
    }
    
    // 根据资源限制调整配置
    if let Some(memory_limit) = capabilities.memory_limit {
        if memory_limit < 10 * 1024 * 1024 { // 小于10MB
            println!("  检测到低内存环境，调整内存使用策略");
        }
    }
    
    if let Some(cpu_limit) = capabilities.cpu_limit {
        if cpu_limit < 100 { // 小于100MHz
            println!("  检测到低CPU环境，调整CPU使用策略");
        }
    }
    
    println!("可靠性策略调整完成");
    Ok(())
}
