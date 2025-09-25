# 运行时环境支持指南

## 概述

c13_reliability框架现在支持多种运行时环境，并提供云原生扩展（CNCF/OCI/Kubernetes）。

1. **操作系统环境 (Operating System)** - 完整的操作系统支持
2. **嵌入式裸机环境 (Embedded Bare Metal)** - 无操作系统，直接运行在硬件上
3. **Docker容器环境 (Container)** - 容器化运行环境
4. **Kubernetes Pod 环境 (K8s)** - 编排与服务发现（按需启用）

## 环境特性对比

| 特性 | 操作系统 | 嵌入式裸机 | Docker容器 |
|------|----------|------------|------------|
| 多进程支持 | ✅ | ❌ | ✅ |
| 多线程支持 | ✅ | ❌ | ✅ |
| 文件系统支持 | ✅ | ❌ | ✅ |
| 网络支持 | ✅ | ❌ | ✅ |
| 内存管理 | ✅ | ✅ | ✅ |
| 进程管理 | ✅ | ❌ | ✅ |
| 系统调用 | ✅ | ❌ | ✅ |
| 中断支持 | ✅ | ✅ | ❌ |
| 定时器支持 | ✅ | ✅ | ✅ |
| 日志记录 | ✅ | ✅ | ✅ |
| 指标收集 | ✅ | ✅ | ✅ |
| 健康检查 | ✅ | ✅ | ✅ |
| 自动恢复 | ✅ | ✅ | ✅ |
| 混沌工程 | ✅ | ❌ | ✅ |

## 使用方法

### 1. 操作系统环境

```rust
use c13_reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建操作系统环境适配器
    let mut adapter = OSEnvironmentAdapter::new();
    adapter.initialize().await?;
    
    // 获取系统信息
    let system_info = adapter.get_system_info().await?;
    println!("系统: {}", system_info.system_name);
    
    // 获取资源使用情况
    let resource_usage = adapter.get_resource_usage().await?;
    println!("CPU使用率: {:.1}%", resource_usage.cpu_usage_percent);
    
    // 检查健康状态
    let health_status = adapter.check_health().await?;
    println!("健康状态: {:?}", health_status.overall_health);
    
    adapter.cleanup().await?;
    Ok(())
}
```

### 2. 嵌入式裸机环境

```rust
use c13_reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建嵌入式环境适配器（指定资源限制）
    let mut adapter = EmbeddedEnvironmentAdapter::with_config(
        2 * 1024 * 1024, // 2MB 内存
        2, // 2个CPU核心
        1 * 1024 * 1024, // 1MB 磁盘
    );
    adapter.initialize().await?;
    
    // 获取系统信息
    let system_info = adapter.get_system_info().await?;
    println!("总内存: {} bytes", system_info.total_memory);
    
    // 获取资源使用情况
    let resource_usage = adapter.get_resource_usage().await?;
    println!("内存使用: {} bytes", resource_usage.memory_usage_bytes);
    
    // 执行恢复操作
    adapter.perform_recovery(RecoveryType::MemoryCleanup).await?;
    
    adapter.cleanup().await?;
    Ok(())
}
```

### 3. Docker 容器环境

```rust
use c13_reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 创建容器环境适配器
    let mut adapter = ContainerEnvironmentAdapter::new();
    adapter.initialize().await?;
    
    // 获取系统信息
    let system_info = adapter.get_system_info().await?;
    if let Some(container_id) = system_info.extra_info.get("container_id") {
        println!("容器ID: {}", container_id);
    }
    
    // 获取资源使用情况
    let resource_usage = adapter.get_resource_usage().await?;
    println!("内存使用率: {:.1}%", resource_usage.memory_usage_percent);
    
    // 检查健康状态
    let health_status = adapter.check_health().await?;
    println!("容器健康状态: {:?}", health_status.overall_health);
    
    adapter.cleanup().await?;
    Ok(())
}
```

### 4. 环境自适应使用

```rust
use c13_reliability::prelude::*;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 检测当前环境
    let environment = detect_current_environment();
    
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
    }
    
    // 初始化环境
    manager.initialize().await?;
    
    // 获取环境能力
    let capabilities = manager.capabilities();
    println!("支持多进程: {}", capabilities.supports_multiprocessing);
    println!("支持网络: {}", capabilities.supports_network);
    
    // 根据环境能力调整可靠性策略
    adjust_reliability_strategy(&capabilities).await?;
    
    manager.cleanup().await?;
    Ok(())
}

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
    
    // 检查是否在嵌入式环境中
    if std::env::var("EMBEDDED_ENVIRONMENT").is_ok() {
        return RuntimeEnvironment::EmbeddedBareMetal;
    }
    
    // 默认认为是操作系统环境
    RuntimeEnvironment::OperatingSystem
}

async fn adjust_reliability_strategy(capabilities: &EnvironmentCapabilities) -> Result<(), UnifiedError> {
    // 根据环境能力调整容错配置
    let mut config = FaultToleranceConfig::default();
    
    if capabilities.supports_multiprocessing {
        config.circuit_breaker.failure_threshold = 10;
    } else {
        config.circuit_breaker.failure_threshold = 5;
    }
    
    if capabilities.supports_network {
        config.retry.max_attempts = 3;
    } else {
        config.retry.max_attempts = 1;
    }
    
    if !capabilities.supports_chaos_engineering {
        // 禁用混沌工程测试
        println!("当前环境不支持混沌工程测试");
    }
    
    Ok(())
}
```

## 环境特定配置

### 操作系统环境配置

```toml
[runtime_environments.os]
enabled = true
monitor_processes = true
monitor_network = true
monitor_file_system = true
enable_system_calls = true
```

### 嵌入式裸机环境配置

```toml
[runtime_environments.embedded]
enabled = true
total_memory = 2097152  # 2MB
total_cpu_cores = 2
total_disk_space = 1048576  # 1MB
monitor_interrupts = true
monitor_timers = true
```

### Docker 容器环境配置

```toml
[runtime_environments.container]
enabled = true
monitor_resource_limits = true
monitor_container_health = true
enable_container_recovery = true
```

## 恢复策略

不同环境支持不同的恢复策略：

### 操作系统环境

- ✅ 内存清理
- ✅ 连接重置
- ✅ 进程重启
- ✅ 服务重启
- ✅ 系统重启

### 嵌入式裸机环境

- ✅ 内存清理
- ✅ 连接重置
- ✅ 进程重启
- ✅ 服务重启
- ✅ 系统重启

### Docker容器环境

- ✅ 内存清理
- ✅ 连接重置
- ✅ 进程重启
- ✅ 服务重启
- ✅ 系统重启

## 云原生扩展（CNCF/OCI/Kubernetes）

### 特性开关

```toml
[features]
containers = []               # 容器运行时抽象（不绑定实现）
docker-runtime = []           # 本地 Docker 占位实现
kubernetes = []               # Kubernetes 占位客户端与抽象
oci = ["oci-spec"]           # 启用 OCI 规范解析（可选）
```

### 容器运行时抽象

```rust
use c13_reliability::runtime_environments::container_runtime::*;

let image: ImageReference = "docker.io/library/nginx:latest".parse().unwrap();
let cfg = ContainerRunConfig {
    image,
    args: vec![],
    env: vec![],
    cpu_limit_millis: Some(500),
    memory_limit_bytes: Some(256 * 1024 * 1024),
    restart_policy: Some(RestartPolicy::OnFailure { max_retries: 3, backoff_secs: 5 }),
    health_probe: None,
};
```

### 编排与监督

```rust
use c13_reliability::runtime_environments::orchestrator::*;
use c13_reliability::runtime_environments::orchestrator_supervisor::*;

// 本地容器编排（需 --features docker-runtime）
let orch = LocalContainerOrchestrator::new(DockerRuntime::new(), cfg);
let sup = OrchestratorSupervisor::new(orch, BackoffPolicy::default());
sup.ensure_running("nginx").await?;
```

### Kubernetes 占位

```rust
use c13_reliability::runtime_environments::kubernetes::*;

let pod = PodSpecMini {
    name: "c13-pod".into(),
    image: "docker.io/library/nginx:latest".into(),
    args: vec![],
    env: vec![],
    cpu_millis: Some(500),
    memory_bytes: Some(256 * 1024 * 1024),
    liveness: None,
    readiness: None,
};
let k8s = KubernetesClientPlaceholder::new();
// k8s.apply_pod("default", &pod).await?; // 接入 kube-rs 后启用
```

## 最佳实践

### 1. 环境检测

- 在应用启动时检测运行环境
- 根据环境特性调整配置
- 使用环境特定的优化策略

### 2. 资源管理

- 嵌入式环境：严格控制内存和CPU使用
- 容器环境：监控资源限制
- 操作系统环境：充分利用系统资源

### 3. 错误处理

- 根据环境能力选择合适的错误恢复策略
- 嵌入式环境：优先使用轻量级恢复操作
- 容器环境：利用容器重启机制

### 4. 监控和指标

- 根据环境特性调整监控频率
- 嵌入式环境：减少监控开销
- 容器环境：关注资源限制

## 故障排除

### 常见问题

1. **环境检测失败**
   - 检查环境变量设置
   - 验证文件系统路径
   - 确认权限设置

2. **资源监控不准确**
   - 检查系统权限
   - 验证监控接口
   - 确认资源限制设置

3. **恢复操作失败**
   - 检查环境能力
   - 验证恢复权限
   - 确认恢复策略配置

### 调试技巧

1. 启用详细日志记录
2. 使用环境特定的调试工具
3. 监控资源使用情况
4. 验证环境检测结果

## 示例代码

查看 `examples/runtime_environment_example.rs` 获取完整的使用示例。

## 贡献

欢迎为运行时环境支持贡献代码！请查看 `CONTRIBUTING.md` 了解详细信息。
