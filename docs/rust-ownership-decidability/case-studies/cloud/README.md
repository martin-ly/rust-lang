# Rust 云计算与容器开发完全指南

> 一份关于使用 Rust 构建云原生应用、容器运行时和 Kubernetes 生态系统的综合指南

---

## 目录

- [Rust 云计算与容器开发完全指南](#rust-云计算与容器开发完全指南)
  - [目录](#目录)
  - [1. 云原生 Rust 概述](#1-云原生-rust-概述)
    - [1.1 Rust 在云原生领域的优势](#11-rust-在云原生领域的优势)
      - [内存安全与性能](#内存安全与性能)
      - [并发模型](#并发模型)
    - [1.2 与 Go 的对比](#12-与-go-的对比)
      - [性能对比](#性能对比)
      - [资源占用对比](#资源占用对比)
    - [1.3 现有项目概览](#13-现有项目概览)
      - [Firecracker - AWS 的微型虚拟机](#firecracker---aws-的微型虚拟机)
      - [Linkerd2-proxy - 服务网格数据平面](#linkerd2-proxy---服务网格数据平面)
  - [2. 容器运行时](#2-容器运行时)
    - [2.1 youki 容器运行时](#21-youki-容器运行时)
    - [2.2 OCI 规范实现](#22-oci-规范实现)
    - [2.3 cgroups v2 实现](#23-cgroups-v2-实现)
    - [2.4 命名空间管理](#24-命名空间管理)
    - [2.5 容器文件系统隔离](#25-容器文件系统隔离)
  - [3. Kubernetes 生态](#3-kubernetes-生态)
    - [3.1 kube-rs 客户端基础](#31-kube-rs-客户端基础)
    - [3.2 Operator 开发框架](#32-operator-开发框架)
    - [3.3 CRD 定义与代码生成](#33-crd-定义与代码生成)
    - [3.4 Controller 实现详解](#34-controller-实现详解)
    - [3.5 高级 API 操作](#35-高级-api-操作)
  - [4. 服务网格](#4-服务网格)
    - [4.1 Linkerd2-proxy 架构分析](#41-linkerd2-proxy-架构分析)
    - [4.2 mTLS 实现](#42-mtls-实现)
    - [4.3 流量管理](#43-流量管理)
    - [4.4 可观测性集成](#44-可观测性集成)
  - [5. Serverless](#5-serverless)
    - [5.1 AWS Lambda Rust 运行时](#51-aws-lambda-rust-运行时)
    - [5.2 冷启动优化](#52-冷启动优化)
    - [5.3 函数即服务框架](#53-函数即服务框架)
  - [6. 分布式系统](#6-分布式系统)
    - [6.1 Raft 共识算法实现](#61-raft-共识算法实现)
    - [6.2 服务发现](#62-服务发现)
    - [6.3 负载均衡](#63-负载均衡)
    - [6.4 断路器模式](#64-断路器模式)
  - [7. 可观测性](#7-可观测性)
    - [7.1 OpenTelemetry 集成](#71-opentelemetry-集成)
    - [7.2 Prometheus 指标](#72-prometheus-指标)
    - [7.3 结构化日志](#73-结构化日志)
    - [7.4 健康检查与探针](#74-健康检查与探针)
  - [8. 完整示例：微服务部署](#8-完整示例微服务部署)
    - [8.1 微服务代码](#81-微服务代码)
    - [8.2 Dockerfile 多阶段构建](#82-dockerfile-多阶段构建)
    - [8.3 Kubernetes 部署配置](#83-kubernetes-部署配置)
    - [8.4 Istio 服务网格配置](#84-istio-服务网格配置)
    - [8.5 Prometheus 监控告警](#85-prometheus-监控告警)
  - [9. 性能优化](#9-性能优化)
    - [9.1 编译优化](#91-编译优化)
    - [9.2 镜像大小优化](#92-镜像大小优化)
    - [9.3 启动时间优化](#93-启动时间优化)
  - [10. CI/CD](#10-cicd)
    - [10.1 GitHub Actions 工作流](#101-github-actions-工作流)
    - [10.2 容器镜像构建脚本](#102-容器镜像构建脚本)
    - [10.3 安全扫描配置](#103-安全扫描配置)
  - [附录：资源与参考](#附录资源与参考)
    - [推荐 crate](#推荐-crate)
    - [学习资源](#学习资源)

---

## 1. 云原生 Rust 概述

### 1.1 Rust 在云原生领域的优势

Rust 语言在云原生领域展现出独特的优势，使其成为构建基础设施软件的理想选择：

#### 内存安全与性能

```rust
// Rust 的零成本抽象确保高性能
pub struct ConnectionPool<T> {
    connections: Vec<T>,
    max_size: usize,
}

impl<T> ConnectionPool<T> {
    pub fn new(max_size: usize) -> Self {
        Self {
            connections: Vec::with_capacity(max_size),
            max_size,
        }
    }

    // 编译时保证线程安全，无需 GC 暂停
    pub fn acquire(&mut self) -> Option<T> {
        self.connections.pop()
    }
}
```

| 特性 | Rust | Go | Java |
|------|------|-----|------|
| 内存安全 | 编译期保证 | GC | GC |
| 零成本抽象 | ✅ | ❌ | ❌ |
| 二进制大小 | 小 | 较大 | 大 |
| 启动时间 | 毫秒级 | 较快 | 秒级 |
| 运行时依赖 | 无 | 运行时 | JVM |

#### 并发模型

Rust 的所有权系统天然适合云原生环境的高并发需求：

```rust
use tokio::sync::mpsc;
use std::sync::Arc;

// 无数据竞争的并发处理
pub async fn handle_requests(
    mut rx: mpsc::Receiver<Request>,
    state: Arc<AppState>,
) {
    while let Some(req) = rx.recv().await {
        let state = Arc::clone(&state);
        // 每个请求在独立任务中处理
        tokio::spawn(async move {
            process_request(req, state).await;
        });
    }
}
```

### 1.2 与 Go 的对比

#### 性能对比

```rust
// Rust 的高性能 HTTP 服务
use axum::{routing::get, Router};
use std::net::SocketAddr;

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(handler));

    let addr = SocketAddr::from(([0, 0, 0, 0], 3000));
    println!("Listening on {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}

async fn handler() -> &'static str {
    "Hello, Cloud Native!"
}
```

#### 资源占用对比

| 指标 | Rust (Actix-web) | Go (Gin) | 差异 |
|------|------------------|----------|------|
| 内存占用 | ~5MB | ~20MB | 75%↓ |
| QPS (单核) | ~200k | ~120k | 67%↑ |
| P99 延迟 | <1ms | ~2ms | 50%↓ |
| 二进制大小 | ~5MB | ~15MB | 67%↓ |

### 1.3 现有项目概览

#### Firecracker - AWS 的微型虚拟机

```rust
// Firecracker 的核心设计理念
pub struct Vmm {
    // 设备管理
    block_devices: HashMap<String, Arc<Mutex<BlockDevice>>>,
    net_devices: HashMap<String, Arc<Mutex<NetDevice>>>,
    // 内存管理
    guest_memory: GuestMemoryMmap,
    // vCPU 管理
    vcpus: Vec<Vcpu>,
}

impl Vmm {
    /// 启动微型虚拟机
    pub fn start_microvm(&mut self) -> Result<()> {
        // 初始化设备
        self.attach_block_devices()?;
        self.attach_net_devices()?;
        // 启动 vCPU
        self.start_vcpus()?;
        Ok(())
    }
}
```

#### Linkerd2-proxy - 服务网格数据平面

```rust
// Linkerd2-proxy 的连接处理
pub struct Proxy {
    inbound: Inbound,
    outbound: Outbound,
    control: ControlPlane,
}

impl Proxy {
    pub async fn run(self) -> Result<(), Error> {
        tokio::select! {
            res = self.inbound.serve() => res,
            res = self.outbound.serve() => res,
            res = self.control.serve() => res,
        }
    }
}
```

---

## 2. 容器运行时

### 2.1 youki 容器运行时

youki 是使用 Rust 编写的 OCI 运行时，旨在替代 runc：

```rust
// youki 的核心容器生命周期管理
use youki::container::Container;
use youki::spec::Spec;

pub struct ContainerBuilder {
    id: String,
    spec: Spec,
    root: PathBuf,
}

impl ContainerBuilder {
    pub fn new(id: &str) -> Self {
        Self {
            id: id.to_string(),
            spec: Spec::default(),
            root: PathBuf::from("/run/youki"),
        }
    }

    /// 创建并启动容器
    pub fn build(&self) -> Result<Container, ContainerError> {
        // 1. 创建容器状态目录
        self.create_container_dir()?;

        // 2. 设置命名空间
        let namespaces = self.setup_namespaces()?;

        // 3. 配置 cgroups
        self.setup_cgroups()?;

        // 4. 挂载文件系统
        self.setup_mounts()?;

        // 5. 启动容器进程
        self.start_container_process(namespaces)
    }
}
```

### 2.2 OCI 规范实现

```rust
use serde::{Deserialize, Serialize};

/// OCI Runtime Spec 的 Rust 实现
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Spec {
    #[serde(rename = "ociVersion")]
    pub oci_version: String,
    pub process: Option<Process>,
    pub root: Option<Root>,
    pub hostname: Option<String>,
    pub mounts: Option<Vec<Mount>>,
    pub linux: Option<Linux>,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Process {
    pub terminal: Option<bool>,
    pub user: User,
    pub args: Vec<String>,
    pub env: Vec<String>,
    pub cwd: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Linux {
    #[serde(rename = "uidMappings")]
    pub uid_mappings: Option<Vec<IdMapping>>,
    #[serde(rename = "gidMappings")]
    pub gid_mappings: Option<Vec<IdMapping>>,
    pub namespaces: Vec<Namespace>,
    pub resources: Option<Resources>,
    pub cgroups_path: Option<String>,
}

/// 解析 OCI 配置文件
pub fn load_spec(path: &Path) -> Result<Spec, SpecError> {
    let content = fs::read_to_string(path)?;
    let spec: Spec = serde_json::from_str(&content)?;
    Ok(spec)
}
```

### 2.3 cgroups v2 实现

```rust
use std::path::PathBuf;

/// cgroups v2 统一管理器
pub struct CgroupV2 {
    path: PathBuf,
}

impl CgroupV2 {
    pub fn new(cgroup_path: &str) -> Self {
        Self {
            path: PathBuf::from("/sys/fs/cgroup").join(cgroup_path),
        }
    }

    /// 创建 cgroup 并设置资源限制
    pub fn create(&self) -> Result<(), CgroupError> {
        fs::create_dir_all(&self.path)?;
        Ok(())
    }

    /// 设置 CPU 限制
    pub fn set_cpu_limit(&self, quota: i64, period: u64) -> Result<(), CgroupError> {
        let max = if quota > 0 {
            format!("{} {}", quota, period)
        } else {
            "max".to_string()
        };
        fs::write(self.path.join("cpu.max"), max)?;
        Ok(())
    }

    /// 设置内存限制
    pub fn set_memory_limit(&self, limit: i64) -> Result<(), CgroupError> {
        let max = if limit > 0 {
            limit.to_string()
        } else {
            "max".to_string()
        };
        fs::write(self.path.join("memory.max"), max)?;
        Ok(())
    }

    /// 添加进程到 cgroup
    pub fn add_process(&self, pid: Pid) -> Result<(), CgroupError> {
        fs::write(self.path.join("cgroup.procs"), pid.as_raw().to_string())?;
        Ok(())
    }

    /// 删除 cgroup
    pub fn delete(&self) -> Result<(), CgroupError> {
        fs::remove_dir(&self.path)?;
        Ok(())
    }
}

/// 完整的资源限制配置
pub struct ResourceLimits {
    pub cpu_shares: Option<u64>,
    pub cpu_quota: Option<i64>,
    pub cpu_period: Option<u64>,
    pub memory_limit: Option<i64>,
    pub memory_swap: Option<i64>,
    pub pids_limit: Option<i64>,
}

impl CgroupV2 {
    pub fn apply_limits(&self, limits: &ResourceLimits) -> Result<(), CgroupError> {
        if let Some(limit) = limits.memory_limit {
            self.set_memory_limit(limit)?;
        }

        if let (Some(quota), Some(period)) = (limits.cpu_quota, limits.cpu_period) {
            self.set_cpu_limit(quota, period)?;
        }

        if let Some(pids) = limits.pids_limit {
            fs::write(self.path.join("pids.max"), pids.to_string())?;
        }

        Ok(())
    }
}
```

### 2.4 命名空间管理

```rust
use nix::sched::{clone, unshare, CloneFlags};
use nix::sys::wait::waitpid;
use nix::unistd::Pid;

/// Linux 命名空间配置
pub struct NamespaceConfig {
    pub new_ipc: bool,
    pub new_net: bool,
    pub new_pid: bool,
    pub new_user: bool,
    pub new_uts: bool,
    pub new_cgroup: bool,
}

impl NamespaceConfig {
    pub fn all() -> Self {
        Self {
            new_ipc: true,
            new_net: true,
            new_pid: true,
            new_user: true,
            new_uts: true,
            new_cgroup: true,
        }
    }
}

/// 设置容器命名空间
pub fn setup_namespaces(config: &NamespaceConfig) -> Result<(), NamespaceError> {
    let mut flags = CloneFlags::empty();

    if config.new_ipc {
        flags.insert(CloneFlags::CLONE_NEWIPC);
    }
    if config.new_net {
        flags.insert(CloneFlags::CLONE_NEWNET);
    }
    if config.new_pid {
        flags.insert(CloneFlags::CLONE_NEWPID);
    }
    if config.new_user {
        flags.insert(CloneFlags::CLONE_NEWUSER);
    }
    if config.new_uts {
        flags.insert(CloneFlags::CLONE_NEWUTS);
    }
    if config.new_cgroup {
        flags.insert(CloneFlags::CLONE_NEWCGROUP);
    }

    unshare(flags)?;
    Ok(())
}

/// 在指定命名空间中执行命令
pub fn run_in_namespace<F>(
    config: &NamespaceConfig,
    f: F,
) -> Result<Pid, NamespaceError>
where
    F: FnOnce() -> i32,
{
    let mut flags = CloneFlags::empty();
    flags.insert(CloneFlags::CLONE_NEWNS); // 挂载命名空间

    if config.new_ipc {
        flags.insert(CloneFlags::CLONE_NEWIPC);
    }
    if config.new_net {
        flags.insert(CloneFlags::CLONE_NEWNET);
    }
    if config.new_pid {
        flags.insert(CloneFlags::CLONE_NEWPID);
    }
    if config.new_user {
        flags.insert(CloneFlags::CLONE_NEWUSER);
    }
    if config.new_uts {
        flags.insert(CloneFlags::CLONE_NEWUTS);
    }

    const STACK_SIZE: usize = 1024 * 1024;
    let mut stack = vec![0u8; STACK_SIZE];

    let pid = unsafe {
        clone(
            Box::new(f),
            &mut stack,
            flags,
            Some(nix::sys::signal::Signal::SIGCHLD as i32),
        )?
    };

    Ok(pid)
}
```

### 2.5 容器文件系统隔离

```rust
use nix::mount::{mount, umount, MsFlags};

/// 设置容器的根文件系统
pub fn setup_rootfs(rootfs: &Path, readonly: bool) -> Result<(), MountError> {
    // 挂载 proc
    mount(
        Some("proc"),
        &rootfs.join("proc"),
        Some("proc"),
        MsFlags::MS_NOSUID | MsFlags::MS_NOEXEC | MsFlags::MS_NODEV,
        None::<&str>,
    )?;

    // 挂载 sysfs
    mount(
        Some("sysfs"),
        &rootfs.join("sys"),
        Some("sysfs"),
        MsFlags::MS_NOSUID | MsFlags::MS_NOEXEC | MsFlags::MS_NODEV | MsFlags::MS_RDONLY,
        None::<&str>,
    )?;

    // 挂载 tmpfs
    mount(
        Some("tmpfs"),
        &rootfs.join("dev"),
        Some("tmpfs"),
        MsFlags::MS_NOSUID | MsFlags::MS_STRICTATIME,
        Some("mode=755"),
    )?;

    // 创建必要设备节点
    create_devices(rootfs)?;

    // 如果需要只读根文件系统
    if readonly {
        mount(
            None::<&str>,
            rootfs,
            None::<&str>,
            MsFlags::MS_BIND | MsFlags::MS_REMOUNT | MsFlags::MS_RDONLY | MsFlags::MS_NOSUID | MsFlags::MS_NODEV,
            None::<&str>,
        )?;
    }

    Ok(())
}

/// pivot_root 实现
pub fn pivot_rootfs(new_root: &Path, put_old: &Path) -> Result<(), MountError> {
    // 确保 new_root 是挂载点
    mount(
        Some(new_root),
        new_root,
        None::<&str>,
        MsFlags::MS_BIND | MsFlags::MS_REC,
        None::<&str>,
    )?;

    // 创建 put_old 目录
    fs::create_dir_all(new_root.join(put_old))?;

    // 执行 pivot_root
    nix::unistd::pivot_root(new_root, &new_root.join(put_old))?;

    // 切换当前目录到 /
    std::env::set_current_dir("/")?;

    // 卸载旧的根文件系统
    umount("/.old_root")?;

    Ok(())
}
```

---

## 3. Kubernetes 生态

### 3.1 kube-rs 客户端基础

kube-rs 是 Kubernetes 的官方 Rust 客户端：

```rust
use kube::{Client, Config, api::{Api, ListParams, ResourceExt}};
use k8s_openapi::api::core::v1::Pod;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 加载 kubeconfig
    let config = Config::infer().await?;
    let client = Client::try_from(config)?;

    // 创建 Pod API 客户端
    let pods: Api<Pod> = Api::default_namespaced(client);

    // 列出所有 Pod
    let lp = ListParams::default();
    for pod in pods.list(&lp).await? {
        println!("Found Pod: {}", pod.name_any());
    }

    Ok(())
}
```

### 3.2 Operator 开发框架

```rust
use kube::runtime::controller::{Action, Controller};
use kube::runtime::finalizer::{finalizer, Event as FinalizerEvent};
use kube::{Resource, ResourceExt};
use std::sync::Arc;
use tokio::time::Duration;

/// 自定义资源定义
#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[serde(rename_all = "camelCase")]
pub struct MyAppSpec {
    pub image: String,
    pub replicas: i32,
    pub port: i32,
}

/// Operator 上下文
pub struct Context {
    client: Client,
}

/// 主要调谐函数
async fn reconcile(app: Arc<MyApp>, ctx: Arc<Context>) -> Result<Action, Error> {
    let client = &ctx.client;
    let ns = app.namespace().unwrap();
    let name = app.name_any();

    println!("Reconciling MyApp: {} in namespace {}", name, ns);

    // 1. 确保 Deployment 存在
    ensure_deployment(client, &app, &ns).await?;

    // 2. 确保 Service 存在
    ensure_service(client, &app, &ns).await?;

    // 3. 更新状态
    update_status(client, &app, &ns).await?;

    Ok(Action::requeue(Duration::from_secs(300)))
}

/// 错误处理
fn error_policy(_app: Arc<MyApp>, error: &Error, _ctx: Arc<Context>) -> Action {
    eprintln!("Reconcile failed: {:?}", error);
    Action::requeue(Duration::from_secs(60))
}

/// 启动 Controller
pub async fn run(client: Client) -> Result<(), Error> {
    let context = Arc::new(Context { client: client.clone() });

    Controller::new(Api::<MyApp>::all(client), ListParams::default())
        .run(reconcile, error_policy, context)
        .for_each(|_| async {})
        .await;

    Ok(())
}
```

### 3.3 CRD 定义与代码生成

```rust
use kube::CustomResource;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// 定义自定义资源
#[derive(CustomResource, Clone, Debug, Deserialize, Serialize, JsonSchema)]
#[kube(
    group = "example.com",
    version = "v1",
    kind = "Database",
    namespaced,
    status = "DatabaseStatus",
    shortname = "db"
)]
#[serde(rename_all = "camelCase")]
pub struct DatabaseSpec {
    pub engine: DatabaseEngine,
    pub version: String,
    pub storage: StorageSpec,
    pub replicas: i32,
    pub backup: Option<BackupSpec>,
}

#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub enum DatabaseEngine {
    PostgreSQL,
    MySQL,
    MongoDB,
    Redis,
}

#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub struct StorageSpec {
    pub size: String,
    pub storage_class: Option<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub struct BackupSpec {
    pub enabled: bool,
    pub schedule: String,
    pub retention_days: i32,
}

#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub struct DatabaseStatus {
    pub phase: DatabasePhase,
    pub message: String,
    pub last_backup: Option<String>,
    pub endpoints: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize, JsonSchema)]
pub enum DatabasePhase {
    Pending,
    Creating,
    Running,
    Failed,
    Deleting,
}
```

### 3.4 Controller 实现详解

```rust
use k8s_openapi::api::apps::v1::{Deployment, DeploymentSpec};
use k8s_openapi::api::core::v1::{Container, ContainerPort, PodSpec, PodTemplateSpec};
use k8s_openapi::apimachinery::pkg::apis::meta::v1::{LabelSelector, ObjectMeta};

/// 确保 Deployment 存在
async fn ensure_deployment(
    client: &Client,
    app: &MyApp,
    ns: &str,
) -> Result<(), Error> {
    let deployment_api: Api<Deployment> = Api::namespaced(client.clone(), ns);

    let name = app.name_any();
    let labels = vec![
        ("app".to_string(), name.clone()),
        ("managed-by".to_string(), "my-operator".to_string()),
    ]
    .into_iter()
    .collect();

    let deployment = Deployment {
        metadata: ObjectMeta {
            name: Some(name.clone()),
            namespace: Some(ns.to_string()),
            owner_references: Some(vec![app.controller_owner_ref(&()).unwrap()]),
            ..Default::default()
        },
        spec: Some(DeploymentSpec {
            replicas: Some(app.spec.replicas),
            selector: LabelSelector {
                match_labels: Some(labels.clone()),
                ..Default::default()
            },
            template: PodTemplateSpec {
                metadata: Some(ObjectMeta {
                    labels: Some(labels),
                    ..Default::default()
                }),
                spec: Some(PodSpec {
                    containers: vec![Container {
                        name: "app".to_string(),
                        image: Some(app.spec.image.clone()),
                        ports: Some(vec![ContainerPort {
                            container_port: app.spec.port,
                            ..Default::default()
                        }]),
                        ..Default::default()
                    }],
                    ..Default::default()
                }),
            },
            ..Default::default()
        }),
        status: None,
    };

    // 应用或更新 Deployment
    match deployment_api.get(&name).await {
        Ok(_) => {
            deployment_api.replace(&name, &Default::default(), &deployment).await?;
        }
        Err(_) => {
            deployment_api.create(&Default::default(), &deployment).await?;
        }
    }

    Ok(())
}

/// 确保 Service 存在
async fn ensure_service(
    client: &Client,
    app: &MyApp,
    ns: &str,
) -> Result<(), Error> {
    use k8s_openapi::api::core::v1::{Service, ServicePort, ServiceSpec};

    let service_api: Api<Service> = Api::namespaced(client.clone(), ns);
    let name = app.name_any();

    let service = Service {
        metadata: ObjectMeta {
            name: Some(name.clone()),
            namespace: Some(ns.to_string()),
            owner_references: Some(vec![app.controller_owner_ref(&()).unwrap()]),
            ..Default::default()
        },
        spec: Some(ServiceSpec {
            selector: Some(
                vec![("app".to_string(), name.clone())]
                    .into_iter()
                    .collect(),
            ),
            ports: Some(vec![ServicePort {
                port: 80,
                target_port: Some(k8s_openapi::apimachinery::pkg::util::intstr::IntOrString::Int(app.spec.port)),
                ..Default::default()
            }]),
            ..Default::default()
        }),
        status: None,
    };

    match service_api.get(&name).await {
        Ok(_) => {
            service_api.replace(&name, &Default::default(), &service).await?;
        }
        Err(_) => {
            service_api.create(&Default::default(), &service).await?;
        }
    }

    Ok(())
}
```

### 3.5 高级 API 操作

```rust
use kube::api::{DeleteParams, Patch, PatchParams, WatchEvent};

/// 使用 Patch 更新资源
async fn patch_deployment_replicas(
    client: &Client,
    name: &str,
    ns: &str,
    replicas: i32,
) -> Result<(), Error> {
    let deployments: Api<Deployment> = Api::namespaced(client.clone(), ns);

    let patch = serde_json::json!({
        "spec": {
            "replicas": replicas
        }
    });

    let patch_params = PatchParams::apply("my-controller");
    deployments
        .patch(name, &patch_params, &Patch::Apply(&patch))
        .await?;

    Ok(())
}

/// 流式监控资源变化
async fn watch_pods(client: &Client, ns: &str) -> Result<(), Error> {
    let pods: Api<Pod> = Api::namespaced(client.clone(), ns);
    let lp = ListParams::default();

    let mut stream = pods.watch(&lp, "0").await?.boxed();

    while let Some(event) = stream.try_next().await? {
        match event {
            WatchEvent::Added(pod) => {
                println!("Pod added: {}", pod.name_any());
            }
            WatchEvent::Modified(pod) => {
                let phase = pod.status.as_ref().and_then(|s| s.phase.clone());
                println!("Pod modified: {} - {:?}", pod.name_any(), phase);
            }
            WatchEvent::Deleted(pod) => {
                println!("Pod deleted: {}", pod.name_any());
            }
            WatchEvent::Error(e) => {
                eprintln!("Watch error: {:?}", e);
            }
            _ => {}
        }
    }

    Ok(())
}

/// 优雅删除资源
async fn delete_pod_with_grace_period(
    client: &Client,
    name: &str,
    ns: &str,
    grace_period: i64,
) -> Result<(), Error> {
    let pods: Api<Pod> = Api::namespaced(client.clone(), ns);

    let dp = DeleteParams {
        grace_period_seconds: Some(grace_period),
        ..Default::default()
    };

    pods.delete(name, &dp).await?;
    println!("Pod {} deletion initiated", name);

    Ok(())
}
```

---

## 4. 服务网格

### 4.1 Linkerd2-proxy 架构分析

Linkerd2-proxy 是 Linkerd 服务网格的数据平面代理：

```rust
use tower::ServiceBuilder;
use tower_http::trace::TraceLayer;

/// 简化的服务网格代理架构
pub struct ServiceMeshProxy {
    inbound: InboundProxy,
    outbound: OutboundProxy,
    control_plane: ControlPlaneClient,
    identity: IdentityClient,
}

impl ServiceMeshProxy {
    pub async fn run(self) -> Result<(), ProxyError> {
        tokio::try_join!(
            self.inbound.serve(),
            self.outbound.serve(),
            self.control_plane.serve(),
            self.identity.serve(),
        )?;
        Ok(())
    }
}

/// 入站代理
pub struct InboundProxy {
    listener: TcpListener,
    policy: Arc<RwLock<AuthorizationPolicy>>,
}

impl InboundProxy {
    pub async fn serve(self) -> Result<(), ProxyError> {
        loop {
            let (socket, addr) = self.listener.accept().await?;
            let policy = Arc::clone(&self.policy);

            tokio::spawn(async move {
                // 1. 执行授权策略检查
                if !policy.read().await.allow(&addr) {
                    return;
                }

                // 2. 执行 mTLS 握手
                let tls = accept_mtls(socket).await?;

                // 3. 解析 HTTP 请求
                let http = handle_http(tls).await?;

                // 4. 记录指标
                record_metrics(&http);

                Ok::<_, ProxyError>(())
            });
        }
    }
}
```

### 4.2 mTLS 实现

```rust
use rustls::{Certificate, PrivateKey, ServerConfig, ClientConfig};
use rustls_pemfile::{certs, pkcs8_private_keys};

/// 服务网格 mTLS 证书管理
pub struct MeshIdentity {
    cert: Certificate,
    key: PrivateKey,
    trust_anchor: RootCertStore,
}

impl MeshIdentity {
    /// 从控制平面获取证书
    pub async fn from_control_plane(endpoint: &str) -> Result<Self, IdentityError> {
        let mut client = IdentityClient::connect(endpoint).await?;

        let response = client.get_certificate(GetCertificateRequest {
            identity: get_pod_identity(),
        }).await?;

        let cert = Certificate(response.certificate_der);
        let key = PrivateKey(response.key_der);
        let trust_anchor = load_trust_anchor(&response.trust_anchor_pem)?;

        Ok(Self { cert, key, trust_anchor })
    }

    /// 创建 TLS 服务端配置
    pub fn server_config(&self) -> Result<ServerConfig, IdentityError> {
        let mut config = ServerConfig::builder()
            .with_safe_defaults()
            .with_client_cert_verifier(Arc::new(WebPkiClientVerifier::builder(
                Arc::new(self.trust_anchor.clone())
            ).build()?))
            .with_single_cert(vec![self.cert.clone()], self.key.clone_key())?;

        config.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
        Ok(config)
    }

    /// 创建 TLS 客户端配置
    pub fn client_config(&self) -> Result<ClientConfig, IdentityError> {
        let mut config = ClientConfig::builder()
            .with_safe_defaults()
            .with_root_certificates(self.trust_anchor.clone())
            .with_client_auth_cert(vec![self.cert.clone()], self.key.clone_key())?;

        config.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
        Ok(config)
    }
}

/// 自动证书轮换
pub struct RotatingIdentity {
    inner: Arc<RwLock<MeshIdentity>>,
}

impl RotatingIdentity {
    pub async fn start_rotation(&self, interval: Duration) {
        loop {
            tokio::time::sleep(interval).await;

            match MeshIdentity::from_control_plane("control-plane:8080").await {
                Ok(new_identity) => {
                    let mut guard = self.inner.write().await;
                    *guard = new_identity;
                    info!("Certificates rotated successfully");
                }
                Err(e) => {
                    error!("Failed to rotate certificates: {}", e);
                }
            }
        }
    }
}
```

### 4.3 流量管理

```rust
use std::collections::HashMap;
use regex::Regex;

/// 流量路由配置
#[derive(Clone, Debug)]
pub struct Route {
    pub path: PathMatch,
    pub methods: Vec<Method>,
    pub backends: Vec<Backend>,
    pub retries: Option<RetryPolicy>,
    pub timeout: Option<Duration>,
}

#[derive(Clone, Debug)]
pub enum PathMatch {
    Exact(String),
    Prefix(String),
    Regex(Regex),
}

#[derive(Clone, Debug)]
pub struct Backend {
    pub address: SocketAddr,
    pub weight: u32,
    pub metadata: HashMap<String, String>,
}

/// 流量路由器
pub struct TrafficRouter {
    routes: Vec<Route>,
    load_balancer: Arc<dyn LoadBalancer>,
}

impl TrafficRouter {
    /// 匹配请求到后端
    pub fn route(&self, req: &Request) -> Option<Backend> {
        for route in &self.routes {
            if self.matches(route, req) {
                return self.load_balancer.select(&route.backends);
            }
        }
        None
    }

    fn matches(&self, route: &Route, req: &Request) -> bool {
        // 检查路径匹配
        let path_match = match &route.path {
            PathMatch::Exact(p) => req.uri().path() == p,
            PathMatch::Prefix(p) => req.uri().path().starts_with(p),
            PathMatch::Regex(r) => r.is_match(req.uri().path()),
        };

        // 检查方法匹配
        let method_match = route.methods.is_empty()
            || route.methods.contains(req.method());

        path_match && method_match
    }
}

/// 超时和重试中间件
pub struct TimeoutRetryLayer {
    timeout: Duration,
    retry_policy: RetryPolicy,
}

#[derive(Clone, Debug)]
pub struct RetryPolicy {
    pub max_retries: u32,
    pub retryable_statuses: Vec<StatusCode>,
    pub backoff: ExponentialBackoff,
}

impl<S> Layer<S> for TimeoutRetryLayer {
    type Service = TimeoutRetryService<S>;

    fn layer(&self, inner: S) -> Self::Service {
        TimeoutRetryService {
            inner,
            timeout: self.timeout,
            retry_policy: self.retry_policy.clone(),
        }
    }
}
```

### 4.4 可观测性集成

```rust
use opentelemetry::trace::{Tracer, SpanKind};
use prometheus::{Counter, Histogram, Registry};

/// 代理指标收集
pub struct ProxyMetrics {
    request_total: Counter,
    request_duration: Histogram,
    response_size: Histogram,
    active_connections: Gauge,
}

impl ProxyMetrics {
    pub fn new(registry: &Registry) -> Result<Self, MetricsError> {
        let request_total = Counter::new(
            "proxy_requests_total",
            "Total number of HTTP requests"
        )?;

        let request_duration = Histogram::with_opts(
            HistogramOpts::new(
                "proxy_request_duration_seconds",
                "HTTP request latency"
            )
            .buckets(vec![0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0])
        )?;

        let response_size = Histogram::with_opts(
            HistogramOpts::new(
                "proxy_response_size_bytes",
                "HTTP response size"
            )
            .buckets(prometheus::exponential_buckets(100.0, 10.0, 8)?)
        )?;

        let active_connections = Gauge::new(
            "proxy_active_connections",
            "Number of active connections"
        )?;

        registry.register(Box::new(request_total.clone()))?;
        registry.register(Box::new(request_duration.clone()))?;
        registry.register(Box::new(response_size.clone()))?;
        registry.register(Box::new(active_connections.clone()))?;

        Ok(Self {
            request_total,
            request_duration,
            response_size,
            active_connections,
        })
    }

    pub fn record_request(&self, duration: Duration, status: StatusCode) {
        let labels = &[status.as_str()];
        self.request_total.with_label_values(labels).inc();
        self.request_duration.observe(duration.as_secs_f64());
    }
}

/// 分布式追踪中间件
pub struct TracingMiddleware {
    tracer: Arc<dyn Tracer>,
}

impl<S> tower::Service<Request<Body>> for TracingMiddleware<S>
where
    S: tower::Service<Request<Body>>,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = TracingFuture<S::Future>;

    fn call(&mut self, req: Request<Body>) -> Self::Future {
        let span = self.tracer
            .span_builder("proxy_request")
            .with_kind(SpanKind::Server)
            .start(&*self.tracer);

        // 从请求头中提取 trace context
        let parent_cx = extract_context(&req);
        let cx = Context::current_with_span(span);

        // 添加属性
        span.set_attribute(KeyValue::new("http.method", req.method().to_string()));
        span.set_attribute(KeyValue::new("http.url", req.uri().to_string()));

        TracingFuture {
            inner: self.inner.call(req),
            span,
        }
    }
}
```

---

## 5. Serverless

### 5.1 AWS Lambda Rust 运行时

```rust
use lambda_runtime::{service_fn, LambdaEvent, Error};
use serde_json::{json, Value};

/// Lambda 处理器函数
async fn handler(event: LambdaEvent<Value>) -> Result<Value, Error> {
    // 从事件中提取请求信息
    let method = event.payload["httpMethod"].as_str().unwrap_or("GET");
    let path = event.payload["path"].as_str().unwrap_or("/");

    println!("Request: {} {}", method, path);

    // 路由处理
    let response = match (method, path) {
        ("GET", "/") => json!({
            "statusCode": 200,
            "body": "Hello from Rust Lambda!",
        }),
        ("GET", "/health") => json!({
            "statusCode": 200,
            "body": json!({"status": "healthy"}),
        }),
        ("POST", "/users") => {
            // 处理创建用户逻辑
            create_user(&event.payload).await?
        }
        _ => json!({
            "statusCode": 404,
            "body": "Not Found",
        }),
    };

    Ok(response)
}

#[tokio::main]
async fn main() -> Result<(), Error> {
    lambda_runtime::run(service_fn(handler)).await
}
```

### 5.2 冷启动优化

```rust
use std::sync::OnceLock;
use aws_sdk_dynamodb::Client as DynamoClient;
use aws_sdk_s3::Client as S3Client;

/// 全局客户端 - 在初始化阶段创建
static DYNAMODB: OnceLock<DynamoClient> = OnceLock::new();
static S3: OnceLock<S3Client> = OnceLock::new();

/// Lambda 扩展初始化
struct LambdaExtension {
    db_client: DynamoClient,
    s3_client: S3Client,
}

impl LambdaExtension {
    async fn new() -> Self {
        let config = aws_config::load_from_env().await;

        Self {
            db_client: DynamoClient::new(&config),
            s3_client: S3Client::new(&config),
        }
    }

    /// 预连接和预热
    async fn warmup(&self) {
        // 预热数据库连接池
        let _ = self.db_client
            .list_tables()
            .limit(1)
            .send()
            .await;

        // 预加载缓存
        self.preload_cache().await;
    }
}

/// 使用懒加载减少冷启动时间
pub struct AppState {
    db_pool: OnceLock<Pool<Postgres>>,
    redis: OnceLock<RedisClient>,
}

impl AppState {
    pub fn db(&self) -> &Pool<Postgres> {
        self.db_pool.get_or_init(|| {
            Pool::connect_lazy("postgres://...")
                .expect("Failed to create DB pool")
        })
    }

    pub fn redis(&self) -> &RedisClient {
        self.redis.get_or_init(|| {
            RedisClient::open("redis://...")
                .expect("Failed to create Redis client")
        })
    }
}
```

### 5.3 函数即服务框架

```rust
use actix_web::{web, App, HttpResponse, HttpServer};
use std::collections::HashMap;

/// FaaS 运行时
pub struct FaasRuntime {
    functions: HashMap<String, Box<dyn FunctionHandler>>,
    registry: FunctionRegistry,
}

#[async_trait]
pub trait FunctionHandler: Send + Sync {
    async fn invoke(&self, ctx: &FunctionContext, payload: Value) -> Result<Value, FunctionError>;
}

/// 函数上下文
pub struct FunctionContext {
    pub function_name: String,
    pub request_id: String,
    pub memory_limit: usize,
    pub timeout: Duration,
    pub environment: HashMap<String, String>,
}

impl FaasRuntime {
    pub async fn invoke(
        &self,
        name: &str,
        payload: Value,
    ) -> Result<Value, FunctionError> {
        let function = self.functions.get(name)
            .ok_or(FunctionError::NotFound)?;

        let ctx = FunctionContext {
            function_name: name.to_string(),
            request_id: generate_request_id(),
            memory_limit: self.registry.get_memory_limit(name),
            timeout: self.registry.get_timeout(name),
            environment: self.registry.get_environment(name),
        };

        // 设置超时
        match tokio::time::timeout(ctx.timeout, function.invoke(&ctx, payload)).await {
            Ok(result) => result,
            Err(_) => Err(FunctionError::Timeout),
        }
    }
}

/// WebAssembly 函数运行时
pub struct WasmRuntime {
    engine: Engine,
    store: Store<HostState>,
}

impl WasmRuntime {
    pub fn load_function(&mut self, wasm_bytes: &[u8]) -> Result<Instance, WasmError> {
        let module = Module::new(&self.engine, wasm_bytes)?;

        let mut linker = Linker::new(&self.engine);

        // 定义宿主函数
        linker.func_wrap("env", "log", |caller: Caller<HostState>, ptr: i32, len: i32| {
            let memory = caller.get_export("memory").unwrap().into_memory().unwrap();
            let mut buffer = vec![0u8; len as usize];
            memory.read(&caller, ptr as usize, &mut buffer).unwrap();
            println!("WASM: {}", String::from_utf8_lossy(&buffer));
        })?;

        let instance = linker.instantiate(&mut self.store, &module)?;
        Ok(instance)
    }
}
```

---

## 6. 分布式系统

### 6.1 Raft 共识算法实现

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{mpsc, RwLock};
use tokio::time::{interval, Duration, Instant};

/// Raft 节点状态
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum NodeState {
    Follower,
    Candidate,
    Leader,
}

/// Raft 节点
pub struct RaftNode<T: StateMachine> {
    /// 节点 ID
    id: NodeId,
    /// 当前任期
    current_term: u64,
    /// 投票给哪个节点
    voted_for: Option<NodeId>,
    /// 日志条目
    log: Vec<LogEntry>,
    /// 提交索引
    commit_index: u64,
    /// 最后应用索引
    last_applied: u64,

    // Leader 状态
    next_index: HashMap<NodeId, u64>,
    match_index: HashMap<NodeId, u64>,

    /// 节点状态
    state: NodeState,
    /// 状态机
    state_machine: T,

    /// 其他节点地址
    peers: Vec<NodeId>,

    /// 心跳定时器
    election_timer: Instant,
    heartbeat_interval: Duration,
    election_timeout: Duration,
}

/// 日志条目
#[derive(Clone, Debug)]
pub struct LogEntry {
    pub term: u64,
    pub index: u64,
    pub command: Vec<u8>,
}

/// Raft RPC 消息
#[derive(Clone, Debug)]
pub enum Message {
    AppendEntries {
        term: u64,
        leader_id: NodeId,
        prev_log_index: u64,
        prev_log_term: u64,
        entries: Vec<LogEntry>,
        leader_commit: u64,
    },
    AppendEntriesResponse {
        term: u64,
        success: bool,
        match_index: u64,
    },
    RequestVote {
        term: u64,
        candidate_id: NodeId,
        last_log_index: u64,
        last_log_term: u64,
    },
    RequestVoteResponse {
        term: u64,
        vote_granted: bool,
    },
}

impl<T: StateMachine> RaftNode<T> {
    pub fn new(id: NodeId, peers: Vec<NodeId>, state_machine: T) -> Self {
        Self {
            id,
            current_term: 0,
            voted_for: None,
            log: vec![],
            commit_index: 0,
            last_applied: 0,
            next_index: HashMap::new(),
            match_index: HashMap::new(),
            state: NodeState::Follower,
            state_machine,
            peers,
            election_timer: Instant::now(),
            heartbeat_interval: Duration::from_millis(100),
            election_timeout: Duration::from_millis(300 + (id * 50) as u64),
        }
    }

    /// 处理附加日志请求
    pub fn handle_append_entries(&mut self, msg: Message) -> Message {
        let Message::AppendEntries {
            term, leader_id, prev_log_index, prev_log_term, entries, leader_commit
        } = msg else {
            panic!("Expected AppendEntries message");
        };

        // 如果任期更小，拒绝请求
        if term < self.current_term {
            return Message::AppendEntriesResponse {
                term: self.current_term,
                success: false,
                match_index: 0,
            };
        }

        // 更新任期并转换为 Follower
        if term > self.current_term {
            self.current_term = term;
            self.voted_for = None;
            self.state = NodeState::Follower;
        }

        // 重置选举定时器
        self.election_timer = Instant::now();

        // 检查日志一致性
        if prev_log_index > 0 {
            if self.log.len() < prev_log_index as usize {
                return Message::AppendEntriesResponse {
                    term: self.current_term,
                    success: false,
                    match_index: self.log.len() as u64,
                };
            }
            if self.log[prev_log_index as usize - 1].term != prev_log_term {
                return Message::AppendEntriesResponse {
                    term: self.current_term,
                    success: false,
                    match_index: prev_log_index - 1,
                };
            }
        }

        // 附加新条目
        for (i, entry) in entries.iter().enumerate() {
            let idx = prev_log_index as usize + i + 1;
            if self.log.len() >= idx {
                if self.log[idx - 1].term != entry.term {
                    self.log.truncate(idx - 1);
                } else {
                    continue;
                }
            }
            self.log.push(entry.clone());
        }

        // 更新提交索引
        if leader_commit > self.commit_index {
            self.commit_index = leader_commit.min(self.log.len() as u64);
            self.apply_committed().await;
        }

        Message::AppendEntriesResponse {
            term: self.current_term,
            success: true,
            match_index: prev_log_index + entries.len() as u64,
        }
    }

    /// Leader 发送心跳
    pub async fn send_heartbeats(&mut self) {
        if self.state != NodeState::Leader {
            return;
        }

        for peer in &self.peers {
            let next_idx = self.next_index.get(peer).copied().unwrap_or(1);
            let prev_log_index = next_idx - 1;
            let prev_log_term = if prev_log_index > 0 {
                self.log[prev_log_index as usize - 1].term
            } else {
                0
            };

            let entries: Vec<_> = self.log[(next_idx as usize - 1)..].to_vec();

            let msg = Message::AppendEntries {
                term: self.current_term,
                leader_id: self.id,
                prev_log_index,
                prev_log_term,
                entries,
                leader_commit: self.commit_index,
            };

            // 发送 RPC (实际实现需要网络层)
            // send_rpc(peer, msg).await;
        }
    }

    /// 应用已提交的日志到状态机
    async fn apply_committed(&mut self) {
        while self.last_applied < self.commit_index {
            self.last_applied += 1;
            let entry = &self.log[self.last_applied as usize - 1];
            self.state_machine.apply(&entry.command).await;
        }
    }
}
```

### 6.2 服务发现

```rust
use std::collections::HashMap;
use std::net::SocketAddr;
use tokio::sync::RwLock;
use std::sync::Arc;

/// 服务实例
#[derive(Clone, Debug)]
pub struct ServiceInstance {
    pub id: String,
    pub service_name: String,
    pub address: SocketAddr,
    pub metadata: HashMap<String, String>,
    pub health: HealthStatus,
    pub last_heartbeat: Instant,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

/// 服务注册中心
pub struct ServiceRegistry {
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    heartbeat_timeout: Duration,
}

impl ServiceRegistry {
    pub fn new() -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            heartbeat_timeout: Duration::from_secs(30),
        }
    }

    /// 注册服务实例
    pub async fn register(&self, instance: ServiceInstance) {
        let mut services = self.services.write().await;
        services
            .entry(instance.service_name.clone())
            .or_default()
            .push(instance);
    }

    /// 服务发现
    pub async fn discover(&self, service_name: &str) -> Option<Vec<ServiceInstance>> {
        let services = self.services.read().await;
        services.get(service_name).cloned()
    }

    /// 心跳续约
    pub async fn heartbeat(&self, service_name: &str, instance_id: &str) {
        let mut services = self.services.write().await;
        if let Some(instances) = services.get_mut(service_name) {
            if let Some(instance) = instances.iter_mut().find(|i| i.id == instance_id) {
                instance.last_heartbeat = Instant::now();
                instance.health = HealthStatus::Healthy;
            }
        }
    }

    /// 健康检查
    pub async fn health_check(&self) {
        let mut services = self.services.write().await;
        let now = Instant::now();

        for instances in services.values_mut() {
            instances.retain(|instance| {
                if now.duration_since(instance.last_heartbeat) > self.heartbeat_timeout {
                    false // 移除过期实例
                } else {
                    true
                }
            });
        }
    }
}

/// Consul 集成
pub struct ConsulClient {
    client: reqwest::Client,
    consul_addr: String,
}

impl ConsulClient {
    pub async fn register_service(&self, instance: &ServiceInstance) -> Result<(), Error> {
        let payload = json!({
            "ID": instance.id,
            "Name": instance.service_name,
            "Address": instance.address.ip().to_string(),
            "Port": instance.address.port(),
            "Meta": instance.metadata,
            "Check": {
                "HTTP": format!("http://{}/health", instance.address),
                "Interval": "10s",
                "Timeout": "5s"
            }
        });

        self.client
            .put(format!("{}/v1/agent/service/register", self.consul_addr))
            .json(&payload)
            .send()
            .await?;

        Ok(())
    }

    pub async fn query_service(&self, name: &str) -> Result<Vec<ServiceInstance>, Error> {
        let resp: Value = self.client
            .get(format!("{}/v1/health/service/{}", self.consul_addr, name))
            .send()
            .await?
            .json()
            .await?;

        // 解析响应
        let instances: Vec<ServiceInstance> = resp.as_array()
            .unwrap_or(&vec![])
            .iter()
            .filter_map(|entry| self.parse_service_entry(entry))
            .collect();

        Ok(instances)
    }
}
```

### 6.3 负载均衡

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

/// 负载均衡器 trait
pub trait LoadBalancer: Send + Sync {
    fn select(&self, backends: &[Backend]) -> Option<Backend>;
}

/// 轮询负载均衡
pub struct RoundRobin {
    counter: AtomicUsize,
}

impl RoundRobin {
    pub fn new() -> Self {
        Self {
            counter: AtomicUsize::new(0),
        }
    }
}

impl LoadBalancer for RoundRobin {
    fn select(&self, backends: &[Backend]) -> Option<Backend> {
        if backends.is_empty() {
            return None;
        }
        let idx = self.counter.fetch_add(1, Ordering::Relaxed) % backends.len();
        Some(backends[idx].clone())
    }
}

/// 加权轮询
pub struct WeightedRoundRobin {
    weights: Vec<u32>,
    current: AtomicUsize,
}

impl LoadBalancer for WeightedRoundRobin {
    fn select(&self, backends: &[Backend]) -> Option<Backend> {
        // 实现加权选择逻辑
        // ...
        backends.first().cloned()
    }
}

/// 最少连接
pub struct LeastConnections {
    connections: Arc<RwLock<HashMap<SocketAddr, usize>>>,
}

impl LoadBalancer for LeastConnections {
    fn select(&self, backends: &[Backend]) -> Option<Backend> {
        let connections = self.connections.read().unwrap();

        backends
            .iter()
            .min_by_key(|b| connections.get(&b.address).unwrap_or(&0))
            .cloned()
    }
}

/// 一致性哈希
pub struct ConsistentHash {
    ring: BTreeMap<u64, Backend>,
    replicas: usize,
}

impl ConsistentHash {
    pub fn new(replicas: usize) -> Self {
        Self {
            ring: BTreeMap::new(),
            replicas,
        }
    }

    pub fn add_node(&mut self, backend: Backend) {
        for i in 0..self.replicas {
            let key = self.hash(&format!("{}:{}", backend.address, i));
            self.ring.insert(key, backend.clone());
        }
    }

    pub fn get_node(&self, key: &str) -> Option<Backend> {
        let hash = self.hash(key);
        self.ring
            .range(hash..)
            .next()
            .or_else(|| self.ring.first_key_value())
            .map(|(_, v)| v.clone())
    }

    fn hash(&self, key: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }
}
```

### 6.4 断路器模式

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use tokio::time::{Duration, Instant};

/// 断路器状态
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum CircuitState {
    Closed,      // 正常
    Open,        // 断开
    HalfOpen,    // 半开
}

/// 断路器配置
pub struct CircuitBreakerConfig {
    pub failure_threshold: u32,
    pub success_threshold: u32,
    pub timeout: Duration,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            success_threshold: 3,
            timeout: Duration::from_secs(30),
        }
    }
}

/// 断路器
pub struct CircuitBreaker {
    state: AtomicU64, // 用于存储状态和时间戳
    failures: AtomicU64,
    successes: AtomicU64,
    last_failure_time: RwLock<Option<Instant>>,
    config: CircuitBreakerConfig,
}

impl CircuitBreaker {
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            state: AtomicU64::new(CircuitState::Closed as u64),
            failures: AtomicU64::new(0),
            successes: AtomicU64::new(0),
            last_failure_time: RwLock::new(None),
            config,
        }
    }

    /// 获取当前状态
    pub fn state(&self) -> CircuitState {
        match self.state.load(Ordering::Relaxed) {
            0 => CircuitState::Closed,
            1 => CircuitState::Open,
            2 => CircuitState::HalfOpen,
            _ => CircuitState::Closed,
        }
    }

    /// 检查是否允许请求
    pub async fn allow_request(&self) -> bool {
        let state = self.state();

        match state {
            CircuitState::Closed => true,
            CircuitState::Open => {
                // 检查超时时间是否已过
                let last_failure = *self.last_failure_time.read().await;
                if let Some(time) = last_failure {
                    if time.elapsed() > self.config.timeout {
                        // 切换到半开状态
                        self.transition_to(CircuitState::HalfOpen);
                        self.successes.store(0, Ordering::Relaxed);
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            CircuitState::HalfOpen => true,
        }
    }

    /// 记录成功
    pub async fn record_success(&self) {
        match self.state() {
            CircuitState::HalfOpen => {
                let successes = self.successes.fetch_add(1, Ordering::Relaxed) + 1;
                if successes >= self.config.success_threshold as u64 {
                    self.transition_to(CircuitState::Closed);
                    self.failures.store(0, Ordering::Relaxed);
                    self.successes.store(0, Ordering::Relaxed);
                }
            }
            CircuitState::Closed => {
                self.failures.store(0, Ordering::Relaxed);
            }
            _ => {}
        }
    }

    /// 记录失败
    pub async fn record_failure(&self) {
        *self.last_failure_time.write().await = Some(Instant::now());

        match self.state() {
            CircuitState::Closed => {
                let failures = self.failures.fetch_add(1, Ordering::Relaxed) + 1;
                if failures >= self.config.failure_threshold as u64 {
                    self.transition_to(CircuitState::Open);
                }
            }
            CircuitState::HalfOpen => {
                self.transition_to(CircuitState::Open);
            }
            _ => {}
        }
    }

    fn transition_to(&self, new_state: CircuitState) {
        self.state.store(new_state as u64, Ordering::Relaxed);
    }
}

/// 断路器包装函数
pub async fn with_circuit_breaker<F, Fut, T>(
    breaker: &CircuitBreaker,
    f: F,
) -> Result<T, CircuitError>
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = Result<T, Error>>,
{
    if !breaker.allow_request().await {
        return Err(CircuitError::Open);
    }

    match f().await {
        Ok(result) => {
            breaker.record_success().await;
            Ok(result)
        }
        Err(e) => {
            breaker.record_failure().await;
            Err(CircuitError::Underlying(e))
        }
    }
}
```

---

## 7. 可观测性

### 7.1 OpenTelemetry 集成

```rust
use opentelemetry::trace::{Tracer, SpanKind, TraceContextExt};
use opentelemetry::global;
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::trace::{TracerProvider, Config};
use opentelemetry_sdk::Resource;
use opentelemetry_semantic_conventions::resource::SERVICE_NAME;

/// 初始化 OpenTelemetry
pub fn init_tracer(service_name: &str, endpoint: &str) -> Result<TracerProvider, Error> {
    let resource = Resource::new(vec![
        KeyValue::new(SERVICE_NAME, service_name.to_string()),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
    ]);

    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(endpoint);

    let provider = TracerProvider::builder()
        .with_config(Config::default().with_resource(resource))
        .with_batch_exporter(exporter, tokio::runtime::Handle::current())
        .build();

    global::set_tracer_provider(provider.clone());

    Ok(provider)
}

/// HTTP 追踪中间件
pub async fn tracing_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Response {
    let tracer = global::tracer("http-server");

    // 从请求头提取 trace context
    let parent_context = extract_context(&req);

    let mut span = tracer
        .span_builder(format!("{} {}", req.method(), req.uri().path()))
        .with_kind(SpanKind::Server)
        .start_with_context(&tracer, &parent_context);

    // 添加属性
    span.set_attribute(KeyValue::new("http.method", req.method().to_string()));
    span.set_attribute(KeyValue::new("http.url", req.uri().to_string()));
    span.set_attribute(KeyValue::new("http.host",
        req.headers().get("host")
            .and_then(|h| h.to_str().ok())
            .unwrap_or("unknown")
            .to_string()
    ));

    let cx = Context::current_with_span(span);

    // 执行请求
    let response = next.run(req).await;

    // 记录响应信息
    cx.span().set_attribute(KeyValue::new("http.status_code", response.status().as_u16() as i64));

    if response.status().is_server_error() {
        cx.span().set_status(Status::error(format!("HTTP {}", response.status())));
    }

    response
}

/// 数据库追踪
pub async fn traced_query<F, Fut, T>(
    operation: &str,
    table: &str,
    f: F,
) -> Result<T, Error>
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = Result<T, Error>>,
{
    let tracer = global::tracer("database");
    let _span = tracer
        .span_builder(format!("{} {}", operation, table))
        .with_attributes(vec![
            KeyValue::new("db.system", "postgresql"),
            KeyValue::new("db.operation", operation.to_string()),
            KeyValue::new("db.sql.table", table.to_string()),
        ])
        .start(&tracer);

    f().await
}
```

### 7.2 Prometheus 指标

```rust
use prometheus::{Counter, Histogram, Gauge, Registry, Encoder, TextEncoder};
use prometheus::{register_counter, register_histogram, register_gauge};
use std::time::Instant;

/// 应用指标
pub struct Metrics {
    pub http_requests_total: Counter,
    pub http_request_duration: Histogram,
    pub active_connections: Gauge,
    pub database_connections: Gauge,
    pub cache_hit_ratio: Gauge,
}

impl Metrics {
    pub fn new() -> Result<Self, prometheus::Error> {
        let http_requests_total = register_counter!(
            "http_requests_total",
            "Total number of HTTP requests",
            &["method", "path", "status"]
        )?;

        let http_request_duration = register_histogram!(
            "http_request_duration_seconds",
            "HTTP request latency",
            &["method", "path"],
            vec![0.001, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0]
        )?;

        let active_connections = register_gauge!(
            "active_connections",
            "Number of active connections"
        )?;

        let database_connections = register_gauge!(
            "database_connections",
            "Number of database connections",
            &["state"]
        )?;

        let cache_hit_ratio = register_gauge!(
            "cache_hit_ratio",
            "Cache hit ratio"
        )?;

        Ok(Self {
            http_requests_total,
            http_request_duration,
            active_connections,
            database_connections,
            cache_hit_ratio,
        })
    }

    /// 记录 HTTP 请求
    pub fn record_http_request(&self, method: &str, path: &str, status: u16, duration: Duration) {
        let labels = &[method, path, &status.to_string()];
        self.http_requests_total.with_label_values(labels).inc();

        let labels = &[method, path];
        self.http_request_duration
            .with_label_values(labels)
            .observe(duration.as_secs_f64());
    }
}

/// 指标中间件
pub struct MetricsMiddleware {
    metrics: Arc<Metrics>,
}

impl<B> tower::Service<Request<B>> for MetricsMiddleware {
    type Response = Response;
    type Error = Error;
    type Future = MetricsFuture;

    fn call(&mut self, req: Request<B>) -> Self::Future {
        let start = Instant::now();
        let method = req.method().to_string();
        let path = req.uri().path().to_string();
        let metrics = Arc::clone(&self.metrics);

        MetricsFuture {
            inner: self.inner.call(req),
            start,
            method,
            path,
            metrics,
        }
    }
}

impl std::future::Future for MetricsFuture {
    type Output = Result<Response, Error>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.inner.poll(cx) {
            Poll::Ready(Ok(response)) => {
                let duration = self.start.elapsed();
                self.metrics.record_http_request(
                    &self.method,
                    &self.path,
                    response.status().as_u16(),
                    duration,
                );
                Poll::Ready(Ok(response))
            }
            other => other,
        }
    }
}

/// 暴露指标端点
async fn metrics_endpoint() -> impl IntoResponse {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buffer = vec![];
    encoder.encode(&metric_families, &mut buffer).unwrap();

    String::from_utf8(buffer).unwrap()
}
```

### 7.3 结构化日志

```rust
use tracing::{info, warn, error, debug, span, Level, Instrument};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
use tracing_subscriber::fmt::format::FmtSpan;

/// 初始化结构化日志
pub fn init_logging() {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with(
            tracing_subscriber::fmt::layer()
                .json()
                .with_span_events(FmtSpan::NEW | FmtSpan::CLOSE)
                .with_timer(tracing_subscriber::fmt::time::UtcTime::rfc_3339()),
        )
        .with(
            // 发送到 OpenTelemetry
            tracing_opentelemetry::layer().with_tracer(global::tracer("app")),
        )
        .init();
}

/// 带上下文的日志记录
#[derive(Debug)]
pub struct RequestContext {
    pub request_id: String,
    pub user_id: Option<String>,
    pub trace_id: String,
}

pub async fn handle_request(ctx: RequestContext, req: Request) -> Response {
    // 创建 span，自动包含上下文信息
    let span = span!(
        Level::INFO,
        "handle_request",
        request_id = %ctx.request_id,
        user_id = ?ctx.user_id,
        trace_id = %ctx.trace_id,
        path = %req.uri().path(),
    );

    async move {
        info!("Processing request");

        match process_request(&req).await {
            Ok(response) => {
                info!(
                    status = response.status().as_u16(),
                    "Request processed successfully"
                );
                response
            }
            Err(e) => {
                error!(
                    error = %e,
                    "Request processing failed"
                );
                create_error_response(e)
            }
        }
    }
    .instrument(span)
    .await
}

/// 结构化日志宏
#[macro_export]
macro_rules! app_log {
    (info, $ctx:expr, $($field:tt)*) => {
        tracing::info!(
            request_id = %$ctx.request_id,
            trace_id = %$ctx.trace_id,
            $($field)*
        )
    };
    (error, $ctx:expr, $($field:tt)*) => {
        tracing::error!(
            request_id = %$ctx.request_id,
            trace_id = %$ctx.trace_id,
            $($field)*
        )
    };
}
```

### 7.4 健康检查与探针

```rust
use std::collections::HashMap;

/// 健康检查类型
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

/// 健康检查组件
#[async_trait]
pub trait HealthCheck: Send + Sync {
    fn name(&self) -> &str;
    async fn check(&self) -> HealthStatus;
}

/// 健康检查注册表
pub struct HealthRegistry {
    checks: Vec<Box<dyn HealthCheck>>,
}

impl HealthRegistry {
    pub fn new() -> Self {
        Self { checks: vec![] }
    }

    pub fn register(&mut self, check: Box<dyn HealthCheck>) {
        self.checks.push(check);
    }

    pub async fn check_all(&self) -> OverallHealth {
        let mut components = HashMap::new();
        let mut overall = HealthStatus::Healthy;

        for check in &self.checks {
            let status = check.check().await;
            components.insert(check.name().to_string(), status);

            if status == HealthStatus::Unhealthy {
                overall = HealthStatus::Unhealthy;
            } else if status == HealthStatus::Degraded && overall == HealthStatus::Healthy {
                overall = HealthStatus::Degraded;
            }
        }

        OverallHealth {
            status: overall,
            components,
        }
    }
}

/// 数据库健康检查
pub struct DatabaseHealthCheck {
    pool: Pool<Postgres>,
}

#[async_trait]
impl HealthCheck for DatabaseHealthCheck {
    fn name(&self) -> &str {
        "database"
    }

    async fn check(&self) -> HealthStatus {
        match sqlx::query("SELECT 1").fetch_one(&self.pool).await {
            Ok(_) => HealthStatus::Healthy,
            Err(_) => HealthStatus::Unhealthy,
        }
    }
}

/// 外部服务健康检查
pub struct ExternalServiceCheck {
    name: String,
    client: reqwest::Client,
    url: String,
}

#[async_trait]
impl HealthCheck for ExternalServiceCheck {
    fn name(&self) -> &str {
        &self.name
    }

    async fn check(&self) -> HealthStatus {
        match self.client.get(&self.url).timeout(Duration::from_secs(5)).send().await {
            Ok(resp) if resp.status().is_success() => HealthStatus::Healthy,
            Ok(_) => HealthStatus::Degraded,
            Err(_) => HealthStatus::Unhealthy,
        }
    }
}

/// Kubernetes 探针端点
async fn liveness_probe(State(registry): State<Arc<HealthRegistry>>) -> impl IntoResponse {
    // 存活探针：只要进程活着就返回 200
    StatusCode::OK
}

async fn readiness_probe(State(registry): State<Arc<HealthRegistry>>) -> impl IntoResponse {
    // 就绪探针：检查是否可以接收流量
    let health = registry.check_all().await;

    match health.status {
        HealthStatus::Healthy => (StatusCode::OK, Json(health)),
        _ => (StatusCode::SERVICE_UNAVAILABLE, Json(health)),
    }
}

async fn startup_probe(State(registry): State<Arc<HealthRegistry>>) -> impl IntoResponse {
    // 启动探针：检查应用是否启动完成
    let health = registry.check_all().await;

    match health.status {
        HealthStatus::Healthy | HealthStatus::Degraded => (StatusCode::OK, Json(health)),
        _ => (StatusCode::SERVICE_UNAVAILABLE, Json(health)),
    }
}
```

---

## 8. 完整示例：微服务部署

### 8.1 微服务代码

```rust
// src/main.rs
use axum::{
    routing::{get, post},
    Router, Json, Extension,
    response::IntoResponse,
    http::StatusCode,
};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::sync::RwLock;
use tower_http::trace::TraceLayer;

mod handlers;
mod models;
mod db;
mod metrics;

use crate::models::*;
use crate::handlers::*;
use crate::metrics::Metrics;

#[derive(Clone)]
pub struct AppState {
    db: db::Database,
    metrics: Arc<Metrics>,
    config: Config,
}

#[derive(Clone)]
pub struct Config {
    pub database_url: String,
    pub port: u16,
    pub log_level: String,
}

impl Config {
    fn from_env() -> Self {
        Self {
            database_url: std::env::var("DATABASE_URL")
                .expect("DATABASE_URL must be set"),
            port: std::env::var("PORT")
                .ok()
                .and_then(|p| p.parse().ok())
                .unwrap_or(8080),
            log_level: std::env::var("LOG_LEVEL").unwrap_or_else(|_| "info".to_string()),
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .json()
        .init();

    let config = Config::from_env();

    // 初始化数据库
    let db = db::Database::connect(&config.database_url).await?;

    // 初始化指标
    let metrics = Arc::new(Metrics::new()?);

    let state = AppState {
        db,
        metrics,
        config: config.clone(),
    };

    // 构建路由
    let app = Router::new()
        .route("/health", get(health_handler))
        .route("/ready", get(ready_handler))
        .route("/users", post(create_user))
        .route("/users/:id", get(get_user))
        .route("/metrics", get(metrics_handler))
        .layer(TraceLayer::new_for_http())
        .layer(Extension(state));

    let addr = SocketAddr::from(([0, 0, 0, 0], config.port));

    tracing::info!("Starting server on {}", addr);

    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await?;

    Ok(())
}
```

### 8.2 Dockerfile 多阶段构建

```dockerfile
# 构建阶段
FROM rust:1.75-slim-bookworm AS builder

WORKDIR /app

# 安装依赖
RUN apt-get update && apt-get install -y \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 缓存依赖
COPY Cargo.toml Cargo.lock ./
RUN mkdir src && echo "fn main() {}" > src/main.rs
RUN cargo build --release && rm -rf src

# 复制源码并构建
COPY . .
RUN touch src/main.rs
RUN cargo build --release

# 运行阶段 - 使用 distroless 镜像
FROM gcr.io/distroless/cc-debian12

WORKDIR /app

# 复制二进制文件
COPY --from=builder /app/target/release/my-service /app/

# 非 root 用户运行
USER 65532:65532

EXPOSE 8080

ENTRYPOINT ["/app/my-service"]
```

### 8.3 Kubernetes 部署配置

```yaml
# k8s/namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: rust-microservices
  labels:
    istio-injection: enabled

---
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: user-service
  namespace: rust-microservices
  labels:
    app: user-service
spec:
  replicas: 3
  selector:
    matchLabels:
      app: user-service
  template:
    metadata:
      labels:
        app: user-service
      annotations:
        prometheus.io/scrape: "true"
        prometheus.io/port: "8080"
        prometheus.io/path: "/metrics"
    spec:
      serviceAccountName: user-service
      securityContext:
        runAsNonRoot: true
        runAsUser: 65532
        fsGroup: 65532
      containers:
      - name: user-service
        image: myregistry/user-service:v1.0.0
        imagePullPolicy: Always
        ports:
        - name: http
          containerPort: 8080
          protocol: TCP
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: user-service-db
              key: url
        - name: RUST_LOG
          value: "info"
        - name: PORT
          value: "8080"
        resources:
          requests:
            memory: "64Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: http
          initialDelaySeconds: 10
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: http
          initialDelaySeconds: 5
          periodSeconds: 5
        securityContext:
          allowPrivilegeEscalation: false
          readOnlyRootFilesystem: true
          capabilities:
            drop:
            - ALL
        volumeMounts:
        - name: tmp
          mountPath: /tmp
      volumes:
      - name: tmp
        emptyDir: {}

---
# k8s/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: user-service
  namespace: rust-microservices
  labels:
    app: user-service
spec:
  type: ClusterIP
  ports:
  - port: 80
    targetPort: http
    protocol: TCP
    name: http
  selector:
    app: user-service

---
# k8s/hpa.yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: user-service
  namespace: rust-microservices
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: user-service
  minReplicas: 3
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
  behavior:
    scaleDown:
      stabilizationWindowSeconds: 300
      policies:
      - type: Percent
        value: 10
        periodSeconds: 60
    scaleUp:
      stabilizationWindowSeconds: 0
      policies:
      - type: Percent
        value: 100
        periodSeconds: 15

---
# k8s/pdb.yaml
apiVersion: policy/v1
kind: PodDisruptionBudget
metadata:
  name: user-service
  namespace: rust-microservices
spec:
  minAvailable: 2
  selector:
    matchLabels:
      app: user-service
```

### 8.4 Istio 服务网格配置

```yaml
# istio/gateway.yaml
apiVersion: networking.istio.io/v1beta1
kind: Gateway
metadata:
  name: microservices-gateway
  namespace: rust-microservices
spec:
  selector:
    istio: ingressgateway
  servers:
  - port:
      number: 80
      name: http
      protocol: HTTP
    hosts:
    - "api.example.com"
    tls:
      httpsRedirect: true
  - port:
      number: 443
      name: https
      protocol: HTTPS
    tls:
      mode: SIMPLE
      credentialName: api-tls-secret
    hosts:
    - "api.example.com"

---
# istio/virtualservice.yaml
apiVersion: networking.istio.io/v1beta1
kind: VirtualService
metadata:
  name: user-service
  namespace: rust-microservices
spec:
  hosts:
  - "api.example.com"
  gateways:
  - microservices-gateway
  http:
  - match:
    - uri:
        prefix: /api/users
    route:
    - destination:
        host: user-service
        port:
          number: 80
    retries:
      attempts: 3
      perTryTimeout: 2s
      retryOn: gateway-error,connect-failure,refused-stream
    timeout: 10s
    corsPolicy:
      allowOrigins:
      - exact: "https://app.example.com"
      allowMethods:
      - GET
      - POST
      - PUT
      - DELETE
      allowHeaders:
      - authorization
      - content-type
      allowCredentials: true

---
# istio/destinationrule.yaml
apiVersion: networking.istio.io/v1beta1
kind: DestinationRule
metadata:
  name: user-service
  namespace: rust-microservices
spec:
  host: user-service
  trafficPolicy:
    connectionPool:
      tcp:
        maxConnections: 100
      http:
        http1MaxPendingRequests: 50
        maxRequestsPerConnection: 10
    loadBalancer:
      simple: LEAST_CONN
    outlierDetection:
      consecutive5xxErrors: 5
      interval: 30s
      baseEjectionTime: 30s
  subsets:
  - name: stable
    labels:
      version: stable
  - name: canary
    labels:
      version: canary

---
# istio/peerauthentication.yaml
apiVersion: security.istio.io/v1beta1
kind: PeerAuthentication
metadata:
  name: default
  namespace: rust-microservices
spec:
  mtls:
    mode: STRICT

---
# istio/authorizationpolicy.yaml
apiVersion: security.istio.io/v1beta1
kind: AuthorizationPolicy
metadata:
  name: user-service-policy
  namespace: rust-microservices
spec:
  selector:
    matchLabels:
      app: user-service
  action: ALLOW
  rules:
  - from:
    - source:
        principals: ["cluster.local/ns/rust-microservices/sa/api-gateway"]
    to:
    - operation:
        methods: ["GET", "POST"]
        paths: ["/api/users/*"]
```

### 8.5 Prometheus 监控告警

```yaml
# monitoring/servicemonitor.yaml
apiVersion: monitoring.coreos.com/v1
kind: ServiceMonitor
metadata:
  name: user-service
  namespace: monitoring
  labels:
    release: prometheus
spec:
  namespaceSelector:
    matchNames:
    - rust-microservices
  selector:
    matchLabels:
      app: user-service
  endpoints:
  - port: http
    path: /metrics
    interval: 15s
    scrapeTimeout: 10s

---
# monitoring/prometheusrules.yaml
apiVersion: monitoring.coreos.com/v1
kind: PrometheusRule
metadata:
  name: user-service-alerts
  namespace: monitoring
  labels:
    release: prometheus
spec:
  groups:
  - name: user-service
    rules:
    - alert: HighErrorRate
      expr: |
        (
          sum(rate(http_requests_total{status=~"5.."}[5m]))
          /
          sum(rate(http_requests_total[5m]))
        ) > 0.01
      for: 5m
      labels:
        severity: critical
      annotations:
        summary: "High error rate detected"
        description: "Error rate is above 1% for {{ $labels.service }}"

    - alert: HighLatency
      expr: |
        histogram_quantile(0.95,
          sum(rate(http_request_duration_seconds_bucket[5m])) by (le, service)
        ) > 0.5
      for: 5m
      labels:
        severity: warning
      annotations:
        summary: "High latency detected"
        description: "P95 latency is above 500ms for {{ $labels.service }}"

    - alert: PodCrashLooping
      expr: |
        rate(kube_pod_container_status_restarts_total[15m]) > 0
      for: 5m
      labels:
        severity: critical
      annotations:
        summary: "Pod is crash looping"
        description: "Pod {{ $labels.pod }} is restarting frequently"
```

---

## 9. 性能优化

### 9.1 编译优化

```toml
# Cargo.toml 优化配置
[package]
name = "cloud-native-app"
version = "1.0.0"
edition = "2021"

[profile.release]
opt-level = 3          # 最高优化级别
lto = true             # 链接时优化
codegen-units = 1      # 单代码生成单元，提高优化效果
panic = "abort"        # 使用 abort 替代 unwind，减小二进制
strip = true           # 去除符号表

# 针对特定 CPU 架构优化
[profile.release.build-override]
opt-level = 3

# 对于容器环境，静态链接 MUSL
[target.x86_64-unknown-linux-musl]
linker = "rust-lld"
```

### 9.2 镜像大小优化

```dockerfile
# 多阶段构建优化版
FROM rust:1.75-slim-bookworm AS builder

WORKDIR /app

# 只安装必要的构建依赖
RUN apt-get update && apt-get install -y --no-install-recommends \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# 使用 cargo-chef 缓存依赖
FROM lukemathwalker/cargo-chef:latest-rust-1.75 AS chef
WORKDIR /app

FROM chef AS planner
COPY . .
RUN cargo chef prepare --recipe-path recipe.json

FROM builder AS builder
COPY --from=planner /app/recipe.json recipe.json
RUN cargo chef cook --release --recipe-path recipe.json

COPY . .
RUN cargo build --release

# 运行时镜像 - 最小化
FROM scratch
COPY --from=builder /app/target/release/my-app /app/
COPY --from=builder /etc/ssl/certs/ca-certificates.crt /etc/ssl/certs/
EXPOSE 8080
ENTRYPOINT ["/app/my-app"]
```

### 9.3 启动时间优化

```rust
// 延迟初始化减少启动时间
use std::sync::OnceLock;

static DB_POOL: OnceLock<PgPool> = OnceLock::new();

pub fn get_db_pool() -> &'static PgPool {
    DB_POOL.get_or_init(|| {
        tokio::runtime::Handle::current().block_on(async {
            PgPool::connect(&std::env::var("DATABASE_URL").unwrap())
                .await
                .expect("Failed to connect to database")
        })
    })
}

// 预编译模板
use askama::Template;

#[derive(Template)]
#[template(path = "index.html")]
struct IndexTemplate {
    title: String,
}

// 预加载配置
pub struct Config {
    pub database_url: String,
    pub cache_size: usize,
}

impl Config {
    pub fn load() -> Self {
        // 使用 lazy_static 或 OnceCell 缓存配置
        Self {
            database_url: std::env::var("DATABASE_URL").expect("DATABASE_URL required"),
            cache_size: std::env::var("CACHE_SIZE")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(1000),
        }
    }
}
```

---

## 10. CI/CD

### 10.1 GitHub Actions 工作流

```yaml
# .github/workflows/ci-cd.yaml
name: CI/CD

on:
  push:
    branches: [main]
    tags: ['v*']
  pull_request:
    branches: [main]

env:
  CARGO_TERM_COLOR: always
  REGISTRY: ghcr.io
  IMAGE_NAME: ${{ github.repository }}

jobs:
  test:
    name: Test
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v4

    - name: Install Rust
      uses: dtolnay/rust-toolchain@stable
      with:
        components: rustfmt, clippy

    - name: Cache cargo dependencies
      uses: actions/cache@v3
      with:
        path: |
          ~/.cargo/registry
          ~/.cargo/git
          target
        key: ${{ runner.os }}-cargo-${{ hashFiles('**/Cargo.lock') }}

    - name: Check formatting
      run: cargo fmt -- --check

    - name: Run clippy
      run: cargo clippy --all-targets --all-features -- -D warnings

    - name: Run tests
      run: cargo test --all-features --verbose

    - name: Generate coverage report
      run: |
        cargo install cargo-tarpaulin
        cargo tarpaulin --out Xml

    - name: Upload coverage
      uses: codecov/codecov-action@v3
      with:
        file: ./cobertura.xml

  security-audit:
    name: Security Audit
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v4

    - name: Run cargo-audit
      uses: rustsec/audit-check@v1
      with:
        token: ${{ secrets.GITHUB_TOKEN }}

    - name: Run cargo-deny
      uses: EmbarkStudios/cargo-deny-action@v1

  build:
    name: Build
    needs: [test, security-audit]
    runs-on: ubuntu-latest
    permissions:
      contents: read
      packages: write
    steps:
    - uses: actions/checkout@v4

    - name: Set up Docker Buildx
      uses: docker/setup-buildx-action@v3

    - name: Log in to Container Registry
      uses: docker/login-action@v3
      with:
        registry: ${{ env.REGISTRY }}
        username: ${{ github.actor }}
        password: ${{ secrets.GITHUB_TOKEN }}

    - name: Extract metadata
      id: meta
      uses: docker/metadata-action@v5
      with:
        images: ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}
        tags: |
          type=ref,event=branch
          type=ref,event=pr
          type=semver,pattern={{version}}
          type=semver,pattern={{major}}.{{minor}}

    - name: Build and push
      uses: docker/build-push-action@v5
      with:
        context: .
        push: true
        tags: ${{ steps.meta.outputs.tags }}
        labels: ${{ steps.meta.outputs.labels }}
        cache-from: type=gha
        cache-to: type=gha,mode=max
        platforms: linux/amd64,linux/arm64

  deploy-staging:
    name: Deploy to Staging
    needs: build
    if: github.ref == 'refs/heads/main'
    runs-on: ubuntu-latest
    environment: staging
    steps:
    - uses: actions/checkout@v4

    - name: Configure kubectl
      uses: azure/setup-kubectl@v3

    - name: Deploy to staging
      run: |
        kubectl set image deployment/user-service \
          user-service=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:main \
          -n staging
        kubectl rollout status deployment/user-service -n staging

  deploy-production:
    name: Deploy to Production
    needs: build
    if: startsWith(github.ref, 'refs/tags/v')
    runs-on: ubuntu-latest
    environment: production
    steps:
    - uses: actions/checkout@v4

    - name: Deploy to production
      run: |
        kubectl set image deployment/user-service \
          user-service=${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:${{ github.ref_name }} \
          -n production
        kubectl rollout status deployment/user-service -n production
```

### 10.2 容器镜像构建脚本

```bash
#!/bin/bash
# scripts/build.sh

set -e

IMAGE_NAME="myapp"
VERSION=$(git describe --tags --always --dirty)
REGISTRY="ghcr.io/myorg"

echo "Building ${IMAGE_NAME}:${VERSION}"

# 构建多平台镜像
docker buildx build \
  --platform linux/amd64,linux/arm64 \
  --tag "${REGISTRY}/${IMAGE_NAME}:${VERSION}" \
  --tag "${REGISTRY}/${IMAGE_NAME}:latest" \
  --cache-from type=local,src=/tmp/.buildx-cache \
  --cache-to type=local,dest=/tmp/.buildx-cache,mode=max \
  --push \
  .

# 扫描镜像漏洞
echo "Scanning image for vulnerabilities..."
trivy image "${REGISTRY}/${IMAGE_NAME}:${VERSION}"

echo "Build complete: ${REGISTRY}/${IMAGE_NAME}:${VERSION}"
```

### 10.3 安全扫描配置

```yaml
# .cargo/audit.toml
[advisories]
ignore = [
    # 忽略特定 advisory（如果有合理的理由）
]

[output]
deny = []

# cargo-deny 配置
# deny.toml
[graph]
targets = [
    { triple = "x86_64-unknown-linux-gnu" },
    { triple = "x86_64-unknown-linux-musl" },
]

[advisories]
version = 2
db-urls = ["https://github.com/rustsec/advisory-db"]
ignore = []

[licenses]
version = 2
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
]

deny = [
    "GPL-2.0",
    "GPL-3.0",
]

[bans]
multiple-versions = "warn"
wildcards = "warn"

[sources]
unknown-registry = "deny"
unknown-git = "deny"
allow-registry = ["https://github.com/rust-lang/crates.io-index"]
```

---

## 附录：资源与参考

### 推荐 crate

| 用途 | Crate | 说明 |
|------|-------|------|
| HTTP 服务 | axum, actix-web | Web 框架 |
| 异步运行时 | tokio | 异步 IO |
| Kubernetes | kube, k8s-openapi | K8s 客户端 |
| 可观测性 | tracing, opentelemetry | 日志追踪 |
| 指标 | prometheus | 指标收集 |
| 序列化 | serde | JSON/序列化 |
| 配置 | config, envy | 配置管理 |
| 数据库 | sqlx, sea-orm | ORM/查询 |
| 缓存 | redis, deadpool-redis | Redis 客户端 |
| 消息队列 | lapin, rdkafka | MQ 客户端 |
| 安全 | rustls, ring | TLS/加密 |
| 测试 | mockall, test-context | 测试工具 |

### 学习资源

- [Rust Cloud Native](https://rust-cloud-native.github.io/)
- [Kube-rs 文档](https://docs.rs/kube/)
- [Linkerd2-proxy](https://github.com/linkerd/linkerd2-proxy)
- [youki 容器运行时](https://github.com/containers/youki)
- [Rust AWS Lambda](https://github.com/awslabs/aws-lambda-rust-runtime)

---

*文档版本：1.0.0*
*最后更新：2026-03-04*
