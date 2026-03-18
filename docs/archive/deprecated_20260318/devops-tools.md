# Rust DevOps 工具

DevOps 工具需要高可靠性、低资源消耗和快速启动，Rust 的这些特性使其成为构建现代 DevOps 工具链的理想选择。
本文档深入介绍 Rust 在 DevOps 领域的应用。

## 目录

- [Rust DevOps 工具](#rust-devops-工具)
  - [目录](#目录)
  - [DevOps 工具概述](#devops-工具概述)
    - [Rust 在 DevOps 中的优势](#rust-在-devops-中的优势)
    - [主要工具生态](#主要工具生态)
  - [容器技术](#容器技术)
    - [OCI 运行时实现](#oci-运行时实现)
    - [容器镜像构建](#容器镜像构建)
  - [CI/CD 系统](#cicd-系统)
    - [流水线引擎](#流水线引擎)
  - [监控与可观测性](#监控与可观测性)
    - [指标收集器](#指标收集器)
    - [OpenTelemetry 集成](#opentelemetry-集成)
  - [日志处理](#日志处理)
    - [高性能日志收集器](#高性能日志收集器)
  - [配置管理](#配置管理)
    - [动态配置管理](#动态配置管理)
  - [基础设施即代码](#基础设施即代码)
    - [Terraform Provider SDK](#terraform-provider-sdk)
  - [最佳实践](#最佳实践)
    - [1. CLI 工具开发](#1-cli-工具开发)
    - [2. 错误处理与重试](#2-错误处理与重试)
  - [总结](#总结)

---

## DevOps 工具概述

### Rust 在 DevOps 中的优势

| 特性 | Rust 实现 | Go 对比 | Python 对比 |
|------|-----------|---------|-------------|
| 启动时间 | < 10ms | ~20ms | ~100ms+ |
| 内存占用 | 5-20MB | 10-50MB | 50-200MB |
| 单二进制文件 | 是 | 是 | 否 |
| 静态链接 | 是 | 部分 | 否 |
| 运行时崩溃 | 极少 | 少 | 较多 |

### 主要工具生态

| 类别 | Rust 工具 | 替代方案 | 优势 |
|------|-----------|----------|------|
| 容器运行时 | youki, crun | runc | 更安全、更快 |
| 镜像构建 | packer-rs | Docker Build | 可复现、安全 |
| CI/CD | Woodpecker, Drone | Jenkins, GitLab CI | 资源占用低 |
| 监控 | Vector | Fluentd, Logstash | 高性能、多功能 |
| 服务网格 | Linkerd2-proxy | Envoy | 内存效率高 |

---

## 容器技术

### OCI 运行时实现

```rust
//! OCI 容器运行时核心

use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};
use serde::{Serialize, Deserialize};

/// OCI 容器状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ContainerState {
    Creating,
    Created,
    Running,
    Stopped,
}

/// OCI Runtime Spec
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuntimeSpec {
    pub oci_version: String,
    pub process: Process,
    pub root: Root,
    pub hostname: Option<String>,
    pub mounts: Vec<Mount>,
    pub linux: Linux,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Process {
    pub terminal: bool,
    pub user: User,
    pub args: Vec<String>,
    pub env: Vec<String>,
    pub cwd: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub uid: u32,
    pub gid: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Root {
    pub path: String,
    pub readonly: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Mount {
    pub destination: String,
    pub source: String,
    pub mount_type: String,
    pub options: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Linux {
    pub namespaces: Vec<Namespace>,
    pub uid_mappings: Vec<IdMapping>,
    pub gid_mappings: Vec<IdMapping>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Namespace {
    pub namespace_type: String,
    pub path: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IdMapping {
    pub container_id: u32,
    pub host_id: u32,
    pub size: u32,
}

/// 容器管理器
pub struct ContainerManager {
    state_dir: String,
}

impl ContainerManager {
    pub fn new(state_dir: &str) -> Self {
        fs::create_dir_all(state_dir).unwrap();
        Self { state_dir: state_dir.to_string() }
    }

    /// 创建容器
    pub fn create(&self, id: &str, bundle: &str) -> Result<ContainerState, ContainerError> {
        let config_path = Path::new(bundle).join("config.json");
        let config_str = fs::read_to_string(config_path)
            .map_err(|e| ContainerError::ConfigRead(e.to_string()))?;

        let spec: RuntimeSpec = serde_json::from_str(&config_str)
            .map_err(|e| ContainerError::ConfigParse(e.to_string()))?;

        // 创建状态目录
        let container_dir = Path::new(&self.state_dir).join(id);
        fs::create_dir_all(&container_dir)?;

        // 保存状态
        let state = ContainerStateInfo {
            oci_version: spec.oci_version,
            id: id.to_string(),
            status: ContainerState::Created,
            bundle: bundle.to_string(),
            rootfs: Path::new(bundle).join(&spec.root.path).to_string_lossy().to_string(),
            created: chrono::Utc::now(),
            owner: std::process::id(),
        };

        let state_file = container_dir.join("state.json");
        fs::write(state_file, serde_json::to_string_pretty(&state)?)?;

        Ok(ContainerState::Created)
    }

    /// 启动容器
    pub fn start(&self, id: &str) -> Result<(), ContainerError> {
        let state = self.get_state(id)?;

        if state.status != ContainerState::Created {
            return Err(ContainerError::InvalidState(format!(
                "Container is in {:?} state, expected Created", state.status
            )));
        }

        // 读取配置
        let config_path = Path::new(&state.bundle).join("config.json");
        let spec: RuntimeSpec = serde_json::from_str(&fs::read_to_string(config_path)?)?;

        // 启动容器进程（简化实现）
        let mut cmd = Command::new(&spec.process.args[0]);
        cmd.args(&spec.process.args[1..])
            .current_dir(&spec.process.cwd)
            .env_clear()
            .envs(spec.process.env.iter().map(|e| {
                let parts: Vec<&str> = e.splitn(2, '=').collect();
                (parts[0], parts.get(1).unwrap_or(&""))
            }))
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        // 启动进程
        let mut child = cmd.spawn()?;

        // 更新状态为 Running
        self.update_state(id, ContainerState::Running, Some(child.id() as i64))?;

        Ok(())
    }

    /// 停止容器
    pub fn stop(&self, id: &str, signal: &str) -> Result<(), ContainerError> {
        let state = self.get_state(id)?;

        if state.status != ContainerState::Running {
            return Err(ContainerError::InvalidState(
                "Container is not running".to_string()
            ));
        }

        // 发送信号停止容器
        if let Some(pid) = state.pid {
            let sig = match signal {
                "SIGTERM" => 15,
                "SIGKILL" => 9,
                _ => 15,
            };

            unsafe {
                libc::kill(pid as i32, sig);
            }
        }

        self.update_state(id, ContainerState::Stopped, None)?;
        Ok(())
    }

    /// 删除容器
    pub fn delete(&self, id: &str) -> Result<(), ContainerError> {
        let state = self.get_state(id)?;

        if state.status == ContainerState::Running {
            return Err(ContainerError::InvalidState(
                "Cannot delete running container".to_string()
            ));
        }

        let container_dir = Path::new(&self.state_dir).join(id);
        fs::remove_dir_all(container_dir)?;

        Ok(())
    }

    /// 获取容器状态
    pub fn get_state(&self, id: &str) -> Result<ContainerStateInfo, ContainerError> {
        let state_file = Path::new(&self.state_dir).join(id).join("state.json");
        let content = fs::read_to_string(state_file)?;
        Ok(serde_json::from_str(&content)?)
    }

    fn update_state(&self, id: &str, status: ContainerState, pid: Option<i64>) -> Result<(), ContainerError> {
        let mut state = self.get_state(id)?;
        state.status = status;
        state.pid = pid;

        let state_file = Path::new(&self.state_dir).join(id).join("state.json");
        fs::write(state_file, serde_json::to_string_pretty(&state)?)?;
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContainerStateInfo {
    pub oci_version: String,
    pub id: String,
    pub status: ContainerState,
    pub pid: Option<i64>,
    pub bundle: String,
    pub rootfs: String,
    pub created: chrono::DateTime<chrono::Utc>,
    pub owner: u32,
}

#[derive(Debug)]
pub enum ContainerError {
    Io(std::io::Error),
    Serde(serde_json::Error),
    ConfigRead(String),
    ConfigParse(String),
    InvalidState(String),
}

impl From<std::io::Error> for ContainerError {
    fn from(e: std::io::Error) -> Self { Self::Io(e) }
}

impl From<serde_json::Error> for ContainerError {
    fn from(e: serde_json::Error) -> Self { Self::Serde(e) }
}
```

### 容器镜像构建

```rust
//! 容器镜像构建器

use std::collections::HashMap;
use tar::Builder;
use flate2::write::GzEncoder;
use flate2::Compression;
use serde::{Serialize, Deserialize};
use sha2::{Sha256, Digest};

/// Dockerfile 指令
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Instruction {
    From { image: String, tag: String },
    Run { command: String },
    Copy { src: String, dest: String },
    Env { key: String, value: String },
    Workdir { path: String },
    Cmd { args: Vec<String> },
    Expose { port: u16 },
}

/// 镜像层
#[derive(Debug, Clone)]
pub struct Layer {
    pub id: String,
    pub parent: Option<String>,
    pub created: chrono::DateTime<chrono::Utc>,
    pub created_by: String,
    pub size: u64,
    pub content: Vec<u8>,
}

/// 镜像构建器
pub struct ImageBuilder {
    name: String,
    tag: String,
    layers: Vec<Layer>,
    config: ImageConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ImageConfig {
    pub architecture: String,
    pub os: String,
    pub config: ContainerConfig,
    pub rootfs: RootFs,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContainerConfig {
    pub Env: Vec<String>,
    pub WorkingDir: String,
    pub Cmd: Vec<String>,
    pub ExposedPorts: HashMap<String, serde_json::Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RootFs {
    pub docker_type: String,
    pub diff_ids: Vec<String>,
}

impl ImageBuilder {
    pub fn new(name: &str, tag: &str) -> Self {
        Self {
            name: name.to_string(),
            tag: tag.to_string(),
            layers: Vec::new(),
            config: ImageConfig {
                architecture: "amd64".to_string(),
                os: "linux".to_string(),
                config: ContainerConfig {
                    Env: vec!["PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin".to_string()],
                    WorkingDir: "/".to_string(),
                    Cmd: vec!["sh".to_string()],
                    ExposedPorts: HashMap::new(),
                },
                rootfs: RootFs {
                    docker_type: "layers".to_string(),
                    diff_ids: Vec::new(),
                },
            },
        }
    }

    /// 添加层
    pub fn add_layer(&mut self, files: HashMap<String, Vec<u8>>, created_by: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut tar_buffer = Vec::new();
        {
            let mut tar = Builder::new(&mut tar_buffer);

            for (path, content) in files {
                let mut header = tar::Header::new_gnu();
                header.set_path(&path)?;
                header.set_size(content.len() as u64);
                header.set_mode(0o644);
                header.set_cksum();
                tar.append(&header, content.as_slice())?;
            }

            tar.finish()?;
        }

        // 压缩层
        let mut compressed = Vec::new();
        {
            let mut encoder = GzEncoder::new(&mut compressed, Compression::default());
            std::io::Write::write_all(&mut encoder, &tar_buffer)?;
            encoder.finish()?;
        }

        // 计算层 ID
        let mut hasher = Sha256::new();
        hasher.update(&compressed);
        let layer_id = format!("sha256:{:x}", hasher.finalize());

        let layer = Layer {
            id: layer_id.clone(),
            parent: self.layers.last().map(|l| l.id.clone()),
            created: chrono::Utc::now(),
            created_by: created_by.to_string(),
            size: compressed.len() as u64,
            content: compressed,
        };

        self.config.rootfs.diff_ids.push(layer_id);
        self.layers.push(layer);

        Ok(())
    }

    /// 设置环境变量
    pub fn set_env(&mut self, key: &str, value: &str) {
        self.config.config.Env.push(format!("{}={}", key, value));
    }

    /// 设置工作目录
    pub fn set_workdir(&mut self, path: &str) {
        self.config.config.WorkingDir = path.to_string();
    }

    /// 设置启动命令
    pub fn set_cmd(&mut self, args: Vec<String>) {
        self.config.config.Cmd = args;
    }

    /// 暴露端口
    pub fn expose_port(&mut self, port: u16) {
        self.config.config.ExposedPorts.insert(
            format!("{}/tcp", port),
            serde_json::json!({}),
        );
    }

    /// 构建镜像
    pub fn build(self) -> Image {
        Image {
            name: self.name,
            tag: self.tag,
            layers: self.layers,
            config: self.config,
        }
    }
}

pub struct Image {
    pub name: String,
    pub tag: String,
    pub layers: Vec<Layer>,
    pub config: ImageConfig,
}

impl Image {
    /// 导出为 OCI 格式
    pub fn export_oci(&self, output_dir: &str) -> Result<(), Box<dyn std::error::Error>> {
        std::fs::create_dir_all(output_dir)?;

        // 写入层
        let blobs_dir = format!("{}/blobs/sha256", output_dir);
        std::fs::create_dir_all(&blobs_dir)?;

        for layer in &self.layers {
            let layer_path = format!("{}/{}", blobs_dir, &layer.id[7..]); // 去掉 sha256: 前缀
            std::fs::write(layer_path, &layer.content)?;
        }

        // 写入配置
        let config_json = serde_json::to_string(&self.config)?;
        let mut config_hasher = Sha256::new();
        config_hasher.update(&config_json);
        let config_digest = format!("{:x}", config_hasher.finalize());
        std::fs::write(format!("{}/{}", blobs_dir, config_digest), config_json)?;

        // 创建索引
        let index = serde_json::json!({
            "schemaVersion": 2,
            "mediaType": "application/vnd.oci.image.index.v1+json",
            "manifests": [{
                "mediaType": "application/vnd.oci.image.manifest.v1+json",
                "digest": format!("sha256:{}", config_digest),
                "size": config_json.len(),
                "platform": {
                    "architecture": "amd64",
                    "os": "linux"
                }
            }]
        });

        std::fs::write(
            format!("{}/index.json", output_dir),
            serde_json::to_string_pretty(&index)?
        )?;

        Ok(())
    }
}
```

---

## CI/CD 系统

### 流水线引擎

```rust
//! CI/CD 流水线引擎

use serde::{Serialize, Deserialize};
use std::collections::HashMap;
use std::process::Stdio;
use tokio::process::Command;
use tokio::sync::{mpsc, RwLock};
use std::sync::Arc;

/// 流水线配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelineConfig {
    pub name: String,
    pub triggers: Vec<Trigger>,
    pub stages: Vec<Stage>,
    pub variables: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum Trigger {
    #[serde(rename = "push")]
    Push { branches: Vec<String> },
    #[serde(rename = "pull_request")]
    PullRequest { branches: Vec<String> },
    #[serde(rename = "schedule")]
    Schedule { cron: String },
    #[serde(rename = "manual")]
    Manual,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Stage {
    pub name: String,
    pub steps: Vec<Step>,
    pub depends_on: Option<Vec<String>>,
    pub condition: Option<String>,
    pub parallel: Option<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Step {
    pub name: String,
    pub image: String,
    pub commands: Vec<String>,
    pub environment: Option<HashMap<String, String>>,
    pub artifacts: Option<Vec<String>>,
    pub cache: Option<Vec<String>>,
}

/// 流水线状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PipelineStatus {
    Pending,
    Running,
    Success,
    Failed,
    Cancelled,
}

/// 流水线执行器
pub struct PipelineRunner {
    pipelines: Arc<RwLock<HashMap<String, PipelineExecution>>>,
    executor: Arc<dyn StepExecutor>,
}

pub struct PipelineExecution {
    pub id: String,
    pub config: PipelineConfig,
    pub status: PipelineStatus,
    pub stages: Vec<StageExecution>,
    pub start_time: Option<chrono::DateTime<chrono::Utc>>,
    pub end_time: Option<chrono::DateTime<chrono::Utc>>,
    pub logs: Vec<LogEntry>,
}

pub struct StageExecution {
    pub name: String,
    pub status: PipelineStatus,
    pub steps: Vec<StepExecution>,
    pub start_time: Option<chrono::DateTime<chrono::Utc>>,
    pub end_time: Option<chrono::DateTime<chrono::Utc>>,
}

pub struct StepExecution {
    pub name: String,
    pub status: PipelineStatus,
    pub log: String,
    pub exit_code: Option<i32>,
    pub start_time: Option<chrono::DateTime<chrono::Utc>>,
    pub end_time: Option<chrono::DateTime<chrono::Utc>>,
}

#[derive(Debug, Clone)]
pub struct LogEntry {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub level: LogLevel,
    pub message: String,
    pub stage: Option<String>,
    pub step: Option<String>,
}

#[derive(Debug, Clone)]
pub enum LogLevel { Info, Warning, Error, Debug }

#[async_trait::async_trait]
pub trait StepExecutor: Send + Sync {
    async fn execute(&self, step: &Step, ctx: &ExecutionContext) -> Result<StepResult, ExecutionError>;
}

pub struct StepResult {
    pub exit_code: i32,
    pub stdout: String,
    pub stderr: String,
    pub duration: std::time::Duration,
}

pub struct ExecutionContext {
    pub pipeline_id: String,
    pub workspace: String,
    pub variables: HashMap<String, String>,
}

pub struct ExecutionError(String);

impl PipelineRunner {
    pub fn new(executor: Arc<dyn StepExecutor>) -> Self {
        Self {
            pipelines: Arc::new(RwLock::new(HashMap::new())),
            executor,
        }
    }

    pub async fn trigger(&self, config: PipelineConfig, trigger: Trigger) -> Result<String, PipelineError> {
        let id = uuid::Uuid::new_v4().to_string();

        // 创建执行
        let execution = PipelineExecution {
            id: id.clone(),
            stages: config.stages.iter().map(|s| StageExecution {
                name: s.name.clone(),
                status: PipelineStatus::Pending,
                steps: s.steps.iter().map(|step| StepExecution {
                    name: step.name.clone(),
                    status: PipelineStatus::Pending,
                    log: String::new(),
                    exit_code: None,
                    start_time: None,
                    end_time: None,
                }).collect(),
                start_time: None,
                end_time: None,
            }).collect(),
            config: config.clone(),
            status: PipelineStatus::Pending,
            start_time: None,
            end_time: None,
            logs: Vec::new(),
        };

        self.pipelines.write().await.insert(id.clone(), execution);

        // 启动执行
        let pipelines = self.pipelines.clone();
        let executor = self.executor.clone();
        tokio::spawn(async move {
            Self::run_pipeline(id, config, pipelines, executor).await;
        });

        Ok(id)
    }

    async fn run_pipeline(
        id: String,
        config: PipelineConfig,
        pipelines: Arc<RwLock<HashMap<String, PipelineExecution>>>,
        executor: Arc<dyn StepExecutor>,
    ) {
        // 更新状态为运行中
        {
            let mut pipelines = pipelines.write().await;
            if let Some(exec) = pipelines.get_mut(&id) {
                exec.status = PipelineStatus::Running;
                exec.start_time = Some(chrono::Utc::now());
            }
        }

        // 按依赖顺序执行阶段
        for stage_idx in 0..config.stages.len() {
            let stage = config.stages[stage_idx].clone();

            // 检查依赖
            if let Some(depends_on) = &stage.depends_on {
                let pipelines_guard = pipelines.read().await;
                if let Some(exec) = pipelines_guard.get(&id) {
                    for dep in depends_on {
                        if let Some(dep_stage) = exec.stages.iter().find(|s| &s.name == dep) {
                            if dep_stage.status != PipelineStatus::Success {
                                // 依赖失败
                                drop(pipelines_guard);
                                Self::fail_pipeline(&id, &pipelines).await;
                                return;
                            }
                        }
                    }
                }
            }

            // 执行阶段
            Self::execute_stage(&id, &stage, &config, &executor, &pipelines).await;
        }

        // 更新最终状态
        {
            let mut pipelines = pipelines.write().await;
            if let Some(exec) = pipelines.get_mut(&id) {
                exec.status = if exec.stages.iter().all(|s| s.status == PipelineStatus::Success) {
                    PipelineStatus::Success
                } else {
                    PipelineStatus::Failed
                };
                exec.end_time = Some(chrono::Utc::now());
            }
        }
    }

    async fn execute_stage(
        pipeline_id: &str,
        stage: &Stage,
        config: &PipelineConfig,
        executor: &Arc<dyn StepExecutor>,
        pipelines: &Arc<RwLock<HashMap<String, PipelineExecution>>>,
    ) {
        // 更新阶段状态
        {
            let mut pipelines = pipelines.write().await;
            if let Some(exec) = pipelines.get_mut(pipeline_id) {
                if let Some(stage_exec) = exec.stages.iter_mut().find(|s| s.name == stage.name) {
                    stage_exec.status = PipelineStatus::Running;
                    stage_exec.start_time = Some(chrono::Utc::now());
                }
            }
        }

        let ctx = ExecutionContext {
            pipeline_id: pipeline_id.to_string(),
            workspace: format!("/tmp/pipelines/{}", pipeline_id),
            variables: config.variables.clone(),
        };

        // 执行步骤
        for (step_idx, step) in stage.steps.iter().enumerate() {
            let result = executor.execute(step, &ctx).await;

            // 更新步骤状态
            {
                let mut pipelines = pipelines.write().await;
                if let Some(exec) = pipelines.get_mut(pipeline_id) {
                    if let Some(stage_exec) = exec.stages.iter_mut().find(|s| s.name == stage.name) {
                        if let Some(step_exec) = stage_exec.steps.get_mut(step_idx) {
                            step_exec.end_time = Some(chrono::Utc::now());

                            match result {
                                Ok(res) => {
                                    step_exec.exit_code = Some(res.exit_code);
                                    step_exec.log = format!("{}/n{}", res.stdout, res.stderr);
                                    step_exec.status = if res.exit_code == 0 {
                                        PipelineStatus::Success
                                    } else {
                                        PipelineStatus::Failed
                                    };
                                }
                                Err(e) => {
                                    step_exec.status = PipelineStatus::Failed;
                                    step_exec.log = e.0;
                                }
                            }
                        }
                    }
                }
            }
        }

        // 更新阶段最终状态
        {
            let mut pipelines = pipelines.write().await;
            if let Some(exec) = pipelines.get_mut(pipeline_id) {
                if let Some(stage_exec) = exec.stages.iter_mut().find(|s| s.name == stage.name) {
                    stage_exec.status = if stage_exec.steps.iter().all(|s| s.status == PipelineStatus::Success) {
                        PipelineStatus::Success
                    } else {
                        PipelineStatus::Failed
                    };
                    stage_exec.end_time = Some(chrono::Utc::now());
                }
            }
        }
    }

    async fn fail_pipeline(id: &str, pipelines: &Arc<RwLock<HashMap<String, PipelineExecution>>>) {
        let mut pipelines = pipelines.write().await;
        if let Some(exec) = pipelines.get_mut(id) {
            exec.status = PipelineStatus::Failed;
            exec.end_time = Some(chrono::Utc::now());
        }
    }

    pub async fn get_status(&self, id: &str) -> Option<PipelineStatus> {
        self.pipelines.read().await.get(id).map(|e| e.status.clone())
    }

    pub async fn get_logs(&self, id: &str) -> Option<Vec<LogEntry>> {
        self.pipelines.read().await.get(id).map(|e| e.logs.clone())
    }
}

#[derive(Debug)]
pub enum PipelineError {
    ConfigError(String),
    ExecutionError(String),
}

/// Docker 执行器实现
pub struct DockerExecutor;

#[async_trait::async_trait]
impl StepExecutor for DockerExecutor {
    async fn execute(&self, step: &Step, ctx: &ExecutionContext) -> Result<StepResult, ExecutionError> {
        let start = std::time::Instant::now();

        let mut cmd = Command::new("docker");
        cmd.arg("run")
            .arg("--rm")
            .arg("-v").arg(format!("{}:/workspace", ctx.workspace))
            .arg("-w").arg("/workspace");

        // 添加环境变量
        for (key, value) in step.environment.as_ref().unwrap_or(&HashMap::new()) {
            cmd.arg("-e").arg(format!("{}={}", key, value));
        }

        cmd.arg(&step.image)
            .arg("sh")
            .arg("-c")
            .arg(step.commands.join(" && "));

        let output = cmd.output().await.map_err(|e| ExecutionError(e.to_string()))?;

        Ok(StepResult {
            exit_code: output.status.code().unwrap_or(-1),
            stdout: String::from_utf8_lossy(&output.stdout).to_string(),
            stderr: String::from_utf8_lossy(&output.stderr).to_string(),
            duration: start.elapsed(),
        })
    }
}
```

---

## 监控与可观测性

### 指标收集器

```rust
//! 系统指标收集器

use sysinfo::{System, SystemExt, ProcessExt, CpuExt, NetworkExt, DiskExt};
use std::time::Duration;
use tokio::time::interval;
use serde::{Serialize, Deserialize};
use std::sync::Arc;
use tokio::sync::RwLock;

/// 系统指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemMetrics {
    pub timestamp: u64,
    pub cpu: CpuMetrics,
    pub memory: MemoryMetrics,
    pub disks: Vec<DiskMetrics>,
    pub network: NetworkMetrics,
    pub processes: Vec<ProcessMetrics>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CpuMetrics {
    pub usage_percent: f32,
    pub core_count: usize,
    pub per_core_usage: Vec<f32>,
    pub load_average: [f64; 3],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryMetrics {
    pub total: u64,
    pub used: u64,
    pub free: u64,
    pub available: u64,
    pub buffers: u64,
    pub cached: u64,
    pub swap_total: u64,
    pub swap_used: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiskMetrics {
    pub name: String,
    pub mount_point: String,
    pub total: u64,
    pub used: u64,
    pub free: u64,
    pub usage_percent: f32,
    pub filesystem_type: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkMetrics {
    pub interfaces: Vec<NetworkInterface>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkInterface {
    pub name: String,
    pub rx_bytes: u64,
    pub tx_bytes: u64,
    pub rx_packets: u64,
    pub tx_packets: u64,
    pub rx_errors: u64,
    pub tx_errors: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProcessMetrics {
    pub pid: i32,
    pub name: String,
    pub cpu_usage: f32,
    pub memory_bytes: u64,
    pub virtual_memory: u64,
    pub status: String,
    pub parent_pid: Option<i32>,
}

/// 指标收集器
pub struct MetricsCollector {
    system: Arc<RwLock<System>>,
    collection_interval: Duration,
    history: Arc<RwLock<Vec<SystemMetrics>>>,
    max_history: usize,
}

impl MetricsCollector {
    pub fn new(collection_interval_secs: u64, max_history: usize) -> Self {
        let mut system = System::new_all();
        system.refresh_all();

        Self {
            system: Arc::new(RwLock::new(system)),
            collection_interval: Duration::from_secs(collection_interval_secs),
            history: Arc::new(RwLock::new(Vec::with_capacity(max_history))),
            max_history,
        }
    }

    /// 启动收集循环
    pub async fn start(&self) {
        let system = self.system.clone();
        let history = self.history.clone();
        let max_history = self.max_history;
        let mut ticker = interval(self.collection_interval);

        loop {
            ticker.tick().await;

            let metrics = self.collect().await;

            let mut history = history.write().await;
            history.push(metrics);

            // 限制历史记录大小
            if history.len() > max_history {
                history.remove(0);
            }
        }
    }

    /// 收集当前指标
    pub async fn collect(&self) -> SystemMetrics {
        let mut system = self.system.write().await;

        // 刷新系统信息
        system.refresh_all();

        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // CPU 指标
        let cpu = CpuMetrics {
            usage_percent: system.global_cpu_info().cpu_usage(),
            core_count: system.cpus().len(),
            per_core_usage: system.cpus().iter().map(|c| c.cpu_usage()).collect(),
            load_average: [
                system.load_average().one,
                system.load_average().five,
                system.load_average().fifteen,
            ],
        };

        // 内存指标
        let memory = MemoryMetrics {
            total: system.total_memory(),
            used: system.used_memory(),
            free: system.free_memory(),
            available: system.available_memory(),
            buffers: 0, // sysinfo 可能不提供
            cached: 0,
            swap_total: system.total_swap(),
            swap_used: system.used_swap(),
        };

        // 磁盘指标
        let disks: Vec<DiskMetrics> = system.disks().iter().map(|d| {
            let total = d.total_space();
            let used = total - d.available_space();
            DiskMetrics {
                name: d.name().to_string_lossy().to_string(),
                mount_point: d.mount_point().to_string_lossy().to_string(),
                total,
                used,
                free: d.available_space(),
                usage_percent: (used as f32 / total as f32) * 100.0,
                filesystem_type: d.file_system().to_string_lossy().to_string(),
            }
        }).collect();

        // 网络指标
        let interfaces: Vec<NetworkInterface> = system.networks().iter().map(|(name, data)| {
            NetworkInterface {
                name: name.clone(),
                rx_bytes: data.received(),
                tx_bytes: data.transmitted(),
                rx_packets: data.packets_received(),
                tx_packets: data.packets_transmitted(),
                rx_errors: data.errors_on_received(),
                tx_errors: data.total_errors_on_transmitted(),
            }
        }).collect();

        let network = NetworkMetrics { interfaces };

        // 进程指标（Top 20 按 CPU）
        let mut processes: Vec<ProcessMetrics> = system.processes().values()
            .map(|p| ProcessMetrics {
                pid: p.pid().into(),
                name: p.name().to_string(),
                cpu_usage: p.cpu_usage(),
                memory_bytes: p.memory(),
                virtual_memory: p.virtual_memory(),
                status: format!("{:?}", p.status()),
                parent_pid: p.parent().map(|p| p.into()),
            })
            .collect();

        processes.sort_by(|a, b| b.cpu_usage.partial_cmp(&a.cpu_usage).unwrap());
        processes.truncate(20);

        SystemMetrics {
            timestamp,
            cpu,
            memory,
            disks,
            network,
            processes,
        }
    }

    /// 获取历史指标
    pub async fn get_history(&self) -> Vec<SystemMetrics> {
        self.history.read().await.clone()
    }

    /// 获取最新指标
    pub async fn get_latest(&self) -> Option<SystemMetrics> {
        self.history.read().await.last().cloned()
    }

    /// 获取特定时间范围的指标
    pub async fn get_range(&self, start: u64, end: u64) -> Vec<SystemMetrics> {
        self.history.read().await.iter()
            .filter(|m| m.timestamp >= start && m.timestamp <= end)
            .cloned()
            .collect()
    }
}

/// 指标导出器
pub struct MetricsExporter;

impl MetricsExporter {
    /// 导出为 Prometheus 格式
    pub fn to_prometheus(metrics: &SystemMetrics) -> String {
        let mut output = String::new();

        // CPU 指标
        output.push_str(&format!("# HELP node_cpu_usage_percent CPU usage percent\n"));
        output.push_str(&format!("# TYPE node_cpu_usage_percent gauge\n"));
        output.push_str(&format!("node_cpu_usage_percent {}\n", metrics.cpu.usage_percent));

        // 内存指标
        output.push_str(&format!("# HELP node_memory_total_bytes Total memory\n"));
        output.push_str(&format!("# TYPE node_memory_total_bytes gauge\n"));
        output.push_str(&format!("node_memory_total_bytes {}\n", metrics.memory.total));

        output.push_str(&format!("# HELP node_memory_used_bytes Used memory\n"));
        output.push_str(&format!("# TYPE node_memory_used_bytes gauge\n"));
        output.push_str(&format!("node_memory_used_bytes {}\n", metrics.memory.used));

        // 磁盘指标
        for disk in &metrics.disks {
            output.push_str(&format!(
                "node_disk_usage_percent{{mountpoint=\"{}\"}} {}\n",
                disk.mount_point, disk.usage_percent
            ));
        }

        output
    }

    /// 导出为 InfluxDB Line Protocol
    pub fn to_influxdb(metrics: &SystemMetrics) -> String {
        let mut output = String::new();

        output.push_str(&format!(
            "system_metrics cpu_usage={},memory_used={},memory_total={} {}\n",
            metrics.cpu.usage_percent,
            metrics.memory.used,
            metrics.memory.total,
            metrics.timestamp * 1_000_000_000 // 转换为纳秒
        ));

        output
    }
}
```

### OpenTelemetry 集成

```rust
//! OpenTelemetry 可观测性集成

use opentelemetry::{
    global,
    trace::{Tracer, TraceContextExt, SpanKind, FutureExt},
    Context, KeyValue,
};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{
    trace::{self, RandomIdGenerator, Sampler},
    Resource,
};
use tracing::{info, error, Span};
use tracing_opentelemetry::OpenTelemetrySpanExt;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

/// 初始化 OpenTelemetry
pub fn init_telemetry(service_name: &str, otlp_endpoint: &str) {
    // 创建资源
    let resource = Resource::new(vec![
        KeyValue::new("service.name", service_name.to_string()),
        KeyValue::new("service.version", env!("CARGO_PKG_VERSION")),
        KeyValue::new("deployment.environment", std::env::var("ENV").unwrap_or_else(|_| "dev".to_string())),
    ]);

    // 配置 OTLP 导出器
    let tracer = opentelemetry_otlp::new_pipeline()
        .tracing()
        .with_exporter(
            opentelemetry_otlp::new_exporter()
                .tonic()
                .with_endpoint(otlp_endpoint),
        )
        .with_trace_config(
            trace::config()
                .with_sampler(Sampler::TraceIdRatioBased(1.0))
                .with_id_generator(RandomIdGenerator::default())
                .with_resource(resource),
        )
        .install_batch(opentelemetry_sdk::runtime::Tokio)
        .expect("Failed to install OpenTelemetry pipeline");

    // 设置全局 tracer
    global::set_tracer_provider(tracer.provider().clone());

    // 配置 tracing subscriber
    let telemetry_layer = tracing_opentelemetry::layer().with_tracer(tracer);
    let fmt_layer = tracing_subscriber::fmt::layer();

    tracing_subscriber::registry()
        .with(telemetry_layer)
        .with(fmt_layer)
        .init();
}

/// 创建 Span 的宏
#[macro_export]
macro_rules! instrumented {
    ($name:expr, $body:block) => {{
        let tracer = opentelemetry::global::tracer("default");
        let mut span = tracer.start($name);
        span.set_attribute(opentelemetry::KeyValue::new("code.function", $name));

        let cx = opentelemetry::Context::current_with_span(span);
        let _guard = cx.attach();

        $body
    }};
}

/// HTTP 请求追踪
pub async fn traced_http_request<F, Fut, T>(
    method: &str,
    url: &str,
    operation: F,
) -> T
where
    F: FnOnce() -> Fut,
    Fut: std::future::Future<Output = T>,
{
    let tracer = global::tracer("http_client");
    let mut span = tracer.span_builder(format!("HTTP {}", method))
        .with_kind(SpanKind::Client)
        .with_attributes(vec![
            KeyValue::new("http.method", method.to_string()),
            KeyValue::new("http.url", url.to_string()),
        ])
        .start(&tracer);

    let cx = Context::current_with_span(span);

    operation
        .with_context(cx.clone())
        .await
}

/// 记录业务指标
pub fn record_business_metric(name: &str, value: f64, attributes: Vec<KeyValue>) {
    // 在实际实现中，这里会记录到 OpenTelemetry metrics
    tracing::info!(
        metric_name = name,
        metric_value = value,
        attributes = ?attributes,
        "Business metric recorded"
    );
}

/// 清理资源
pub fn shutdown_telemetry() {
    global::shutdown_tracer_provider();
}
```

---

## 日志处理

### 高性能日志收集器

```rust
//! 高性能日志收集器

use serde::{Serialize, Deserialize};
use tokio::sync::mpsc;
use std::time::{Duration, Instant};
use regex::Regex;
use std::collections::HashMap;

/// 结构化日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub level: LogLevel,
    pub message: String,
    pub source: String,
    pub fields: HashMap<String, serde_json::Value>,
    pub raw: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warning,
    Error,
    Fatal,
}

impl From<&str> for LogLevel {
    fn from(s: &str) -> Self {
        match s.to_uppercase().as_str() {
            "TRACE" => LogLevel::Trace,
            "DEBUG" => LogLevel::Debug,
            "INFO" => LogLevel::Info,
            "WARN" | "WARNING" => LogLevel::Warning,
            "ERROR" => LogLevel::Error,
            "FATAL" => LogLevel::Fatal,
            _ => LogLevel::Info,
        }
    }
}

/// 日志解析器
pub struct LogParser {
    patterns: Vec<(Regex, Box<dyn Fn(&regex::Captures) -> LogEntry + Send + Sync>)>,
}

impl LogParser {
    pub fn new() -> Self {
        Self { patterns: Vec::new() }
    }

    pub fn add_pattern<F>(&mut self, pattern: &str, parser: F)
    where
        F: Fn(&regex::Captures) -> LogEntry + Send + Sync + 'static,
    {
        let regex = Regex::new(pattern).expect("Invalid regex pattern");
        self.patterns.push((regex, Box::new(parser)));
    }

    pub fn parse(&self, line: &str, source: &str) -> Option<LogEntry> {
        for (regex, parser) in &self.patterns {
            if let Some(captures) = regex.captures(line) {
                let mut entry = parser(&captures);
                entry.source = source.to_string();
                entry.raw = line.to_string();
                return Some(entry);
            }
        }

        // 默认解析
        Some(LogEntry {
            timestamp: chrono::Utc::now(),
            level: LogLevel::Info,
            message: line.to_string(),
            source: source.to_string(),
            fields: HashMap::new(),
            raw: line.to_string(),
        })
    }
}

/// 日志收集器
pub struct LogCollector {
    parser: LogParser,
    processors: Vec<Box<dyn LogProcessor>>,
    batch_size: usize,
    flush_interval: Duration,
}

#[async_trait::async_trait]
pub trait LogProcessor: Send + Sync {
    async fn process(&self, entries: Vec<LogEntry>) -> Result<(), LogError>;
}

pub struct ElasticsearchProcessor {
    client: reqwest::Client,
    url: String,
    index: String,
}

impl ElasticsearchProcessor {
    pub fn new(url: &str, index: &str) -> Self {
        Self {
            client: reqwest::Client::new(),
            url: url.to_string(),
            index: index.to_string(),
        }
    }
}

#[async_trait::async_trait]
impl LogProcessor for ElasticsearchProcessor {
    async fn process(&self, entries: Vec<LogEntry>) -> Result<(), LogError> {
        let mut bulk_body = String::new();

        for entry in entries {
            let index_line = format!(
                r#"{{"index":{{"_index":"{}","_type":"_doc"}}}}"#,
                self.index
            );
            let doc = serde_json::to_string(&entry).map_err(|e| LogError::Serialize(e.to_string()))?;

            bulk_body.push_str(&index_line);
            bulk_body.push('\n');
            bulk_body.push_str(&doc);
            bulk_body.push('\n');
        }

        let response = self.client
            .post(format!("{}/_bulk", self.url))
            .header("Content-Type", "application/json")
            .body(bulk_body)
            .send()
            .await
            .map_err(|e| LogError::Network(e.to_string()))?;

        if !response.status().is_success() {
            return Err(LogError::Api(format!(
                "Elasticsearch error: {}",
                response.text().await.unwrap_or_default()
            )));
        }

        Ok(())
    }
}

pub struct FileProcessor {
    path: String,
    rotation_size: u64,
}

impl LogCollector {
    pub fn new(parser: LogParser, batch_size: usize, flush_interval_secs: u64) -> Self {
        Self {
            parser,
            processors: Vec::new(),
            batch_size,
            flush_interval: Duration::from_secs(flush_interval_secs),
        }
    }

    pub fn add_processor(&mut self, processor: Box<dyn LogProcessor>) {
        self.processors.push(processor);
    }

    pub async fn collect<R>(&self, reader: R, source: &str)
    where
        R: tokio::io::AsyncBufRead + Unpin,
    {
        use tokio::io::AsyncBufReadExt;

        let mut lines = reader.lines();
        let mut buffer = Vec::with_capacity(self.batch_size);
        let mut last_flush = Instant::now();

        while let Ok(Some(line)) = lines.next_line().await {
            if let Some(entry) = self.parser.parse(&line, source) {
                buffer.push(entry);

                if buffer.len() >= self.batch_size || last_flush.elapsed() >= self.flush_interval {
                    self.flush(&buffer).await;
                    buffer.clear();
                    last_flush = Instant::now();
                }
            }
        }

        // 刷新剩余
        if !buffer.is_empty() {
            self.flush(&buffer).await;
        }
    }

    async fn flush(&self, entries: &[LogEntry]) {
        for processor in &self.processors {
            if let Err(e) = processor.process(entries.to_vec()).await {
                eprintln!("Processor error: {:?}", e);
            }
        }
    }
}

#[derive(Debug)]
pub enum LogError {
    Serialize(String),
    Network(String),
    Api(String),
}
```

---

## 配置管理

### 动态配置管理

```rust
//! 动态配置管理系统

use serde::{Serialize, Deserialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, watch};
use notify::{Watcher, RecursiveMode, RecommendedWatcher, Config};
use std::path::Path;

/// 配置结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub features: FeatureFlags,
    pub limits: RateLimits,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
    pub timeout_seconds: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub connection_timeout: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeatureFlags {
    pub enable_new_ui: bool,
    pub enable_beta_features: bool,
    pub maintenance_mode: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimits {
    pub requests_per_minute: u32,
    pub burst_size: u32,
}

/// 配置管理器
pub struct ConfigManager {
    current: Arc<RwLock<AppConfig>>,
    tx: watch::Sender<AppConfig>,
    rx: watch::Receiver<AppConfig>,
}

impl ConfigManager {
    pub fn new(initial: AppConfig) -> Self {
        let (tx, rx) = watch::channel(initial.clone());

        Self {
            current: Arc::new(RwLock::new(initial)),
            tx,
            rx,
        }
    }

    pub async fn load_from_file<P: AsRef<Path>>(&self, path: P) -> Result<(), ConfigError> {
        let content = tokio::fs::read_to_string(path).await?;
        let config: AppConfig = serde_yaml::from_str(&content)?;

        self.update(config).await;
        Ok(())
    }

    pub async fn update(&self, new_config: AppConfig) {
        let mut current = self.current.write().await;
        *current = new_config.clone();
        let _ = self.tx.send(new_config);
    }

    pub async fn get(&self) -> AppConfig {
        self.current.read().await.clone()
    }

    pub fn subscribe(&self) -> watch::Receiver<AppConfig> {
        self.rx.clone()
    }

    /// 启动文件监控
    pub async fn watch_file<P: AsRef<Path>>(self: Arc<Self>, path: P) -> Result<(), ConfigError> {
        let path = path.as_ref().to_path_buf();
        let (tx, mut rx) = tokio::sync::mpsc::channel(10);

        let mut watcher = RecommendedWatcher::new(
            move |res| {
                if let Ok(event) = res {
                    let _ = tx.blocking_send(event);
                }
            },
            Config::default(),
        )?;

        watcher.watch(&path, RecursiveMode::NonRecursive)?;

        // 处理文件变更
        tokio::spawn(async move {
            while let Some(_event) = rx.recv().await {
                // 防抖处理
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

                if let Err(e) = self.load_from_file(&path).await {
                    eprintln!("Failed to reload config: {}", e);
                } else {
                    println!("Config reloaded successfully");
                }
            }
        });

        Ok(())
    }

    /// 更新单个配置项
    pub async fn update_field<F>(&self, updater: F)
    where
        F: FnOnce(&mut AppConfig),
    {
        let mut config = self.current.write().await;
        updater(&mut config);
        let _ = self.tx.send(config.clone());
    }
}

#[derive(Debug)]
pub enum ConfigError {
    Io(std::io::Error),
    Yaml(serde_yaml::Error),
    Json(serde_json::Error),
    Notify(notify::Error),
}

impl From<std::io::Error> for ConfigError {
    fn from(e: std::io::Error) -> Self { Self::Io(e) }
}

impl From<serde_yaml::Error> for ConfigError {
    fn from(e: serde_yaml::Error) -> Self { Self::Yaml(e) }
}

impl From<serde_json::Error> for ConfigError {
    fn from(e: serde_json::Error) -> Self { Self::Json(e) }
}

impl From<notify::Error> for ConfigError {
    fn from(e: notify::Error) -> Self { Self::Notify(e) }
}
```

---

## 基础设施即代码

### Terraform Provider SDK

```rust
//! Terraform Provider SDK 示例

use serde::{Serialize, Deserialize};
use std::collections::HashMap;

/// Terraform Provider 配置
#[derive(Debug, Clone, Deserialize)]
pub struct ProviderConfig {
    pub endpoint: String,
    pub api_key: String,
    pub timeout: Option<u64>,
}

/// 资源配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceConfig {
    pub id: Option<String>,
    pub name: String,
    pub attributes: HashMap<String, serde_json::Value>,
}

/// Provider 接口
#[async_trait::async_trait]
pub trait TerraformProvider: Send + Sync {
    /// 配置 Provider
    async fn configure(&mut self, config: ProviderConfig) -> Result<(), ProviderError>;

    /// 创建资源
    async fn create_resource(&self, config: &ResourceConfig) -> Result<String, ProviderError>;

    /// 读取资源
    async fn read_resource(&self, id: &str) -> Result<ResourceConfig, ProviderError>;

    /// 更新资源
    async fn update_resource(&self, id: &str, config: &ResourceConfig) -> Result<(), ProviderError>;

    /// 删除资源
    async fn delete_resource(&self, id: &str) -> Result<(), ProviderError>;

    /// 导入资源
    async fn import_resource(&self, id: &str) -> Result<ResourceConfig, ProviderError>;
}

/// 示例：云服务器 Provider
pub struct CloudProvider {
    client: reqwest::Client,
    config: Option<ProviderConfig>,
}

#[derive(Debug)]
pub struct ServerResource {
    pub id: String,
    pub name: String,
    pub instance_type: String,
    pub region: String,
    pub status: String,
}

#[async_trait::async_trait]
impl TerraformProvider for CloudProvider {
    async fn configure(&mut self, config: ProviderConfig) -> Result<(), ProviderError> {
        // 验证配置
        if config.endpoint.is_empty() || config.api_key.is_empty() {
            return Err(ProviderError::InvalidConfig("Missing required fields".to_string()));
        }

        // 测试连接
        let response = self.client
            .get(format!("{}/api/v1/health", config.endpoint))
            .header("Authorization", format!("Bearer {}", config.api_key))
            .send()
            .await?;

        if !response.status().is_success() {
            return Err(ProviderError::ConnectionFailed(
                response.text().await.unwrap_or_default()
            ));
        }

        self.config = Some(config);
        Ok(())
    }

    async fn create_resource(&self, config: &ResourceConfig) -> Result<String, ProviderError> {
        let cfg = self.config.as_ref().ok_or(ProviderError::NotConfigured)?;

        let response = self.client
            .post(format!("{}/api/v1/servers", cfg.endpoint))
            .header("Authorization", format!("Bearer {}", cfg.api_key))
            .json(config)
            .send()
            .await?;

        if response.status().is_success() {
            let result: serde_json::Value = response.json().await?;
            Ok(result["id"].as_str().unwrap_or_default().to_string())
        } else {
            Err(ProviderError::ApiError(response.text().await?))
        }
    }

    async fn read_resource(&self, id: &str) -> Result<ResourceConfig, ProviderError> {
        let cfg = self.config.as_ref().ok_or(ProviderError::NotConfigured)?;

        let response = self.client
            .get(format!("{}/api/v1/servers/{}", cfg.endpoint, id))
            .header("Authorization", format!("Bearer {}", cfg.api_key))
            .send()
            .await?;

        if response.status().is_success() {
            let config: ResourceConfig = response.json().await?;
            Ok(config)
        } else if response.status().as_u16() == 404 {
            Err(ProviderError::ResourceNotFound(id.to_string()))
        } else {
            Err(ProviderError::ApiError(response.text().await?))
        }
    }

    async fn update_resource(&self, id: &str, config: &ResourceConfig) -> Result<(), ProviderError> {
        let cfg = self.config.as_ref().ok_or(ProviderError::NotConfigured)?;

        let response = self.client
            .put(format!("{}/api/v1/servers/{}", cfg.endpoint, id))
            .header("Authorization", format!("Bearer {}", cfg.api_key))
            .json(config)
            .send()
            .await?;

        if response.status().is_success() {
            Ok(())
        } else {
            Err(ProviderError::ApiError(response.text().await?))
        }
    }

    async fn delete_resource(&self, id: &str) -> Result<(), ProviderError> {
        let cfg = self.config.as_ref().ok_or(ProviderError::NotConfigured)?;

        let response = self.client
            .delete(format!("{}/api/v1/servers/{}", cfg.endpoint, id))
            .header("Authorization", format!("Bearer {}", cfg.api_key))
            .send()
            .await?;

        if response.status().is_success() {
            Ok(())
        } else {
            Err(ProviderError::ApiError(response.text().await?))
        }
    }

    async fn import_resource(&self, id: &str) -> Result<ResourceConfig, ProviderError> {
        self.read_resource(id).await
    }
}

#[derive(Debug)]
pub enum ProviderError {
    NotConfigured,
    InvalidConfig(String),
    ConnectionFailed(String),
    ResourceNotFound(String),
    ApiError(String),
    Http(reqwest::Error),
    Json(serde_json::Error),
}

impl From<reqwest::Error> for ProviderError {
    fn from(e: reqwest::Error) -> Self { Self::Http(e) }
}

impl From<serde_json::Error> for ProviderError {
    fn from(e: serde_json::Error) -> Self { Self::Json(e) }
}
```

---

## 最佳实践

### 1. CLI 工具开发

```rust
//! DevOps CLI 工具最佳实践

use clap::{Parser, Subcommand};
use anyhow::Result;
use tracing::{info, error};

#[derive(Parser)]
#[command(name = "devops-cli")]
#[command(about = "A CLI tool for DevOps operations")]
#[command(version = env!("CARGO_PKG_VERSION"))]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    #[arg(short, long, global = true)]
    verbose: bool,

    #[arg(short, long, global = true, default_value = "config.yaml")]
    config: String,
}

#[derive(Subcommand)]
enum Commands {
    /// Deploy application to target environment
    Deploy {
        #[arg(short, long)]
        environment: String,

        #[arg(short, long)]
        version: String,

        #[arg(long)]
        dry_run: bool,
    },

    /// Monitor system metrics
    Monitor {
        #[arg(short, long, default_value = "5")]
        interval: u64,

        #[arg(short, long)]
        format: Option<String>,
    },

    /// Manage configuration
    Config {
        #[command(subcommand)]
        action: ConfigAction,
    },
}

#[derive(Subcommand)]
enum ConfigAction {
    Get { key: String },
    Set { key: String, value: String },
    List,
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();

    // 初始化日志
    let subscriber = tracing_subscriber::fmt()
        .with_max_level(if cli.verbose {
            tracing::Level::DEBUG
        } else {
            tracing::Level::INFO
        })
        .finish();

    tracing::subscriber::set_global_default(subscriber)?;

    match cli.command {
        Commands::Deploy { environment, version, dry_run } => {
            info!("Deploying version {} to {}", version, environment);
            if dry_run {
                println!("Dry run mode - no actual deployment");
            }
            // 部署逻辑...
        }
        Commands::Monitor { interval, format } => {
            info!("Starting monitoring with {}s interval", interval);
            // 监控逻辑...
        }
        Commands::Config { action } => {
            match action {
                ConfigAction::Get { key } => {
                    println!("Getting config: {}", key);
                }
                ConfigAction::Set { key, value } => {
                    println!("Setting {} = {}", key, value);
                }
                ConfigAction::List => {
                    println!("Listing all configs");
                }
            }
        }
    }

    Ok(())
}
```

### 2. 错误处理与重试

```rust
//! 健壮的错误处理和重试机制

use std::time::Duration;
use tokio::time::sleep;
use tracing::{warn, error};

/// 重试配置
#[derive(Debug, Clone)]
pub struct RetryConfig {
    pub max_attempts: u32,
    pub base_delay: Duration,
    pub max_delay: Duration,
    pub exponential_base: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            base_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(30),
            exponential_base: 2.0,
        }
    }
}

/// 带重试的异步操作
pub async fn retry<F, Fut, T, E>(
    operation_name: &str,
    config: &RetryConfig,
    operation: F,
) -> Result<T, E>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
    E: std::fmt::Display,
{
    let mut attempts = 0;
    let mut delay = config.base_delay;

    loop {
        attempts += 1;

        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                if attempts >= config.max_attempts {
                    error!("{} failed after {} attempts: {}", operation_name, attempts, e);
                    return Err(e);
                }

                warn!(
                    "{} failed (attempt {}/{}): {}. Retrying in {:?}...",
                    operation_name, attempts, config.max_attempts, e, delay
                );

                sleep(delay).await;

                // 指数退避
                delay = std::cmp::min(
                    Duration::from_millis(
                        (delay.as_millis() as f64 * config.exponential_base) as u64
                    ),
                    config.max_delay,
                );
            }
        }
    }
}
```

---

## 总结

Rust 在 DevOps 工具开发中提供了独特的优势：

1. **快速启动**: 适合 CLI 工具、短暂运行的作业
2. **低资源占用**: 适合容器化、资源受限环境
3. **单二进制部署**: 易于分发和安装
4. **内存安全**: 减少运行时崩溃和安全漏洞
5. **并发性能**: 高效处理并行任务

通过本文档介绍的技术，开发者可以构建高性能、高可靠性的 DevOps 工具链。
