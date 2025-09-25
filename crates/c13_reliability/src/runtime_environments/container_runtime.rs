//! Cloud Native: 容器运行时抽象（CNCF/OCI 对齐）
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use crate::error_handling::UnifiedError;
use std::str::FromStr;

/// 容器镜像引用（兼容 OCI image ref 基本形式）
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ImageReference {
    pub registry: Option<String>,
    pub repository: String,
    pub tag: Option<String>,
    pub digest: Option<String>,
}

impl ImageReference {
    pub fn new(repository: impl Into<String>) -> Self {
        Self { registry: None, repository: repository.into(), tag: None, digest: None }
    }

    pub fn with_tag(mut self, tag: impl Into<String>) -> Self {
        self.tag = Some(tag.into());
        self
    }

    pub fn with_registry(mut self, registry: impl Into<String>) -> Self {
        self.registry = Some(registry.into());
        self
    }

    pub fn with_digest(mut self, digest: impl Into<String>) -> Self {
        self.digest = Some(digest.into());
        self
    }
}

impl FromStr for ImageReference {
    type Err = String;

    // 简易解析：registry.io/ns/repo:tag@sha256:... 的子集
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (name_part, digest_part) = match s.split_once('@') {
            Some((n, d)) => (n, Some(d.to_string())),
            None => (s, None),
        };

        let (name_part, tag_part) = match name_part.rsplit_once(':') {
            Some((left, t)) if !t.contains('/') => (left, Some(t.to_string())),
            _ => (name_part, None),
        };

        let (registry, repository) = match name_part.split_once('/') {
            Some((first, rest)) if first.contains('.') || first.contains(':') || first == "localhost" => {
                (Some(first.to_string()), format!("{rest}"))
            }
            _ => (None, name_part.to_string()),
        };

        Ok(ImageReference { registry, repository, tag: tag_part, digest: digest_part })
    }
}

impl ToString for ImageReference {
    fn to_string(&self) -> String {
        let mut s = String::new();
        if let Some(reg) = &self.registry { s.push_str(reg); s.push('/'); }
        s.push_str(&self.repository);
        if let Some(tag) = &self.tag { s.push(':'); s.push_str(tag); }
        if let Some(d) = &self.digest { s.push('@'); s.push_str(d); }
        s
    }
}

/// 容器 ID
pub type ContainerId = String;

/// 基本容器状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ContainerState {
    Created,
    Running,
    Exited(i32),
    Failed(String),
}

/// 容器运行配置（子集）
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContainerRunConfig {
    pub image: ImageReference,
    pub args: Vec<String>,
    pub env: Vec<(String, String)>,
    pub cpu_limit_millis: Option<u64>,
    pub memory_limit_bytes: Option<u64>,
    pub restart_policy: Option<RestartPolicy>,
    pub health_probe: Option<HealthProbe>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RestartPolicy {
    Never,
    OnFailure { max_retries: u32, backoff_secs: u64 },
    Always,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthProbe {
    pub initial_delay_secs: u64,
    pub period_secs: u64,
    pub timeout_secs: u64,
}

/// 容器事件（用于上报与监控）
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ContainerEvent {
    Started(ContainerId),
    Stopped(ContainerId, i32),
    Crashed(ContainerId, String),
    Unhealthy(ContainerId, String),
    Healthy(ContainerId),
}

/// CNCF/CRI 风格的容器运行时抽象
#[async_trait]
pub trait ContainerRuntime: Send + Sync {
    async fn pull_image(&self, image: &ImageReference) -> Result<(), UnifiedError>;
    async fn run(&self, cfg: &ContainerRunConfig) -> Result<ContainerId, UnifiedError>;
    async fn stop(&self, id: &ContainerId) -> Result<(), UnifiedError>;
    async fn inspect(&self, id: &ContainerId) -> Result<ContainerState, UnifiedError>;
}

/// 本地 Docker 运行时的占位实现（可选 feature: docker-runtime）
#[cfg(feature = "docker-runtime")]
pub mod docker_local {
    use super::*;

    pub struct DockerRuntime;

    impl DockerRuntime {
        pub fn new() -> Self { Self }
    }

    #[async_trait]
    impl ContainerRuntime for DockerRuntime {
        async fn pull_image(&self, _image: &ImageReference) -> Result<(), UnifiedError> {
            Ok(())
        }
        async fn run(&self, _cfg: &ContainerRunConfig) -> Result<ContainerId, UnifiedError> {
            Ok("container-123".to_string())
        }
        async fn stop(&self, _id: &ContainerId) -> Result<(), UnifiedError> { Ok(()) }
        async fn inspect(&self, _id: &ContainerId) -> Result<ContainerState, UnifiedError> {
            Ok(ContainerState::Running)
        }
    }
}


