//! 统一编排抽象：可在本地容器运行时与 Kubernetes 之间切换
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use crate::error_handling::UnifiedError;

#[cfg(feature = "containers")]
use super::container_runtime::{ContainerRunConfig, ContainerRuntime, ContainerState, ContainerId};
#[cfg(feature = "kubernetes")]
use super::kubernetes::{PodSpecMini, KubernetesClientPlaceholder};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WorkloadStatus {
    Pending,
    Running,
    Succeeded,
    Failed(String),
}

#[async_trait]
pub trait Orchestrator: Send + Sync {
    async fn deploy(&self, name: &str) -> Result<(), UnifiedError>;
    async fn terminate(&self, name: &str) -> Result<(), UnifiedError>;
    async fn status(&self, name: &str) -> Result<WorkloadStatus, UnifiedError>;
}

/// 本地容器编排：基于容器运行时（CRI/OCI 抽象）
#[cfg(feature = "containers")]
pub struct LocalContainerOrchestrator<R: ContainerRuntime> {
    runtime: R,
    config: ContainerRunConfig,
    last_id: std::sync::Mutex<Option<ContainerId>>,
}

#[cfg(feature = "containers")]
impl<R: ContainerRuntime> LocalContainerOrchestrator<R> {
    pub fn new(runtime: R, config: ContainerRunConfig) -> Self {
        Self { runtime, config, last_id: std::sync::Mutex::new(None) }
    }
}

#[cfg(feature = "containers")]
#[async_trait]
impl<R: ContainerRuntime + Send + Sync> Orchestrator for LocalContainerOrchestrator<R> {
    async fn deploy(&self, _name: &str) -> Result<(), UnifiedError> {
        self.runtime.pull_image(&self.config.image).await?;
        let id = self.runtime.run(&self.config).await?;
        *self.last_id.lock().unwrap() = Some(id);
        Ok(())
    }

    async fn terminate(&self, _name: &str) -> Result<(), UnifiedError> {
        if let Some(id) = self.last_id.lock().unwrap().clone() {
            self.runtime.stop(&id).await?;
        }
        Ok(())
    }

    async fn status(&self, _name: &str) -> Result<WorkloadStatus, UnifiedError> {
        if let Some(id) = self.last_id.lock().unwrap().clone() {
            match self.runtime.inspect(&id).await? {
                ContainerState::Created => Ok(WorkloadStatus::Pending),
                ContainerState::Running => Ok(WorkloadStatus::Running),
                ContainerState::Exited(code) if code == 0 => Ok(WorkloadStatus::Succeeded),
                ContainerState::Exited(code) => Ok(WorkloadStatus::Failed(format!("exit code {code}"))),
                ContainerState::Failed(e) => Ok(WorkloadStatus::Failed(e)),
            }
        } else {
            Ok(WorkloadStatus::Pending)
        }
    }
}

/// Kubernetes 编排：基于占位客户端（后续可替换为 kube-rs）
#[cfg(feature = "kubernetes")]
pub struct KubernetesOrchestrator {
    client: KubernetesClientPlaceholder,
    namespace: String,
    pod: PodSpecMini,
}

#[cfg(feature = "kubernetes")]
impl KubernetesOrchestrator {
    pub fn new(namespace: impl Into<String>, pod: PodSpecMini) -> Self {
        Self { client: KubernetesClientPlaceholder::new(), namespace: namespace.into(), pod }
    }
}

#[cfg(feature = "kubernetes")]
#[async_trait]
impl Orchestrator for KubernetesOrchestrator {
    async fn deploy(&self, _name: &str) -> Result<(), UnifiedError> {
        self.client.apply_pod(&self.namespace, &self.pod).await.map_err(|e| UnifiedError::new(
            &format!("k8s apply failed: {e}"),
            crate::error_handling::ErrorSeverity::High,
            "kubernetes",
            crate::error_handling::ErrorContext::new("kubernetes","apply_pod", file!(), line!(), crate::error_handling::ErrorSeverity::High, "kubernetes")
        ))
    }

    async fn terminate(&self, _name: &str) -> Result<(), UnifiedError> {
        self.client.delete_pod(&self.namespace, &self.pod.name).await.map_err(|e| UnifiedError::new(
            &format!("k8s delete failed: {e}"),
            crate::error_handling::ErrorSeverity::High,
            "kubernetes",
            crate::error_handling::ErrorContext::new("kubernetes","delete_pod", file!(), line!(), crate::error_handling::ErrorSeverity::High, "kubernetes")
        ))
    }

    async fn status(&self, _name: &str) -> Result<WorkloadStatus, UnifiedError> {
        // 占位：真实实现应查询 Pod 状态
        Ok(WorkloadStatus::Running)
    }
}


