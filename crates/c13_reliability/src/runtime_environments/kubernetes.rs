//! Cloud Native: Kubernetes 编排抽象（轻量占位，后续可接入 kube-rs）
use serde::{Deserialize, Serialize};
#[cfg(feature = "containers")]
use super::container_runtime::{ContainerRunConfig, HealthProbe};

/// K8s 探针配置（与容器健康探针对齐）
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KubernetesProbeSpec {
    pub initial_delay_secs: u64,
    pub period_secs: u64,
    pub timeout_secs: u64,
}

/// K8s Pod 期望状态（子集）
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PodSpecMini {
    pub name: String,
    pub image: String,
    pub args: Vec<String>,
    pub env: Vec<(String, String)>,
    pub cpu_millis: Option<u64>,
    pub memory_bytes: Option<u64>,
    pub liveness: Option<KubernetesProbeSpec>,
    pub readiness: Option<KubernetesProbeSpec>,
}

/// 轻量客户端接口（后续以 kube-rs 实现）
#[derive(Debug, Clone)]
pub struct KubernetesClientPlaceholder;

impl KubernetesClientPlaceholder {
    pub fn new() -> Self { Self }
    pub async fn apply_pod(&self, _ns: &str, _pod: &PodSpecMini) -> anyhow::Result<()> { Ok(()) }
    pub async fn delete_pod(&self, _ns: &str, _name: &str) -> anyhow::Result<()> { Ok(()) }
}

#[cfg(feature = "containers")]
impl From<&ContainerRunConfig> for PodSpecMini {
    fn from(cfg: &ContainerRunConfig) -> Self {
        let (l, r) = cfg.health_probe.as_ref().map(|p| {
            (
                KubernetesProbeSpec { initial_delay_secs: p.initial_delay_secs, period_secs: p.period_secs, timeout_secs: p.timeout_secs },
                KubernetesProbeSpec { initial_delay_secs: p.initial_delay_secs, period_secs: p.period_secs, timeout_secs: p.timeout_secs },
            )
        }).unwrap_or((
            KubernetesProbeSpec { initial_delay_secs: 0, period_secs: 10, timeout_secs: 1 },
            KubernetesProbeSpec { initial_delay_secs: 0, period_secs: 10, timeout_secs: 1 },
        ));

        PodSpecMini {
            name: "c13-pod".to_string(),
            image: cfg.image.to_string(),
            args: cfg.args.clone(),
            env: cfg.env.clone(),
            cpu_millis: cfg.cpu_limit_millis,
            memory_bytes: cfg.memory_limit_bytes,
            liveness: Some(l),
            readiness: Some(r),
        }
    }
}


