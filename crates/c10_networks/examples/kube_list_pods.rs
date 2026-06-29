//! kube-rs 查询 Pod 列表示例
//!
//! 运行时需要 Kubernetes 集群与有效的 kubeconfig。默认使用 `KUBECONFIG`
//! 环境变量或 `~/.kube/config`；可通过 `NAMESPACE` 环境变量指定命名空间。
//! 本示例仅做编译检查用，运行时若无集群将连接失败。

use k8s_openapi::api::core::v1::Pod;
use kube::{api::ListParams, Api, Client};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let namespace = std::env::var("NAMESPACE").unwrap_or_else(|_| "default".into());

    let client = Client::try_default().await?;
    let pods: Api<Pod> = Api::namespaced(client, &namespace);

    let list = pods.list(&ListParams::default().limit(10)).await?;
    println!("namespace={} pod_count={}", namespace, list.items.len());
    for pod in &list.items {
        let name = pod.metadata.name.as_deref().unwrap_or("<unknown>");
        let phase = pod
            .status
            .as_ref()
            .and_then(|s| s.phase.as_deref())
            .unwrap_or("<unknown>");
        println!("  pod={} phase={}", name, phase);
    }

    Ok(())
}
