//! kube-rs 监听 Pod 变更事件示例
//!
//! 运行时需要 Kubernetes 集群与有效的 kubeconfig。默认使用 `KUBECONFIG`
//! 环境变量或 `~/.kube/config`；可通过 `NAMESPACE` 环境变量指定命名空间。
//! 使用 `watcher` 监听 Pod 的 Applied / Deleted / Modified 事件，持续运行直到被中断。
//! 本示例仅做编译检查用，运行时若无集群将连接失败。

use futures::StreamExt;
use k8s_openapi::api::core::v1::Pod;
use kube::runtime::{WatchStreamExt, watcher};
use kube::{Api, Client};
use std::pin::pin;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let namespace = std::env::var("NAMESPACE").unwrap_or_else(|_| "default".into());

    let client = Client::try_default().await?;
    let pods: Api<Pod> = Api::namespaced(client, &namespace);

    let stream = watcher(pods, watcher::Config::default()).applied_objects();
    let mut stream = pin!(stream);
    while let Some(result) = stream.next().await {
        match result {
            Ok(pod) => {
                let name = pod.metadata.name.as_deref().unwrap_or("<unknown>");
                let resource_version = pod.metadata.resource_version.as_deref().unwrap_or("");
                println!("applied pod={} resource_version={}", name, resource_version);
            }
            Err(e) => {
                eprintln!("watch error: {e}");
            }
        }
    }

    Ok(())
}
