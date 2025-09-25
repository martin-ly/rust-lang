#[cfg(all(feature = "containers"))]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    use c13_reliability::runtime_environments::orchestrator::{Orchestrator, LocalContainerOrchestrator, WorkloadStatus};
    use c13_reliability::runtime_environments::container_runtime::{ImageReference, ContainerRunConfig, RestartPolicy};
    #[cfg(feature = "docker-runtime")] use c13_reliability::runtime_environments::container_runtime::docker_local::DockerRuntime;

    let img: ImageReference = "docker.io/library/nginx:latest".parse().unwrap();
    let cfg = ContainerRunConfig {
        image: img,
        args: vec![],
        env: vec![],
        cpu_limit_millis: Some(500),
        memory_limit_bytes: Some(256 * 1024 * 1024),
        restart_policy: Some(RestartPolicy::OnFailure { max_retries: 3, backoff_secs: 5 }),
        health_probe: None,
    };

    #[cfg(feature = "docker-runtime")]
    let orch = LocalContainerOrchestrator::new(DockerRuntime::new(), cfg);
    #[cfg(not(feature = "docker-runtime"))]
    {
        println!("Enable --features docker-runtime for runnable orchestrator example.");
        let _ = cfg; // silence unused warnings
        return Ok(());
    }

    #[cfg(feature = "docker-runtime")]
    {
        orch.deploy("nginx").await?;
        let st = orch.status("nginx").await?;
        println!("status: {:?}", st);
        orch.terminate("nginx").await?;
        if matches!(st, WorkloadStatus::Running | WorkloadStatus::Pending | WorkloadStatus::Succeeded | WorkloadStatus::Failed(_)) {}
        Ok(())
    }
}

#[cfg(not(all(feature = "containers")))]
fn main() { println!("Enable --features containers to run this example."); }


