#[cfg(all(feature = "containers"))]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    use c13_reliability::runtime_environments::container_runtime::{ImageReference, ContainerRunConfig, RestartPolicy};
    use c13_reliability::runtime_environments::orchestrator::{LocalContainerOrchestrator, Orchestrator};
    use c13_reliability::runtime_environments::orchestrator_supervisor::{OrchestratorSupervisor, BackoffPolicy};
    #[cfg(feature = "docker-runtime")] use c13_reliability::runtime_environments::container_runtime::docker_local::DockerRuntime;

    let img: ImageReference = "docker.io/library/nginx:latest".parse().unwrap();
    let cfg = ContainerRunConfig {
        image: img,
        args: vec![],
        env: vec![],
        cpu_limit_millis: Some(500),
        memory_limit_bytes: Some(256 * 1024 * 1024),
        restart_policy: Some(RestartPolicy::Always),
        health_probe: None,
    };

    #[cfg(feature = "docker-runtime")]
    let orch = LocalContainerOrchestrator::new(DockerRuntime::new(), cfg);
    #[cfg(not(feature = "docker-runtime"))]
    { println!("Enable --features docker-runtime for runnable supervisor example."); return Ok(()); }

    let sup = OrchestratorSupervisor::new(orch, BackoffPolicy::default());
    sup.ensure_running("nginx").await?;
    Ok(())
}

#[cfg(not(all(feature = "containers")))]
fn main() { println!("Enable --features containers to run this example."); }


