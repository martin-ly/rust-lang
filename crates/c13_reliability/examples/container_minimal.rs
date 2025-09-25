#[cfg(all(feature = "containers"))]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    use c13_reliability::runtime_environments::container_runtime::{ImageReference, ContainerRunConfig, RestartPolicy};

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

    // 仅验证类型与编译，不实际运行容器
    let _ = cfg;
    Ok(())
}

#[cfg(not(all(feature = "containers")))]
fn main() { println!("Enable --features containers to run this example."); }


