use std::time::Duration;
use tracing::{info, instrument, Level};

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    // 安装 tracing subscriber 和 console 层（如果 tokio-console 已启用）
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_max_level(Level::INFO)
        .finish();
    tracing::subscriber::set_global_default(subscriber).ok();

    info!("startup");
    job_a().await;
    job_b().await;
}

#[instrument]
async fn job_a() {
    info!("job_a begin");
    tokio::time::sleep(Duration::from_millis(120)).await;
    info!("job_a end");
}

#[instrument]
async fn job_b() {
    let h1 = tokio::spawn(async {
        tokio::time::sleep(Duration::from_millis(50)).await;
        info!("sub-1 done");
    });
    let h2 = tokio::spawn(async {
        tokio::time::sleep(Duration::from_millis(80)).await;
        info!("sub-2 done");
    });
    let _ = tokio::join!(h1, h2);
}


