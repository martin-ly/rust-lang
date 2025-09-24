#[cfg(feature = "obs-tracing")]
use tracing::{info, info_span, Instrument};
#[cfg(feature = "obs-tracing")]
use tracing_subscriber::{fmt, EnvFilter};

#[cfg(feature = "obs-tracing")]
async fn chain_process(input: &str) -> String {
    let span = info_span!("chain", request = input);
    async move {
        let s1 = step("auth", input).await;
        let s2 = step("rate", &s1).await;
        step("biz", &s2).await
    }
    .instrument(span)
    .await
}

#[cfg(feature = "obs-tracing")]
async fn step(tag: &str, v: &str) -> String {
    info!(stage = tag, "handling");
    format!("{}:{}", tag, v)
}

#[cfg(feature = "obs-tracing")]
fn init_tracing() {
    let filter = EnvFilter::try_from_default_env()
        .unwrap_or_else(|_| EnvFilter::new("info"));
    let subscriber = fmt().with_env_filter(filter).finish();
    tracing::subscriber::set_global_default(subscriber).ok();
}

#[cfg(feature = "obs-tracing")]
#[tokio::main]
async fn main() {
    init_tracing();
    let out = chain_process("request-1").await;
    println!("out={}", out);
}

#[cfg(not(feature = "obs-tracing"))]
fn main() {
    eprintln!(
        "This example requires feature 'obs-tracing'.\nRun with: cargo run --example tracing_chain --features obs-tracing"
    );
}