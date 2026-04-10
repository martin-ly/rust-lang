use tracing::{Instrument, info, info_span};
use tracing_subscriber::{EnvFilter, fmt};

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

async fn step(tag: &str, v: &str) -> String {
    info!(stage = tag, "handling");
    format!("{}:{}", tag, v)
}

fn init_tracing() {
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    let subscriber = fmt().with_env_filter(filter).finish();
    tracing::subscriber::set_global_default(subscriber).ok();
}

#[tokio::main]
async fn main() {
    init_tracing();
    let out = chain_process("request-1").await;
    println!("out={}", out);
}
