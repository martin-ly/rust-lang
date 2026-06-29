//! sentry 错误捕获、面包屑与性能监控示例
//!
//! 运行时需要 Sentry DSN。默认使用占位 DSN；可通过 `SENTRY_DSN` 环境变量覆盖。
//! 本示例仅做编译检查用，若 DSN 无效则事件不会真正上报。

use sentry::{ClientOptions, Level};
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let dsn = std::env::var("SENTRY_DSN")
        .unwrap_or_else(|_| "https://public@sentry.example.com/1".into());

    let _guard = sentry::init((
        dsn,
        ClientOptions {
            release: sentry::release_name!(),
            ..Default::default()
        },
    ));

    sentry::capture_message("Sentry integration demo started", Level::Info);

    sentry::configure_scope(|scope| {
        scope.set_tag("component", "c06_async_demo");
        scope.set_user(Some(sentry::User {
            username: Some("demo".into()),
            ..Default::default()
        }));
    });

    if let Err(e) = fallible_operation().await {
        sentry::capture_error(&e);
    }

    let tx_ctx = sentry::TransactionContext::new("demo_transaction", "demo_operation");
    let transaction = sentry::start_transaction(tx_ctx);
    {
        let _span = transaction.start_child("compute", "simulate_work");
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    transaction.finish();

    Ok(())
}

async fn fallible_operation() -> Result<(), std::io::Error> {
    Err(std::io::Error::other(
        "simulated failure for Sentry capture",
    ))
}
