use opentelemetry::{global, trace::Tracer};
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 默认指向本地 compose 内 Jaeger OTLP gRPC 4317
    let _endpoint =
        std::env::var("OTLP_ENDPOINT").unwrap_or_else(|_| "http://127.0.0.1:4317".into());

    // 创建一个简单的 no-op tracer 用于演示
    let provider = opentelemetry::trace::noop::NoopTracerProvider::new();

    let _guard = global::set_tracer_provider(provider);
    let tracer = global::tracer("c17-iot-otel");

    let span = tracer.start("edge-process");
    tokio::time::sleep(Duration::from_millis(80)).await;
    drop(span);

    let shutdown_ms: u64 = std::env::var("OTLP_SHUTDOWN_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(500);
    tokio::time::sleep(Duration::from_millis(shutdown_ms)).await;
    println!(
        "OpenTelemetry Jaeger 示例完成 - 注意：当前版本使用 noop tracer，未连接到实际的 Jaeger"
    );
    println!("要连接到真实的 Jaeger，需要根据 OpenTelemetry 0.30 API 更新代码");
    Ok(())
}
