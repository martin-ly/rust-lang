use opentelemetry::{global, trace::Tracer, KeyValue};
use opentelemetry_otlp::WithExportConfig;
use opentelemetry_sdk::{trace as sdktrace, Resource};
use std::time::Duration;

fn init_tracer() -> anyhow::Result<sdktrace::TracerProvider> {
    // 默认指向本地 compose 内 Jaeger OTLP gRPC 4317
    let endpoint = std::env::var("OTLP_ENDPOINT").unwrap_or_else(|_| "http://127.0.0.1:4317".into());

    let exporter = opentelemetry_otlp::new_exporter()
        .tonic()
        .with_endpoint(endpoint)
        .build_span_exporter()?;

    let provider = sdktrace::TracerProvider::builder()
        .with_config(sdktrace::Config::default().with_resource(Resource::new(vec![
            KeyValue::new("service.name", "c17-iot-jaeger"),
        ])))
        .with_batch_exporter(exporter, opentelemetry_sdk::runtime::Tokio)
        .build();
    Ok(provider)
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let provider = init_tracer()?;
    let _guard = global::set_tracer_provider(provider);
    let tracer = global::tracer("c17-iot-otel");

    let span = tracer.start("edge-process");
    tokio::time::sleep(Duration::from_millis(80)).await;
    drop(span);

    let shutdown_ms: u64 = std::env::var("OTLP_SHUTDOWN_MS").ok().and_then(|v| v.parse().ok()).unwrap_or(500);
    global::shutdown_tracer_provider();
    tokio::time::sleep(Duration::from_millis(shutdown_ms)).await;
    Ok(())
}


