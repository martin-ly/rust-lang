use opentelemetry::{global, trace::Tracer};
use opentelemetry_sdk::{trace as sdktrace, Resource};
use opentelemetry::KeyValue;

fn init_tracer() -> anyhow::Result<sdktrace::TracerProvider> {
    // 使用默认的无导出 Provider，避免依赖额外特性/导出器
    let provider = sdktrace::TracerProvider::builder()
        .with_config(sdktrace::Config::default().with_resource(Resource::new(vec![
            KeyValue::new("service.name", "c17-iot-otel"),
        ])))
        .build();
    Ok(provider)
}

fn main() -> anyhow::Result<()> {
    let provider = init_tracer()?;
    let _guard = global::set_tracer_provider(provider);
    let tracer = global::tracer("c17-iot-example");

    let _span = tracer.start("edge-collect");
    // 模拟一次边缘采集与处理
    std::thread::sleep(std::time::Duration::from_millis(50));
    drop(_span);

    // 关闭并刷新
    global::shutdown_tracer_provider();
    Ok(())
}


