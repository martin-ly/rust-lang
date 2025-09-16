use opentelemetry::{global, trace::Tracer};
use std::time::Duration;

fn main() -> anyhow::Result<()> {
    // 使用 noop tracer provider 避免 API 兼容性问题
    let provider = opentelemetry::trace::noop::NoopTracerProvider::new();
    let _guard = global::set_tracer_provider(provider);
    let tracer = global::tracer("c17-iot-example");

    let _span = tracer.start("edge-collect");
    // 模拟一次边缘采集与处理
    std::thread::sleep(Duration::from_millis(50));
    drop(_span);

    println!("OpenTelemetry stdout 示例完成 - 注意：当前版本使用 noop tracer");
    println!("要输出到 stdout，需要根据 OpenTelemetry 0.30 API 更新代码");
    Ok(())
}
