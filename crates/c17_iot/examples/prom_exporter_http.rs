use hyper::{Body, Request, Response, Server};
use hyper::service::{make_service_fn, service_fn};
use prometheus::{Encoder, TextEncoder, IntCounter, IntGauge, register_int_counter, register_int_gauge};
use std::convert::Infallible;
use std::net::SocketAddr;
use std::time::Duration;
use tokio::signal;

async fn metrics(_req: Request<Body>) -> Result<Response<Body>, Infallible> {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buf = Vec::new();
    encoder.encode(&metric_families, &mut buf).unwrap();
    Ok(Response::new(Body::from(buf)))
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 注册一些示例指标
    let counter: IntCounter = register_int_counter!("iot_packets_total", "Total packets").unwrap();
    let gauge: IntGauge = register_int_gauge!("iot_temp_c_int", "Temp int").unwrap();
    counter.inc_by(5);
    gauge.set(22);

    // 简单定时更新（后台任务）
    tokio::spawn(async move {
        loop {
            counter.inc();
            gauge.set(((gauge.get() + 1) % 30).max(20));
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    });

    let addr = SocketAddr::from(([127, 0, 0, 1], 9898));
    let make_svc = make_service_fn(|_conn| async {
        Ok::<_, Infallible>(service_fn(|req| async move {
            match req.uri().path() {
                "/metrics" => metrics(req).await,
                _ => Ok(Response::new(Body::from("ok"))),
            }
        }))
    });

    let server = Server::bind(&addr).serve(make_svc);
    println!("metrics listening on http://{}/metrics", addr);

    // 优雅停机：Ctrl+C 触发
    let graceful = server.with_graceful_shutdown(async {
        let _ = signal::ctrl_c().await;
        println!("shutting down...");
    });

    graceful.await?;
    Ok(())
}


