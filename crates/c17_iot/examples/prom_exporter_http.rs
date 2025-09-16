use hyper::body::Incoming;
use hyper::service::service_fn;
use hyper::{Method, Request, Response, StatusCode};
use hyper_util::rt::TokioExecutor;
use hyper_util::server::conn::auto::Builder;
use hyper_util::rt::TokioIo;
use prometheus::{Encoder, TextEncoder, IntCounter, IntGauge, register_int_counter, register_int_gauge};
use std::convert::Infallible;
use std::net::SocketAddr;
use std::time::Duration;
use tokio::net::TcpListener;
use tokio::signal;

async fn metrics(_req: Request<Incoming>) -> Result<Response<String>, Infallible> {
    let encoder = TextEncoder::new();
    let metric_families = prometheus::gather();
    let mut buf = Vec::new();
    encoder.encode(&metric_families, &mut buf).unwrap();
    Ok(Response::new(String::from_utf8(buf).unwrap()))
}

async fn handle_request(req: Request<Incoming>) -> Result<Response<String>, Infallible> {
    match (req.method(), req.uri().path()) {
        (&Method::GET, "/metrics") => metrics(req).await,
        _ => {
            let mut response = Response::new("ok".to_string());
            *response.status_mut() = StatusCode::OK;
            Ok(response)
        }
    }
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
    let listener = TcpListener::bind(addr).await?;
    println!("metrics listening on http://{}/metrics", addr);

    loop {
        tokio::select! {
            result = listener.accept() => {
                match result {
                    Ok((stream, _)) => {
                        let service = service_fn(handle_request);
                        tokio::task::spawn(async move {
                            let io = TokioIo::new(stream);
                            if let Err(err) = Builder::new(TokioExecutor::new())
                                .serve_connection(io, service)
                                .await
                            {
                                eprintln!("Error serving connection: {:?}", err);
                            }
                        });
                    }
                    Err(e) => {
                        eprintln!("Failed to accept connection: {}", e);
                    }
                }
            }
            _ = signal::ctrl_c() => {
                println!("shutting down...");
                break;
            }
        }
    }

    Ok(())
}


