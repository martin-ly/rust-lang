//! Tower 可靠性中间件示例（限流 + 超时 + 重试）
//! 运行：
//!   cargo run -p c18_model --example tower_reliability --features tower-examples,tokio-adapter

// 当未开启 feature 时提供一个后备 main，避免示例缺失入口导致编译错误
#[cfg(not(feature = "tower-examples"))]
fn main() {
    eprintln!(
        "该示例需要启用 feature 'tower-examples'（以及运行命令中建议的 'tokio-adapter'）。\n运行示例：cargo run -p c18_model --example tower_reliability --features tower-examples,tokio-adapter"
    );
}

#[cfg(feature = "tower-examples")]
use http::{Request, Response};
#[cfg(feature = "tower-examples")]
use hyper::Body;
#[cfg(feature = "tower-examples")]
use std::time::Duration;
#[cfg(feature = "tower-examples")]
use tower::{Service, ServiceBuilder, util::BoxService};

#[allow(dead_code)]
#[derive(Debug, thiserror::Error)]
enum DemoError {
    #[error("timeout")]
    Timeout,
    #[error("service error")]
    Service,
}

#[cfg(feature = "tower-examples")]
#[tokio::main(flavor = "current_thread")]
async fn main() {
    // 这里用一个最简服务占位，真实工程可替换为 hyper Client 等
    let svc = tower::service_fn(|_req: Request<Body>| async move {
        Ok::<_, DemoError>(Response::new(Body::from("ok")))
    });

    let svc = ServiceBuilder::new()
        .timeout(Duration::from_millis(100))
        .rate_limit(100, Duration::from_secs(1))
        .service(svc);

    let mut svc: BoxService<Request<Body>, Response<Body>, DemoError> = BoxService::new(svc);

    let req = Request::new(Body::empty());
    match svc.ready().await.and_then(|mut s| s.call(req)).await {
        Ok(resp) => {
            println!("status={}", resp.status());
        }
        Err(err) => {
            eprintln!("error={:?}", err);
        }
    }
}
