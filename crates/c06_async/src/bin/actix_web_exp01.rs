use actix_web::{App, HttpResponse, HttpServer, Responder, web, middleware::Logger};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use c06_async::utils::{SemaphoreLimiter, with_timeout};

struct Metrics {
    requests: AtomicU64,
    total_ns: AtomicU64,
}

// 定义一个处理函数
async fn greet(name: web::Path<String>) -> impl Responder {
    HttpResponse::Ok().body(format!("Hello, {}!", name))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    env_logger::init();
    let limiter = SemaphoreLimiter::new(64);
    let metrics = Arc::new(Metrics { requests: AtomicU64::new(0), total_ns: AtomicU64::new(0) });

    // 启动 HTTP 服务器
    let limiter_data = limiter.clone();
    let metrics_data = Arc::clone(&metrics);
    HttpServer::new(move || {
        let limiter = limiter_data.clone();
        let metrics = Arc::clone(&metrics_data);
        App::new()
            .wrap(Logger::default())
            .app_data(web::Data::new(limiter))
            .app_data(web::Data::new(metrics))
            .route("/greet/{name}", web::get().to(greet))
            .route("/greet2/{name}", web::get().to(greet_with_metrics))
            .route("/slow", web::get().to(slow_handler))
            .route("/metrics", web::get().to(metrics_handler))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}

async fn slow_handler(limiter: web::Data<SemaphoreLimiter>, metrics: web::Data<Arc<Metrics>>) -> impl Responder {
    // 每个请求受限流；并设置超时保护
    let fut = limiter.run(async move {
        let start = std::time::Instant::now();
        tokio::time::sleep(Duration::from_millis(200)).await;
        let dur = start.elapsed().as_nanos() as u64;
        metrics.total_ns.fetch_add(dur, Ordering::Relaxed);
        metrics.requests.fetch_add(1, Ordering::Relaxed);
        HttpResponse::Ok().body("slow ok")
    });
    match with_timeout(Duration::from_millis(150), fut).await {
        Some(resp) => resp,
        None => HttpResponse::GatewayTimeout().body("timeout"),
    }
}

async fn metrics_handler(metrics: web::Data<Arc<Metrics>>) -> impl Responder {
    let total = metrics.requests.load(Ordering::Relaxed);
    let ns = metrics.total_ns.load(Ordering::Relaxed);
    let avg_ns = if total > 0 { ns / total } else { 0 };
    let body = format!(
        "# HELP http_requests_total Total HTTP requests\n# TYPE http_requests_total counter\nhttp_requests_total {}\n# HELP http_avg_latency_ns Average latency in nanoseconds\n# TYPE http_avg_latency_ns gauge\nhttp_avg_latency_ns {}\n",
        total, avg_ns
    );
    HttpResponse::Ok()
        .content_type("text/plain; version=0.0.4")
        .body(body)
}

// 简单请求计数中间件示例（可扩展为真正的中间件）
#[allow(dead_code)]
async fn greet_counted(path: web::Path<String>, metrics: web::Data<Arc<Metrics>>) -> impl Responder {
    metrics.requests.fetch_add(1, Ordering::Relaxed);
    greet(path).await
}

async fn greet_with_metrics(path: web::Path<String>, metrics: web::Data<Arc<Metrics>>) -> impl Responder {
    let start = std::time::Instant::now();
    let body = format!("Hello, {}!", path.into_inner());
    let dur = start.elapsed().as_nanos() as u64;
    metrics.total_ns.fetch_add(dur, Ordering::Relaxed);
    metrics.requests.fetch_add(1, Ordering::Relaxed);
    HttpResponse::Ok().body(body)
}
