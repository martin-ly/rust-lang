use actix_web::{get, post, web, App, HttpServer, Responder, middleware::Logger};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};
use c06_async::utils;

// 扩展指标结构
#[derive(Default)]
struct Metrics {
    total_requests: AtomicU64,
    total_latency: AtomicU64,
    error_count: AtomicU64,
    slow_requests: AtomicU64,
}

impl Metrics {
    fn record_request(&self, latency: Duration, is_error: bool, is_slow: bool) {
        self.total_requests.fetch_add(1, Ordering::Relaxed);
        self.total_latency.fetch_add(latency.as_nanos() as u64, Ordering::Relaxed);
        if is_error {
            self.error_count.fetch_add(1, Ordering::Relaxed);
        }
        if is_slow {
            self.slow_requests.fetch_add(1, Ordering::Relaxed);
        }
    }

    fn get_avg_latency(&self) -> f64 {
        let total = self.total_requests.load(Ordering::Relaxed);
        if total == 0 {
            0.0
        } else {
            self.total_latency.load(Ordering::Relaxed) as f64 / total as f64
        }
    }

    fn get_error_rate(&self) -> f64 {
        let total = self.total_requests.load(Ordering::Relaxed);
        if total == 0 {
            0.0
        } else {
            self.error_count.load(Ordering::Relaxed) as f64 / total as f64 * 100.0
        }
    }
}

#[get("/greet/{name}")]
async fn greet(name: web::Path<String>) -> impl Responder {
    format!("Hello, {}!", name)
}

#[get("/greet2/{name}")]
async fn greet2(name: web::Path<String>, metrics: web::Data<Metrics>) -> impl Responder {
    let start = Instant::now();
    let response = format!("Hello, {}!", name);
    let latency = start.elapsed();
    
    metrics.record_request(latency, false, false);
    
    response
}

#[post("/slow")]
async fn slow_endpoint(metrics: web::Data<Metrics>) -> impl Responder {
    let start = Instant::now();
    
    // 使用 SemaphoreLimiter 进行限流
    let limiter = utils::SemaphoreLimiter::new(2);
    
    let result = utils::with_timeout(
        Duration::from_secs(5),
        limiter.run(async {
            tokio::time::sleep(Duration::from_millis(200)).await;
        })
    ).await;

    let latency = start.elapsed();
    let is_error = result.is_none(); // timeout 表示错误
    let is_slow = latency > Duration::from_secs(1);
    
    metrics.record_request(latency, is_error, is_slow);

    match result {
        Some(_) => {
            if is_slow {
                format!("Slow request completed in {:?}", latency)
            } else {
                format!("Request completed in {:?}", latency)
            }
        }
        None => {
            "Request failed or timed out".to_string()
        }
    }
}

#[get("/metrics")]
async fn metrics_handler(metrics: web::Data<Metrics>) -> impl Responder {
    let total_requests = metrics.total_requests.load(Ordering::Relaxed);
    let total_latency = metrics.total_latency.load(Ordering::Relaxed);
    let error_count = metrics.error_count.load(Ordering::Relaxed);
    let slow_requests = metrics.slow_requests.load(Ordering::Relaxed);
    let avg_latency = metrics.get_avg_latency();
    let error_rate = metrics.get_error_rate();

    let prometheus_output = format!(
        "# HELP http_requests_total Total number of HTTP requests
# TYPE http_requests_total counter
http_requests_total {total_requests}

# HELP http_request_duration_nanoseconds_total Total duration of all requests in nanoseconds
# TYPE http_request_duration_nanoseconds_total counter
http_request_duration_nanoseconds_total {total_latency}

# HELP http_requests_errors_total Total number of HTTP requests that resulted in errors
# TYPE http_requests_errors_total counter
http_requests_errors_total {error_count}

# HELP http_slow_requests_total Total number of slow requests (>1s)
# TYPE http_slow_requests_total counter
http_slow_requests_total {slow_requests}

# HELP http_request_duration_average_nanoseconds Average duration of requests in nanoseconds
# TYPE http_request_duration_average_nanoseconds gauge
http_request_duration_average_nanoseconds {avg_latency}

# HELP http_error_rate_percentage Error rate as a percentage
# TYPE http_error_rate_percentage gauge
http_error_rate_percentage {error_rate}
"
    );

    actix_web::HttpResponse::Ok()
        .content_type("text/plain; version=0.0.4; charset=utf-8")
        .body(prometheus_output)
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    env_logger::init_from_env(env_logger::Env::new().default_filter_or("info"));
    
    let metrics = web::Data::new(Metrics::default());
    
    println!("🚀 Actix Web 服务器启动在 http://127.0.0.1:8080");
    println!("📊 指标端点: http://127.0.0.1:8080/metrics");
    println!("🐌 慢速端点: http://127.0.0.1:8080/slow");
    println!("👋 问候端点: http://127.0.0.1:8080/greet/YourName");
    
    HttpServer::new(move || {
        App::new()
            .wrap(Logger::default())
            .app_data(metrics.clone())
            .service(greet)
            .service(greet2)
            .service(slow_endpoint)
            .service(metrics_handler)
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
