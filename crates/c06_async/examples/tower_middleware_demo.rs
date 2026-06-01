//! Tower 中间件栈演示
//! Tower middleware stack demonstration
//! - Service trait: 异步请求-响应处理
//! - Service trait: async -
//!
//! 运行:
//! cargo run --example tower_middleware_demo -p c06_async

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;
use tokio::time::sleep;
use tower::{Service, ServiceBuilder, ServiceExt};

// ============================================================
// 1. 自定义 Service: 模拟后端 API 调用
// ============================================================

#[derive(Clone)]
struct ApiService {
    name: String,
    fail_every_n: usize,
    latency_ms: u64,
    counter: std::sync::Arc<std::sync::atomic::AtomicUsize>,
}

impl ApiService {
    fn new(name: &str, fail_every_n: usize, latency_ms: u64) -> Self {
        Self {
            name: name.to_string(),
            fail_every_n,
            latency_ms,
            counter: std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0)),
        }
    }
}

#[derive(Clone, Debug)]
struct ApiRequest {
    payload: String,
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
struct ApiResponse {
    status: u16,
    body: String,
}

impl Service<ApiRequest> for ApiService {
    type Response = ApiResponse;
    type Error = String;
    type Future = Pin<Box<dyn Future<Output = Result<Self::Response, Self::Error>> + Send>>;

    fn poll_ready(&mut self, _cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        Poll::Ready(Ok(()))
    }

    fn call(&mut self, req: ApiRequest) -> Self::Future {
        let name = self.name.clone();
        let latency = self.latency_ms;
        let count = self
            .counter
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let fail_every = self.fail_every_n;

        Box::pin(async move {
            sleep(Duration::from_millis(latency)).await;
            if fail_every > 0 && count % fail_every == (fail_every - 1) {
                return Err(format!("{}: 模拟故障 (#{})", name, count));
            }
            Ok(ApiResponse {
                status: 200,
                body: format!("{} 处理成功: {:?}", name, req.payload),
            })
        })
    }
}

// ============================================================
// 2. 演示: 纯 Service 调用
// ============================================================

async fn demo_basic_service() {
    println!("=== 基础 Service 调用 ===");
    let mut api = ApiService::new("基础API", 0, 10);
    let req = ApiRequest {
        payload: "hello".to_string(),
    };
    let res = api.call(req).await.unwrap();
    println!("✅ 直接调用结果: {:?}\n", res);
}

// ============================================================
// 3. 演示: ServiceBuilder 链式组合
// ============================================================

async fn demo_service_builder() {
    println!("=== ServiceBuilder 中间件栈 ===");

    let api = ApiService::new("组合API", 0, 50);

    let mut service = ServiceBuilder::new()
        .timeout(Duration::from_millis(100))
        .rate_limit(5, Duration::from_secs(1))
        .service(api);

    for i in 0..3 {
        let req = ApiRequest {
            payload: format!("msg-{}", i),
        };
        match service.ready().await.unwrap().call(req).await {
            Ok(resp) => println!("  请求 {} 成功: {}\n", i, resp.body),
            Err(e) => println!("  请求 {} 失败: {}\n", i, e),
        }
    }
    println!("✅ ServiceBuilder 链式组合成功\n");
}

// ============================================================
// 4. 演示: 超时中间件
// ============================================================

async fn demo_timeout() {
    println!("=== Timeout 中间件演示 ===");

    let slow_api = ApiService::new("慢API", 0, 200);
    let mut service = ServiceBuilder::new()
        .timeout(Duration::from_millis(100))
        .service(slow_api);

    let req = ApiRequest {
        payload: "timeout-test".to_string(),
    };
    match service.call(req).await {
        Ok(resp) => println!("  意外成功: {:?}", resp),
        Err(e) => println!("  ✅ 预期超时: {}", e),
    }
    println!();
}

// ============================================================
// 5. 演示: 手动重试 + map_request / map_response
// ============================================================

async fn demo_map_and_retry() {
    println!("=== map_request / map_response + 手动重试 ===");

    let flaky_api = ApiService::new("不稳定API", 3, 10);

    let mut service = ServiceBuilder::new()
        .map_request(|req: ApiRequest| {
            println!("  [map_request] 原始请求: {:?}", req);
            req
        })
        .map_response(|resp: ApiResponse| {
            println!("  [map_response] 原始响应: {:?}", resp);
            resp
        })
        .service(flaky_api);

    for i in 0..5 {
        let req = ApiRequest {
            payload: format!("retry-{}", i),
        };
        let mut last_err = None;
        let mut result = None;
        for attempt in 0..3 {
            match service.ready().await.unwrap().call(req.clone()).await {
                Ok(resp) => {
                    result = Some(resp);
                    break;
                }
                Err(e) => {
                    last_err = Some(e);
                    if attempt < 2 {
                        sleep(Duration::from_millis(20 * (attempt + 1) as u64)).await;
                    }
                }
            }
        }
        match result {
            Some(resp) => println!("  请求 {}: {}\n", i, resp.body),
            None => println!("  请求 {}: 重试耗尽 -> {}\n", i, last_err.unwrap()),
        }
    }
    println!("✅ map + 重试演示完成\n");
}

// ============================================================
// 6. 演示: Buffer 中间件 (并发控制)
// ============================================================

async fn demo_buffer() {
    println!("=== Buffer 并发控制演示 ===");

    let api = ApiService::new("缓冲API", 0, 30);

    let service = ServiceBuilder::new()
        .buffer(3) // 最多 3 个并发请求
        .service(api);

    let mut handles = Vec::new();
    for i in 0..5 {
        let mut svc = service.clone();
        let req = ApiRequest {
            payload: format!("concurrent-{}", i),
        };
        handles.push(tokio::spawn(async move {
            match svc.ready().await.unwrap().call(req).await {
                Ok(resp) => println!("  并发请求 {} 完成: {}", i, resp.body),
                Err(e) => println!("  并发请求 {} 失败: {}", i, e),
            }
        }));
    }

    for h in handles {
        h.await.unwrap();
    }
    println!("✅ Buffer 并发控制演示完成\n");
}

// ============================================================
// main
// ============================================================

#[tokio::main]
async fn main() {
    demo_basic_service().await;
    demo_service_builder().await;
    demo_timeout().await;
    demo_map_and_retry().await;
    demo_buffer().await;
    println!("🎉 Tower 中间件栈演示全部通过！");
}
