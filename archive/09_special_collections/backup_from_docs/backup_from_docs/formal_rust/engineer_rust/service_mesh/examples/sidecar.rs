// 服务网格：Sidecar代理拦截示例 Service Mesh: Sidecar Intercept Example
trait Sidecar {
    async fn intercept(&self, req: &str) -> String;
}

struct LoggerSidecar;

#[tokio::main]
async fn main() {
    let s = LoggerSidecar;
    let resp = s.intercept("GET /").await;
    println!("Response: {}", resp);
}

impl Sidecar for LoggerSidecar {
    async fn intercept(&self, req: &str) -> String {
        format!("[sidecar log] intercepted: {}", req)
    }
} 