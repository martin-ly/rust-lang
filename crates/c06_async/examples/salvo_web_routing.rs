//! Salvo Web 路由示例
//!
//! 展示 Salvo 框架的核心路由注册、路径参数提取与 handler 组合。
//!
//! 运行：
//! ```bash
//! cargo run -p c06_async --example salvo_web_routing
//! ```
//! 测试：
//! ```bash
//! curl http://127.0.0.1:5800/
//! curl http://127.0.0.1:5800/greet/Salvo
//! ```

use salvo::prelude::*;

#[handler]
async fn hello() -> &'static str {
    "Hello, Salvo!"
}

#[handler]
async fn greet(req: &mut Request) -> String {
    let name = req
        .param::<String>("name")
        .unwrap_or_else(|| "World".into());
    format!("Hello, {name}!")
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let router = Router::new()
        .get(hello)
        .push(Router::with_path("greet/<name>").get(greet));

    let acceptor = TcpListener::new("127.0.0.1:5800").bind().await;
    tracing::info!("Salvo server listening on http://127.0.0.1:5800");
    Server::new(acceptor).serve(router).await;
}
