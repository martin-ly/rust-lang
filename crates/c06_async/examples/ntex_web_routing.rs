//! ntex Web 路由示例
//!
//! 展示 ntex 框架的服务注册、路径参数提取与基于 tokio 的运行时启动。
//!
//! 运行：
//! ```bash
//! cargo run -p c06_async --example ntex_web_routing
//! ```
//! 测试：
//! ```bash
//! curl http://127.0.0.1:5801/
//! curl http://127.0.0.1:5801/greet/ntex
//! ```

use ntex::web::{self, App, HttpResponse, HttpServer};

#[web::get("/")]
async fn hello() -> impl web::Responder {
    HttpResponse::Ok().body("Hello, ntex!")
}

#[web::get("/greet/{name}")]
async fn greet(name: web::types::Path<String>) -> impl web::Responder {
    HttpResponse::Ok().body(format!("Hello, {}!", name.into_inner()))
}

#[ntex::main]
async fn main() -> std::io::Result<()> {
    tracing_subscriber::fmt::init();

    HttpServer::new(|| async { App::new().service(hello).service(greet) })
        .bind(("127.0.0.1", 5801))?
        .run()
        .await
}
