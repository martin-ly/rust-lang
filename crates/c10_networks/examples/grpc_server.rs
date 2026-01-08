//! gRPC 服务器示例
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **gRPC**: 高性能、跨语言的RPC框架
//!   - **属性**: Protocol Buffers、HTTP/2、流式传输、跨语言
//!   - **关系**: 与RPC、微服务、网络编程相关
//!
//! ### 思维导图
//!
//! ```text
//! gRPC 服务器演示
//! │
//! ├── 服务定义
//! │   └── Protocol Buffers
//! ├── 服务实现
//! │   └── Trait实现
//! ├── 服务器启动
//! │   └── Tonic服务器
//! └── 请求处理
//!     └── 异步处理
//! ```

use tonic::{Request, Response, Status};
use c10_networks::hello::{HelloRequest, HelloReply};

// 手动定义gRPC服务trait
#[tonic::async_trait]
pub trait Greeter: Send + Sync + 'static {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status>;
}

// 简化的gRPC服务器实现
#[allow(dead_code)]
pub struct GreeterServer<T: Greeter> {
    inner: T,
}

impl<T: Greeter> GreeterServer<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }
}

#[derive(Default, Clone)]
#[allow(dead_code)]
struct MyGreeter;

#[tonic::async_trait]
impl Greeter for MyGreeter {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status> {
        let name = request.into_inner().name;
        Ok(Response::new(HelloReply {
            message: format!("Hello, {}", name),
        }))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let greeter = MyGreeter::default();
    
    // 创建一个简单的HTTP服务器来演示protobuf消息的使用
    let addr: std::net::SocketAddr = "127.0.0.1:8080".parse()?;
    println!("HTTP Greeter server listening on {}", addr);
    
    // 使用axum创建一个简单的HTTP服务器
    use axum::{
        extract::{Query, State},
        response::Json,
        routing::get,
        Router,
    };
    use serde::Deserialize;
    use serde_json::json;
    
    #[derive(Deserialize)]
    struct Params {
        name: Option<String>,
    }
    
    #[derive(Clone)]
    struct AppState {
        greeter: MyGreeter,
    }

    async fn hello_handler(
        State(state): State<AppState>,
        Query(params): Query<Params>,
    ) -> Json<serde_json::Value> {
        let name = params.name.unwrap_or_else(|| "World".to_string());
        let reply = state
            .greeter
            .say_hello(Request::new(HelloRequest { name }))
            .await
            .unwrap()
            .into_inner();
        // 避免直接对 prost 生成的类型做 Json 序列化（其未实现 Serialize）
        Json(json!({ "message": reply.message }))
    }

    let app = Router::new()
        .route("/hello", get(hello_handler))
        .with_state(AppState { greeter });
    
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
