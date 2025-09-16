use tonic::{Request, Response, Status, transport::Server};

// 包含生成的protobuf代码
include!(concat!(env!("OUT_DIR"), "/hello.rs"));

// 手动定义gRPC服务trait
#[tonic::async_trait]
pub trait Greeter: Send + Sync + 'static {
    async fn say_hello(
        &self,
        request: Request<HelloRequest>,
    ) -> Result<Response<HelloReply>, Status>;
}

// 简化的gRPC服务器实现
pub struct GreeterServer<T: Greeter> {
    inner: T,
}

impl<T: Greeter> GreeterServer<T> {
    pub fn new(inner: T) -> Self {
        Self { inner }
    }
}

#[derive(Default, Clone)]
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
    let addr = "127.0.0.1:8080".parse()?;
    println!("HTTP Greeter server listening on {}", addr);
    
    // 使用axum创建一个简单的HTTP服务器
    use axum::{
        extract::Query,
        response::Json,
        routing::get,
        Router,
    };
    use serde::Deserialize;
    use std::collections::HashMap;
    
    #[derive(Deserialize)]
    struct Params {
        name: Option<String>,
    }
    
    async fn hello_handler(Query(params): Query<Params>) -> Json<HelloReply> {
        let name = params.name.unwrap_or_else(|| "World".to_string());
        let reply = greeter.say_hello(Request::new(HelloRequest { name })).await.unwrap();
        Json(reply.into_inner())
    }
    
    let app = Router::new().route("/hello", get(hello_handler));
    
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    
    Ok(())
}
