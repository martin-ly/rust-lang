use actix_web::{web, App, HttpServer, HttpResponse, Responder};

// 定义一个处理函数
async fn greet(name: web::Path<String>) -> impl Responder {
    HttpResponse::Ok().body(format!("Hello, {}!", name))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // 启动 HTTP 服务器
    HttpServer::new(|| {
        App::new()
            .route("/greet/{name}", web::get().to(greet)) // 路由
    })
    .bind("127.0.0.1:8080")? // 绑定地址
    .run()
    .await
}
