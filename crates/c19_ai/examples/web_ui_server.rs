//! Web UI服务器示例
//! 
//! 展示如何启动一个完整的Web管理界面服务器

use c19_ai::web_ui::{create_web_ui_routes, WebUIState};
use axum::Router;
use std::net::SocketAddr;
use tokio::net::TcpListener;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    env_logger::init();

    // 创建Web UI状态
    let state = WebUIState {
        api_base_url: "http://localhost:3000/api".to_string(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        build_time: chrono::Utc::now().to_rfc3339(),
    };

    // 创建Web UI路由
    let app = create_web_ui_routes(state);

    // 启动服务器
    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    let listener = TcpListener::bind(addr).await?;
    
    println!("Web UI服务器启动在 http://{}", addr);
    println!("访问 http://localhost:8080 查看管理界面");
    
    axum::serve(listener, app).await?;

    Ok(())
}
