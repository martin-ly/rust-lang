//! API服务器
//! 
//! 提供API服务器的启动和配置

use super::{routes::create_app_routes, handlers::AppState};
use axum::Router;
use std::net::SocketAddr;
use tokio::net::TcpListener;

/// 启动API服务器
pub async fn start_server(
    state: AppState,
    addr: SocketAddr,
) -> Result<(), Box<dyn std::error::Error>> {
    let app = create_app_routes(state);
    let listener = TcpListener::bind(addr).await?;
    
    println!("🚀 服务器启动在 {}", addr);
    axum::serve(listener, app).await?;
    
    Ok(())
}

/// 创建默认服务器
pub async fn create_default_server(
    state: AppState,
) -> Result<(), Box<dyn std::error::Error>> {
    let addr = SocketAddr::from(([0, 0, 0, 0], 8080));
    start_server(state, addr).await
}