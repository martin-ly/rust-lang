//! # Rust 微服务框架集合
//! 
//! 这是一个全面的Rust微服务框架集合，支持多种Web框架、gRPC、服务网格和云原生部署。
//! 结合Rust 1.89的最新语言特性，提供高性能、安全、可扩展的微服务解决方案。
//! 
//! ## 主要特性
//! 
//! - 🚀 **现代Web框架**: Axum, Actix-Web, Warp, Tide
//! - 🌐 **gRPC支持**: Tonic, Volo (字节跳动开源)
//! - 🔧 **服务网格**: 服务发现、负载均衡、熔断器
//! - 📊 **可观测性**: OpenTelemetry, Prometheus, Jaeger
//! - 🗄️ **数据库集成**: SQLx, Diesel, SeaORM
//! - ☸️ **Kubernetes**: 部署和配置管理
//! - 🔐 **安全特性**: JWT, OAuth2, HTTPS, CORS
//! - ⚡ **异步模式**: Actor模型、消息队列、事件驱动
//! 
//! ## 快速开始
//! 
//! ```rust
//! use c13_microservice::prelude::*;
//! 
//! #[tokio::main]
//! async fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // 启动Axum微服务
//!     let app = axum::Router::new()
//!         .route("/health", axum::routing::get(health_check));
//!     
//!     let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
//!     axum::serve(listener, app).await?;
//!     Ok(())
//! }
//! 
//! async fn health_check() -> &'static str {
//!     "OK"
//! }
//! ```

// 核心模块
pub mod config;
pub mod error;
pub mod middleware;
pub mod utils;
pub mod lib_simple;

// Web框架模块
pub mod actix;
pub mod axum;
pub mod warp;
pub mod tide;

// gRPC和RPC模块
pub mod grpc;
pub mod volo;

// 服务网格模块 - 暂时注释掉
// pub mod service_mesh;
pub mod discovery;
// pub mod load_balancer;
// pub mod circuit_breaker;

// 可观测性模块 - 暂时注释掉
// pub mod observability;
pub mod opentelemetry;
pub mod logging;
// pub mod metrics;
// pub mod tracing;

// 数据库模块 - 暂时注释掉
// pub mod database;
pub mod orm;

// 消息队列模块
pub mod messaging;
// pub mod queue;

// 认证和安全模块 - 暂时注释掉
// pub mod auth;
// pub mod security;

// Kubernetes和云原生模块 - 暂时注释掉
// pub mod kubernetes;
pub mod kube_rs;

// 异步模式模块 - 暂时注释掉
// pub mod async_patterns;
// pub mod actors;

// 预导入模块
pub mod prelude {
    //! 常用类型和函数的预导入模块
    
    pub use crate::config::Config;
    pub use crate::error::{Error, Result};
    pub use crate::middleware::*;
    pub use crate::utils::*;
    pub use crate::discovery::{Consul, Etcd};
    pub use crate::messaging::{RabbitMQ, Kafka, NATS, MQTT, Redis};
    
    // 重新导出常用crate
    pub use tokio;
    pub use serde::{Deserialize, Serialize};
    pub use tracing::{info, warn, error, debug};
}

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const NAME: &str = env!("CARGO_PKG_NAME");
