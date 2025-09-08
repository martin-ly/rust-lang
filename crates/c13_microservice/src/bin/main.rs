//! 微服务主程序
//! 
//! 展示如何使用c13_microservice框架构建和运行微服务。

use c13_microservice::{
    axum::AxumMicroservice,
    actix::ActixMicroservice,
    grpc::GrpcMicroservice,
    volo::VoloMicroservice,
    prelude::Config,
};
use clap::{Parser, Subcommand};
use tracing_subscriber;

/// 微服务命令行工具
#[derive(Parser)]
#[command(name = "microservice")]
#[command(about = "Rust微服务框架示例")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

/// 支持的命令
#[derive(Subcommand, Clone)]
enum Commands {
    /// 启动Axum Web服务
    Axum {
        /// 配置文件路径
        #[arg(short, long)]
        config: Option<String>,
    },
    /// 启动Actix-Web服务
    Actix {
        /// 配置文件路径
        #[arg(short, long)]
        config: Option<String>,
    },
    /// 启动gRPC服务
    Grpc {
        /// 配置文件路径
        #[arg(short, long)]
        config: Option<String>,
    },
    /// 启动Volo RPC服务
    Volo {
        /// 配置文件路径
        #[arg(short, long)]
        config: Option<String>,
    },
    /// 显示配置信息
    Config {
        /// 配置文件路径
        #[arg(short, long)]
        config: Option<String>,
    },
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();
    
    let cli = Cli::parse();
    
    match cli.command {
        Commands::Axum { config } => {
            run_axum_service(config).await?;
        }
        Commands::Actix { config } => {
            run_actix_service(config).await?;
        }
        Commands::Grpc { config } => {
            run_grpc_service(config).await?;
        }
        Commands::Volo { config } => {
            run_volo_service(config).await?;
        }
        Commands::Config { config } => {
            show_config(config).await?;
        }
    }
    
    Ok(())
}

/// 运行Axum服务
async fn run_axum_service(config_path: Option<String>) -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("启动Axum微服务");
    
    let config = load_config(config_path)?;
    let microservice = AxumMicroservice::new(config);
    
    microservice.serve().await?;
    Ok(())
}

/// 运行Actix-Web服务
async fn run_actix_service(config_path: Option<String>) -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("启动Actix-Web微服务");
    
    let config = load_config(config_path)?;
    let microservice = ActixMicroservice::new(config);
    
    microservice.serve().await?;
    Ok(())
}

/// 运行gRPC服务
async fn run_grpc_service(config_path: Option<String>) -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("启动gRPC微服务");
    
    let config = load_config(config_path)?;
    let microservice = GrpcMicroservice::new(config);
    
    microservice.serve().await?;
    Ok(())
}

/// 运行Volo RPC服务
async fn run_volo_service(config_path: Option<String>) -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("启动Volo RPC微服务");
    
    let config = load_config(config_path)?;
    let microservice = VoloMicroservice::new(config);
    
    microservice.serve().await?;
    Ok(())
}

/// 显示配置信息
async fn show_config(config_path: Option<String>) -> Result<(), Box<dyn std::error::Error>> {
    let config = load_config(config_path)?;
    
    println!("微服务配置信息:");
    println!("  服务名称: {}", config.service.name);
    println!("  服务版本: {}", config.service.version);
    println!("  监听地址: {}", config.service_address());
    
    Ok(())
}

/// 加载配置
fn load_config(config_path: Option<String>) -> Result<Config, Box<dyn std::error::Error>> {
    let config = if let Some(_path) = config_path {
        tracing::info!("从文件加载配置");
        Config::default() // 简化实现
    } else {
        tracing::info!("从环境变量加载配置");
        Config::from_env()?
    };
    
    config.validate()?;
    Ok(config)
}
