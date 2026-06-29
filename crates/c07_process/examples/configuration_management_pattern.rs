//! 配置管理模式示例
//!
//! 演示如何使用 `config` crate 组合三种配置来源：
//! 1. 硬编码默认值（TOML 字符串源）
//! 2. 可选配置文件 `config/app.{toml,json,yaml,...}`
//! 3. 环境变量，前缀为 `APP__`，层级分隔符为 `__`
//!
//! 运行示例：
//!
//! ```bash
//! # 仅使用默认值
//! cargo run -p c07_process --example configuration_management_pattern
//!
//! # 使用环境变量覆盖
//! APP__SERVER__PORT=9000 APP__LOG_LEVEL=debug \
//!   cargo run -p c07_process --example configuration_management_pattern
//! ```

use config::{Config, Environment, File, FileFormat};
use serde::Deserialize;

/// 应用顶层配置。
#[derive(Debug, Clone, Deserialize)]
struct AppConfig {
    server: ServerConfig,
    log_level: String,
    #[serde(default = "default_features")]
    features: Vec<String>,
}

/// 服务端点配置。
#[derive(Debug, Clone, Deserialize)]
struct ServerConfig {
    #[serde(default = "default_host")]
    host: String,
    #[serde(default = "default_port")]
    port: u16,
    #[serde(default = "default_workers")]
    workers: usize,
}

fn default_host() -> String {
    "127.0.0.1".into()
}

fn default_port() -> u16 {
    8080
}

fn default_workers() -> usize {
    4
}

fn default_features() -> Vec<String> {
    vec!["default".into()]
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            server: ServerConfig::default(),
            log_level: "info".into(),
            features: default_features(),
        }
    }
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: default_host(),
            port: default_port(),
            workers: default_workers(),
        }
    }
}

/// 分层加载配置：默认值 → 可选配置文件 → 环境变量。
fn load_config() -> Result<AppConfig, config::ConfigError> {
    Config::builder()
        // Layer 1: 硬编码默认值，使用内联 TOML 字符串源。
        .add_source(File::from_str(
            r#"
[server]
host = "127.0.0.1"
port = 8080
workers = 4

log_level = "info"
features = ["default"]
"#,
            FileFormat::Toml,
        ))
        // Layer 2: 可选配置文件，例如 `config/app.toml`。
        .add_source(File::with_name("config/app").required(false))
        // Layer 3: 环境变量，例如 `APP__SERVER__PORT=9000`。
        .add_source(
            Environment::with_prefix("APP")
                .separator("__")
                .try_parsing(true),
        )
        .build()?
        .try_deserialize()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cfg = load_config()?;

    println!("✅ 已加载配置:");
    println!("{:#?}", cfg);
    println!();
    println!(
        "🌐 服务将监听 {}:{}，工作线程数为 {}",
        cfg.server.host, cfg.server.port, cfg.server.workers
    );
    println!("📝 日志级别: {}", cfg.log_level);
    println!("🚀 特性开关: {:?}", cfg.features);

    Ok(())
}
