//! 开源生态集成示例
//!
//! 本示例展示如何集成和使用主流开源库：
//! - serde - 序列化/反序列化
//! - toml - 配置文件解析
//! - chrono - 日期时间处理
//! - regex - 正则表达式
//! - tracing - 结构化日志和追踪
//! - anyhow/thiserror - 错误处理
//!
//! # 运行前准备
//! 在 Cargo.toml 中添加依赖：
//! ```toml
//! [dependencies]
//! serde = { version = "1.0", features = ["derive"] }
//! toml = "0.8"
//! chrono = { version = "0.4", features = ["serde"] }
//! regex = "1.10"
//! tracing = "0.1"
//! tracing-subscriber = "0.3"
//! anyhow = "1.0"
//! thiserror = "1.0"
//! ```

#![allow(unused)]
#![allow(unexpected_cfgs)]

// 注意：这些示例使用了条件编译，即使没有依赖也能编译通过
// 实际使用时需要添加对应的依赖

#[cfg(feature = "serde_examples")]
mod serde_examples {
    use serde::{Deserialize, Serialize};
    use std::collections::HashMap;

    /// # Serde 序列化最佳实践
    ///
    /// ## 基本用法
    #[derive(Debug, Serialize, Deserialize)]
    pub struct Config {
        // 重命名字段（用于不同命名风格）
        #[serde(rename = "appName")]
        pub app_name: String,

        // 默认值
        #[serde(default = "default_port")]
        pub port: u16,

        // 可选字段
        #[serde(skip_serializing_if = "Option::is_none")]
        pub description: Option<String>,

        // 扁平化嵌套结构
        #[serde(flatten)]
        pub extra: HashMap<String, serde_json::Value>,
    }

    fn default_port() -> u16 {
        8080
    }

    impl Default for Config {
        fn default() -> Self {
            Self {
                app_name: "MyApp".to_string(),
                port: default_port(),
                description: None,
                extra: HashMap::new(),
            }
        }
    }

    /// ## 自定义序列化
    #[derive(Debug)]
    pub struct SensitiveString(String);

    impl Serialize for SensitiveString {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: serde::Serializer,
        {
            // 敏感数据脱敏显示
            serializer.serialize_str("***REDACTED***")
        }
    }

    impl<'de> Deserialize<'de> for SensitiveString {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: serde::Deserializer<'de>,
        {
            let s = String::deserialize(deserializer)?;
            Ok(SensitiveString(s))
        }
    }

    /// ## 枚举序列化模式
    #[derive(Debug, Serialize, Deserialize)]
    #[serde(tag = "type", content = "data")]
    pub enum Event {
        #[serde(rename = "user_login")]
        UserLogin { user_id: u64, timestamp: String },

        #[serde(rename = "user_logout")]
        UserLogout { user_id: u64 },

        #[serde(rename = "page_view")]
        PageView { path: String, duration_secs: u32 },
    }

    /// ## 运行示例
    pub fn run_examples() {
        println!("=== Serde 序列化示例 ===\n");

        // JSON 序列化
        let config = Config {
            app_name: "MyServer".to_string(),
            port: 3000,
            description: Some("A test server".to_string()),
            extra: {
                let mut map = HashMap::new();
                map.insert("version".to_string(), serde_json::json!("1.0.0"));
                map.insert("debug".to_string(), serde_json::json!(true));
                map
            },
        };

        let json = serde_json::to_string_pretty(&config).unwrap();
        println!("Serialized JSON:\n{}\n", json);

        // 反序列化
        let parsed: Config = serde_json::from_str(&json).unwrap();
        println!("Parsed config: {:?}\n", parsed);

        // 枚举序列化
        let events = vec![
            Event::UserLogin {
                user_id: 123,
                timestamp: "2024-01-01T00:00:00Z".to_string(),
            },
            Event::PageView {
                path: "/home".to_string(),
                duration_secs: 30,
            },
        ];

        for event in &events {
            println!("Event JSON: {}", serde_json::to_string(event).unwrap());
        }
    }
}

#[cfg(feature = "toml_examples")]
mod toml_examples {
    use serde::{Deserialize, Serialize};
    use std::collections::HashMap;

    /// # TOML 配置解析最佳实践
    ///
    /// ## 配置文件结构
    #[derive(Debug, Serialize, Deserialize)]
    pub struct AppConfig {
        /// 应用基本信息
        pub app: AppInfo,

        /// 服务器配置
        #[serde(default)]
        pub server: ServerConfig,

        /// 数据库配置
        pub database: DatabaseConfig,

        /// 日志配置（可选）
        #[serde(default)]
        pub logging: Option<LoggingConfig>,

        /// 额外配置（动态键值）
        #[serde(default)]
        pub features: HashMap<String, serde_json::Value>,
    }

    #[derive(Debug, Serialize, Deserialize)]
    pub struct AppInfo {
        pub name: String,
        #[serde(default = "default_version")]
        pub version: String,
        pub description: Option<String>,
    }

    fn default_version() -> String {
        "0.1.0".to_string()
    }

    #[derive(Debug, Serialize, Deserialize, Default)]
    pub struct ServerConfig {
        #[serde(default = "default_host")]
        pub host: String,
        #[serde(default = "default_port")]
        pub port: u16,
        #[serde(default)]
        pub workers: usize,
    }

    fn default_host() -> String {
        "127.0.0.1".to_string()
    }
    fn default_port() -> u16 {
        8080
    }

    #[derive(Debug, Serialize, Deserialize)]
    pub struct DatabaseConfig {
        pub url: String,
        #[serde(default = "default_pool_size")]
        pub pool_size: u32,
        #[serde(default)]
        pub timeout_seconds: u64,
    }

    fn default_pool_size() -> u32 {
        10
    }

    #[derive(Debug, Serialize, Deserialize)]
    pub struct LoggingConfig {
        pub level: String,
        #[serde(default)]
        pub format: String,
        pub output: Vec<String>,
    }

    /// ## 配置加载模式
    impl AppConfig {
        /// 从文件加载配置
        pub fn from_file(path: &str) -> anyhow::Result<Self> {
            let content = std::fs::read_to_string(path)
                .map_err(|e| anyhow::anyhow!("Failed to read config file: {}", e))?;

            let config: Self = toml::from_str(&content)
                .map_err(|e| anyhow::anyhow!("Failed to parse TOML: {}", e))?;

            config.validate()?;
            Ok(config)
        }

        /// 从环境变量覆盖配置
        pub fn merge_env(&mut self) {
            if let Ok(port) = std::env::var("APP_PORT") {
                if let Ok(port_num) = port.parse() {
                    self.server.port = port_num;
                }
            }

            if let Ok(db_url) = std::env::var("DATABASE_URL") {
                self.database.url = db_url;
            }
        }

        /// 配置验证
        fn validate(&self) -> anyhow::Result<()> {
            if self.server.port == 0 {
                return Err(anyhow::anyhow!("Server port cannot be 0"));
            }

            if self.database.url.is_empty() {
                return Err(anyhow::anyhow!("Database URL cannot be empty"));
            }

            Ok(())
        }
    }

    /// ## 示例 TOML 配置
    const SAMPLE_CONFIG: &str = r#"
[app]
name = "MyApplication"
version = "1.0.0"
description = "A sample application"

[server]
host = "0.0.0.0"
port = 3000
workers = 4

[database]
url = "postgres://localhost/mydb"
pool_size = 20
timeout_seconds = 30

[logging]
level = "info"
format = "json"
output = ["stdout", "file"]

[features]
cache = true
rate_limit = { requests = 100, window = 60 }
"#;

    pub fn run_examples() {
        println!("\n=== TOML 配置解析示例 ===\n");

        // 解析 TOML
        let config: AppConfig = toml::from_str(SAMPLE_CONFIG).unwrap();
        println!("Parsed config:\n{:#?}\n", config);

        // 序列化回 TOML
        let toml_string = toml::to_string_pretty(&config).unwrap();
        println!("Serialized TOML:\n{}\n", toml_string);

        // 处理缺失字段（使用默认值）
        let partial = r#"
[app]
name = "MinimalApp"

[database]
url = "sqlite::memory:"
"#;

        let minimal: AppConfig = toml::from_str(partial).unwrap();
        println!("Minimal config with defaults:");
        println!("  Port: {} (default)", minimal.server.port);
        println!("  Pool size: {} (default)", minimal.database.pool_size);
    }
}

#[cfg(feature = "chrono_examples")]
mod chrono_examples {
    use chrono::{DateTime, Duration, Local, NaiveDate, NaiveDateTime, TimeZone, Utc};

    /// # Chrono 日期时间处理最佳实践
    ///
    /// ## 创建日期时间
    pub fn creation_examples() {
        println!("\n=== Chrono 日期时间创建 ===\n");

        // 当前时间
        let now_utc: DateTime<Utc> = Utc::now();
        let now_local: DateTime<Local> = Local::now();

        println!("UTC now: {}", now_utc);
        println!("Local now: {}", now_local);

        // 从字符串解析
        let dt = DateTime::parse_from_rfc3339("2024-01-15T10:30:00+08:00").unwrap();
        println!("Parsed RFC3339: {}", dt);

        let dt2 =
            NaiveDateTime::parse_from_str("2024-01-15 10:30:00", "%Y-%m-%d %H:%M:%S").unwrap();
        println!("Parsed custom format: {}", dt2);

        // 构造特定日期
        let date = NaiveDate::from_ymd_opt(2024, 1, 15).unwrap();
        let datetime = date.and_hms_opt(10, 30, 0).unwrap();
        println!("Constructed: {}", datetime);
    }

    /// ## 时间运算
    pub fn arithmetic_examples() {
        println!("\n=== Chrono 时间运算 ===\n");

        let now = Utc::now();

        // 加减时间
        let tomorrow = now + Duration::days(1);
        let last_week = now - Duration::weeks(1);
        let ten_minutes_later = now + Duration::minutes(10);

        println!("Now: {}", now);
        println!("Tomorrow: {}", tomorrow);
        println!("Last week: {}", last_week);
        println!("10 minutes later: {}", ten_minutes_later);

        // 时间差
        let start = Utc::now();
        // ... 一些操作
        let end = Utc::now();
        let diff = end.signed_duration_since(start);
        println!(
            "Duration: {:?} ({} nanoseconds)",
            diff,
            diff.num_nanoseconds().unwrap_or(0)
        );
    }

    /// ## 格式化与显示
    pub fn formatting_examples() {
        println!("\n=== Chrono 格式化 ===\n");

        let now = Utc::now();

        // 标准格式
        println!("RFC3339: {}", now.to_rfc3339());
        println!("RFC2822: {}", now.to_rfc2822());

        // 自定义格式
        println!("Custom: {}", now.format("%Y年%m月%d日 %H:%M:%S"));
        println!("Compact: {}", now.format("%Y%m%d_%H%M%S"));
        println!("Date only: {}", now.format("%Y-%m-%d"));
        println!("Time only: {}", now.format("%H:%M:%S"));

        // 文件名安全格式
        let filename_safe = now.format("%Y%m%d_%H%M%S").to_string();
        println!("Filename safe: backup_{}.tar.gz", filename_safe);
    }

    /// ## 时区处理
    pub fn timezone_examples() {
        println!("\n=== Chrono 时区处理 ===\n");

        let utc = Utc::now();

        // 转换为本地时间
        let local = utc.with_timezone(&Local);
        println!("UTC: {}", utc);
        println!("Local: {}", local);

        // 转换为特定时区（需要 chrono-tz）
        // use chrono_tz::Asia::Shanghai;
        // let shanghai = utc.with_timezone(&Shanghai);
    }

    /// ## 实用函数集合
    pub fn utility_examples() {
        println!("\n=== Chrono 实用函数 ===\n");

        // 判断闰年
        let year = 2024;
        let is_leap = NaiveDate::from_ymd_opt(year, 2, 29).is_some();
        println!("{} is leap year: {}", year, is_leap);

        // 获取月初和月末
        let today = Local::now().date_naive();
        let first_day = today.with_day(1).unwrap();
        println!("First day of month: {}", first_day);

        // 获取星期几
        let weekday = today.weekday();
        println!("Today is: {:?}", weekday);

        // 时间戳转换
        let timestamp = Utc::now().timestamp();
        println!("Unix timestamp: {}", timestamp);

        let from_ts = DateTime::from_timestamp(timestamp, 0).unwrap();
        println!("From timestamp: {}", from_ts);
    }

    pub fn run_examples() {
        creation_examples();
        arithmetic_examples();
        formatting_examples();
        timezone_examples();
        utility_examples();
    }
}

#[cfg(feature = "regex_examples")]
mod regex_examples {
    use regex::Regex;
    use std::collections::HashMap;

    /// # Regex 正则表达式最佳实践
    ///
    /// ## 编译和缓存模式
    ///
    /// 注意：正则应该在循环外编译，避免重复编译开销
    pub struct RegexCache {
        patterns: HashMap<String, Regex>,
    }

    impl RegexCache {
        pub fn new() -> Self {
            Self {
                patterns: HashMap::new(),
            }
        }

        pub fn get(&mut self, pattern: &str) -> Result<&Regex, regex::Error> {
            if !self.patterns.contains_key(pattern) {
                let regex = Regex::new(pattern)?;
                self.patterns.insert(pattern.to_string(), regex);
            }
            Ok(self.patterns.get(pattern).unwrap())
        }
    }

    /// ## 常用验证模式
    pub fn validation_examples() {
        println!("\n=== Regex 验证示例 ===\n");

        // 邮箱验证
        let email_re = Regex::new(r"^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$").unwrap();

        let emails = vec!["user@example.com", "invalid.email", "test+tag@domain.co.uk"];

        for email in emails {
            println!("{} is valid email: {}", email, email_re.is_match(email));
        }

        // 手机号验证（中国）
        let phone_re = Regex::new(r"^1[3-9]\d{9}$").unwrap();
        println!(
            "\n13800138000 is valid: {}",
            phone_re.is_match("13800138000")
        );
        println!("12345678901 is valid: {}", phone_re.is_match("12345678901"));

        // 密码强度验证
        let password_re = Regex::new(r"^(?=.*[a-z])(?=.*[A-Z])(?=.*\d).{8,}$").unwrap();
        println!(
            "\n'Password123' is strong: {}",
            password_re.is_match("Password123")
        );
        println!("'weak' is strong: {}", password_re.is_match("weak"));
    }

    /// ## 提取和捕获
    pub fn extraction_examples() {
        println!("\n=== Regex 提取示例 ===\n");

        // 日志解析
        let log_re = Regex::new(
            r"^(?P<timestamp>\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2})\s+\[(?P<level>\w+)\]\s+(?P<message>.*)$"
        ).unwrap();

        let log_line = "2024-01-15 10:30:00 [INFO] Application started successfully";

        if let Some(caps) = log_re.captures(log_line) {
            println!("Timestamp: {}", &caps["timestamp"]);
            println!("Level: {}", &caps["level"]);
            println!("Message: {}", &caps["message"]);
        }

        // 提取所有匹配
        let text = "Contact us at support@example.com or sales@company.org";
        let email_re = Regex::new(r"\b[\w.-]+@[\w.-]+\.\w+\b").unwrap();

        let emails: Vec<&str> = email_re.find_iter(text).map(|m| m.as_str()).collect();
        println!("\nFound emails: {:?}", emails);

        // 替换
        let anonymized = email_re.replace_all(text, "***@***.***");
        println!("Anonymized: {}", anonymized);
    }

    /// ## 分割和解析
    pub fn splitting_examples() {
        println!("\n=== Regex 分割示例 ===\n");

        // CSV 解析（简单情况）
        let csv_line = r#"John Doe, 30, "New York, NY", johndoe@example.com"#;
        let re = Regex::new(r"\s*,\s*").unwrap();
        let fields: Vec<&str> = re.split(csv_line).collect();
        println!("CSV fields: {:?}", fields);

        // 多行分割
        let text = "Line1\r\nLine2\nLine3\rLine4";
        let line_re = Regex::new(r"\r\n|\n|\r").unwrap();
        let lines: Vec<&str> = line_re.split(text).collect();
        println!("Lines: {:?}", lines);
    }

    pub fn run_examples() {
        validation_examples();
        extraction_examples();
        splitting_examples();
    }
}

/// # 错误处理最佳实践（使用 anyhow/thiserror）
#[cfg(feature = "error_handling_examples")]
mod error_handling_examples {
    use thiserror::Error;

    /// ## 定义错误类型（thiserror）
    #[derive(Error, Debug)]
    pub enum ConfigError {
        #[error("配置文件未找到: {0}")]
        NotFound(String),

        #[error("解析错误: {0}")]
        ParseError(#[from] toml::de::Error),

        #[error("验证失败: {field} - {message}")]
        ValidationError { field: String, message: String },

        #[error("IO错误: {0}")]
        Io(#[from] std::io::Error),
    }

    /// ## 应用级错误（anyhow）
    pub fn application_function() -> anyhow::Result<()> {
        // 使用 anyhow::Context 添加上下文
        let config =
            std::fs::read_to_string("config.toml").context("Failed to read configuration file")?;

        let parsed: toml::Value = config
            .parse()
            .context("Failed to parse TOML configuration")?;

        println!("Config loaded: {:?}", parsed);
        Ok(())
    }

    use anyhow::Context;

    pub fn run_examples() {
        println!("\n=== 错误处理示例 ===\n");

        // thiserror 示例
        let err = ConfigError::ValidationError {
            field: "port".to_string(),
            message: "must be between 1 and 65535".to_string(),
        };
        println!("Error: {}", err);

        // anyhow 示例
        if let Err(e) = application_function() {
            println!("Application error: {:#}", e);
        }
    }
}

// 主函数 - 根据启用的特性运行对应的示例
fn main() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║     Rust 开源生态集成示例                                 ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    #[cfg(feature = "serde_examples")]
    serde_examples::run_examples();

    #[cfg(feature = "toml_examples")]
    toml_examples::run_examples();

    #[cfg(feature = "chrono_examples")]
    chrono_examples::run_examples();

    #[cfg(feature = "regex_examples")]
    regex_examples::run_examples();

    #[cfg(feature = "error_handling_examples")]
    error_handling_examples::run_examples();

    // 默认运行所有示例（如果依赖可用）
    #[cfg(not(any(
        feature = "serde_examples",
        feature = "toml_examples",
        feature = "chrono_examples",
        feature = "regex_examples",
        feature = "error_handling_examples"
    )))]
    {
        println!("\n注意: 要运行完整示例，请在 Cargo.toml 中添加以下依赖:");
        println!("\n[dependencies]");
        println!("serde = {{ version = \"1.0\", features = [\"derive\"] }}");
        println!("serde_json = \"1.0\"");
        println!("toml = \"0.8\"");
        println!("chrono = {{ version = \"0.4\", features = [\"serde\"] }}");
        println!("regex = \"1.10\"");
        println!("anyhow = \"1.0\"");
        println!("thiserror = \"1.0\"");

        println!("\n或者启用默认特性运行简化版本。");
    }

    println!("\n✅ 开源生态示例完成!");
}
