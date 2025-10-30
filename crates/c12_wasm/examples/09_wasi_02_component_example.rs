//! # WASI 0.2 组件模型示例
//!
//! 本示例展示如何使用 WASI 0.2 (Preview 2) 组件模型构建模块化应用
//!
//! ## 特性
//! - WASI 0.2 标准接口
//! - 组件模型架构
//! - WIT 接口定义
//! - 资源管理
//! - 类型安全的互操作
//!
//! ## 编译
//! ```bash
//! # 安装 wasm32-wasip2 target
//! rustup target add wasm32-wasip2
//!
//! # 编译
//! cargo build --example 09_wasi_02_component_example --target wasm32-wasip2 --release
//! ```
//!
//! ## WIT 定义
//!
//! ```wit
//! // wit/world.wit
//! package example:component@1.0.0;
//!
//! world example-world {
//!     import wasi:cli/environment@2.0.0;
//!     import wasi:cli/exit@2.0.0;
//!     import wasi:io/streams@2.0.0;
//!     import wasi:filesystem/types@2.0.0;
//!     export run;
//! }
//!
//! interface run {
//!     execute: func() -> result<_, string>;
//! }
//! ```
//!
//! ## 运行
//! ```bash
//! wasmtime run target/wasm32-wasip2/release/examples/09_wasi_02_component_example.wasm
//! ```

use std::fs;

/// 应用配置
#[derive(Debug)]
struct AppConfig {
    /// 工作目录
    work_dir: String,
    /// 输出文件
    output_file: String,
    /// 日志级别
    log_level: LogLevel,
}

#[derive(Debug, Clone, Copy)]
enum LogLevel {
    Debug,
    Info,
    Warning,
    Error,
}

impl AppConfig {
    /// 从环境变量加载配置
    fn from_env() -> Result<Self, String> {
        let work_dir = std::env::var("WORK_DIR").unwrap_or_else(|_| ".".to_string());
        let output_file =
            std::env::var("OUTPUT_FILE").unwrap_or_else(|_| "output.txt".to_string());

        let log_level = match std::env::var("LOG_LEVEL").as_deref() {
            Ok("debug") => LogLevel::Debug,
            Ok("info") => LogLevel::Info,
            Ok("warning") => LogLevel::Warning,
            Ok("error") => LogLevel::Error,
            Ok(_) | Err(_) => LogLevel::Info,
        };

        Ok(Self {
            work_dir,
            output_file,
            log_level,
        })
    }
}

/// 日志系统
struct Logger {
    level: LogLevel,
}

impl Logger {
    fn new(level: LogLevel) -> Self {
        Self { level }
    }

    fn log(&self, level: LogLevel, message: &str) {
        let level_num = match level {
            LogLevel::Debug => 0,
            LogLevel::Info => 1,
            LogLevel::Warning => 2,
            LogLevel::Error => 3,
        };

        let current_level_num = match self.level {
            LogLevel::Debug => 0,
            LogLevel::Info => 1,
            LogLevel::Warning => 2,
            LogLevel::Error => 3,
        };

        if level_num >= current_level_num {
            let level_str = match level {
                LogLevel::Debug => "DEBUG",
                LogLevel::Info => "INFO",
                LogLevel::Warning => "WARN",
                LogLevel::Error => "ERROR",
            };
            println!("[{}] {}", level_str, message);
        }
    }

    fn debug(&self, message: &str) {
        self.log(LogLevel::Debug, message);
    }

    fn info(&self, message: &str) {
        self.log(LogLevel::Info, message);
    }

    fn warning(&self, message: &str) {
        self.log(LogLevel::Warning, message);
    }

    #[allow(dead_code)]
    fn error(&self, message: &str) {
        self.log(LogLevel::Error, message);
    }
}

/// 文件处理器 - 展示 WASI 0.2 文件系统 API
struct FileProcessor {
    logger: Logger,
}

impl FileProcessor {
    fn new(logger: Logger) -> Self {
        Self { logger }
    }

    /// 列出目录中的文件
    fn list_files(&self, dir: &str) -> Result<Vec<String>, String> {
        self.logger
            .debug(&format!("Listing files in directory: {}", dir));

        let entries = fs::read_dir(dir).map_err(|e| format!("Failed to read directory: {}", e))?;

        let mut files = Vec::new();
        for entry in entries {
            let entry = entry.map_err(|e| format!("Failed to read entry: {}", e))?;
            let file_name = entry
                .file_name()
                .into_string()
                .map_err(|_| "Invalid UTF-8 in filename".to_string())?;
            files.push(file_name);
        }

        self.logger.info(&format!("Found {} files", files.len()));
        Ok(files)
    }

    /// 读取文件内容
    fn read_file(&self, path: &str) -> Result<String, String> {
        self.logger.debug(&format!("Reading file: {}", path));

        let content = fs::read_to_string(path).map_err(|e| format!("Failed to read file: {}", e))?;

        self.logger
            .info(&format!("Read {} bytes from {}", content.len(), path));
        Ok(content)
    }

    /// 写入文件
    fn write_file(&self, path: &str, content: &str) -> Result<(), String> {
        self.logger
            .debug(&format!("Writing {} bytes to {}", content.len(), path));

        fs::write(path, content).map_err(|e| format!("Failed to write file: {}", e))?;

        self.logger.info(&format!("Successfully wrote to {}", path));
        Ok(())
    }

    /// 处理文本文件（统计信息）
    fn analyze_text(&self, content: &str) -> TextStats {
        self.logger.debug("Analyzing text");

        let stats = TextStats {
            char_count: content.chars().count(),
            word_count: content.split_whitespace().count(),
            line_count: content.lines().count(),
            byte_count: content.len(),
        };

        self.logger
            .info(&format!("Text analysis: {:?}", stats));
        stats
    }
}

/// 文本统计信息
#[derive(Debug)]
struct TextStats {
    char_count: usize,
    word_count: usize,
    line_count: usize,
    byte_count: usize,
}

impl TextStats {
    fn to_string(&self) -> String {
        format!(
            "Text Statistics:\n\
             - Characters: {}\n\
             - Words: {}\n\
             - Lines: {}\n\
             - Bytes: {}",
            self.char_count, self.word_count, self.line_count, self.byte_count
        )
    }
}

/// 数据转换器 - 展示组件间数据流
struct DataTransformer {
    logger: Logger,
}

impl DataTransformer {
    fn new(logger: Logger) -> Self {
        Self { logger }
    }

    /// 转换为大写
    fn to_uppercase(&self, text: &str) -> String {
        self.logger
            .debug(&format!("Transforming {} chars to uppercase", text.len()));
        text.to_uppercase()
    }

    /// 转换为小写
    fn to_lowercase(&self, text: &str) -> String {
        self.logger
            .debug(&format!("Transforming {} chars to lowercase", text.len()));
        text.to_lowercase()
    }

    /// 反转文本
    fn reverse(&self, text: &str) -> String {
        self.logger.debug("Reversing text");
        text.chars().rev().collect()
    }

    /// 去除空白
    fn trim_whitespace(&self, text: &str) -> String {
        self.logger.debug("Trimming whitespace");
        text.split_whitespace().collect::<Vec<_>>().join(" ")
    }
}

/// 主应用程序
struct Application {
    config: AppConfig,
    logger: Logger,
    file_processor: FileProcessor,
    transformer: DataTransformer,
}

impl Application {
    fn new() -> Result<Self, String> {
        let config = AppConfig::from_env()?;
        let logger = Logger::new(config.log_level);

        logger.info("Initializing WASI 0.2 Component Application");
        logger.debug(&format!("Configuration: {:?}", config));

        let file_processor = FileProcessor::new(Logger::new(config.log_level));
        let transformer = DataTransformer::new(Logger::new(config.log_level));

        Ok(Self {
            config,
            logger,
            file_processor,
            transformer,
        })
    }

    /// 运行应用程序
    fn run(&self) -> Result<(), String> {
        self.logger.info("Starting application");

        // 获取命令行参数
        let args: Vec<String> = std::env::args().collect();
        self.logger
            .debug(&format!("Command line arguments: {:?}", args));

        // 演示文件系统操作
        self.demo_filesystem()?;

        // 演示文本处理
        self.demo_text_processing()?;

        // 演示环境变量
        self.demo_environment_vars();

        self.logger.info("Application completed successfully");
        Ok(())
    }

    /// 演示文件系统操作
    fn demo_filesystem(&self) -> Result<(), String> {
        self.logger.info("=== File System Demo ===");

        // 列出当前目录的文件
        match self.file_processor.list_files(&self.config.work_dir) {
            Ok(files) => {
                self.logger.info("Files in directory:");
                for file in files {
                    println!("  - {}", file);
                }
            }
            Err(e) => {
                self.logger.warning(&format!("Could not list files: {}", e));
            }
        }

        // 创建示例文件
        let sample_content = "Hello from WASI 0.2 Component Model!\n\
                             This is a demonstration of file operations.\n\
                             WebAssembly components are modular and composable.";

        let output_path = format!("{}/{}", self.config.work_dir, self.config.output_file);
        self.file_processor
            .write_file(&output_path, sample_content)?;

        // 读取刚创建的文件
        let content = self.file_processor.read_file(&output_path)?;
        self.logger.info("File content preview:");
        println!("{}", &content[..content.len().min(100)]);

        Ok(())
    }

    /// 演示文本处理
    fn demo_text_processing(&self) -> Result<(), String> {
        self.logger.info("=== Text Processing Demo ===");

        let sample_text = "  WASI 0.2 brings Component Model   to WebAssembly!  ";

        // 统计分析
        let stats = self.file_processor.analyze_text(sample_text);
        println!("{}", stats.to_string());

        // 各种转换
        println!("\nTransformations:");
        println!("Original: '{}'", sample_text);
        println!("Uppercase: '{}'", self.transformer.to_uppercase(sample_text));
        println!("Lowercase: '{}'", self.transformer.to_lowercase(sample_text));
        println!("Trimmed: '{}'", self.transformer.trim_whitespace(sample_text));
        println!("Reversed: '{}'", self.transformer.reverse(sample_text));

        Ok(())
    }

    /// 演示环境变量
    fn demo_environment_vars(&self) {
        self.logger.info("=== Environment Variables Demo ===");

        // 列出一些常见的环境变量
        let vars = ["PATH", "HOME", "USER", "WORK_DIR", "LOG_LEVEL"];

        for var in vars {
            match std::env::var(var) {
                Ok(value) => println!("{}={}", var, value),
                Err(_) => println!("{}=<not set>", var),
            }
        }
    }
}

fn main() {
    println!("===========================================");
    println!("  WASI 0.2 Component Model Example");
    println!("  Rust Edition 2024 | WASI Preview 2");
    println!("===========================================\n");

    // 创建并运行应用
    match Application::new() {
        Ok(app) => {
            if let Err(e) = app.run() {
                eprintln!("Application error: {}", e);
                std::process::exit(1);
            }
        }
        Err(e) => {
            eprintln!("Initialization error: {}", e);
            std::process::exit(1);
        }
    }

    println!("\n===========================================");
    println!("  Application finished successfully!");
    println!("===========================================");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_logger() {
        let logger = Logger::new(LogLevel::Info);
        logger.info("Test message");
        // 应该输出消息

        logger.debug("Debug message");
        // 不应该输出（级别太低）
    }

    #[test]
    fn test_transformer() {
        let logger = Logger::new(LogLevel::Error);
        let transformer = DataTransformer::new(logger);

        assert_eq!(transformer.to_uppercase("hello"), "HELLO");
        assert_eq!(transformer.to_lowercase("WORLD"), "world");
        assert_eq!(transformer.reverse("abc"), "cba");
        assert_eq!(transformer.trim_whitespace("  hello   world  "), "hello world");
    }

    #[test]
    fn test_text_stats() {
        let logger = Logger::new(LogLevel::Error);
        let processor = FileProcessor::new(logger);

        let text = "hello world\nrust wasm";
        let stats = processor.analyze_text(text);

        assert_eq!(stats.word_count, 4);
        assert_eq!(stats.line_count, 2);
    }

    #[test]
    fn test_config_from_env() {
        unsafe {
            std::env::set_var("WORK_DIR", "/tmp");
            std::env::set_var("OUTPUT_FILE", "test.txt");
            std::env::set_var("LOG_LEVEL", "debug");
        }

        let config = AppConfig::from_env().unwrap();
        assert_eq!(config.work_dir, "/tmp");
        assert_eq!(config.output_file, "test.txt");
    }
}

