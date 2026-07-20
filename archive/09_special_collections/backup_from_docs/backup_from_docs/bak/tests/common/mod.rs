//! 公共测试工具模块
//! 
//! 提供测试中使用的公共工具和辅助函数

pub mod fixtures;
pub mod helpers;

// 重新导出常用的测试工具
pub use fixtures::*;
pub use helpers::*;

/// 测试配置
pub struct TestConfig {
    pub timeout: std::time::Duration,
    pub max_memory: usize,
    pub verbose: bool,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            timeout: std::time::Duration::from_secs(30),
            max_memory: 100 * 1024 * 1024, // 100MB
            verbose: false,
        }
    }
}

/// 测试结果
pub struct TestResult {
    pub success: bool,
    pub duration: std::time::Duration,
    pub memory_usage: usize,
    pub error_message: Option<String>,
}

impl TestResult {
    pub fn success(duration: std::time::Duration, memory_usage: usize) -> Self {
        Self {
            success: true,
            duration,
            memory_usage,
            error_message: None,
        }
    }
    
    pub fn failure(duration: std::time::Duration, error: String) -> Self {
        Self {
            success: false,
            duration,
            memory_usage: 0,
            error_message: Some(error),
        }
    }
}
