//! 示例和演示代码模块
//! 
//! 本模块提供了基于Rust 1.90的IoT应用示例和演示代码，包括：
//! - 基础设备管理示例
//! - 传感器数据采集示例
//! - 边缘计算示例
//! - 通信协议示例
//! - 数据存储示例
//! - 安全认证示例
//! - 监控告警示例
//! - 完整IoT应用示例

// pub mod basic_device;
// pub mod sensor_collection;
// pub mod edge_computing;
// pub mod communication;
// pub mod data_storage;
// pub mod security;
// pub mod monitoring;
pub mod complete_iot_app;
pub mod advanced_iot_demo;
pub mod performance_benchmark;
pub mod security_test;

// pub use basic_device::BasicDeviceExample;
// pub use sensor_collection::SensorCollectionExample;
// pub use edge_computing::EdgeComputingExample;
// pub use communication::CommunicationExample;
// pub use data_storage::DataStorageExample;
// pub use security::SecurityExample;
// pub use monitoring::MonitoringExample;
pub use complete_iot_app::CompleteIoTAppExample;
pub use advanced_iot_demo::AdvancedIoTDemo;
pub use performance_benchmark::PerformanceBenchmark;
pub use security_test::SecurityTest;

/// 示例运行器
pub struct ExampleRunner {
    // examples: std::collections::HashMap<String, Box<dyn Example + Send + Sync>>,
}

/// 示例接口
pub trait Example {
    /// 获取示例名称
    fn name(&self) -> &'static str;
    
    /// 获取示例描述
    fn description(&self) -> &'static str;
    
    /// 获取示例参数
    fn parameters(&self) -> Vec<ExampleParameter>;
    
    /// 运行示例
    fn run(&mut self, parameters: std::collections::HashMap<String, String>) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error>>> + Send;
}

/// 示例参数
#[derive(Debug, Clone)]
pub struct ExampleParameter {
    pub name: String,
    pub description: String,
    pub parameter_type: ParameterType,
    pub required: bool,
    pub default_value: Option<String>,
}

/// 参数类型
#[derive(Debug, Clone, PartialEq)]
pub enum ParameterType {
    String,
    Integer,
    Float,
    Boolean,
    Duration,
    Url,
    FilePath,
}

impl ExampleRunner {
    /// 创建新的示例运行器
    pub fn new() -> Self {
        Self {
            // examples: std::collections::HashMap::new(),
        }
    }

    // /// 注册示例
    // pub fn register_example(&mut self, example: Box<dyn Example + Send + Sync>) {
    //     self.examples.insert(example.name().to_string(), example);
    // }

    // /// 运行指定示例
    // pub async fn run_example(&self, name: &str) -> Result<(), Box<dyn std::error::Error>> {
    //     if let Some(example) = self.examples.get(name) {
    //         println!("运行示例: {}", example.name());
    //         println!("描述: {}", example.description());
    //         println!("参数:");
            
    //         for param in example.get_parameters() {
    //             println!("  - {}: {} ({})", 
    //                 param.name, 
    //                 param.description,
    //                 if param.required { "必需" } else { "可选" }
    //             );
    //         }
            
    //         println!("\n开始运行...");
    //         example.run().await?;
    //         println!("示例运行完成!");
    //         Ok(())
    //     } else {
    //         Err(format!("示例 '{}' 未找到", name).into())
    //     }
    // }

    // /// 列出所有示例
    // pub fn list_examples(&self) -> Vec<&str> {
    //     self.examples.keys().map(|k| k.as_str()).collect()
    // }

    // /// 获取示例信息
    // pub fn get_example_info(&self, name: &str) -> Option<(&str, &str, Vec<ExampleParameter>)> {
    //     self.examples.get(name).map(|example| {
    //         (example.name(), example.description(), example.get_parameters())
    //     })
    // }
}

impl Default for ExampleRunner {
    fn default() -> Self {
        Self::new()
    }
}

/// 示例配置
#[derive(Debug, Clone)]
pub struct ExampleConfig {
    pub name: String,
    pub parameters: std::collections::HashMap<String, String>,
    pub timeout: Option<std::time::Duration>,
    pub verbose: bool,
}

impl ExampleConfig {
    /// 创建新的示例配置
    pub fn new(name: String) -> Self {
        Self {
            name,
            parameters: std::collections::HashMap::new(),
            timeout: None,
            verbose: false,
        }
    }

    /// 设置参数
    pub fn with_parameter(mut self, key: String, value: String) -> Self {
        self.parameters.insert(key, value);
        self
    }

    /// 设置超时
    pub fn with_timeout(mut self, timeout: std::time::Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }

    /// 设置详细输出
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}

/// 示例结果
#[derive(Debug, Clone)]
pub struct ExampleResult {
    pub success: bool,
    pub duration: std::time::Duration,
    pub message: String,
    pub metrics: std::collections::HashMap<String, f64>,
}

impl ExampleResult {
    /// 创建成功结果
    pub fn success(duration: std::time::Duration, message: String) -> Self {
        Self {
            success: true,
            duration,
            message,
            metrics: std::collections::HashMap::new(),
        }
    }

    /// 创建失败结果
    pub fn failure(duration: std::time::Duration, message: String) -> Self {
        Self {
            success: false,
            duration,
            message,
            metrics: std::collections::HashMap::new(),
        }
    }

    /// 添加指标
    pub fn with_metric(mut self, name: String, value: f64) -> Self {
        self.metrics.insert(name, value);
        self
    }
}

/// 示例基准测试
pub struct ExampleBenchmark {
    results: Vec<ExampleResult>,
}

impl ExampleBenchmark {
    /// 创建新的基准测试
    pub fn new() -> Self {
        Self {
            results: Vec::new(),
        }
    }

    /// 添加结果
    pub fn add_result(&mut self, result: ExampleResult) {
        self.results.push(result);
    }

    /// 获取平均执行时间
    pub fn average_duration(&self) -> std::time::Duration {
        if self.results.is_empty() {
            return std::time::Duration::ZERO;
        }

        let total_nanos: u128 = self.results.iter()
            .map(|r| r.duration.as_nanos())
            .sum();
        
        std::time::Duration::from_nanos((total_nanos / self.results.len() as u128) as u64)
    }

    /// 获取成功率
    pub fn success_rate(&self) -> f64 {
        if self.results.is_empty() {
            return 0.0;
        }

        let success_count = self.results.iter().filter(|r| r.success).count();
        success_count as f64 / self.results.len() as f64
    }

    /// 获取结果统计
    pub fn get_statistics(&self) -> BenchmarkStatistics {
        BenchmarkStatistics {
            total_runs: self.results.len(),
            successful_runs: self.results.iter().filter(|r| r.success).count(),
            failed_runs: self.results.iter().filter(|r| !r.success).count(),
            average_duration: self.average_duration(),
            success_rate: self.success_rate(),
            min_duration: self.results.iter().map(|r| r.duration).min().unwrap_or_default(),
            max_duration: self.results.iter().map(|r| r.duration).max().unwrap_or_default(),
        }
    }
}

/// 基准测试统计信息
#[derive(Debug, Clone)]
pub struct BenchmarkStatistics {
    pub total_runs: usize,
    pub successful_runs: usize,
    pub failed_runs: usize,
    pub average_duration: std::time::Duration,
    pub success_rate: f64,
    pub min_duration: std::time::Duration,
    pub max_duration: std::time::Duration,
}

impl Default for ExampleBenchmark {
    fn default() -> Self {
        Self::new()
    }
}
