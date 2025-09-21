//! 性能基准测试示例
//! 
//! 本示例提供了全面的性能基准测试，包括：
//! - 通信协议性能测试
//! - 数据处理性能测试
//! - 缓存系统性能测试
//! - 规则引擎性能测试
//! - 安全认证性能测试

use super::{Example, ExampleParameter, ParameterType};
use crate::communication::{CommunicationManager, ProtocolType, Message};
use crate::edge_computing::{RuleEngine, Rule, Condition, Action};
use crate::edge_computing::rule_engine::{Operator, AlertLevel, RuleContext};
use crate::security::DeviceAuthenticator;
use crate::security::authentication::AuthenticationConfig;
use crate::data_storage::{StorageManager, StorageType, DataPoint, StorageConfig};
use crate::data_storage::cache::{CacheSystem, RedisCache, CacheConfig, CacheStrategy};
use crate::data_storage::traits::StorageInterface;
use crate::hardware_abstraction::gpio::{GPIOManager, PinConfig, PinMode, PinState};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use chrono::Utc;
use serde_json::Value;
use std::sync::Arc;
use tokio::sync::Mutex;

/// 性能基准测试结果
#[derive(Debug, Clone, serde::Serialize)]
pub struct BenchmarkResult {
    pub test_name: String,
    pub total_operations: u64,
    pub total_duration: Duration,
    pub operations_per_second: f64,
    pub average_latency: Duration,
    pub min_latency: Duration,
    pub max_latency: Duration,
    pub success_rate: f64,
    pub error_count: u64,
    pub memory_usage: u64,
    pub cpu_usage: f64,
}

/// 性能基准测试套件
pub struct PerformanceBenchmark {
    communication_manager: CommunicationManager,
    rule_engine: RuleEngine,
    authenticator: DeviceAuthenticator,
    storage_manager: StorageManager,
    cache_system: RedisCache,
    gpio_manager: GPIOManager,
    results: Arc<Mutex<Vec<BenchmarkResult>>>,
}

impl PerformanceBenchmark {
    /// 创建新的性能基准测试
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        // 初始化通信管理器
        let communication_manager = CommunicationManager::new();

        // 初始化规则引擎
        let rule_engine = RuleEngine::new();

        // 初始化认证器
        let auth_config = AuthenticationConfig {
            token_expiry_hours: 24,
            max_active_tokens: 1000,
            enable_token_refresh: true,
            refresh_token_expiry_days: 30,
            enable_mfa: true,
        };
        let authenticator = DeviceAuthenticator::new(auth_config);

        // 初始化存储管理器
        let _storage_config = StorageConfig {
            storage_type: StorageType::TimeSeries,
            connection_string: "memory://".to_string(),
            database_name: "benchmark_db".to_string(),
            username: None,
            password: None,
            max_connections: Some(10),
            connection_timeout: Some(Duration::from_secs(30)),
            query_timeout: Some(Duration::from_secs(30)),
            enable_ssl: false,
            enable_compression: false,
            backup_enabled: false,
            backup_interval: None,
            retention_policy: None,
        };
        let storage_manager = StorageManager::new();

        // 初始化缓存系统
        let cache_config = CacheConfig {
            max_size: 10000,
            default_ttl: 3600,
            strategy: CacheStrategy::LRU,
            enable_compression: true,
            enable_persistence: false,
            cleanup_interval: 300,
        };
        let cache_system = RedisCache::with_config(
            "redis://localhost:6379".to_string(),
            0,
            cache_config,
        );

        // 初始化GPIO管理器
        let gpio_manager = GPIOManager::new();

        Ok(Self {
            communication_manager,
            rule_engine,
            authenticator,
            storage_manager,
            cache_system,
            gpio_manager,
            results: Arc::new(Mutex::new(Vec::new())),
        })
    }

    /// 运行完整的性能基准测试
    pub async fn run_full_benchmark(&mut self) -> Result<Vec<BenchmarkResult>, Box<dyn std::error::Error>> {
        println!("🚀 开始性能基准测试...");

        // 初始化所有组件
        self.initialize_components().await?;

        // 运行各种性能测试
        self.run_mqtt_performance_test().await?;
        self.run_coap_performance_test().await?;
        self.run_cache_performance_test().await?;
        self.run_storage_performance_test().await?;
        self.run_rule_engine_performance_test().await?;
        self.run_security_performance_test().await?;
        self.run_gpio_performance_test().await?;
        self.run_concurrent_performance_test().await?;

        // 获取所有测试结果
        let results = self.results.lock().await.clone();
        
        // 生成测试报告
        self.generate_benchmark_report(&results).await?;

        println!("✅ 性能基准测试完成");
        Ok(results)
    }

    /// 初始化所有组件
    async fn initialize_components(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔧 初始化测试组件...");

        // 初始化通信管理器
        self.communication_manager.initialize().await?;

        // 初始化存储管理器
        self.storage_manager.initialize().await?;

        // 初始化缓存系统
        self.cache_system.connect().await?;

        // 初始化GPIO管理器
        self.gpio_manager.initialize().await?;

        println!("✅ 所有组件已初始化");
        Ok(())
    }

    /// 运行MQTT性能测试
    async fn run_mqtt_performance_test(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("📡 运行MQTT性能测试...");

        // 连接MQTT协议
        self.communication_manager.connect(ProtocolType::MQTT, "localhost:1883".to_string()).await?;

        let test_name = "MQTT消息发布性能";
        let total_operations = 1000;
        let mut latencies = Vec::new();
        let mut error_count = 0;
        let start_time = Instant::now();

        for i in 0..total_operations {
            let operation_start = Instant::now();
            
            let message = Message::new(
                ProtocolType::MQTT,
                format!("benchmark/test/{}", i),
                format!("Test message {}", i).into_bytes(),
            );

            match self.communication_manager.send_message(message).await {
                Ok(_) => {
                    let latency = operation_start.elapsed();
                    latencies.push(latency);
                }
                Err(_) => {
                    error_count += 1;
                }
            }
        }

        let total_duration = start_time.elapsed();
        let result = self.calculate_benchmark_result(
            test_name.to_string(),
            total_operations,
            total_duration,
            latencies,
            error_count,
        );

        self.results.lock().await.push(result);
        println!("✅ MQTT性能测试完成");
        Ok(())
    }

    /// 运行CoAP性能测试
    async fn run_coap_performance_test(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🌐 运行CoAP性能测试...");

        // 连接CoAP协议
        self.communication_manager.connect(ProtocolType::CoAP, "localhost:5683".to_string()).await?;

        let test_name = "CoAP请求性能";
        let total_operations = 500;
        let mut latencies = Vec::new();
        let mut error_count = 0;
        let start_time = Instant::now();

        for i in 0..total_operations {
            let operation_start = Instant::now();
            
            let message = Message::new(
                ProtocolType::CoAP,
                format!("/benchmark/test/{}", i),
                vec![],
            );

            match self.communication_manager.send_message(message).await {
                Ok(_) => {
                    let latency = operation_start.elapsed();
                    latencies.push(latency);
                }
                Err(_) => {
                    error_count += 1;
                }
            }
        }

        let total_duration = start_time.elapsed();
        let result = self.calculate_benchmark_result(
            test_name.to_string(),
            total_operations,
            total_duration,
            latencies,
            error_count,
        );

        self.results.lock().await.push(result);
        println!("✅ CoAP性能测试完成");
        Ok(())
    }

    /// 运行缓存性能测试
    async fn run_cache_performance_test(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("💾 运行缓存性能测试...");

        let test_name = "缓存读写性能";
        let total_operations = 2000;
        let mut latencies = Vec::new();
        let mut error_count = 0;
        let start_time = Instant::now();

        for i in 0..total_operations {
            let operation_start = Instant::now();
            
            let key = format!("benchmark_key_{}", i);
            let value = format!("benchmark_value_{}", i);

            // 写入测试
            match self.cache_system.set(&key, &value, Some(300)).await {
                Ok(_) => {
                    // 读取测试
                    match self.cache_system.get(&key).await {
                        Ok(_) => {
                            let latency = operation_start.elapsed();
                            latencies.push(latency);
                        }
                        Err(_) => {
                            error_count += 1;
                        }
                    }
                }
                Err(_) => {
                    error_count += 1;
                }
            }
        }

        let total_duration = start_time.elapsed();
        let result = self.calculate_benchmark_result(
            test_name.to_string(),
            total_operations,
            total_duration,
            latencies,
            error_count,
        );

        self.results.lock().await.push(result);
        println!("✅ 缓存性能测试完成");
        Ok(())
    }

    /// 运行存储性能测试
    async fn run_storage_performance_test(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🗄️ 运行存储性能测试...");

        let test_name = "数据存储性能";
        let total_operations = 1000;
        let mut latencies = Vec::new();
        let mut error_count = 0;
        let start_time = Instant::now();

        for i in 0..total_operations {
            let operation_start = Instant::now();
            
            let mut fields = HashMap::new();
            fields.insert("value".to_string(), serde_json::Value::Number(serde_json::Number::from(i)));
            
            let mut tags = HashMap::new();
            tags.insert("device_id".to_string(), "benchmark_device".to_string());
            
            let data_point = DataPoint {
                timestamp: Utc::now(),
                measurement: "benchmark_data".to_string(),
                tags,
                fields,
            };

            match self.storage_manager.insert_data(StorageType::TimeSeries, data_point).await {
                Ok(_) => {
                    let latency = operation_start.elapsed();
                    latencies.push(latency);
                }
                Err(_) => {
                    error_count += 1;
                }
            }
        }

        let total_duration = start_time.elapsed();
        let result = self.calculate_benchmark_result(
            test_name.to_string(),
            total_operations,
            total_duration,
            latencies,
            error_count,
        );

        self.results.lock().await.push(result);
        println!("✅ 存储性能测试完成");
        Ok(())
    }

    /// 运行规则引擎性能测试
    async fn run_rule_engine_performance_test(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🧠 运行规则引擎性能测试...");

        // 添加测试规则
        self.add_test_rules().await?;

        let test_name = "规则引擎评估性能";
        let total_operations = 500;
        let mut latencies = Vec::new();
        let mut error_count = 0;
        let start_time = Instant::now();

        for i in 0..total_operations {
            let operation_start = Instant::now();
            
            let context = RuleContext {
                data: HashMap::from([
                    ("temperature".to_string(), Value::Number(serde_json::Number::from_f64(20.0 + (i as f64 % 20.0)).unwrap())),
                    ("humidity".to_string(), Value::Number(serde_json::Number::from_f64(40.0 + (i as f64 % 40.0)).unwrap())),
                ]),
                timestamp: Utc::now(),
                device_id: Some("benchmark_device".to_string()),
                location: Some("Benchmark Location".to_string()),
                event_type: Some("sensor_data".to_string()),
                metadata: HashMap::new(),
            };

            match self.rule_engine.evaluate_rules(context).await {
                Ok(_) => {
                    let latency = operation_start.elapsed();
                    latencies.push(latency);
                }
                Err(_) => {
                    error_count += 1;
                }
            }
        }

        let total_duration = start_time.elapsed();
        let result = self.calculate_benchmark_result(
            test_name.to_string(),
            total_operations,
            total_duration,
            latencies,
            error_count,
        );

        self.results.lock().await.push(result);
        println!("✅ 规则引擎性能测试完成");
        Ok(())
    }

    /// 添加测试规则
    async fn add_test_rules(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // 温度监控规则
        let temp_condition = Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        };

        let temp_action = Action::SendAlert {
            message: "温度过高".to_string(),
            recipients: vec!["admin@example.com".to_string()],
            level: AlertLevel::Warning,
        };

        let temp_rule = Rule::new(
            "temp_monitor".to_string(),
            "温度监控".to_string(),
            temp_condition,
            temp_action,
            1,
        );

        self.rule_engine.add_rule(temp_rule).await?;

        // 湿度监控规则
        let humidity_condition = Condition::Simple {
            field: "humidity".to_string(),
            operator: Operator::LessThan,
            value: Value::Number(serde_json::Number::from_f64(20.0).unwrap()),
        };

        let humidity_action = Action::SendAlert {
            message: "湿度过低".to_string(),
            recipients: vec!["operator@example.com".to_string()],
            level: AlertLevel::Info,
        };

        let humidity_rule = Rule::new(
            "humidity_monitor".to_string(),
            "湿度监控".to_string(),
            humidity_condition,
            humidity_action,
            2,
        );

        self.rule_engine.add_rule(humidity_rule).await?;

        Ok(())
    }

    /// 运行安全认证性能测试
    async fn run_security_performance_test(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔐 运行安全认证性能测试...");

        let test_name = "安全认证性能";
        let total_operations = 1000;
        let mut latencies = Vec::new();
        let mut error_count = 0;
        let start_time = Instant::now();

        for i in 0..total_operations {
            let operation_start = Instant::now();
            
            let device_id = format!("benchmark_device_{}", i);
            
            // 创建会话
            let _session = self.authenticator.create_session(
                device_id.clone(),
                Some("benchmark_user".to_string()),
                Some("192.168.1.100".to_string()),
                Some("Performance Test".to_string()),
            );
            
            // 检查访问权限
            if self.authenticator.check_access(&device_id, "sensors/temperature", "read") {
                let latency = operation_start.elapsed();
                latencies.push(latency);
            } else {
                error_count += 1;
            }
        }

        let total_duration = start_time.elapsed();
        let result = self.calculate_benchmark_result(
            test_name.to_string(),
            total_operations,
            total_duration,
            latencies,
            error_count,
        );

        self.results.lock().await.push(result);
        println!("✅ 安全认证性能测试完成");
        Ok(())
    }

    /// 运行GPIO性能测试
    async fn run_gpio_performance_test(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🔌 运行GPIO性能测试...");

        // 配置测试引脚
        let pin_config = PinConfig {
            mode: PinMode::Output,
            initial_state: Some(PinState::Low),
            interrupt_trigger: None,
            debounce_time: None,
        };
        self.gpio_manager.configure_pin(18, pin_config).await?;

        let test_name = "GPIO操作性能";
        let total_operations = 2000;
        let mut latencies = Vec::new();
        let mut error_count = 0;
        let start_time = Instant::now();

        for i in 0..total_operations {
            let operation_start = Instant::now();
            
            let state = if i % 2 == 0 { PinState::High } else { PinState::Low };
            
            match self.gpio_manager.write_pin(18, state).await {
                Ok(_) => {
                    let latency = operation_start.elapsed();
                    latencies.push(latency);
                }
                Err(_) => {
                    error_count += 1;
                }
            }
        }

        let total_duration = start_time.elapsed();
        let result = self.calculate_benchmark_result(
            test_name.to_string(),
            total_operations,
            total_duration,
            latencies,
            error_count,
        );

        self.results.lock().await.push(result);
        println!("✅ GPIO性能测试完成");
        Ok(())
    }

    /// 运行并发性能测试
    async fn run_concurrent_performance_test(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        println!("⚡ 运行并发性能测试...");

        let test_name = "并发操作性能";
        let total_operations = 1000;
        let concurrent_tasks = 10;
        let operations_per_task = total_operations / concurrent_tasks;
        
        let mut latencies = Vec::new();
        let mut error_count = 0;
        let start_time = Instant::now();

        let mut handles = Vec::new();

        for task_id in 0..concurrent_tasks {
            let mut cache_system = self.cache_system.clone();
            let mut storage_manager = self.storage_manager.clone();
            let _rule_engine = self.rule_engine.clone();

            let handle = tokio::spawn(async move {
                let mut task_latencies = Vec::new();
                let mut task_errors = 0;

                for i in 0..operations_per_task {
                    let operation_start = Instant::now();
                    
                    let key = format!("concurrent_key_{}_{}", task_id, i);
                    let value = format!("concurrent_value_{}_{}", task_id, i);

                    // 并发缓存操作
                    match cache_system.set(&key, &value, Some(300)).await {
                        Ok(_) => {
                            // 并发存储操作
                            let mut fields = HashMap::new();
                            fields.insert("value".to_string(), serde_json::Value::Number(serde_json::Number::from(i)));
                            fields.insert("task_id".to_string(), serde_json::Value::Number(serde_json::Number::from(task_id)));
                            
                            let mut tags = HashMap::new();
                            tags.insert("device_id".to_string(), format!("concurrent_device_{}", task_id));
                            
                            let data_point = DataPoint {
                                timestamp: Utc::now(),
                                measurement: "concurrent_data".to_string(),
                                tags,
                                fields,
                            };

                            match storage_manager.store_data(data_point).await {
                                Ok(_) => {
                                    let latency = operation_start.elapsed();
                                    task_latencies.push(latency);
                                }
                                Err(_) => {
                                    task_errors += 1;
                                }
                            }
                        }
                        Err(_) => {
                            task_errors += 1;
                        }
                    }
                }

                (task_latencies, task_errors)
            });

            handles.push(handle);
        }

        // 等待所有任务完成
        for handle in handles {
            match handle.await {
                Ok((task_latencies, task_errors)) => {
                    latencies.extend(task_latencies);
                    error_count += task_errors;
                }
                Err(_) => {
                    error_count += operations_per_task;
                }
            }
        }

        let total_duration = start_time.elapsed();
        let result = self.calculate_benchmark_result(
            test_name.to_string(),
            total_operations,
            total_duration,
            latencies,
            error_count,
        );

        self.results.lock().await.push(result);
        println!("✅ 并发性能测试完成");
        Ok(())
    }

    /// 计算基准测试结果
    fn calculate_benchmark_result(
        &self,
        test_name: String,
        total_operations: u64,
        total_duration: Duration,
        latencies: Vec<Duration>,
        error_count: u64,
    ) -> BenchmarkResult {
        let success_count = total_operations - error_count;
        let success_rate = if total_operations > 0 {
            (success_count as f64 / total_operations as f64) * 100.0
        } else {
            0.0
        };

        let operations_per_second = if total_duration.as_secs() > 0 {
            total_operations as f64 / total_duration.as_secs() as f64
        } else {
            0.0
        };

        let average_latency = if !latencies.is_empty() {
            let total_latency: Duration = latencies.iter().sum();
            total_latency / latencies.len() as u32
        } else {
            Duration::from_millis(0)
        };

        let min_latency = latencies.iter().min().copied().unwrap_or(Duration::from_millis(0));
        let max_latency = latencies.iter().max().copied().unwrap_or(Duration::from_millis(0));

        BenchmarkResult {
            test_name: test_name.to_string(),
            total_operations,
            total_duration,
            operations_per_second,
            average_latency,
            min_latency,
            max_latency,
            success_rate,
            error_count,
            memory_usage: 0, // 需要系统特定的内存监控
            cpu_usage: 0.0,  // 需要系统特定的CPU监控
        }
    }

    /// 生成基准测试报告
    async fn generate_benchmark_report(&self, results: &[BenchmarkResult]) -> Result<(), Box<dyn std::error::Error>> {
        println!("\n📊 性能基准测试报告");
        println!("{}", "=".repeat(80));

        for result in results {
            println!("\n🔍 测试: {}", result.test_name);
            println!("  总操作数: {}", result.total_operations);
            println!("  总耗时: {:?}", result.total_duration);
            println!("  每秒操作数: {:.2}", result.operations_per_second);
            println!("  平均延迟: {:?}", result.average_latency);
            println!("  最小延迟: {:?}", result.min_latency);
            println!("  最大延迟: {:?}", result.max_latency);
            println!("  成功率: {:.2}%", result.success_rate);
            println!("  错误数: {}", result.error_count);
        }

        // 计算总体统计
        let total_operations: u64 = results.iter().map(|r| r.total_operations).sum();
        let total_duration: Duration = results.iter().map(|r| r.total_duration).sum();
        let total_errors: u64 = results.iter().map(|r| r.error_count).sum();
        let overall_success_rate = if total_operations > 0 {
            ((total_operations - total_errors) as f64 / total_operations as f64) * 100.0
        } else {
            0.0
        };

        println!("\n📈 总体统计");
        println!("  总操作数: {}", total_operations);
        println!("  总耗时: {:?}", total_duration);
        println!("  总体成功率: {:.2}%", overall_success_rate);
        println!("  总错误数: {}", total_errors);

        // 导出报告到JSON
        let report_data = serde_json::json!({
            "timestamp": Utc::now(),
            "results": results,
            "summary": {
                "total_operations": total_operations,
                "total_duration": total_duration.as_millis(),
                "overall_success_rate": overall_success_rate,
                "total_errors": total_errors,
            }
        });

        let report_json = serde_json::to_string_pretty(&report_data)?;
        println!("\n📄 详细报告 (JSON):");
        println!("{}", report_json);

        Ok(())
    }

    /// 获取测试结果
    pub async fn get_results(&self) -> Vec<BenchmarkResult> {
        self.results.lock().await.clone()
    }

    /// 清除测试结果
    pub async fn clear_results(&self) {
        self.results.lock().await.clear();
    }
}

impl Example for PerformanceBenchmark {
    fn name(&self) -> &'static str {
        "性能基准测试"
    }

    fn description(&self) -> &'static str {
        "全面的性能基准测试，包括通信、存储、缓存、规则引擎等各个组件的性能评估"
    }

    fn parameters(&self) -> Vec<ExampleParameter> {
        vec![
            ExampleParameter {
                name: "test_duration".to_string(),
                description: "测试持续时间（秒）".to_string(),
                parameter_type: ParameterType::Integer,
                default_value: Some("300".to_string()),
                required: false,
            },
            ExampleParameter {
                name: "concurrent_tasks".to_string(),
                description: "并发任务数".to_string(),
                parameter_type: ParameterType::Integer,
                default_value: Some("10".to_string()),
                required: false,
            },
            ExampleParameter {
                name: "operations_per_test".to_string(),
                description: "每个测试的操作数".to_string(),
                parameter_type: ParameterType::Integer,
                default_value: Some("1000".to_string()),
                required: false,
            },
        ]
    }

    fn run(&mut self, _parameters: HashMap<String, String>) -> impl std::future::Future<Output = Result<(), Box<dyn std::error::Error>>> + Send {
        async move {
            self.run_full_benchmark().await?;
            Ok(())
        }
    }
}

impl Default for PerformanceBenchmark {
    fn default() -> Self {
        Self::new().expect("Failed to create PerformanceBenchmark")
    }
}
