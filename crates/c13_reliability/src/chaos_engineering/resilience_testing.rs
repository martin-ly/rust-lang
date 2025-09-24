//! 弹性测试实现
//!
//! 提供系统弹性测试功能，包括负载测试、压力测试、恢复测试等。

use std::collections::HashMap;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use tracing::{error, info};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 弹性测试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResilienceTestingConfig {
    /// 是否启用弹性测试
    pub enabled: bool,
    /// 测试间隔
    pub test_interval: Duration,
    /// 测试持续时间
    pub test_duration: Duration,
    /// 测试类型
    pub test_types: Vec<ResilienceTestType>,
    /// 负载级别
    pub load_levels: Vec<LoadLevel>,
    /// 最大并发测试数
    pub max_concurrent_tests: usize,
}

impl Default for ResilienceTestingConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            test_interval: Duration::from_secs(600), // 10分钟
            test_duration: Duration::from_secs(300), // 5分钟
            test_types: vec![
                ResilienceTestType::LoadTest,
                ResilienceTestType::StressTest,
                ResilienceTestType::RecoveryTest,
                ResilienceTestType::EnduranceTest,
            ],
            load_levels: vec![
                LoadLevel::Normal,
                LoadLevel::High,
                LoadLevel::Extreme,
            ],
            max_concurrent_tests: 5,
        }
    }
}

/// 弹性测试类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ResilienceTestType {
    /// 负载测试
    LoadTest,
    /// 压力测试
    StressTest,
    /// 恢复测试
    RecoveryTest,
    /// 耐力测试
    EnduranceTest,
    /// 峰值测试
    SpikeTest,
    /// 容量测试
    CapacityTest,
    /// 自定义测试
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

/// 负载级别
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LoadLevel {
    /// 正常负载
    Normal,
    /// 高负载
    High,
    /// 极限负载
    Extreme,
    /// 自定义负载
    Custom {
        level: u32,
        description: String,
    },
}

impl LoadLevel {
    /// 获取负载级别的数值
    pub fn as_numeric(&self) -> u32 {
        match self {
            LoadLevel::Normal => 1,
            LoadLevel::High => 2,
            LoadLevel::Extreme => 3,
            LoadLevel::Custom { level, .. } => *level,
        }
    }
}

/// 弹性测试结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResilienceTestingResult {
    /// 测试时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 总测试数
    pub total_tests: usize,
    /// 成功测试数
    pub successful_tests: usize,
    /// 失败测试数
    pub failed_tests: usize,
    /// 测试详情
    pub test_details: Vec<ResilienceTestDetail>,
    /// 平均响应时间
    pub average_response_time: Duration,
    /// 最大响应时间
    pub max_response_time: Duration,
    /// 最小响应时间
    pub min_response_time: Duration,
    /// 成功率
    pub success_rate: f64,
    /// 吞吐量
    pub throughput: f64,
    /// 错误率
    pub error_rate: f64,
}

/// 弹性测试详情
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResilienceTestDetail {
    /// 测试ID
    pub test_id: String,
    /// 测试类型
    pub test_type: ResilienceTestType,
    /// 负载级别
    pub load_level: LoadLevel,
    /// 开始时间
    pub start_time: chrono::DateTime<chrono::Utc>,
    /// 结束时间
    pub end_time: Option<chrono::DateTime<chrono::Utc>>,
    /// 持续时间
    pub duration: Duration,
    /// 是否成功
    pub success: bool,
    /// 响应时间
    pub response_time: Duration,
    /// 测试参数
    pub parameters: HashMap<String, String>,
    /// 测试指标
    pub metrics: HashMap<String, f64>,
}

/// 弹性测试器
pub struct ResilienceTester {
    config: ResilienceTestingConfig,
    active_tests: std::sync::Mutex<HashMap<String, ResilienceTestDetail>>,
    test_history: std::sync::Mutex<Vec<ResilienceTestDetail>>,
    is_running: std::sync::atomic::AtomicBool,
}

impl ResilienceTester {
    /// 创建新的弹性测试器
    pub fn new(config: ResilienceTestingConfig) -> Self {
        Self {
            config,
            active_tests: std::sync::Mutex::new(HashMap::new()),
            test_history: std::sync::Mutex::new(Vec::new()),
            is_running: std::sync::atomic::AtomicBool::new(false),
        }
    }

    /// 启动弹性测试
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if !self.config.enabled {
            return Err(UnifiedError::new(
                "弹性测试未启用",
                ErrorSeverity::Medium,
                "resilience_testing",
                ErrorContext::new("resilience_testing", "start", file!(), line!(), ErrorSeverity::Medium, "resilience_testing")
            ));
        }

        self.is_running.store(true, std::sync::atomic::Ordering::Relaxed);
        info!("弹性测试器启动");
        Ok(())
    }

    /// 停止弹性测试
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        
        // 清理所有活动测试
        self.clear_all_tests().await;
        
        info!("弹性测试器停止");
        Ok(())
    }

    /// 测试弹性
    pub async fn test_resilience(&self) -> Result<ResilienceTestingResult, UnifiedError> {
        let timestamp = chrono::Utc::now();
        let mut total_tests = 0;
        let mut successful_tests = 0;
        let mut failed_tests = 0;
        let mut test_details = Vec::new();
        let mut total_response_time = Duration::ZERO;
        let mut max_response_time = Duration::ZERO;
        let mut min_response_time = Duration::MAX;
        let mut total_requests = 0;
        let mut total_errors = 0;

        // 执行各种类型的弹性测试
        for test_type in &self.config.test_types {
            for load_level in &self.config.load_levels {
                total_tests += 1;
                
                match self.execute_single_test(test_type.clone(), load_level.clone()).await {
                    Ok(test_detail) => {
                        if test_detail.success {
                            successful_tests += 1;
                        } else {
                            failed_tests += 1;
                        }
                        
                        // 更新响应时间统计
                        total_response_time += test_detail.response_time;
                        if test_detail.response_time > max_response_time {
                            max_response_time = test_detail.response_time;
                        }
                        if test_detail.response_time < min_response_time {
                            min_response_time = test_detail.response_time;
                        }
                        
                        // 更新请求和错误统计
                        if let Some(requests) = test_detail.metrics.get("total_requests") {
                            total_requests += *requests as u64;
                        }
                        if let Some(errors) = test_detail.metrics.get("total_errors") {
                            total_errors += *errors as u64;
                        }
                        
                        test_details.push(test_detail);
                    }
                    Err(error) => {
                        failed_tests += 1;
                        error!("弹性测试执行失败: {}", error);
                    }
                }
            }
        }

        // 计算成功率
        let success_rate = if total_tests > 0 {
            successful_tests as f64 / total_tests as f64
        } else {
            0.0
        };

        // 计算平均响应时间
        let average_response_time = if total_tests > 0 {
            total_response_time / total_tests as u32
        } else {
            Duration::ZERO
        };

        // 计算吞吐量
        let throughput = if total_requests > 0 {
            total_requests as f64 / self.config.test_duration.as_secs() as f64
        } else {
            0.0
        };

        // 计算错误率
        let error_rate = if total_requests > 0 {
            total_errors as f64 / total_requests as f64
        } else {
            0.0
        };

        let result = ResilienceTestingResult {
            timestamp,
            total_tests,
            successful_tests,
            failed_tests,
            test_details,
            average_response_time,
            max_response_time,
            min_response_time,
            success_rate,
            throughput,
            error_rate,
        };

        info!("弹性测试完成，成功率: {:.2}%，吞吐量: {:.2} req/s，错误率: {:.2}%", 
              success_rate * 100.0, throughput, error_rate * 100.0);

        Ok(result)
    }

    /// 执行单个测试
    async fn execute_single_test(&self, test_type: ResilienceTestType, load_level: LoadLevel) -> Result<ResilienceTestDetail, UnifiedError> {
        let test_id = self.generate_test_id();
        let start_time = chrono::Utc::now();
        
        info!("执行弹性测试: {} (负载级别: {}) (ID: {})", 
              self.test_type_to_string(&test_type), 
              self.load_level_to_string(&load_level), 
              test_id);

        // 创建测试详情
        let mut test_detail = ResilienceTestDetail {
            test_id: test_id.clone(),
            test_type: test_type.clone(),
            load_level: load_level.clone(),
            start_time,
            end_time: None,
            duration: Duration::ZERO,
            success: false,
            response_time: Duration::ZERO,
            parameters: HashMap::new(),
            metrics: HashMap::new(),
        };

        // 执行测试
        match self.execute_test(&test_type, &load_level, &mut test_detail).await {
            Ok(()) => {
                let end_time = chrono::Utc::now();
                test_detail.end_time = Some(end_time);
                test_detail.duration = end_time.signed_duration_since(start_time).to_std().unwrap_or(Duration::ZERO);
                test_detail.success = true;
                
                // 添加到历史记录
                self.add_to_history(test_detail.clone());
                
                Ok(test_detail)
            }
            Err(error) => {
                error!("弹性测试执行失败: {}", error);
                Err(error)
            }
        }
    }

    /// 执行测试
    async fn execute_test(&self, test_type: &ResilienceTestType, load_level: &LoadLevel, test_detail: &mut ResilienceTestDetail) -> Result<(), UnifiedError> {
        match test_type {
            ResilienceTestType::LoadTest => {
                self.execute_load_test(load_level, test_detail).await
            }
            ResilienceTestType::StressTest => {
                self.execute_stress_test(load_level, test_detail).await
            }
            ResilienceTestType::RecoveryTest => {
                self.execute_recovery_test(load_level, test_detail).await
            }
            ResilienceTestType::EnduranceTest => {
                self.execute_endurance_test(load_level, test_detail).await
            }
            ResilienceTestType::SpikeTest => {
                self.execute_spike_test(load_level, test_detail).await
            }
            ResilienceTestType::CapacityTest => {
                self.execute_capacity_test(load_level, test_detail).await
            }
            ResilienceTestType::Custom { name, parameters } => {
                self.execute_custom_test(name, parameters, load_level, test_detail).await
            }
        }
    }

    /// 执行负载测试
    async fn execute_load_test(&self, load_level: &LoadLevel, test_detail: &mut ResilienceTestDetail) -> Result<(), UnifiedError> {
        test_detail.parameters.insert("test_type".to_string(), "load_test".to_string());
        test_detail.parameters.insert("load_level".to_string(), self.load_level_to_string(load_level));
        
        let load_multiplier = load_level.as_numeric() as f64;
        let concurrent_users = (100.0 * load_multiplier) as u32;
        let requests_per_second = (50.0 * load_multiplier) as u32;
        
        test_detail.parameters.insert("concurrent_users".to_string(), concurrent_users.to_string());
        test_detail.parameters.insert("requests_per_second".to_string(), requests_per_second.to_string());
        
        // 模拟负载测试
        let start_time = std::time::Instant::now();
        self.simulate_load(concurrent_users, requests_per_second).await;
        test_detail.response_time = start_time.elapsed();
        
        // 设置测试指标
        test_detail.metrics.insert("concurrent_users".to_string(), concurrent_users as f64);
        test_detail.metrics.insert("requests_per_second".to_string(), requests_per_second as f64);
        test_detail.metrics.insert("total_requests".to_string(), requests_per_second as f64 * 10.0);
        test_detail.metrics.insert("total_errors".to_string(), requests_per_second as f64 * 0.01);
        
        info!("负载测试完成，并发用户: {}，每秒请求: {}", concurrent_users, requests_per_second);
        Ok(())
    }

    /// 执行压力测试
    async fn execute_stress_test(&self, load_level: &LoadLevel, test_detail: &mut ResilienceTestDetail) -> Result<(), UnifiedError> {
        test_detail.parameters.insert("test_type".to_string(), "stress_test".to_string());
        test_detail.parameters.insert("load_level".to_string(), self.load_level_to_string(load_level));
        
        let stress_multiplier = load_level.as_numeric() as f64 * 2.0; // 压力测试使用更高的负载
        let concurrent_users = (200.0 * stress_multiplier) as u32;
        let requests_per_second = (100.0 * stress_multiplier) as u32;
        
        test_detail.parameters.insert("concurrent_users".to_string(), concurrent_users.to_string());
        test_detail.parameters.insert("requests_per_second".to_string(), requests_per_second.to_string());
        
        // 模拟压力测试
        let start_time = std::time::Instant::now();
        self.simulate_stress(concurrent_users, requests_per_second).await;
        test_detail.response_time = start_time.elapsed();
        
        // 设置测试指标
        test_detail.metrics.insert("concurrent_users".to_string(), concurrent_users as f64);
        test_detail.metrics.insert("requests_per_second".to_string(), requests_per_second as f64);
        test_detail.metrics.insert("total_requests".to_string(), requests_per_second as f64 * 15.0);
        test_detail.metrics.insert("total_errors".to_string(), requests_per_second as f64 * 0.05);
        
        info!("压力测试完成，并发用户: {}，每秒请求: {}", concurrent_users, requests_per_second);
        Ok(())
    }

    /// 执行恢复测试
    async fn execute_recovery_test(&self, load_level: &LoadLevel, test_detail: &mut ResilienceTestDetail) -> Result<(), UnifiedError> {
        test_detail.parameters.insert("test_type".to_string(), "recovery_test".to_string());
        test_detail.parameters.insert("load_level".to_string(), self.load_level_to_string(load_level));
        
        let recovery_multiplier = load_level.as_numeric() as f64;
        let failure_duration = Duration::from_secs((10.0 * recovery_multiplier) as u64);
        let recovery_time = Duration::from_secs((5.0 * recovery_multiplier) as u64);
        
        test_detail.parameters.insert("failure_duration".to_string(), failure_duration.as_secs().to_string());
        test_detail.parameters.insert("recovery_time".to_string(), recovery_time.as_secs().to_string());
        
        // 模拟恢复测试
        let start_time = std::time::Instant::now();
        self.simulate_recovery(failure_duration, recovery_time).await;
        test_detail.response_time = start_time.elapsed();
        
        // 设置测试指标
        test_detail.metrics.insert("failure_duration".to_string(), failure_duration.as_secs() as f64);
        test_detail.metrics.insert("recovery_time".to_string(), recovery_time.as_secs() as f64);
        test_detail.metrics.insert("recovery_success_rate".to_string(), 0.95);
        
        info!("恢复测试完成，故障持续时间: {:?}，恢复时间: {:?}", failure_duration, recovery_time);
        Ok(())
    }

    /// 执行耐力测试
    async fn execute_endurance_test(&self, load_level: &LoadLevel, test_detail: &mut ResilienceTestDetail) -> Result<(), UnifiedError> {
        test_detail.parameters.insert("test_type".to_string(), "endurance_test".to_string());
        test_detail.parameters.insert("load_level".to_string(), self.load_level_to_string(load_level));
        
        let endurance_multiplier = load_level.as_numeric() as f64;
        let test_duration = Duration::from_secs((300.0 * endurance_multiplier) as u64);
        let concurrent_users = (50.0 * endurance_multiplier) as u32;
        
        test_detail.parameters.insert("test_duration".to_string(), test_duration.as_secs().to_string());
        test_detail.parameters.insert("concurrent_users".to_string(), concurrent_users.to_string());
        
        // 模拟耐力测试
        let start_time = std::time::Instant::now();
        self.simulate_endurance(test_duration, concurrent_users).await;
        test_detail.response_time = start_time.elapsed();
        
        // 设置测试指标
        test_detail.metrics.insert("test_duration".to_string(), test_duration.as_secs() as f64);
        test_detail.metrics.insert("concurrent_users".to_string(), concurrent_users as f64);
        test_detail.metrics.insert("total_requests".to_string(), concurrent_users as f64 * 100.0);
        test_detail.metrics.insert("total_errors".to_string(), concurrent_users as f64 * 0.02);
        
        info!("耐力测试完成，测试持续时间: {:?}，并发用户: {}", test_duration, concurrent_users);
        Ok(())
    }

    /// 执行峰值测试
    async fn execute_spike_test(&self, load_level: &LoadLevel, test_detail: &mut ResilienceTestDetail) -> Result<(), UnifiedError> {
        test_detail.parameters.insert("test_type".to_string(), "spike_test".to_string());
        test_detail.parameters.insert("load_level".to_string(), self.load_level_to_string(load_level));
        
        let spike_multiplier = load_level.as_numeric() as f64 * 3.0; // 峰值测试使用更高的负载
        let spike_duration = Duration::from_secs(30);
        let concurrent_users = (300.0 * spike_multiplier) as u32;
        
        test_detail.parameters.insert("spike_duration".to_string(), spike_duration.as_secs().to_string());
        test_detail.parameters.insert("concurrent_users".to_string(), concurrent_users.to_string());
        
        // 模拟峰值测试
        let start_time = std::time::Instant::now();
        self.simulate_spike(spike_duration, concurrent_users).await;
        test_detail.response_time = start_time.elapsed();
        
        // 设置测试指标
        test_detail.metrics.insert("spike_duration".to_string(), spike_duration.as_secs() as f64);
        test_detail.metrics.insert("concurrent_users".to_string(), concurrent_users as f64);
        test_detail.metrics.insert("total_requests".to_string(), concurrent_users as f64 * 5.0);
        test_detail.metrics.insert("total_errors".to_string(), concurrent_users as f64 * 0.1);
        
        info!("峰值测试完成，峰值持续时间: {:?}，并发用户: {}", spike_duration, concurrent_users);
        Ok(())
    }

    /// 执行容量测试
    async fn execute_capacity_test(&self, load_level: &LoadLevel, test_detail: &mut ResilienceTestDetail) -> Result<(), UnifiedError> {
        test_detail.parameters.insert("test_type".to_string(), "capacity_test".to_string());
        test_detail.parameters.insert("load_level".to_string(), self.load_level_to_string(load_level));
        
        let capacity_multiplier = load_level.as_numeric() as f64;
        let max_concurrent_users = (500.0 * capacity_multiplier) as u32;
        let max_requests_per_second = (200.0 * capacity_multiplier) as u32;
        
        test_detail.parameters.insert("max_concurrent_users".to_string(), max_concurrent_users.to_string());
        test_detail.parameters.insert("max_requests_per_second".to_string(), max_requests_per_second.to_string());
        
        // 模拟容量测试
        let start_time = std::time::Instant::now();
        self.simulate_capacity(max_concurrent_users, max_requests_per_second).await;
        test_detail.response_time = start_time.elapsed();
        
        // 设置测试指标
        test_detail.metrics.insert("max_concurrent_users".to_string(), max_concurrent_users as f64);
        test_detail.metrics.insert("max_requests_per_second".to_string(), max_requests_per_second as f64);
        test_detail.metrics.insert("total_requests".to_string(), max_requests_per_second as f64 * 20.0);
        test_detail.metrics.insert("total_errors".to_string(), max_requests_per_second as f64 * 0.03);
        
        info!("容量测试完成，最大并发用户: {}，最大每秒请求: {}", max_concurrent_users, max_requests_per_second);
        Ok(())
    }

    /// 执行自定义测试
    async fn execute_custom_test(&self, name: &str, parameters: &HashMap<String, String>, load_level: &LoadLevel, test_detail: &mut ResilienceTestDetail) -> Result<(), UnifiedError> {
        test_detail.parameters.insert("test_type".to_string(), format!("custom_test: {}", name));
        test_detail.parameters.insert("load_level".to_string(), self.load_level_to_string(load_level));
        test_detail.parameters.extend(parameters.clone());
        
        // 模拟自定义测试
        let start_time = std::time::Instant::now();
        self.simulate_custom_test(name, parameters).await;
        test_detail.response_time = start_time.elapsed();
        
        // 设置测试指标
        test_detail.metrics.insert("custom_test_name".to_string(), name.len() as f64);
        test_detail.metrics.insert("total_requests".to_string(), 100.0);
        test_detail.metrics.insert("total_errors".to_string(), 2.0);
        
        info!("自定义测试完成: {}", name);
        Ok(())
    }

    /// 模拟负载
    async fn simulate_load(&self, concurrent_users: u32, requests_per_second: u32) {
        let mut handles = Vec::new();
        
        for _ in 0..concurrent_users {
            let handle = tokio::spawn(async move {
                for _ in 0..requests_per_second {
                    // 模拟请求处理
                    tokio::time::sleep(Duration::from_millis(10)).await;
                }
            });
            handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in handles {
            let _ = handle.await;
        }
    }

    /// 模拟压力
    async fn simulate_stress(&self, concurrent_users: u32, requests_per_second: u32) {
        let mut handles = Vec::new();
        
        for _ in 0..concurrent_users {
            let handle = tokio::spawn(async move {
                for _ in 0..requests_per_second {
                    // 模拟高压力请求处理
                    tokio::time::sleep(Duration::from_millis(5)).await;
                }
            });
            handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in handles {
            let _ = handle.await;
        }
    }

    /// 模拟恢复
    async fn simulate_recovery(&self, failure_duration: Duration, recovery_time: Duration) {
        // 模拟故障
        tokio::time::sleep(failure_duration).await;
        
        // 模拟恢复
        tokio::time::sleep(recovery_time).await;
    }

    /// 模拟耐力
    async fn simulate_endurance(&self, test_duration: Duration, concurrent_users: u32) {
        let start_time = std::time::Instant::now();
        
        while start_time.elapsed() < test_duration {
            let mut handles = Vec::new();
            
            for _ in 0..concurrent_users {
                let handle = tokio::spawn(async move {
                    // 模拟持续请求
                    tokio::time::sleep(Duration::from_millis(20)).await;
                });
                handles.push(handle);
            }
            
            // 等待所有任务完成
            for handle in handles {
                let _ = handle.await;
            }
        }
    }

    /// 模拟峰值
    async fn simulate_spike(&self, spike_duration: Duration, concurrent_users: u32) {
        let start_time = std::time::Instant::now();
        
        while start_time.elapsed() < spike_duration {
            let mut handles = Vec::new();
            
            for _ in 0..concurrent_users {
                let handle = tokio::spawn(async move {
                    // 模拟峰值请求
                    tokio::time::sleep(Duration::from_millis(2)).await;
                });
                handles.push(handle);
            }
            
            // 等待所有任务完成
            for handle in handles {
                let _ = handle.await;
            }
        }
    }

    /// 模拟容量
    async fn simulate_capacity(&self, max_concurrent_users: u32, max_requests_per_second: u32) {
        let mut handles = Vec::new();
        
        for _ in 0..max_concurrent_users {
            let handle = tokio::spawn(async move {
                for _ in 0..max_requests_per_second {
                    // 模拟容量测试请求
                    tokio::time::sleep(Duration::from_millis(1)).await;
                }
            });
            handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in handles {
            let _ = handle.await;
        }
    }

    /// 模拟自定义测试
    async fn simulate_custom_test(&self, _name: &str, parameters: &HashMap<String, String>) {
        // 模拟自定义测试逻辑
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        // 根据参数调整测试行为
        if let Some(duration) = parameters.get("duration") {
            if let Ok(duration_ms) = duration.parse::<u64>() {
                tokio::time::sleep(Duration::from_millis(duration_ms)).await;
            }
        }
    }

    /// 清理所有测试
    async fn clear_all_tests(&self) {
        let mut active_tests = self.active_tests.lock().unwrap();
        active_tests.clear();
        info!("所有活动测试已清理");
    }

    /// 生成测试ID
    fn generate_test_id(&self) -> String {
        use rand::Rng;
        let mut rng = rand::rng();
        format!("test_{}", rng.random_range(0..u32::MAX))
    }

    /// 测试类型转字符串
    fn test_type_to_string(&self, test_type: &ResilienceTestType) -> String {
        match test_type {
            ResilienceTestType::LoadTest => "负载测试".to_string(),
            ResilienceTestType::StressTest => "压力测试".to_string(),
            ResilienceTestType::RecoveryTest => "恢复测试".to_string(),
            ResilienceTestType::EnduranceTest => "耐力测试".to_string(),
            ResilienceTestType::SpikeTest => "峰值测试".to_string(),
            ResilienceTestType::CapacityTest => "容量测试".to_string(),
            ResilienceTestType::Custom { name, .. } => format!("自定义测试: {}", name),
        }
    }

    /// 负载级别转字符串
    fn load_level_to_string(&self, load_level: &LoadLevel) -> String {
        match load_level {
            LoadLevel::Normal => "正常".to_string(),
            LoadLevel::High => "高".to_string(),
            LoadLevel::Extreme => "极限".to_string(),
            LoadLevel::Custom { level, description } => format!("自定义{}: {}", level, description),
        }
    }

    /// 添加到历史记录
    fn add_to_history(&self, test_detail: ResilienceTestDetail) {
        let mut history = self.test_history.lock().unwrap();
        history.push(test_detail);
        
        // 保持最近1000个测试记录
        if history.len() > 1000 {
            let len = history.len();
            history.drain(0..len - 1000);
        }
    }

    /// 获取测试历史
    pub fn get_test_history(&self) -> Vec<ResilienceTestDetail> {
        self.test_history.lock().unwrap().clone()
    }

    /// 获取活动测试
    pub fn get_active_tests(&self) -> Vec<ResilienceTestDetail> {
        self.active_tests.lock().unwrap().values().cloned().collect()
    }

    /// 获取配置
    pub fn get_config(&self) -> &ResilienceTestingConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: ResilienceTestingConfig) {
        self.config = config;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resilience_testing_config_default() {
        let config = ResilienceTestingConfig::default();
        assert!(!config.enabled);
        assert_eq!(config.test_interval, Duration::from_secs(600));
        assert_eq!(config.test_duration, Duration::from_secs(300));
        assert!(!config.test_types.is_empty());
        assert!(!config.load_levels.is_empty());
        assert_eq!(config.max_concurrent_tests, 5);
    }

    #[test]
    fn test_resilience_test_type() {
        let test_type = ResilienceTestType::LoadTest;
        assert!(matches!(test_type, ResilienceTestType::LoadTest));
    }

    #[test]
    fn test_load_level() {
        assert_eq!(LoadLevel::Normal.as_numeric(), 1);
        assert_eq!(LoadLevel::High.as_numeric(), 2);
        assert_eq!(LoadLevel::Extreme.as_numeric(), 3);
        
        let custom_level = LoadLevel::Custom { level: 5, description: "test".to_string() };
        assert_eq!(custom_level.as_numeric(), 5);
    }

    #[test]
    fn test_resilience_test_detail() {
        let test_detail = ResilienceTestDetail {
            test_id: "test_123".to_string(),
            test_type: ResilienceTestType::LoadTest,
            load_level: LoadLevel::Normal,
            start_time: chrono::Utc::now(),
            end_time: None,
            duration: Duration::ZERO,
            success: false,
            response_time: Duration::ZERO,
            parameters: HashMap::new(),
            metrics: HashMap::new(),
        };
        
        assert_eq!(test_detail.test_id, "test_123");
        assert!(!test_detail.success);
    }

    #[test]
    fn test_resilience_tester_creation() {
        let config = ResilienceTestingConfig::default();
        let tester = ResilienceTester::new(config);
        
        assert!(tester.get_test_history().is_empty());
        assert!(tester.get_active_tests().is_empty());
    }

    #[test]
    fn test_resilience_testing_result() {
        let result = ResilienceTestingResult {
            timestamp: chrono::Utc::now(),
            total_tests: 10,
            successful_tests: 8,
            failed_tests: 2,
            test_details: Vec::new(),
            average_response_time: Duration::from_millis(100),
            max_response_time: Duration::from_millis(500),
            min_response_time: Duration::from_millis(50),
            success_rate: 0.8,
            throughput: 100.0,
            error_rate: 0.02,
        };
        
        assert_eq!(result.total_tests, 10);
        assert_eq!(result.successful_tests, 8);
        assert_eq!(result.failed_tests, 2);
        assert_eq!(result.success_rate, 0.8);
        assert_eq!(result.throughput, 100.0);
        assert_eq!(result.error_rate, 0.02);
    }
}
