use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::sleep;
use tracing::{error, info, warn};
//use std::sync::atomic::{AtomicUsize, AtomicBool, Ordering};

/// 2025年异步混沌工程演示
/// 展示最新的异步混沌工程编程模式和最佳实践

/// 1. 异步混沌实验管理器
#[derive(Debug, Clone)]
pub struct AsyncChaosExperimentManager {
    experiments: Arc<RwLock<HashMap<String, ChaosExperiment>>>,
    active_experiments: Arc<RwLock<HashMap<String, ActiveExperiment>>>,
    config: ChaosConfig,
    stats: Arc<RwLock<ChaosStats>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosExperiment {
    pub id: String,
    pub name: String,
    pub description: String,
    pub chaos_type: ChaosType,
    pub target: ChaosTarget,
    pub parameters: HashMap<String, String>,
    pub duration: Duration,
    pub enabled: bool,
    pub created_at: u64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ChaosType {
    NetworkLatency,
    NetworkPartition,
    ServiceFailure,
    ResourceExhaustion,
    DataCorruption,
    TimeSkew,
    RandomFailure,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChaosTarget {
    pub service_name: String,
    pub instance_id: Option<String>,
    pub endpoint: Option<String>,
    pub percentage: f64,
}

#[derive(Debug, Clone)]
pub struct ActiveExperiment {
    pub experiment: ChaosExperiment,
    pub start_time: u64,
    pub end_time: Option<u64>,
    pub status: ExperimentStatus,
    pub impact_metrics: HashMap<String, f64>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExperimentStatus {
    Running,
    Completed,
    Failed,
    Cancelled,
}

#[derive(Debug, Clone)]
pub struct ChaosConfig {
    pub max_concurrent_experiments: usize,
    pub default_duration: Duration,
    pub safety_checks_enabled: bool,
    pub auto_rollback: bool,
    pub impact_threshold: f64,
}

impl Default for ChaosConfig {
    fn default() -> Self {
        Self {
            max_concurrent_experiments: 3,
            default_duration: Duration::from_secs(300),
            safety_checks_enabled: true,
            auto_rollback: true,
            impact_threshold: 0.8,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct ChaosStats {
    pub total_experiments: usize,
    pub successful_experiments: usize,
    pub failed_experiments: usize,
    pub cancelled_experiments: usize,
    pub auto_rollbacks: usize,
    pub safety_stops: usize,
}

impl AsyncChaosExperimentManager {
    pub fn new(config: ChaosConfig) -> Self {
        Self {
            experiments: Arc::new(RwLock::new(HashMap::new())),
            active_experiments: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(RwLock::new(ChaosStats::default())),
        }
    }

    pub async fn create_experiment(&self, experiment: ChaosExperiment) -> Result<()> {
        let mut experiments = self.experiments.write().await;
        experiments.insert(experiment.id.clone(), experiment.clone());

        let mut stats = self.stats.write().await;
        stats.total_experiments += 1;

        info!("创建混沌实验: {} ({})", experiment.name, experiment.id);
        Ok(())
    }

    pub async fn start_experiment(&self, experiment_id: &str) -> Result<()> {
        let experiments = self.experiments.read().await;
        let experiment = experiments
            .get(experiment_id)
            .ok_or_else(|| anyhow::anyhow!("实验 {} 不存在", experiment_id))?;

        if !experiment.enabled {
            return Err(anyhow::anyhow!("实验 {} 未启用", experiment_id));
        }

        let active_experiments = self.active_experiments.read().await;
        if active_experiments.len() >= self.config.max_concurrent_experiments {
            return Err(anyhow::anyhow!("已达到最大并发实验数限制"));
        }

        let active_experiment = ActiveExperiment {
            experiment: experiment.clone(),
            start_time: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            end_time: None,
            status: ExperimentStatus::Running,
            impact_metrics: HashMap::new(),
        };

        let mut active_experiments_write = self.active_experiments.write().await;
        active_experiments_write.insert(experiment_id.to_string(), active_experiment);

        // 启动实验执行
        let manager_clone = self.clone();
        let experiment_id_clone = experiment_id.to_string();

        tokio::spawn(async move {
            manager_clone.execute_experiment(&experiment_id_clone).await;
        });

        info!("启动混沌实验: {} ({})", experiment.name, experiment_id);
        Ok(())
    }

    #[allow(unused_variables)]
    async fn execute_experiment(&self, experiment_id: &str) {
        let experiment = {
            let active_experiments = self.active_experiments.read().await;
            active_experiments.get(experiment_id).cloned()
        };

        if let Some(mut active_experiment) = experiment {
            let start_time = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs();

            // 执行混沌实验
            match self.apply_chaos(&active_experiment.experiment).await {
                Ok(_) => {
                    info!("混沌实验执行成功: {}", experiment_id);

                    // 监控影响
                    let impact = self.monitor_impact(&active_experiment.experiment).await;
                    active_experiment.impact_metrics = impact;

                    // 等待实验持续时间
                    sleep(active_experiment.experiment.duration).await;

                    // 恢复服务
                    self.recover_service(&active_experiment.experiment).await;

                    active_experiment.end_time = Some(
                        std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .unwrap()
                            .as_secs(),
                    );
                    active_experiment.status = ExperimentStatus::Completed;

                    let mut stats = self.stats.write().await;
                    stats.successful_experiments += 1;
                }
                Err(e) => {
                    error!("混沌实验执行失败: {} - {}", experiment_id, e);

                    active_experiment.end_time = Some(
                        std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                            .unwrap()
                            .as_secs(),
                    );
                    active_experiment.status = ExperimentStatus::Failed;

                    let mut stats = self.stats.write().await;
                    stats.failed_experiments += 1;
                }
            }

            // 更新活跃实验状态
            let mut active_experiments = self.active_experiments.write().await;
            active_experiments.insert(experiment_id.to_string(), active_experiment);
        }
    }

    async fn apply_chaos(&self, experiment: &ChaosExperiment) -> Result<()> {
        match experiment.chaos_type {
            ChaosType::NetworkLatency => self.apply_network_latency(experiment).await,
            ChaosType::NetworkPartition => self.apply_network_partition(experiment).await,
            ChaosType::ServiceFailure => self.apply_service_failure(experiment).await,
            ChaosType::ResourceExhaustion => self.apply_resource_exhaustion(experiment).await,
            ChaosType::DataCorruption => self.apply_data_corruption(experiment).await,
            ChaosType::TimeSkew => self.apply_time_skew(experiment).await,
            ChaosType::RandomFailure => self.apply_random_failure(experiment).await,
        }
    }

    async fn apply_network_latency(&self, experiment: &ChaosExperiment) -> Result<()> {
        let latency_ms = experiment
            .parameters
            .get("latency_ms")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(100);

        info!(
            "应用网络延迟: {}ms 到服务 {}",
            latency_ms, experiment.target.service_name
        );

        // 模拟网络延迟
        sleep(Duration::from_millis(latency_ms)).await;
        Ok(())
    }

    async fn apply_network_partition(&self, experiment: &ChaosExperiment) -> Result<()> {
        info!("应用网络分区: 服务 {}", experiment.target.service_name);

        // 模拟网络分区
        sleep(Duration::from_millis(50)).await;
        Ok(())
    }

    async fn apply_service_failure(&self, experiment: &ChaosExperiment) -> Result<()> {
        let failure_rate = experiment.target.percentage;

        if rand::random::<f64>() < failure_rate {
            return Err(anyhow::anyhow!(
                "模拟服务故障: {}",
                experiment.target.service_name
            ));
        }

        info!(
            "应用服务故障: {} (故障率: {:.1}%)",
            experiment.target.service_name,
            failure_rate * 100.0
        );
        Ok(())
    }

    async fn apply_resource_exhaustion(&self, experiment: &ChaosExperiment) -> Result<()> {
        let cpu_usage = experiment
            .parameters
            .get("cpu_usage")
            .and_then(|s| s.parse::<f64>().ok())
            .unwrap_or(90.0);

        info!("应用资源耗尽: CPU使用率 {}%", cpu_usage);

        // 模拟高CPU使用
        let start = Instant::now();
        while start.elapsed() < Duration::from_millis(100) {
            // 消耗CPU
        }

        Ok(())
    }

    async fn apply_data_corruption(&self, experiment: &ChaosExperiment) -> Result<()> {
        info!("应用数据损坏: 服务 {}", experiment.target.service_name);

        // 模拟数据损坏
        sleep(Duration::from_millis(30)).await;
        Ok(())
    }

    async fn apply_time_skew(&self, experiment: &ChaosExperiment) -> Result<()> {
        let skew_seconds = experiment
            .parameters
            .get("skew_seconds")
            .and_then(|s| s.parse::<i64>().ok())
            .unwrap_or(60);

        info!("应用时间偏移: {} 秒", skew_seconds);

        // 模拟时间偏移
        sleep(Duration::from_millis(20)).await;
        Ok(())
    }

    async fn apply_random_failure(&self, experiment: &ChaosExperiment) -> Result<()> {
        let failure_probability = experiment.target.percentage;

        if rand::random::<f64>() < failure_probability {
            return Err(anyhow::anyhow!(
                "随机故障: {}",
                experiment.target.service_name
            ));
        }

        info!(
            "应用随机故障: {} (概率: {:.1}%)",
            experiment.target.service_name,
            failure_probability * 100.0
        );
        Ok(())
    }

    #[allow(unused_variables)]
    async fn monitor_impact(&self, experiment: &ChaosExperiment) -> HashMap<String, f64> {
        let mut impact_metrics = HashMap::new();

        // 模拟监控影响指标
        impact_metrics.insert("error_rate".to_string(), rand::random::<f64>() * 0.1);
        impact_metrics.insert("response_time".to_string(), rand::random::<f64>() * 1000.0);
        impact_metrics.insert("throughput".to_string(), rand::random::<f64>() * 100.0);

        info!(
            "监控实验影响: 错误率 {:.2}%, 响应时间 {:.0}ms, 吞吐量 {:.0} req/s",
            impact_metrics["error_rate"] * 100.0,
            impact_metrics["response_time"],
            impact_metrics["throughput"]
        );

        impact_metrics
    }

    async fn recover_service(&self, experiment: &ChaosExperiment) {
        info!("恢复服务: {}", experiment.target.service_name);

        // 模拟服务恢复
        sleep(Duration::from_millis(50)).await;
    }

    pub async fn cancel_experiment(&self, experiment_id: &str) -> Result<()> {
        let mut active_experiments = self.active_experiments.write().await;
        if let Some(active_experiment) = active_experiments.get_mut(experiment_id) {
            active_experiment.status = ExperimentStatus::Cancelled;
            active_experiment.end_time = Some(
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_secs(),
            );

            // 立即恢复服务
            self.recover_service(&active_experiment.experiment).await;

            let mut stats = self.stats.write().await;
            stats.cancelled_experiments += 1;

            info!("取消混沌实验: {}", experiment_id);
        }

        Ok(())
    }

    pub async fn get_active_experiments(&self) -> HashMap<String, ActiveExperiment> {
        self.active_experiments.read().await.clone()
    }

    pub async fn get_stats(&self) -> ChaosStats {
        self.stats.read().await.clone()
    }
}

/// 2. 异步故障注入器
#[derive(Debug, Clone)]
pub struct AsyncFaultInjector {
    injectors: Arc<RwLock<HashMap<String, FaultInjector>>>,
    config: FaultConfig,
    stats: Arc<RwLock<FaultStats>>,
}

#[derive(Debug, Clone)]
pub struct FaultInjector {
    pub id: String,
    pub name: String,
    pub fault_type: FaultType,
    pub target: String,
    pub injection_rate: f64,
    pub enabled: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FaultType {
    Exception,
    Timeout,
    MemoryLeak,
    Deadlock,
    ResourceLeak,
}

#[derive(Debug, Clone)]
pub struct FaultConfig {
    pub max_injection_rate: f64,
    pub default_duration: Duration,
    pub safety_enabled: bool,
}

impl Default for FaultConfig {
    fn default() -> Self {
        Self {
            max_injection_rate: 0.5,
            default_duration: Duration::from_secs(60),
            safety_enabled: true,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct FaultStats {
    pub total_injections: usize,
    pub successful_injections: usize,
    pub blocked_injections: usize,
    pub safety_stops: usize,
}

impl AsyncFaultInjector {
    pub fn new(config: FaultConfig) -> Self {
        Self {
            injectors: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(RwLock::new(FaultStats::default())),
        }
    }

    pub async fn add_injector(&self, injector: FaultInjector) -> Result<()> {
        let mut injectors = self.injectors.write().await;
        injectors.insert(injector.id.clone(), injector.clone());

        info!("添加故障注入器: {} ({})", injector.name, injector.id);
        Ok(())
    }

    pub async fn inject_fault(&self, injector_id: &str) -> Result<()> {
        let injectors = self.injectors.read().await;
        let injector = injectors
            .get(injector_id)
            .ok_or_else(|| anyhow::anyhow!("注入器 {} 不存在", injector_id))?;

        if !injector.enabled {
            return Ok(());
        }

        if injector.injection_rate > self.config.max_injection_rate {
            let mut stats = self.stats.write().await;
            stats.blocked_injections += 1;
            return Err(anyhow::anyhow!("注入率超过安全限制"));
        }

        if rand::random::<f64>() > injector.injection_rate {
            return Ok(());
        }

        match injector.fault_type {
            FaultType::Exception => self.inject_exception().await,
            FaultType::Timeout => self.inject_timeout().await,
            FaultType::MemoryLeak => self.inject_memory_leak().await,
            FaultType::Deadlock => self.inject_deadlock().await,
            FaultType::ResourceLeak => self.inject_resource_leak().await,
        }
    }

    async fn inject_exception(&self) -> Result<()> {
        let mut stats = self.stats.write().await;
        stats.total_injections += 1;
        stats.successful_injections += 1;

        error!("注入异常故障");
        Err(anyhow::anyhow!("注入的异常故障"))
    }

    async fn inject_timeout(&self) -> Result<()> {
        let mut stats = self.stats.write().await;
        stats.total_injections += 1;
        stats.successful_injections += 1;

        warn!("注入超时故障");
        sleep(Duration::from_secs(30)).await; // 模拟长时间阻塞
        Ok(())
    }

    async fn inject_memory_leak(&self) -> Result<()> {
        let mut stats = self.stats.write().await;
        stats.total_injections += 1;
        stats.successful_injections += 1;

        warn!("注入内存泄漏故障");

        // 模拟内存泄漏
        let mut _leaked_data = Vec::new();
        for _ in 0..1000 {
            _leaked_data.push(vec![0u8; 1024 * 1024]); // 1MB 泄漏
        }

        Ok(())
    }

    async fn inject_deadlock(&self) -> Result<()> {
        let mut stats = self.stats.write().await;
        stats.total_injections += 1;
        stats.successful_injections += 1;

        warn!("注入死锁故障");

        // 模拟死锁
        let lock1 = Arc::new(Mutex::new(0));
        let lock2 = Arc::new(Mutex::new(0));

        let lock1_clone = lock1.clone();
        let lock2_clone = lock2.clone();

        tokio::spawn(async move {
            let _guard1 = lock1_clone.lock().await;
            sleep(Duration::from_millis(100)).await;
            let _guard2 = lock2_clone.lock().await;
        });

        let _guard2 = lock2.lock().await;
        sleep(Duration::from_millis(100)).await;
        let _guard1 = lock1.lock().await;

        Ok(())
    }

    async fn inject_resource_leak(&self) -> Result<()> {
        let mut stats = self.stats.write().await;
        stats.total_injections += 1;
        stats.successful_injections += 1;

        warn!("注入资源泄漏故障");

        // 模拟资源泄漏
        for _ in 0..100 {
            let _handle = tokio::spawn(async {
                sleep(Duration::from_secs(3600)).await; // 长时间运行的任务
            });
        }

        Ok(())
    }

    pub async fn get_stats(&self) -> FaultStats {
        self.stats.read().await.clone()
    }
}

/// 3. 异步恢复测试器
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct AsyncRecoveryTester {
    recovery_tests: Arc<RwLock<Vec<RecoveryTest>>>,
    config: RecoveryConfig,
    stats: Arc<RwLock<RecoveryStats>>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct RecoveryTest {
    pub id: String,
    pub name: String,
    pub failure_scenario: FailureScenario,
    pub recovery_strategy: RecoveryStrategy,
    pub expected_recovery_time: Duration,
    pub enabled: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum FailureScenario {
    ServiceCrash,
    DatabaseUnavailable,
    NetworkPartition,
    ResourceExhaustion,
    DataCorruption,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RecoveryStrategy {
    AutomaticRestart,
    Failover,
    DataRestore,
    ServiceDegradation,
    ManualIntervention,
}

#[derive(Debug, Clone)]
pub struct RecoveryConfig {
    pub max_recovery_time: Duration,
    pub enable_auto_recovery: bool,
    pub recovery_timeout: Duration,
}

impl Default for RecoveryConfig {
    fn default() -> Self {
        Self {
            max_recovery_time: Duration::from_secs(300),
            enable_auto_recovery: true,
            recovery_timeout: Duration::from_secs(60),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct RecoveryStats {
    pub total_tests: usize,
    pub successful_recoveries: usize,
    pub failed_recoveries: usize,
    pub average_recovery_time: Duration,
}

impl AsyncRecoveryTester {
    pub fn new(config: RecoveryConfig) -> Self {
        Self {
            recovery_tests: Arc::new(RwLock::new(Vec::new())),
            config,
            stats: Arc::new(RwLock::new(RecoveryStats::default())),
        }
    }

    pub async fn add_recovery_test(&self, test: RecoveryTest) -> Result<()> {
        let mut tests = self.recovery_tests.write().await;
        tests.push(test.clone());

        let mut stats = self.stats.write().await;
        stats.total_tests += 1;

        info!("添加恢复测试: {} ({})", test.name, test.id);
        Ok(())
    }

    pub async fn run_recovery_test(&self, test_id: &str) -> Result<RecoveryResult> {
        let test = {
            let tests = self.recovery_tests.read().await;
            tests.iter().find(|t| t.id == test_id).cloned()
        };

        let test = test.ok_or_else(|| anyhow::anyhow!("恢复测试 {} 不存在", test_id))?;

        if !test.enabled {
            return Err(anyhow::anyhow!("恢复测试 {} 未启用", test_id));
        }

        let start_time = Instant::now();

        // 模拟故障
        self.simulate_failure(&test.failure_scenario).await;

        // 执行恢复策略
        let recovery_success = self.execute_recovery(&test.recovery_strategy).await;

        let recovery_time = start_time.elapsed();

        let result = RecoveryResult {
            test_id: test_id.to_string(),
            success: recovery_success,
            recovery_time,
            expected_time: test.expected_recovery_time,
            scenario: test.failure_scenario,
            strategy: test.recovery_strategy,
        };

        // 更新统计
        let mut stats = self.stats.write().await;
        if recovery_success {
            stats.successful_recoveries += 1;
        } else {
            stats.failed_recoveries += 1;
        }

        let total_tests = stats.total_tests;
        let current_avg = stats.average_recovery_time.as_millis() as u64;
        let new_avg = ((current_avg * (total_tests - 1) as u64) + recovery_time.as_millis() as u64)
            / total_tests as u64;
        stats.average_recovery_time = Duration::from_millis(new_avg);

        info!(
            "恢复测试完成: {} - {} (耗时: {:?})",
            test_id,
            if recovery_success { "成功" } else { "失败" },
            recovery_time
        );

        Ok(result)
    }

    async fn simulate_failure(&self, scenario: &FailureScenario) {
        match scenario {
            FailureScenario::ServiceCrash => {
                error!("模拟服务崩溃");
                sleep(Duration::from_millis(100)).await;
            }
            FailureScenario::DatabaseUnavailable => {
                error!("模拟数据库不可用");
                sleep(Duration::from_millis(200)).await;
            }
            FailureScenario::NetworkPartition => {
                error!("模拟网络分区");
                sleep(Duration::from_millis(150)).await;
            }
            FailureScenario::ResourceExhaustion => {
                error!("模拟资源耗尽");
                sleep(Duration::from_millis(300)).await;
            }
            FailureScenario::DataCorruption => {
                error!("模拟数据损坏");
                sleep(Duration::from_millis(250)).await;
            }
        }
    }

    async fn execute_recovery(&self, strategy: &RecoveryStrategy) -> bool {
        match strategy {
            RecoveryStrategy::AutomaticRestart => {
                info!("执行自动重启恢复");
                sleep(Duration::from_millis(500)).await;
                rand::random::<f64>() > 0.1 // 90% 成功率
            }
            RecoveryStrategy::Failover => {
                info!("执行故障转移恢复");
                sleep(Duration::from_millis(300)).await;
                rand::random::<f64>() > 0.05 // 95% 成功率
            }
            RecoveryStrategy::DataRestore => {
                info!("执行数据恢复");
                sleep(Duration::from_millis(1000)).await;
                rand::random::<f64>() > 0.15 // 85% 成功率
            }
            RecoveryStrategy::ServiceDegradation => {
                info!("执行服务降级恢复");
                sleep(Duration::from_millis(200)).await;
                rand::random::<f64>() > 0.02 // 98% 成功率
            }
            RecoveryStrategy::ManualIntervention => {
                info!("执行手动干预恢复");
                sleep(Duration::from_millis(2000)).await;
                rand::random::<f64>() > 0.2 // 80% 成功率
            }
        }
    }

    pub async fn get_stats(&self) -> RecoveryStats {
        self.stats.read().await.clone()
    }
}

#[derive(Debug, Clone)]
pub struct RecoveryResult {
    pub test_id: String,
    pub success: bool,
    pub recovery_time: Duration,
    pub expected_time: Duration,
    pub scenario: FailureScenario,
    pub strategy: RecoveryStrategy,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    info!("🚀 开始 2025 年异步混沌工程演示");

    // 1. 演示异步混沌实验管理器
    info!("🧪 演示异步混沌实验管理器");
    let chaos_config = ChaosConfig::default();
    let chaos_manager = AsyncChaosExperimentManager::new(chaos_config);

    // 创建混沌实验
    let experiments = vec![
        ChaosExperiment {
            id: "exp_1".to_string(),
            name: "网络延迟实验".to_string(),
            description: "测试网络延迟对服务的影响".to_string(),
            chaos_type: ChaosType::NetworkLatency,
            target: ChaosTarget {
                service_name: "api-gateway".to_string(),
                instance_id: None,
                endpoint: Some("/api/users".to_string()),
                percentage: 1.0,
            },
            parameters: [("latency_ms".to_string(), "100".to_string())]
                .iter()
                .cloned()
                .collect(),
            duration: Duration::from_secs(60),
            enabled: true,
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        },
        ChaosExperiment {
            id: "exp_2".to_string(),
            name: "服务故障实验".to_string(),
            description: "测试服务故障的恢复能力".to_string(),
            chaos_type: ChaosType::ServiceFailure,
            target: ChaosTarget {
                service_name: "user-service".to_string(),
                instance_id: Some("instance-1".to_string()),
                endpoint: None,
                percentage: 0.3,
            },
            parameters: HashMap::new(),
            duration: Duration::from_secs(120),
            enabled: true,
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        },
    ];

    for experiment in experiments {
        chaos_manager.create_experiment(experiment).await?;
    }

    // 启动混沌实验
    chaos_manager.start_experiment("exp_1").await?;
    chaos_manager.start_experiment("exp_2").await?;

    // 让实验运行一段时间
    sleep(Duration::from_millis(2000)).await;

    let active_experiments = chaos_manager.get_active_experiments().await;
    let chaos_stats = chaos_manager.get_stats().await;

    info!(
        "混沌实验统计: 总实验 {}, 成功 {}, 失败 {}",
        chaos_stats.total_experiments,
        chaos_stats.successful_experiments,
        chaos_stats.failed_experiments
    );

    for (id, experiment) in active_experiments {
        info!(
            "活跃实验: {} - {} ({:?})",
            id, experiment.experiment.name, experiment.status
        );
    }

    // 2. 演示异步故障注入器
    info!("💉 演示异步故障注入器");
    let fault_config = FaultConfig::default();
    let fault_injector = AsyncFaultInjector::new(fault_config);

    // 添加故障注入器
    let injectors = vec![
        FaultInjector {
            id: "injector_1".to_string(),
            name: "异常注入器".to_string(),
            fault_type: FaultType::Exception,
            target: "api-gateway".to_string(),
            injection_rate: 0.1,
            enabled: true,
        },
        FaultInjector {
            id: "injector_2".to_string(),
            name: "超时注入器".to_string(),
            fault_type: FaultType::Timeout,
            target: "user-service".to_string(),
            injection_rate: 0.05,
            enabled: true,
        },
    ];

    for injector in injectors {
        fault_injector.add_injector(injector).await?;
    }

    // 执行故障注入
    for _ in 0..10 {
        let _ = fault_injector.inject_fault("injector_1").await;
        let _ = fault_injector.inject_fault("injector_2").await;
        sleep(Duration::from_millis(100)).await;
    }

    let fault_stats = fault_injector.get_stats().await;
    info!(
        "故障注入统计: 总注入 {}, 成功注入 {}, 阻止注入 {}",
        fault_stats.total_injections,
        fault_stats.successful_injections,
        fault_stats.blocked_injections
    );

    // 3. 演示异步恢复测试器
    info!("🔄 演示异步恢复测试器");
    let recovery_config = RecoveryConfig::default();
    let recovery_tester = AsyncRecoveryTester::new(recovery_config);

    // 添加恢复测试
    let tests = vec![
        RecoveryTest {
            id: "test_1".to_string(),
            name: "服务崩溃恢复测试".to_string(),
            failure_scenario: FailureScenario::ServiceCrash,
            recovery_strategy: RecoveryStrategy::AutomaticRestart,
            expected_recovery_time: Duration::from_secs(30),
            enabled: true,
        },
        RecoveryTest {
            id: "test_2".to_string(),
            name: "数据库不可用恢复测试".to_string(),
            failure_scenario: FailureScenario::DatabaseUnavailable,
            recovery_strategy: RecoveryStrategy::Failover,
            expected_recovery_time: Duration::from_secs(60),
            enabled: true,
        },
    ];

    for test in tests {
        recovery_tester.add_recovery_test(test).await?;
    }

    // 运行恢复测试
    for test_id in &["test_1", "test_2"] {
        match recovery_tester.run_recovery_test(test_id).await {
            Ok(result) => {
                info!(
                    "恢复测试结果: {} - {} (耗时: {:?}, 预期: {:?})",
                    result.test_id,
                    if result.success { "成功" } else { "失败" },
                    result.recovery_time,
                    result.expected_time
                );
            }
            Err(e) => {
                error!("恢复测试失败: {} - {}", test_id, e);
            }
        }
    }

    let recovery_stats = recovery_tester.get_stats().await;
    info!(
        "恢复测试统计: 总测试 {}, 成功恢复 {}, 失败恢复 {}, 平均恢复时间 {:?}",
        recovery_stats.total_tests,
        recovery_stats.successful_recoveries,
        recovery_stats.failed_recoveries,
        recovery_stats.average_recovery_time
    );

    info!("✅ 2025 年异步混沌工程演示完成!");

    Ok(())
}
