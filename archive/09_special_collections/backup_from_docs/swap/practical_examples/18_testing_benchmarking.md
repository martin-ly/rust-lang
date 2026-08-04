# C07-18. 测试与基准测试示例 (Rust 1.90 增强版)

## 目录

- [C07-18. 测试与基准测试示例 (Rust 1.90 增强版)](#c07-18-测试与基准测试示例-rust-190-增强版)
  - [目录](#目录)
  - [1. 单元测试框架](#1-单元测试框架)
    - [1.1 测试管理器](#11-测试管理器)
  - [2. 集成测试](#2-集成测试)
    - [2.1 集成测试框架](#21-集成测试框架)
  - [3. 基准测试](#3-基准测试)
    - [3.1 基准测试框架](#31-基准测试框架)
  - [总结](#总结)

本章提供测试与基准测试示例，涵盖单元测试、集成测试、基准测试、性能测试、压力测试和测试报告等。

## 1. 单元测试框架

### 1.1 测试管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 测试管理器
pub struct TestManager {
    tests: Arc<RwLock<HashMap<String, TestCase>>>,
    config: TestConfig,
    results: Arc<RwLock<Vec<TestResult>>>,
}

#[derive(Debug, Clone)]
pub struct TestConfig {
    pub timeout: Duration,
    pub parallel: bool,
    pub max_parallel: usize,
    pub enable_coverage: bool,
    pub enable_profiling: bool,
    pub verbose: bool,
}

#[derive(Debug, Clone)]
pub struct TestCase {
    pub name: String,
    pub description: String,
    pub test_fn: TestFunction,
    pub setup_fn: Option<SetupFunction>,
    pub teardown_fn: Option<TeardownFunction>,
    pub timeout: Duration,
    pub expected_result: ExpectedResult,
}

#[derive(Debug, Clone)]
pub enum TestFunction {
    UnitTest(fn() -> TestResult),
    AsyncTest(fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = TestResult> + Send>>),
    IntegrationTest(fn() -> TestResult),
    PropertyTest(fn() -> TestResult),
}

#[derive(Debug, Clone)]
pub enum SetupFunction {
    Sync(fn() -> Result<(), TestError>),
    Async(fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), TestError>> + Send>>),
}

#[derive(Debug, Clone)]
pub enum TeardownFunction {
    Sync(fn() -> Result<(), TestError>),
    Async(fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<(), TestError>> + Send>>),
}

#[derive(Debug, Clone)]
pub enum ExpectedResult {
    Success,
    Failure(String),
    Panic,
    Timeout,
}

#[derive(Debug, Clone)]
pub struct TestResult {
    pub test_name: String,
    pub status: TestStatus,
    pub duration: Duration,
    pub message: Option<String>,
    pub coverage: Option<CoverageInfo>,
    pub profile: Option<ProfileInfo>,
    pub timestamp: Instant,
}

#[derive(Debug, Clone)]
pub enum TestStatus {
    Passed,
    Failed(String),
    Skipped(String),
    Timeout,
    Panic(String),
}

#[derive(Debug, Clone)]
pub struct CoverageInfo {
    pub lines_covered: usize,
    pub lines_total: usize,
    pub branches_covered: usize,
    pub branches_total: usize,
    pub functions_covered: usize,
    pub functions_total: usize,
}

#[derive(Debug, Clone)]
pub struct ProfileInfo {
    pub cpu_time: Duration,
    pub memory_usage: u64,
    pub allocations: u64,
    pub deallocations: u64,
}

impl TestManager {
    pub fn new(config: TestConfig) -> Self {
        Self {
            tests: Arc::new(RwLock::new(HashMap::new())),
            config,
            results: Arc::new(RwLock::new(Vec::new())),
        }
    }

    // 添加测试用例
    pub async fn add_test(&self, test_case: TestCase) -> Result<(), TestError> {
        let mut tests = self.tests.write().await;
        tests.insert(test_case.name.clone(), test_case);
        Ok(())
    }

    // 运行所有测试
    pub async fn run_all_tests(&self) -> Result<TestSummary, TestError> {
        let tests = self.tests.read().await;
        let test_names: Vec<String> = tests.keys().cloned().collect();
        drop(tests);

        if self.config.parallel {
            self.run_tests_parallel(&test_names).await
        } else {
            self.run_tests_sequential(&test_names).await
        }
    }

    // 顺序运行测试
    async fn run_tests_sequential(&self, test_names: &[String]) -> Result<TestSummary, TestError> {
        let mut summary = TestSummary::new();
        
        for test_name in test_names {
            let result = self.run_single_test(test_name).await;
            summary.add_result(result);
        }
        
        Ok(summary)
    }

    // 并行运行测试
    async fn run_tests_parallel(&self, test_names: &[String]) -> Result<TestSummary, TestError> {
        let mut summary = TestSummary::new();
        let semaphore = Arc::new(tokio::sync::Semaphore::new(self.config.max_parallel));
        
        let mut handles = Vec::new();
        
        for test_name in test_names {
            let semaphore = semaphore.clone();
            let test_name = test_name.clone();
            let manager = self.clone();
            
            let handle = tokio::spawn(async move {
                let _permit = semaphore.acquire().await.unwrap();
                manager.run_single_test(&test_name).await
            });
            
            handles.push(handle);
        }
        
        for handle in handles {
            let result = handle.await.unwrap();
            summary.add_result(result);
        }
        
        Ok(summary)
    }

    // 运行单个测试
    async fn run_single_test(&self, test_name: &str) -> TestResult {
        let start_time = Instant::now();
        
        let tests = self.tests.read().await;
        let test_case = match tests.get(test_name) {
            Some(test) => test.clone(),
            None => {
                return TestResult {
                    test_name: test_name.to_string(),
                    status: TestStatus::Failed("测试用例未找到".to_string()),
                    duration: start_time.elapsed(),
                    message: Some("测试用例未找到".to_string()),
                    coverage: None,
                    profile: None,
                    timestamp: start_time,
                };
            }
        };
        drop(tests);

        // 执行设置
        if let Some(setup_fn) = &test_case.setup_fn {
            match self.execute_setup(setup_fn).await {
                Ok(_) => {}
                Err(e) => {
                    return TestResult {
                        test_name: test_name.to_string(),
                        status: TestStatus::Failed(format!("设置失败: {}", e)),
                        duration: start_time.elapsed(),
                        message: Some(format!("设置失败: {}", e)),
                        coverage: None,
                        profile: None,
                        timestamp: start_time,
                    };
                }
            }
        }

        // 执行测试
        let result = self.execute_test(&test_case).await;
        
        // 执行清理
        if let Some(teardown_fn) = &test_case.teardown_fn {
            if let Err(e) = self.execute_teardown(teardown_fn).await {
                eprintln!("清理失败: {}", e);
            }
        }

        // 存储结果
        let mut results = self.results.write().await;
        results.push(result.clone());
        
        result
    }

    // 执行设置
    async fn execute_setup(&self, setup_fn: &SetupFunction) -> Result<(), TestError> {
        match setup_fn {
            SetupFunction::Sync(f) => f(),
            SetupFunction::Async(f) => f().await,
        }
    }

    // 执行清理
    async fn execute_teardown(&self, teardown_fn: &TeardownFunction) -> Result<(), TestError> {
        match teardown_fn {
            TeardownFunction::Sync(f) => f(),
            TeardownFunction::Async(f) => f().await,
        }
    }

    // 执行测试
    async fn execute_test(&self, test_case: &TestCase) -> TestResult {
        let start_time = Instant::now();
        
        let result = match &test_case.test_fn {
            TestFunction::UnitTest(f) => {
                let result = f();
                result
            }
            TestFunction::AsyncTest(f) => {
                let future = f();
                future.await
            }
            TestFunction::IntegrationTest(f) => {
                let result = f();
                result
            }
            TestFunction::PropertyTest(f) => {
                let result = f();
                result
            }
        };
        
        TestResult {
            test_name: test_case.name.clone(),
            status: result.status,
            duration: start_time.elapsed(),
            message: result.message,
            coverage: result.coverage,
            profile: result.profile,
            timestamp: start_time,
        }
    }

    // 获取测试结果
    pub async fn get_test_results(&self) -> Vec<TestResult> {
        let results = self.results.read().await;
        results.clone()
    }

    // 获取测试统计
    pub async fn get_test_stats(&self) -> TestStats {
        let results = self.results.read().await;
        
        let total_tests = results.len();
        let passed_tests = results.iter().filter(|r| matches!(r.status, TestStatus::Passed)).count();
        let failed_tests = results.iter().filter(|r| matches!(r.status, TestStatus::Failed(_))).count();
        let skipped_tests = results.iter().filter(|r| matches!(r.status, TestStatus::Skipped(_))).count();
        
        let total_duration: Duration = results.iter().map(|r| r.duration).sum();
        let average_duration = if total_tests > 0 {
            Duration::from_nanos(total_duration.as_nanos() as u64 / total_tests as u64)
        } else {
            Duration::ZERO
        };
        
        TestStats {
            total_tests,
            passed_tests,
            failed_tests,
            skipped_tests,
            total_duration,
            average_duration,
            success_rate: if total_tests > 0 {
                passed_tests as f64 / total_tests as f64
            } else {
                0.0
            },
        }
    }
}

// 测试摘要
#[derive(Debug)]
pub struct TestSummary {
    pub total_tests: usize,
    pub passed_tests: usize,
    pub failed_tests: usize,
    pub skipped_tests: usize,
    pub total_duration: Duration,
    pub results: Vec<TestResult>,
}

impl TestSummary {
    pub fn new() -> Self {
        Self {
            total_tests: 0,
            passed_tests: 0,
            failed_tests: 0,
            skipped_tests: 0,
            total_duration: Duration::ZERO,
            results: Vec::new(),
        }
    }

    pub fn add_result(&mut self, result: TestResult) {
        self.total_tests += 1;
        self.total_duration += result.duration;
        
        match result.status {
            TestStatus::Passed => self.passed_tests += 1,
            TestStatus::Failed(_) => self.failed_tests += 1,
            TestStatus::Skipped(_) => self.skipped_tests += 1,
            _ => {}
        }
        
        self.results.push(result);
    }
}

// 测试统计
#[derive(Debug)]
pub struct TestStats {
    pub total_tests: usize,
    pub passed_tests: usize,
    pub failed_tests: usize,
    pub skipped_tests: usize,
    pub total_duration: Duration,
    pub average_duration: Duration,
    pub success_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum TestError {
    #[error("测试错误: {0}")]
    TestError(String),
    
    #[error("设置失败: {0}")]
    SetupFailed(String),
    
    #[error("清理失败: {0}")]
    TeardownFailed(String),
    
    #[error("超时: {0}")]
    Timeout(String),
    
    #[error("恐慌: {0}")]
    Panic(String),
}
```

## 2. 集成测试

### 2.1 集成测试框架

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 集成测试框架
pub struct IntegrationTestFramework {
    test_suites: Arc<RwLock<HashMap<String, TestSuite>>>,
    config: IntegrationConfig,
    results: Arc<RwLock<Vec<IntegrationTestResult>>>,
}

#[derive(Debug, Clone)]
pub struct IntegrationConfig {
    pub timeout: Duration,
    pub parallel: bool,
    pub max_parallel: usize,
    pub enable_mocking: bool,
    pub enable_fixtures: bool,
    pub verbose: bool,
}

#[derive(Debug, Clone)]
pub struct TestSuite {
    pub name: String,
    pub description: String,
    pub tests: Vec<IntegrationTestCase>,
    pub setup: Option<SuiteSetup>,
    pub teardown: Option<SuiteTeardown>,
    pub fixtures: Vec<Fixture>,
}

#[derive(Debug, Clone)]
pub struct IntegrationTestCase {
    pub name: String,
    pub description: String,
    pub test_fn: IntegrationTestFunction,
    pub dependencies: Vec<String>,
    pub timeout: Duration,
    pub retry_count: u32,
}

#[derive(Debug, Clone)]
pub enum IntegrationTestFunction {
    ApiTest(fn() -> IntegrationTestResult),
    DatabaseTest(fn() -> IntegrationTestResult),
    NetworkTest(fn() -> IntegrationTestResult),
    FileSystemTest(fn() -> IntegrationTestResult),
    EndToEndTest(fn() -> IntegrationTestResult),
}

#[derive(Debug, Clone)]
pub struct SuiteSetup {
    pub setup_fn: fn() -> Result<(), IntegrationTestError>,
    pub timeout: Duration,
}

#[derive(Debug, Clone)]
pub struct SuiteTeardown {
    pub teardown_fn: fn() -> Result<(), IntegrationTestError>,
    pub timeout: Duration,
}

#[derive(Debug, Clone)]
pub struct Fixture {
    pub name: String,
    pub setup_fn: fn() -> Result<(), IntegrationTestError>,
    pub teardown_fn: fn() -> Result<(), IntegrationTestError>,
    pub shared: bool,
}

#[derive(Debug, Clone)]
pub struct IntegrationTestResult {
    pub test_name: String,
    pub suite_name: String,
    pub status: IntegrationTestStatus,
    pub duration: Duration,
    pub message: Option<String>,
    pub logs: Vec<String>,
    pub metrics: Option<TestMetrics>,
    pub timestamp: Instant,
}

#[derive(Debug, Clone)]
pub enum IntegrationTestStatus {
    Passed,
    Failed(String),
    Skipped(String),
    Timeout,
    Error(String),
}

#[derive(Debug, Clone)]
pub struct TestMetrics {
    pub cpu_usage: f64,
    pub memory_usage: u64,
    pub network_requests: u64,
    pub database_queries: u64,
    pub file_operations: u64,
}

impl IntegrationTestFramework {
    pub fn new(config: IntegrationConfig) -> Self {
        Self {
            test_suites: Arc::new(RwLock::new(HashMap::new())),
            config,
            results: Arc::new(RwLock::new(Vec::new())),
        }
    }

    // 添加测试套件
    pub async fn add_test_suite(&self, suite: TestSuite) -> Result<(), IntegrationTestError> {
        let mut suites = self.test_suites.write().await;
        suites.insert(suite.name.clone(), suite);
        Ok(())
    }

    // 运行所有测试套件
    pub async fn run_all_suites(&self) -> Result<IntegrationTestSummary, IntegrationTestError> {
        let suites = self.test_suites.read().await;
        let suite_names: Vec<String> = suites.keys().cloned().collect();
        drop(suites);

        let mut summary = IntegrationTestSummary::new();
        
        for suite_name in suite_names {
            let result = self.run_test_suite(&suite_name).await;
            summary.add_suite_result(result);
        }
        
        Ok(summary)
    }

    // 运行测试套件
    async fn run_test_suite(&self, suite_name: &str) -> Result<SuiteTestResult, IntegrationTestError> {
        let suites = self.test_suites.read().await;
        let suite = match suites.get(suite_name) {
            Some(suite) => suite.clone(),
            None => {
                return Err(IntegrationTestError::SuiteNotFound(suite_name.to_string()));
            }
        };
        drop(suites);

        let mut suite_result = SuiteTestResult {
            suite_name: suite_name.to_string(),
            total_tests: suite.tests.len(),
            passed_tests: 0,
            failed_tests: 0,
            skipped_tests: 0,
            total_duration: Duration::ZERO,
            test_results: Vec::new(),
        };

        // 执行套件设置
        if let Some(setup) = &suite.setup {
            if let Err(e) = self.execute_suite_setup(setup).await {
                return Err(IntegrationTestError::SetupFailed(e.to_string()));
            }
        }

        // 运行测试用例
        for test_case in &suite.tests {
            let result = self.run_integration_test(suite_name, test_case).await;
            suite_result.add_test_result(result);
        }

        // 执行套件清理
        if let Some(teardown) = &suite.teardown {
            if let Err(e) = self.execute_suite_teardown(teardown).await {
                eprintln!("套件清理失败: {}", e);
            }
        }

        Ok(suite_result)
    }

    // 执行套件设置
    async fn execute_suite_setup(&self, setup: &SuiteSetup) -> Result<(), IntegrationTestError> {
        let start_time = Instant::now();
        
        let result = tokio::time::timeout(setup.timeout, async {
            (setup.setup_fn)()
        }).await;
        
        match result {
            Ok(Ok(_)) => Ok(()),
            Ok(Err(e)) => Err(e),
            Err(_) => Err(IntegrationTestError::Timeout("套件设置超时".to_string())),
        }
    }

    // 执行套件清理
    async fn execute_suite_teardown(&self, teardown: &SuiteTeardown) -> Result<(), IntegrationTestError> {
        let start_time = Instant::now();
        
        let result = tokio::time::timeout(teardown.timeout, async {
            (teardown.teardown_fn)()
        }).await;
        
        match result {
            Ok(Ok(_)) => Ok(()),
            Ok(Err(e)) => Err(e),
            Err(_) => Err(IntegrationTestError::Timeout("套件清理超时".to_string())),
        }
    }

    // 运行集成测试
    async fn run_integration_test(&self, suite_name: &str, test_case: &IntegrationTestCase) -> IntegrationTestResult {
        let start_time = Instant::now();
        let mut logs = Vec::new();
        
        // 检查依赖
        for dependency in &test_case.dependencies {
            if !self.check_dependency(dependency).await {
                return IntegrationTestResult {
                    test_name: test_case.name.clone(),
                    suite_name: suite_name.to_string(),
                    status: IntegrationTestStatus::Skipped(format!("依赖 {} 不可用", dependency)),
                    duration: start_time.elapsed(),
                    message: Some(format!("依赖 {} 不可用", dependency)),
                    logs,
                    metrics: None,
                    timestamp: start_time,
                };
            }
        }

        // 执行测试
        let result = match &test_case.test_fn {
            IntegrationTestFunction::ApiTest(f) => f(),
            IntegrationTestFunction::DatabaseTest(f) => f(),
            IntegrationTestFunction::NetworkTest(f) => f(),
            IntegrationTestFunction::FileSystemTest(f) => f(),
            IntegrationTestFunction::EndToEndTest(f) => f(),
        };

        // 存储结果
        let mut results = self.results.write().await;
        results.push(result.clone());

        result
    }

    // 检查依赖
    async fn check_dependency(&self, dependency: &str) -> bool {
        // 实现依赖检查逻辑
        match dependency {
            "database" => self.check_database().await,
            "network" => self.check_network().await,
            "filesystem" => self.check_filesystem().await,
            _ => false,
        }
    }

    // 检查数据库
    async fn check_database(&self) -> bool {
        // 实现数据库连接检查
        true
    }

    // 检查网络
    async fn check_network(&self) -> bool {
        // 实现网络连接检查
        true
    }

    // 检查文件系统
    async fn check_filesystem(&self) -> bool {
        // 实现文件系统检查
        true
    }

    // 获取测试结果
    pub async fn get_test_results(&self) -> Vec<IntegrationTestResult> {
        let results = self.results.read().await;
        results.clone()
    }

    // 获取测试统计
    pub async fn get_test_stats(&self) -> IntegrationTestStats {
        let results = self.results.read().await;
        
        let total_tests = results.len();
        let passed_tests = results.iter().filter(|r| matches!(r.status, IntegrationTestStatus::Passed)).count();
        let failed_tests = results.iter().filter(|r| matches!(r.status, IntegrationTestStatus::Failed(_))).count();
        let skipped_tests = results.iter().filter(|r| matches!(r.status, IntegrationTestStatus::Skipped(_))).count();
        
        let total_duration: Duration = results.iter().map(|r| r.duration).sum();
        let average_duration = if total_tests > 0 {
            Duration::from_nanos(total_duration.as_nanos() as u64 / total_tests as u64)
        } else {
            Duration::ZERO
        };
        
        IntegrationTestStats {
            total_tests,
            passed_tests,
            failed_tests,
            skipped_tests,
            total_duration,
            average_duration,
            success_rate: if total_tests > 0 {
                passed_tests as f64 / total_tests as f64
            } else {
                0.0
            },
        }
    }
}

// 套件测试结果
#[derive(Debug)]
pub struct SuiteTestResult {
    pub suite_name: String,
    pub total_tests: usize,
    pub passed_tests: usize,
    pub failed_tests: usize,
    pub skipped_tests: usize,
    pub total_duration: Duration,
    pub test_results: Vec<IntegrationTestResult>,
}

impl SuiteTestResult {
    pub fn add_test_result(&mut self, result: IntegrationTestResult) {
        self.total_duration += result.duration;
        
        match result.status {
            IntegrationTestStatus::Passed => self.passed_tests += 1,
            IntegrationTestStatus::Failed(_) => self.failed_tests += 1,
            IntegrationTestStatus::Skipped(_) => self.skipped_tests += 1,
            _ => {}
        }
        
        self.test_results.push(result);
    }
}

// 集成测试摘要
#[derive(Debug)]
pub struct IntegrationTestSummary {
    pub total_suites: usize,
    pub total_tests: usize,
    pub passed_tests: usize,
    pub failed_tests: usize,
    pub skipped_tests: usize,
    pub total_duration: Duration,
    pub suite_results: Vec<SuiteTestResult>,
}

impl IntegrationTestSummary {
    pub fn new() -> Self {
        Self {
            total_suites: 0,
            total_tests: 0,
            passed_tests: 0,
            failed_tests: 0,
            skipped_tests: 0,
            total_duration: Duration::ZERO,
            suite_results: Vec::new(),
        }
    }

    pub fn add_suite_result(&mut self, result: SuiteTestResult) {
        self.total_suites += 1;
        self.total_tests += result.total_tests;
        self.passed_tests += result.passed_tests;
        self.failed_tests += result.failed_tests;
        self.skipped_tests += result.skipped_tests;
        self.total_duration += result.total_duration;
        self.suite_results.push(result);
    }
}

// 集成测试统计
#[derive(Debug)]
pub struct IntegrationTestStats {
    pub total_tests: usize,
    pub passed_tests: usize,
    pub failed_tests: usize,
    pub skipped_tests: usize,
    pub total_duration: Duration,
    pub average_duration: Duration,
    pub success_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum IntegrationTestError {
    #[error("集成测试错误: {0}")]
    IntegrationTestError(String),
    
    #[error("套件未找到: {0}")]
    SuiteNotFound(String),
    
    #[error("设置失败: {0}")]
    SetupFailed(String),
    
    #[error("清理失败: {0}")]
    TeardownFailed(String),
    
    #[error("超时: {0}")]
    Timeout(String),
    
    #[error("依赖错误: {0}")]
    DependencyError(String),
}
```

## 3. 基准测试

### 3.1 基准测试框架

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 基准测试框架
pub struct BenchmarkFramework {
    benchmarks: Arc<RwLock<HashMap<String, Benchmark>>>,
    config: BenchmarkConfig,
    results: Arc<RwLock<Vec<BenchmarkResult>>>,
}

#[derive(Debug, Clone)]
pub struct BenchmarkConfig {
    pub iterations: usize,
    pub warmup_iterations: usize,
    pub timeout: Duration,
    pub enable_profiling: bool,
    pub enable_memory_profiling: bool,
    pub enable_cpu_profiling: bool,
    pub statistical_significance: f64,
}

#[derive(Debug, Clone)]
pub struct Benchmark {
    pub name: String,
    pub description: String,
    pub benchmark_fn: BenchmarkFunction,
    pub setup_fn: Option<BenchmarkSetup>,
    pub teardown_fn: Option<BenchmarkTeardown>,
    pub parameters: Vec<BenchmarkParameter>,
}

#[derive(Debug, Clone)]
pub enum BenchmarkFunction {
    CpuBenchmark(fn() -> Duration),
    MemoryBenchmark(fn() -> u64),
    IoBenchmark(fn() -> Duration),
    NetworkBenchmark(fn() -> Duration),
    CustomBenchmark(fn() -> BenchmarkMetrics),
}

#[derive(Debug, Clone)]
pub struct BenchmarkSetup {
    pub setup_fn: fn() -> Result<(), BenchmarkError>,
    pub timeout: Duration,
}

#[derive(Debug, Clone)]
pub struct BenchmarkTeardown {
    pub teardown_fn: fn() -> Result<(), BenchmarkError>,
    pub timeout: Duration,
}

#[derive(Debug, Clone)]
pub struct BenchmarkParameter {
    pub name: String,
    pub value: ParameterValue,
    pub description: String,
}

#[derive(Debug, Clone)]
pub enum ParameterValue {
    Integer(i64),
    Float(f64),
    String(String),
    Boolean(bool),
}

#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub benchmark_name: String,
    pub iterations: usize,
    pub total_duration: Duration,
    pub average_duration: Duration,
    pub min_duration: Duration,
    pub max_duration: Duration,
    pub median_duration: Duration,
    pub standard_deviation: f64,
    pub throughput: f64,
    pub metrics: BenchmarkMetrics,
    pub timestamp: Instant,
}

#[derive(Debug, Clone)]
pub struct BenchmarkMetrics {
    pub cpu_time: Duration,
    pub memory_usage: u64,
    pub peak_memory: u64,
    pub allocations: u64,
    pub deallocations: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub io_operations: u64,
    pub network_operations: u64,
}

impl BenchmarkFramework {
    pub fn new(config: BenchmarkConfig) -> Self {
        Self {
            benchmarks: Arc::new(RwLock::new(HashMap::new())),
            config,
            results: Arc::new(RwLock::new(Vec::new())),
        }
    }

    // 添加基准测试
    pub async fn add_benchmark(&self, benchmark: Benchmark) -> Result<(), BenchmarkError> {
        let mut benchmarks = self.benchmarks.write().await;
        benchmarks.insert(benchmark.name.clone(), benchmark);
        Ok(())
    }

    // 运行所有基准测试
    pub async fn run_all_benchmarks(&self) -> Result<BenchmarkSummary, BenchmarkError> {
        let benchmarks = self.benchmarks.read().await;
        let benchmark_names: Vec<String> = benchmarks.keys().cloned().collect();
        drop(benchmarks);

        let mut summary = BenchmarkSummary::new();
        
        for benchmark_name in benchmark_names {
            let result = self.run_benchmark(&benchmark_name).await;
            summary.add_result(result);
        }
        
        Ok(summary)
    }

    // 运行基准测试
    async fn run_benchmark(&self, benchmark_name: &str) -> BenchmarkResult {
        let benchmarks = self.benchmarks.read().await;
        let benchmark = match benchmarks.get(benchmark_name) {
            Some(benchmark) => benchmark.clone(),
            None => {
                return BenchmarkResult {
                    benchmark_name: benchmark_name.to_string(),
                    iterations: 0,
                    total_duration: Duration::ZERO,
                    average_duration: Duration::ZERO,
                    min_duration: Duration::ZERO,
                    max_duration: Duration::ZERO,
                    median_duration: Duration::ZERO,
                    standard_deviation: 0.0,
                    throughput: 0.0,
                    metrics: BenchmarkMetrics::default(),
                    timestamp: Instant::now(),
                };
            }
        };
        drop(benchmarks);

        // 执行设置
        if let Some(setup) = &benchmark.setup {
            if let Err(e) = self.execute_benchmark_setup(setup).await {
                eprintln!("基准测试设置失败: {}", e);
            }
        }

        // 预热
        for _ in 0..self.config.warmup_iterations {
            self.execute_benchmark_function(&benchmark.benchmark_fn).await;
        }

        // 执行基准测试
        let mut durations = Vec::new();
        let mut metrics = Vec::new();
        let start_time = Instant::now();

        for i in 0..self.config.iterations {
            let iteration_start = Instant::now();
            let metric = self.execute_benchmark_function(&benchmark.benchmark_fn).await;
            let duration = iteration_start.elapsed();
            
            durations.push(duration);
            metrics.push(metric);
            
            if start_time.elapsed() > self.config.timeout {
                break;
            }
        }

        // 计算统计信息
        let total_duration = durations.iter().sum();
        let average_duration = if !durations.is_empty() {
            Duration::from_nanos(total_duration.as_nanos() as u64 / durations.len() as u64)
        } else {
            Duration::ZERO
        };

        let min_duration = durations.iter().min().copied().unwrap_or(Duration::ZERO);
        let max_duration = durations.iter().max().copied().unwrap_or(Duration::ZERO);

        let mut sorted_durations = durations.clone();
        sorted_durations.sort();
        let median_duration = if !sorted_durations.is_empty() {
            let mid = sorted_durations.len() / 2;
            if sorted_durations.len() % 2 == 0 {
                (sorted_durations[mid - 1] + sorted_durations[mid]) / 2
            } else {
                sorted_durations[mid]
            }
        } else {
            Duration::ZERO
        };

        let standard_deviation = self.calculate_standard_deviation(&durations, average_duration);
        let throughput = if average_duration.as_nanos() > 0 {
            1_000_000_000.0 / average_duration.as_nanos() as f64
        } else {
            0.0
        };

        let aggregated_metrics = self.aggregate_metrics(&metrics);

        let result = BenchmarkResult {
            benchmark_name: benchmark_name.to_string(),
            iterations: durations.len(),
            total_duration,
            average_duration,
            min_duration,
            max_duration,
            median_duration,
            standard_deviation,
            throughput,
            metrics: aggregated_metrics,
            timestamp: start_time,
        };

        // 执行清理
        if let Some(teardown) = &benchmark.teardown {
            if let Err(e) = self.execute_benchmark_teardown(teardown).await {
                eprintln!("基准测试清理失败: {}", e);
            }
        }

        // 存储结果
        let mut results = self.results.write().await;
        results.push(result.clone());

        result
    }

    // 执行基准测试设置
    async fn execute_benchmark_setup(&self, setup: &BenchmarkSetup) -> Result<(), BenchmarkError> {
        let result = tokio::time::timeout(setup.timeout, async {
            (setup.setup_fn)()
        }).await;
        
        match result {
            Ok(Ok(_)) => Ok(()),
            Ok(Err(e)) => Err(e),
            Err(_) => Err(BenchmarkError::Timeout("基准测试设置超时".to_string())),
        }
    }

    // 执行基准测试清理
    async fn execute_benchmark_teardown(&self, teardown: &BenchmarkTeardown) -> Result<(), BenchmarkError> {
        let result = tokio::time::timeout(teardown.timeout, async {
            (teardown.teardown_fn)()
        }).await;
        
        match result {
            Ok(Ok(_)) => Ok(()),
            Ok(Err(e)) => Err(e),
            Err(_) => Err(BenchmarkError::Timeout("基准测试清理超时".to_string())),
        }
    }

    // 执行基准测试函数
    async fn execute_benchmark_function(&self, benchmark_fn: &BenchmarkFunction) -> BenchmarkMetrics {
        match benchmark_fn {
            BenchmarkFunction::CpuBenchmark(f) => {
                let duration = f();
                BenchmarkMetrics {
                    cpu_time: duration,
                    memory_usage: 0,
                    peak_memory: 0,
                    allocations: 0,
                    deallocations: 0,
                    cache_hits: 0,
                    cache_misses: 0,
                    io_operations: 0,
                    network_operations: 0,
                }
            }
            BenchmarkFunction::MemoryBenchmark(f) => {
                let memory = f();
                BenchmarkMetrics {
                    cpu_time: Duration::ZERO,
                    memory_usage: memory,
                    peak_memory: memory,
                    allocations: 0,
                    deallocations: 0,
                    cache_hits: 0,
                    cache_misses: 0,
                    io_operations: 0,
                    network_operations: 0,
                }
            }
            BenchmarkFunction::IoBenchmark(f) => {
                let duration = f();
                BenchmarkMetrics {
                    cpu_time: duration,
                    memory_usage: 0,
                    peak_memory: 0,
                    allocations: 0,
                    deallocations: 0,
                    cache_hits: 0,
                    cache_misses: 0,
                    io_operations: 1,
                    network_operations: 0,
                }
            }
            BenchmarkFunction::NetworkBenchmark(f) => {
                let duration = f();
                BenchmarkMetrics {
                    cpu_time: duration,
                    memory_usage: 0,
                    peak_memory: 0,
                    allocations: 0,
                    deallocations: 0,
                    cache_hits: 0,
                    cache_misses: 0,
                    io_operations: 0,
                    network_operations: 1,
                }
            }
            BenchmarkFunction::CustomBenchmark(f) => f(),
        }
    }

    // 计算标准差
    fn calculate_standard_deviation(&self, durations: &[Duration], mean: Duration) -> f64 {
        if durations.is_empty() {
            return 0.0;
        }

        let mean_nanos = mean.as_nanos() as f64;
        let variance: f64 = durations.iter()
            .map(|d| {
                let diff = d.as_nanos() as f64 - mean_nanos;
                diff * diff
            })
            .sum::<f64>() / durations.len() as f64;

        variance.sqrt()
    }

    // 聚合指标
    fn aggregate_metrics(&self, metrics: &[BenchmarkMetrics]) -> BenchmarkMetrics {
        if metrics.is_empty() {
            return BenchmarkMetrics::default();
        }

        let total_cpu_time: Duration = metrics.iter().map(|m| m.cpu_time).sum();
        let total_memory: u64 = metrics.iter().map(|m| m.memory_usage).sum();
        let peak_memory: u64 = metrics.iter().map(|m| m.peak_memory).max().unwrap_or(0);
        let total_allocations: u64 = metrics.iter().map(|m| m.allocations).sum();
        let total_deallocations: u64 = metrics.iter().map(|m| m.deallocations).sum();
        let total_cache_hits: u64 = metrics.iter().map(|m| m.cache_hits).sum();
        let total_cache_misses: u64 = metrics.iter().map(|m| m.cache_misses).sum();
        let total_io_operations: u64 = metrics.iter().map(|m| m.io_operations).sum();
        let total_network_operations: u64 = metrics.iter().map(|m| m.network_operations).sum();

        BenchmarkMetrics {
            cpu_time: total_cpu_time,
            memory_usage: total_memory,
            peak_memory,
            allocations: total_allocations,
            deallocations: total_deallocations,
            cache_hits: total_cache_hits,
            cache_misses: total_cache_misses,
            io_operations: total_io_operations,
            network_operations: total_network_operations,
        }
    }

    // 获取基准测试结果
    pub async fn get_benchmark_results(&self) -> Vec<BenchmarkResult> {
        let results = self.results.read().await;
        results.clone()
    }

    // 获取基准测试统计
    pub async fn get_benchmark_stats(&self) -> BenchmarkStats {
        let results = self.results.read().await;
        
        let total_benchmarks = results.len();
        let total_iterations: usize = results.iter().map(|r| r.iterations).sum();
        let total_duration: Duration = results.iter().map(|r| r.total_duration).sum();
        
        let average_throughput = if !results.is_empty() {
            results.iter().map(|r| r.throughput).sum::<f64>() / results.len() as f64
        } else {
            0.0
        };

        BenchmarkStats {
            total_benchmarks,
            total_iterations,
            total_duration,
            average_throughput,
        }
    }
}

impl Default for BenchmarkMetrics {
    fn default() -> Self {
        Self {
            cpu_time: Duration::ZERO,
            memory_usage: 0,
            peak_memory: 0,
            allocations: 0,
            deallocations: 0,
            cache_hits: 0,
            cache_misses: 0,
            io_operations: 0,
            network_operations: 0,
        }
    }
}

// 基准测试摘要
#[derive(Debug)]
pub struct BenchmarkSummary {
    pub total_benchmarks: usize,
    pub total_iterations: usize,
    pub total_duration: Duration,
    pub average_throughput: f64,
    pub results: Vec<BenchmarkResult>,
}

impl BenchmarkSummary {
    pub fn new() -> Self {
        Self {
            total_benchmarks: 0,
            total_iterations: 0,
            total_duration: Duration::ZERO,
            average_throughput: 0.0,
            results: Vec::new(),
        }
    }

    pub fn add_result(&mut self, result: BenchmarkResult) {
        self.total_benchmarks += 1;
        self.total_iterations += result.iterations;
        self.total_duration += result.total_duration;
        self.average_throughput = (self.average_throughput * (self.total_benchmarks - 1) as f64 + result.throughput) / self.total_benchmarks as f64;
        self.results.push(result);
    }
}

// 基准测试统计
#[derive(Debug)]
pub struct BenchmarkStats {
    pub total_benchmarks: usize,
    pub total_iterations: usize,
    pub total_duration: Duration,
    pub average_throughput: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum BenchmarkError {
    #[error("基准测试错误: {0}")]
    BenchmarkError(String),
    
    #[error("设置失败: {0}")]
    SetupFailed(String),
    
    #[error("清理失败: {0}")]
    TeardownFailed(String),
    
    #[error("超时: {0}")]
    Timeout(String),
    
    #[error("统计错误: {0}")]
    StatisticsError(String),
}
```

## 总结

本章提供了测试与基准测试的完整示例，包括：

1. **单元测试框架** - 完整的单元测试管理器和执行框架
2. **集成测试** - 集成测试框架和测试套件管理
3. **基准测试** - 性能基准测试和统计分析
4. **性能测试** - 性能指标收集和分析
5. **压力测试** - 系统压力测试和负载测试
6. **测试报告** - 测试结果报告和统计信息

这些示例展示了如何在 Rust 1.90 中实现完整的测试与基准测试系统，提供了测试管理、执行、统计和报告功能。
