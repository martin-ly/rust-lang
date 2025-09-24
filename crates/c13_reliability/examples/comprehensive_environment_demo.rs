//! # 综合环境演示示例
//!
//! 本示例展示了c13_reliability框架的完整功能，包括：
//! - 环境检测和适配
//! - 监控策略配置
//! - 优化算法应用
//! - 测试框架使用

use c13_reliability::prelude::*;
use c13_reliability::runtime_environments::{
    RuntimeEnvironment, RuntimeEnvironmentManager,
    MonitoringStrategyFactory, OptimizationAlgorithmFactory, TestFrameworkFactory,
    OptimizationContext, OptimizationGoal, OptimizationConstraints,
    TestSuite, Test, TestType, ExpectedResult, EnvironmentRequirements,
    ResourceRequirements, PerformanceMetrics, ResourceUsageSnapshot,
    OSEnvironmentAdapter, EmbeddedEnvironmentAdapter, ContainerEnvironmentAdapter,
    VirtualMachineEnvironmentAdapter, WebAssemblyEnvironmentAdapter, FaaSEnvironmentAdapter,
};

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    println!("=== c13_reliability 综合环境演示 ===\n");
    
    // 1. 环境检测和适配
    demonstrate_environment_detection_and_adaptation().await?;
    
    // 2. 监控策略配置
    demonstrate_monitoring_strategies().await?;
    
    // 3. 优化算法应用
    demonstrate_optimization_algorithms().await?;
    
    // 4. 测试框架使用
    demonstrate_testing_framework().await?;
    
    // 5. 综合场景演示
    demonstrate_comprehensive_scenario().await?;
    
    println!("\n=== 演示完成 ===");
    Ok(())
}

/// 演示环境检测和适配
async fn demonstrate_environment_detection_and_adaptation() -> Result<(), UnifiedError> {
    println!("🔍 1. 环境检测和适配演示");
    
    // 自动检测环境
    let detected_env = RuntimeEnvironment::detect_current();
    println!("   检测到的环境: {:?}", detected_env);
    println!("   环境描述: {}", detected_env.description());
    
    // 获取环境能力
    let capabilities = detected_env.capabilities();
    println!("   环境能力:");
    println!("     - 多进程支持: {}", capabilities.supports_multiprocessing);
    println!("     - 多线程支持: {}", capabilities.supports_multithreading);
    println!("     - 网络支持: {}", capabilities.supports_network);
    println!("     - 混沌工程支持: {}", capabilities.supports_chaos_engineering);
    
    // 创建环境管理器
    let mut manager = RuntimeEnvironmentManager::new(detected_env);
    
    // 根据环境类型设置适配器
    match detected_env {
        RuntimeEnvironment::OperatingSystem => {
            let adapter = Box::new(OSEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::EmbeddedBareMetal => {
            let adapter = Box::new(EmbeddedEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::Container => {
            let adapter = Box::new(ContainerEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::VirtualMachine => {
            let adapter = Box::new(VirtualMachineEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::WebAssembly => {
            let adapter = Box::new(WebAssemblyEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        RuntimeEnvironment::FunctionAsAService => {
            let adapter = Box::new(FaaSEnvironmentAdapter::new());
            manager.set_adapter(adapter);
        },
        _ => {
            println!("   使用默认适配器");
        }
    }
    
    // 初始化环境
    manager.initialize().await?;
    println!("   环境初始化成功");
    
    // 获取系统信息
    let system_info = manager.get_system_info().await?;
    println!("   系统信息: {}", system_info.system_name);
    
    // 检查健康状态
    let health_status = manager.check_health().await?;
    println!("   健康状态: {:?}", health_status.overall_health);
    
    // 清理环境
    manager.cleanup().await?;
    println!("   环境清理完成\n");
    
    Ok(())
}

/// 演示监控策略配置
async fn demonstrate_monitoring_strategies() -> Result<(), UnifiedError> {
    println!("📊 2. 监控策略配置演示");
    
    // 检测当前环境
    let environment = RuntimeEnvironment::detect_current();
    
    // 创建监控策略
    let strategy = MonitoringStrategyFactory::create_strategy(environment);
    println!("   监控策略: {}", strategy.name());
    println!("   监控间隔: {:?}", strategy.monitoring_interval());
    println!("   健康检查间隔: {:?}", strategy.health_check_interval());
    println!("   指标收集间隔: {:?}", strategy.metrics_collection_interval());
    
    // 获取监控配置
    let config = strategy.get_monitoring_config();
    println!("   监控配置:");
    println!("     - 详细监控: {}", config.enable_detailed_monitoring);
    println!("     - 性能监控: {}", config.enable_performance_monitoring);
    println!("     - 资源监控: {}", config.enable_resource_monitoring);
    println!("     - 网络监控: {}", config.enable_network_monitoring);
    println!("     - 混沌工程: {}", config.enable_chaos_engineering);
    
    // 根据环境能力创建自定义策略
    let capabilities = environment.capabilities();
    let custom_strategy = MonitoringStrategyFactory::create_custom_strategy(&capabilities);
    println!("   自定义监控策略: {}", custom_strategy.name());
    println!();
    
    Ok(())
}

/// 演示优化算法应用
async fn demonstrate_optimization_algorithms() -> Result<(), UnifiedError> {
    println!("⚡ 3. 优化算法应用演示");
    
    // 检测当前环境
    let environment = RuntimeEnvironment::detect_current();
    
    // 创建优化算法
    let mut algorithm = OptimizationAlgorithmFactory::create_algorithm(environment);
    println!("   优化算法: {}", algorithm.name());
    println!("   算法描述: {}", algorithm.description());
    
    // 创建优化上下文
    let context = create_optimization_context(environment);
    
    // 执行优化
    let optimization_result = algorithm.optimize(&context).await?;
    println!("   优化结果:");
    println!("     - 算法名称: {}", optimization_result.algorithm_name);
    println!("     - 建议数量: {}", optimization_result.suggestions.len());
    println!("     - 风险评估: {:?}", optimization_result.risk_assessment.risk_level);
    println!("     - 实施复杂度: {:?}", optimization_result.implementation_complexity);
    
    // 显示优化建议
    for (i, suggestion) in optimization_result.suggestions.iter().enumerate() {
        println!("     建议 {}: {}", i + 1, suggestion.description);
        println!("       类型: {:?}", suggestion.suggestion_type);
        println!("       预期收益: {:.1}%", suggestion.expected_benefit);
        println!("       实施成本: {:?}", suggestion.implementation_cost);
        println!("       优先级: {:?}", suggestion.priority);
    }
    
    // 获取优化建议
    let suggestions = algorithm.get_optimization_suggestions(&context).await?;
    println!("   额外优化建议数量: {}", suggestions.len());
    
    // 验证优化结果
    let is_valid = algorithm.validate_optimization(&optimization_result).await?;
    println!("   优化结果验证: {}", if is_valid { "通过" } else { "失败" });
    println!();
    
    Ok(())
}

/// 演示测试框架使用
async fn demonstrate_testing_framework() -> Result<(), UnifiedError> {
    println!("🧪 4. 测试框架使用演示");
    
    // 检测当前环境
    let environment = RuntimeEnvironment::detect_current();
    
    // 创建测试框架
    let framework = TestFrameworkFactory::create_framework(environment);
    println!("   测试框架: {}", framework.name());
    
    // 获取支持的测试类型
    let supported_test_types = framework.supported_test_types();
    println!("   支持的测试类型: {:?}", supported_test_types);
    
    // 验证环境兼容性
    let compatibility = framework.validate_environment_compatibility(&environment).await?;
    println!("   环境兼容性:");
    println!("     - 是否兼容: {}", compatibility.is_compatible);
    println!("     - 兼容性分数: {:.1}", compatibility.compatibility_score);
    println!("     - 问题数量: {}", compatibility.issues.len());
    
    // 创建测试套件
    let test_suite = create_test_suite();
    println!("   测试套件: {}", test_suite.name);
    println!("   测试数量: {}", test_suite.tests.len());
    
    // 运行测试套件
    let test_results = framework.run_test_suite(&test_suite).await?;
    println!("   测试结果:");
    println!("     - 总测试数: {}", test_results.statistics.total_tests);
    println!("     - 通过数: {}", test_results.statistics.passed_tests);
    println!("     - 失败数: {}", test_results.statistics.failed_tests);
    println!("     - 通过率: {:.1}%", test_results.statistics.pass_rate);
    println!("     - 总执行时间: {:?}", test_results.total_execution_time);
    
    // 生成测试报告
    let test_report = framework.generate_test_report(&test_results).await?;
    println!("   测试报告:");
    println!("     - 标题: {}", test_report.title);
    println!("     - 摘要: {}", test_report.summary);
    println!("     - 建议数量: {}", test_report.recommendations.len());
    println!();
    
    Ok(())
}

/// 演示综合场景
async fn demonstrate_comprehensive_scenario() -> Result<(), UnifiedError> {
    println!("🎯 5. 综合场景演示");
    
    // 模拟不同环境的处理
    let environments = vec![
        RuntimeEnvironment::OperatingSystem,
        RuntimeEnvironment::EmbeddedBareMetal,
        RuntimeEnvironment::Container,
        RuntimeEnvironment::WebAssembly,
        RuntimeEnvironment::FunctionAsAService,
    ];
    
    for env in environments {
        println!("   处理环境: {:?}", env);
        
        // 1. 创建监控策略
        let monitoring_strategy = MonitoringStrategyFactory::create_strategy(env);
        println!("     - 监控策略: {}", monitoring_strategy.name());
        
        // 2. 创建优化算法
        let optimization_algorithm = OptimizationAlgorithmFactory::create_algorithm(env);
        println!("     - 优化算法: {}", optimization_algorithm.name());
        
        // 3. 创建测试框架
        let test_framework = TestFrameworkFactory::create_framework(env);
        println!("     - 测试框架: {}", test_framework.name());
        
        // 4. 环境特定处理
        match env {
            RuntimeEnvironment::EmbeddedBareMetal => {
                println!("     - 嵌入式环境: 启用轻量级监控，禁用混沌工程");
            },
            RuntimeEnvironment::Container => {
                println!("     - 容器环境: 启用资源限制监控，支持混沌工程");
            },
            RuntimeEnvironment::WebAssembly => {
                println!("     - WASM环境: 启用沙箱监控，优化内存使用");
            },
            RuntimeEnvironment::FunctionAsAService => {
                println!("     - FaaS环境: 启用冷启动监控，优化执行时间");
            },
            _ => {
                println!("     - 通用环境: 启用完整功能");
            }
        }
    }
    
    println!();
    Ok(())
}

/// 创建优化上下文
fn create_optimization_context(environment: RuntimeEnvironment) -> OptimizationContext {
    OptimizationContext {
        environment,
        capabilities: environment.capabilities(),
        current_resource_usage: ResourceUsageSnapshot {
            cpu_usage_percent: 60.0,
            memory_usage_bytes: 200 * 1024 * 1024,
            memory_usage_percent: 40.0,
            disk_usage_bytes: 1 * 1024 * 1024 * 1024,
            disk_usage_percent: 20.0,
            network_rx_rate: 50.0,
            network_tx_rate: 30.0,
            timestamp: chrono::Utc::now(),
        },
        performance_metrics: PerformanceMetrics {
            response_time_ms: 150.0,
            throughput_ops_per_sec: 500.0,
            error_rate_percent: 2.0,
            latency_ms: 75.0,
            availability_percent: 99.5,
        },
        optimization_goals: vec![
            OptimizationGoal::MinimizeLatency,
            OptimizationGoal::MaximizeThroughput,
            OptimizationGoal::MinimizeResourceUsage,
        ],
        constraints: OptimizationConstraints {
            max_memory_usage_percent: 80.0,
            max_cpu_usage_percent: 70.0,
            max_latency_ms: 200.0,
            min_availability_percent: 99.0,
            max_error_rate_percent: 5.0,
            budget_limit: Some(1000.0),
        },
    }
}

/// 创建测试套件
fn create_test_suite() -> TestSuite {
    TestSuite {
        name: "综合测试套件".to_string(),
        description: "包含多种测试类型的综合测试套件".to_string(),
        tests: vec![
            Test {
                name: "单元测试示例".to_string(),
                description: "测试基本功能".to_string(),
                test_type: TestType::UnitTest,
                test_code: "assert_eq!(1 + 1, 2);".to_string(),
                expected_result: ExpectedResult::Success,
                timeout: std::time::Duration::from_secs(30),
                retry_count: 3,
                dependencies: Vec::new(),
            },
            Test {
                name: "性能测试示例".to_string(),
                description: "测试性能指标".to_string(),
                test_type: TestType::PerformanceTest,
                test_code: "measure_performance();".to_string(),
                expected_result: ExpectedResult::RangeValue { min: 100.0, max: 200.0 },
                timeout: std::time::Duration::from_secs(60),
                retry_count: 2,
                dependencies: Vec::new(),
            },
            Test {
                name: "可靠性测试示例".to_string(),
                description: "测试系统可靠性".to_string(),
                test_type: TestType::ReliabilityTest,
                test_code: "test_reliability();".to_string(),
                expected_result: ExpectedResult::Success,
                timeout: std::time::Duration::from_secs(120),
                retry_count: 1,
                dependencies: Vec::new(),
            },
        ],
        timeout: std::time::Duration::from_secs(300),
        parallel_execution: true,
        environment_requirements: EnvironmentRequirements {
            required_capabilities: RuntimeEnvironment::OperatingSystem.capabilities(),
            min_resources: ResourceRequirements {
                min_memory_bytes: 100 * 1024 * 1024,
                min_cpu_cores: 1,
                min_disk_bytes: 500 * 1024 * 1024,
                min_network_bandwidth: 10 * 1024 * 1024,
            },
            supported_environments: vec![
                RuntimeEnvironment::OperatingSystem,
                RuntimeEnvironment::Container,
            ],
            excluded_environments: vec![
                RuntimeEnvironment::EmbeddedBareMetal,
            ],
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_environment_detection() {
        let env = RuntimeEnvironment::detect_current();
        assert!(matches!(env, RuntimeEnvironment::OperatingSystem | RuntimeEnvironment::Container));
    }

    #[tokio::test]
    async fn test_monitoring_strategy_creation() {
        let env = RuntimeEnvironment::detect_current();
        let strategy = MonitoringStrategyFactory::create_strategy(env);
        assert!(!strategy.name().is_empty());
    }

    #[tokio::test]
    async fn test_optimization_algorithm_creation() {
        let env = RuntimeEnvironment::detect_current();
        let algorithm = OptimizationAlgorithmFactory::create_algorithm(env);
        assert!(!algorithm.name().is_empty());
    }

    #[tokio::test]
    async fn test_test_framework_creation() {
        let env = RuntimeEnvironment::detect_current();
        let framework = TestFrameworkFactory::create_framework(env);
        assert!(!framework.name().is_empty());
    }
}
