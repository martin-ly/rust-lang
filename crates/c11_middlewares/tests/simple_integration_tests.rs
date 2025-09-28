//! 简化集成测试模块
//! 
//! 本模块测试 c11_middlewares 各个组件之间的协作和集成功能

use c11_middlewares::prelude::*;

/// 测试 Rust 1.90 优化特性与基准测试的集成
#[test]
fn test_rust190_optimizations_with_benchmarks() {
    // 创建优化的连接池
    let pool: OptimizedConnectionPool<10, 5000> = OptimizedConnectionPool::new();
    assert_eq!(pool.current_connections(), 0);
    
    // 创建优化的缓冲区
    let mut buffer: OptimizedBuffer<1024> = OptimizedBuffer::new();
    let test_data = b"integration test data";
    assert!(buffer.write(test_data).is_ok());
    
    // 创建性能监控器
    let mut monitor: PerformanceMonitor<100> = PerformanceMonitor::new();
    monitor.record_metric(10.0);
    monitor.record_metric(20.0);
    monitor.record_metric(30.0);
    
    let stats = monitor.get_stats();
    assert_eq!(stats.average, 20.0);
    assert_eq!(stats.total_samples, 3);
}

/// 测试高级基准测试与优化特性的集成
#[test]
fn test_advanced_benchmarks_with_optimizations() {
    let mut benchmarker = AdvancedBenchmarker::new();
    
    // 使用优化的缓冲区作为测试操作
    let test_data = b"benchmark test data";
    
    let result = benchmarker.run_single_threaded_benchmark(
        "optimized_buffer_test",
        || {
            let mut buffer: OptimizedBuffer<512> = OptimizedBuffer::new();
            buffer.write(test_data)?;
            let _data = buffer.read();
            Ok(())
        },
        100,
    ).unwrap();
    
    assert_eq!(result.test_name, "optimized_buffer_test");
    assert_eq!(result.operations_performed, 100);
    assert_eq!(result.success_rate, 100.0);
}

/// 测试配置系统与优化特性的集成
#[test]
fn test_config_system_with_optimizations() {
    // 测试中间件配置
    let config: MiddlewareConfig<10, 5000> = MiddlewareConfig::new(
        MiddlewareType::Redis, 
        "redis://localhost:6379".to_string()
    );
    assert!(config.validate().is_ok());
    
    // 测试增强配置
    let enhanced_config: EnhancedRedisConfig<10, 5000> = EnhancedRedisConfig::new("redis://localhost:6379");
    assert_eq!(enhanced_config.url, "redis://localhost:6379");
}

/// 测试错误处理与优化特性的集成
#[test]
fn test_error_handling_with_optimizations() {
    // 测试性能监控器的错误处理
    let mut monitor: PerformanceMonitor<10> = PerformanceMonitor::new();
    
    // 记录一些指标
    monitor.record_metric(1.0);
    monitor.record_metric(2.0);
    monitor.record_metric(3.0);
    
    let stats = monitor.get_stats();
    assert_eq!(stats.average, 2.0);
    assert_eq!(stats.min, 1.0);
    assert_eq!(stats.max, 3.0);
}

/// 测试常量泛型推断功能
#[test]
fn test_const_generic_inference() {
    // 测试不同大小的缓冲区
    let mut small_buffer: OptimizedBuffer<64> = OptimizedBuffer::new();
    let mut large_buffer: OptimizedBuffer<4096> = OptimizedBuffer::new();
    
    let test_data = b"test data";
    
    // 小缓冲区测试
    assert!(small_buffer.write(test_data).is_ok());
    let _data = small_buffer.read();
    
    // 大缓冲区测试
    assert!(large_buffer.write(test_data).is_ok());
    let _data = large_buffer.read();
    
    // 测试不同大小的连接池
    let small_pool: OptimizedConnectionPool<5, 1000> = OptimizedConnectionPool::new();
    let large_pool: OptimizedConnectionPool<50, 10000> = OptimizedConnectionPool::new();
    
    assert_eq!(small_pool.current_connections(), 0);
    assert_eq!(large_pool.current_connections(), 0);
}

/// 测试性能监控与基准测试的集成
#[test]
fn test_performance_monitoring_with_benchmarks() {
    let mut benchmarker = AdvancedBenchmarker::new();
    
    // 运行基准测试并同时监控性能
    let result = benchmarker.run_single_threaded_benchmark(
        "performance_monitoring_test",
        || {
            // 模拟一些工作
            let start = std::time::Instant::now();
            let _sum = 0;
            for i in 0..100 {
                let _ = i;
            }
            let _duration = start.elapsed();
            
            // 记录性能指标到独立的监控器
            let mut local_monitor: PerformanceMonitor<10> = PerformanceMonitor::new();
            local_monitor.record_metric(1.0);
            
            Ok(())
        },
        50,
    ).unwrap();
    
    assert_eq!(result.test_name, "performance_monitoring_test");
    assert_eq!(result.operations_performed, 50);
    
    // 检查性能监控器的统计信息
    let local_monitor: PerformanceMonitor<50> = PerformanceMonitor::new();
    let stats = local_monitor.get_stats();
    assert_eq!(stats.total_samples, 0);
}

/// 测试并发性能与优化特性的集成
#[test]
fn test_concurrent_performance_with_optimizations() {
    let mut benchmarker = AdvancedBenchmarker::new();
    
    // 测试并发操作
    let result = benchmarker.run_concurrent_benchmark(
        "concurrent_optimization_test",
        || {
            // 使用优化的缓冲区进行并发操作
            let mut buffer: OptimizedBuffer<256> = OptimizedBuffer::new();
            let test_data = b"concurrent test data";
            
            buffer.write(test_data)?;
            let _data = buffer.read();
            
            Ok(())
        },
        200,
        4, // 4个线程
    ).unwrap();
    
    assert_eq!(result.test_name, "concurrent_optimization_test");
    assert_eq!(result.operations_performed, 200);
    assert_eq!(result.success_rate, 100.0);
    
    // 检查并发性能指标
    assert!(result.throughput_ops_per_sec > 0.0);
    assert!(result.average_latency_ms > 0.0);
}

/// 测试完整的端到端工作流
#[test]
fn test_end_to_end_workflow() {
    // 1. 创建配置
    let config: MiddlewareConfig<10, 5000> = MiddlewareConfig::new(
        MiddlewareType::Redis,
        "redis://localhost:6379".to_string()
    );
    assert!(config.validate().is_ok());
    
    // 2. 创建优化的组件
    let _pool: OptimizedConnectionPool<10, 5000> = OptimizedConnectionPool::new();
    let _buffer: OptimizedBuffer<1024> = OptimizedBuffer::new();
    let _monitor: PerformanceMonitor<100> = PerformanceMonitor::new();
    
    // 3. 运行基准测试
    let mut benchmarker = AdvancedBenchmarker::new();
    let result = benchmarker.run_single_threaded_benchmark(
        "end_to_end_test",
        || {
            // 记录开始时间
            let start = std::time::Instant::now();
            
            // 执行操作
            let test_data = b"end to end test data";
            let mut local_buffer: OptimizedBuffer<1024> = OptimizedBuffer::new();
            local_buffer.write(test_data)?;
            let _data = local_buffer.read();
            
            // 记录性能指标
            let duration = start.elapsed();
            let mut local_monitor: PerformanceMonitor<100> = PerformanceMonitor::new();
            local_monitor.record_metric(duration.as_nanos() as f64);
            
            Ok(())
        },
        50,
    ).unwrap();
    
    // 4. 验证结果
    assert_eq!(result.test_name, "end_to_end_test");
    assert_eq!(result.operations_performed, 50);
    assert_eq!(result.success_rate, 100.0);
    
    // 5. 生成报告
    let report = benchmarker.generate_report();
    assert!(report.contains("end_to_end_test"));
    assert!(report.contains("50"));
}
