//! Rust 1.92.0 综合特性测试
//!
//! 本测试文件包含 Rust 1.92.0 版本所有新特性的综合测试：
//! - #[track_caller] 在控制流场景中的改进
//! - 更严格的 Never 类型 Lint
//! - Location API 在错误报告中的增强
//! - 改进的控制流分析
//! - 优化的错误处理和上下文捕获
//!
//! 运行方式：
//! ```bash
//! cargo test rust_192_comprehensive_tests
//! ```

use c03_control_fn::rust_192_features::{
    control_flow_check, control_flow_branch, control_flow_loop, control_flow_match,
    control_flow_with_never, LocatedError, ErrorContext,
    ControlFlowAnalyzer, ControlFlowOptimizer,
    ControlFlowMatcher, ControlFlowCombinator, ControlFlowProfiler, ControlFlowValidator,
    ControlFlowStateMachine, ControlFlowState,
    IteratorControlFlow,
    ControlFlowVisualization,
    get_rust_192_control_flow_info, demonstrate_rust_192_control_flow,
};

/// 测试控制流检查功能
#[test]
fn test_control_flow_check() {
    // 测试成功情况
    let result = control_flow_check(true);
    assert_eq!(result, 0);

    // 测试失败情况
    let result = control_flow_check(false);
    assert_eq!(result, -1);
}

/// 测试控制流分支功能
#[test]
fn test_control_flow_branch() {
    // 测试有效值
    assert!(control_flow_branch(42).is_ok());
    assert_eq!(control_flow_branch(42).unwrap(), 84);

    // 测试负值
    assert!(control_flow_branch(-1).is_err());

    // 测试过大值
    assert!(control_flow_branch(101).is_err());
    assert!(control_flow_branch(150).is_err());

    // 测试边界值
    assert!(control_flow_branch(0).is_ok());
    assert_eq!(control_flow_branch(0).unwrap(), 0);

    assert!(control_flow_branch(100).is_ok());
    assert_eq!(control_flow_branch(100).unwrap(), 200);
}

/// 测试控制流循环功能
#[test]
fn test_control_flow_loop() {
    // 测试零迭代
    assert_eq!(control_flow_loop(0), 0);

    // 测试正常迭代
    assert_eq!(control_flow_loop(5), 5);
    assert_eq!(control_flow_loop(10), 10);
    assert_eq!(control_flow_loop(100), 100);
}

/// 测试控制流匹配功能
#[test]
fn test_control_flow_match() {
    // 测试正数
    assert_eq!(control_flow_match(Some(21)), 42);
    assert_eq!(control_flow_match(Some(10)), 20);

    // 测试负数
    assert_eq!(control_flow_match(Some(-21)), 21);
    assert_eq!(control_flow_match(Some(-10)), 10);

    // 测试 None
    assert_eq!(control_flow_match(None), 0);

    // 测试零
    assert_eq!(control_flow_match(Some(0)), 0);
}

/// 测试 Never 类型控制流
#[test]
fn test_never_type_control_flow() {
    // 测试 Ok 情况
    let result = control_flow_with_never(Ok(42));
    assert_eq!(result, 42);

    let result = control_flow_with_never(Ok(100));
    assert_eq!(result, 100);

    // 注意：Err 情况会导致无限循环，不在单元测试中测试
}

/// 测试错误处理和位置追踪
#[test]
fn test_located_error() {
    // 测试错误创建
    let error = LocatedError::new("测试错误");
    assert!(error.message.contains("测试错误"));
    assert!(!error.context.file.is_empty());
    // line 在有效上下文中总是大于等于 1
    assert!(error.context.line >= 1);

    // 测试错误格式化
    let error_str = format!("{}", error);
    assert!(error_str.contains("测试错误"));
    assert!(error_str.contains(&error.context.file.to_string()));
}

/// 测试错误上下文
#[test]
fn test_error_context() {
    let context = ErrorContext::current();

    // 验证上下文包含有效信息
    assert!(!context.file.is_empty());
    // line 和 column 在有效上下文中总是大于等于 1
    assert!(context.line >= 1);
    assert!(context.column >= 1);

    // 验证上下文可以克隆
    let cloned = context.clone();
    assert_eq!(cloned.file, context.file);
    assert_eq!(cloned.line, context.line);
    assert_eq!(cloned.column, context.column);
}

/// 测试控制流分析器
#[test]
fn test_control_flow_analyzer() {
    let mut analyzer = ControlFlowAnalyzer::new();

    // 测试分支分析
    analyzer.analyze_branch(true);
    analyzer.analyze_branch(false);
    analyzer.analyze_branch(true);

    // 测试循环分析
    let count = analyzer.analyze_loop(10, |i| i % 2 == 0);
    assert_eq!(count, 5); // 0, 2, 4, 6, 8

    // 测试匹配分析
    analyzer.analyze_match(Some(42));
    analyzer.analyze_match(None::<i32>);
    analyzer.analyze_match(Some(100));

    // 验证统计信息
    let (branches, loops, matches) = analyzer.get_statistics();
    assert_eq!(branches, 3);
    assert_eq!(loops, 1);
    assert_eq!(matches, 3);
}

/// 测试控制流优化器
#[test]
fn test_control_flow_optimizer() {
    // 测试循环优化
    let result = ControlFlowOptimizer::optimize_loop(10);
    // result 是 usize，总是 >= 0，所以只验证计算完成
    let _ = result;

    let result = ControlFlowOptimizer::optimize_loop(100);
    let _ = result;

    // 测试分支优化 - 成功情况
    assert!(ControlFlowOptimizer::optimize_branch(42).is_ok());
    assert_eq!(ControlFlowOptimizer::optimize_branch(42).unwrap(), 84);

    // 测试分支优化 - 错误情况
    assert!(ControlFlowOptimizer::optimize_branch(-1).is_err());
    assert!(ControlFlowOptimizer::optimize_branch(150).is_err());

    // 测试匹配优化
    assert_eq!(ControlFlowOptimizer::optimize_match(Some(21)), 42);
    assert_eq!(ControlFlowOptimizer::optimize_match(Some(-21)), 21);
    assert_eq!(ControlFlowOptimizer::optimize_match(None), 0);
}

/// 测试信息获取
#[test]
fn test_get_rust_192_info() {
    let info = get_rust_192_control_flow_info();

    assert!(!info.is_empty());
    assert!(info.contains("Rust 1.92.0"));
    assert!(info.contains("track_caller"));
    assert!(info.contains("Never"));
}

/// 测试控制流分析器的默认实现
#[test]
fn test_control_flow_analyzer_default() {
    let analyzer = ControlFlowAnalyzer::default();
    let (branches, loops, matches) = analyzer.get_statistics();

    assert_eq!(branches, 0);
    assert_eq!(loops, 0);
    assert_eq!(matches, 0);
}

/// 测试错误格式化
#[test]
fn test_error_display() {
    let error = LocatedError::new("显示测试");
    let display_str = format!("{}", error);

    assert!(display_str.contains("显示测试"));
    assert!(display_str.contains("Error at"));
}

/// 测试错误的 Error trait 实现
#[test]
fn test_error_trait() {
    use std::error::Error;

    let error = LocatedError::new("Error trait 测试");

    // 测试 source（应该返回 None）
    assert!(error.source().is_none());

    // 测试 Display
    let display = format!("{}", error);
    assert!(!display.is_empty());

    // 测试 Debug
    let debug = format!("{:?}", error);
    assert!(!debug.is_empty());
}

/// 测试复杂的控制流组合场景
#[test]
fn test_complex_control_flow_scenarios() {
    // 场景 1: 嵌套的分析和优化
    let mut analyzer = ControlFlowAnalyzer::new();
    let optimized = ControlFlowOptimizer::optimize_loop(20);
    analyzer.analyze_loop(20, |i| i % 2 == 0);

    // optimized 是 usize，总是 >= 0，所以只验证计算完成
    let _ = optimized;
    let (_, loops, _) = analyzer.get_statistics();
    assert_eq!(loops, 1);

    // 场景 2: 错误处理流程
    let results: Vec<Result<i32, LocatedError>> = vec![
        control_flow_branch(42),
        control_flow_branch(-1),
        control_flow_branch(100),
    ];

    assert!(results[0].is_ok());
    assert!(results[1].is_err());
    assert!(results[2].is_ok());

    // 场景 3: 多种匹配模式
    let match_results: Vec<i32> = vec![
        control_flow_match(Some(21)),
        control_flow_match(Some(-21)),
        control_flow_match(None),
        control_flow_match(Some(0)),
    ];

    assert_eq!(match_results, vec![42, 21, 0, 0]);
}

/// 测试边界条件
#[test]
fn test_edge_cases() {
    // 测试边界值
    assert!(control_flow_branch(0).is_ok());
    assert!(control_flow_branch(100).is_ok());

    // 测试空循环
    assert_eq!(control_flow_loop(0), 0);

    // 测试单个迭代
    assert_eq!(control_flow_loop(1), 1);

    // 测试大值
    assert!(control_flow_loop(100000) >= 100000);
}

/// 测试并发安全性（基本测试）
#[test]
fn test_concurrent_safety() {
    use std::thread;

    // 测试 ErrorContext 在并发场景下的使用
    let contexts: Vec<_> = (0..10)
        .map(|_| {
            thread::spawn(|| ErrorContext::current())
        })
        .map(|handle| handle.join().unwrap())
        .collect();

    // 验证所有上下文都包含有效信息
    for context in contexts {
        assert!(!context.file.is_empty());
        // line 和 column 在有效上下文中总是大于 0
        assert!(context.line >= 1);
    }
}

/// 测试性能相关功能（基本验证）
#[test]
fn test_performance_features() {
    // 测试大量循环的性能
    let start = std::time::Instant::now();
    let _ = control_flow_loop(10000);
    let duration = start.elapsed();

    // 验证循环在合理时间内完成（应该很快）
    // 允许一些灵活性，但应该很快完成
    assert!(duration.as_millis() < 10000);

    // 测试优化器的性能
    let start = std::time::Instant::now();
    let _ = ControlFlowOptimizer::optimize_loop(1000);
    let duration = start.elapsed();

    // 允许一些灵活性，但应该很快完成
    assert!(duration.as_millis() < 10000);
}

/// 集成测试：完整的控制流工作流
#[test]
fn test_complete_workflow() {
    // 1. 创建分析器
    let mut analyzer = ControlFlowAnalyzer::new();

    // 2. 执行各种控制流操作
    for i in 0..10 {
        analyzer.analyze_branch(i % 2 == 0);
    }

    analyzer.analyze_loop(20, |i| i % 3 == 0);

    for i in 0..5 {
        analyzer.analyze_match(Some(i));
    }

    // 3. 执行优化操作
    let optimized = ControlFlowOptimizer::optimize_loop(15);
    // optimized 是 usize，总是 >= 0，所以只验证计算完成
    let _ = optimized;

    // 4. 验证结果
    let (branches, loops, matches) = analyzer.get_statistics();
    assert_eq!(branches, 10);
    assert_eq!(loops, 1);
    assert_eq!(matches, 5);

    // 5. 测试错误处理
    match control_flow_branch(50) {
        Ok(value) => assert_eq!(value, 100),
        Err(e) => panic!("不应该出错: {}", e),
    }

    match control_flow_branch(-10) {
        Ok(_) => panic!("应该出错"),
        Err(e) => assert!(e.message.contains("non-negative")),
    }
}

/// 测试演示函数不会 panic
#[test]
fn test_demonstration_function() {
    // 验证演示函数可以正常执行（不 panic）
    demonstrate_rust_192_control_flow();

    // 这是一个基本测试，主要验证函数不会崩溃
    assert!(true);
}

/// 测试控制流模式匹配器
#[test]
fn test_control_flow_matcher() {
    // 测试带守卫的模式匹配
    assert_eq!(ControlFlowMatcher::match_with_guard(-5), "负数");
    assert_eq!(ControlFlowMatcher::match_with_guard(0), "零");
    assert_eq!(ControlFlowMatcher::match_with_guard(5), "小正数");
    assert_eq!(ControlFlowMatcher::match_with_guard(50), "中等正数");
    assert_eq!(ControlFlowMatcher::match_with_guard(200), "大正数");

    // 测试嵌套模式匹配
    assert_eq!(ControlFlowMatcher::nested_match(Some(Some(21))), 42);
    assert_eq!(ControlFlowMatcher::nested_match(Some(Some(-21))), 21);
    assert_eq!(ControlFlowMatcher::nested_match(Some(None)), 0);
    assert_eq!(ControlFlowMatcher::nested_match(None), -1);

    // 测试元组模式匹配
    assert_eq!(ControlFlowMatcher::tuple_match((3, 3, 3)), 9);
    assert_eq!(ControlFlowMatcher::tuple_match((2, 2, 1)), 4);
    assert_eq!(ControlFlowMatcher::tuple_match((1, 1, 2)), 2);
    assert_eq!(ControlFlowMatcher::tuple_match((1, 2, 3)), 6);

    // 测试范围模式匹配
    assert_eq!(ControlFlowMatcher::range_match(5), "单位数");
    assert_eq!(ControlFlowMatcher::range_match(42), "两位数");
    assert_eq!(ControlFlowMatcher::range_match(123), "三位数");
    assert_eq!(ControlFlowMatcher::range_match(1234), "四位数");
    assert_eq!(ControlFlowMatcher::range_match(12345), "五位数或更大");
}

/// 测试控制流组合器
#[test]
fn test_control_flow_combinator() {
    // 测试链式条件检查
    let valid_values = vec![10, 20, 30];
    let result = ControlFlowCombinator::chain_conditions(&valid_values).unwrap();
    assert_eq!(result, vec![20, 40, 60]);

    let invalid_values = vec![10, -5, 30];
    assert!(ControlFlowCombinator::chain_conditions(&invalid_values).is_err());

    // 测试组合循环和匹配
    let items = vec![Some(21), Some(-21), None, Some(10)];
    let results = ControlFlowCombinator::combine_loop_and_match(&items);
    assert_eq!(results, vec![42, 21, 0, 20]);

    // 测试组合分析和优化
    let items = vec![10, 20, 30];
    let (branches, _loops, _matches, optimized) = ControlFlowCombinator::analyze_and_optimize(&items);
    assert_eq!(branches, 3);
    let _ = optimized; // optimized 是 usize，总是 >= 0
}

/// 测试控制流性能分析器
#[test]
fn test_control_flow_profiler() {
    let mut profiler = ControlFlowProfiler::new();

    // 测试性能分析
    profiler.profile_branch(|| {
        let _ = control_flow_branch(42);
    });
    profiler.profile_loop(|| {
        let _ = control_flow_loop(100);
    });
    profiler.profile_match(|| {
        let _ = control_flow_match(Some(21));
    });

    let (branch_avg, loop_avg, match_avg) = profiler.get_stats();
    assert!(branch_avg >= 0.0);
    assert!(loop_avg >= 0.0);
    assert!(match_avg >= 0.0);

    // 测试重置
    profiler.reset();
    let (branch_avg, loop_avg, match_avg) = profiler.get_stats();
    assert_eq!(branch_avg, 0.0);
    assert_eq!(loop_avg, 0.0);
    assert_eq!(match_avg, 0.0);
}

/// 测试控制流验证器
#[test]
fn test_control_flow_validator() {
    // 测试分支验证
    assert!(ControlFlowValidator::validate_branch(42).is_ok());
    assert!(ControlFlowValidator::validate_branch(-1).is_err());
    assert!(ControlFlowValidator::validate_branch(1001).is_err());
    assert!(ControlFlowValidator::validate_branch(500).is_ok());

    // 测试循环终止验证
    assert!(ControlFlowValidator::validate_loop_termination(0).is_ok());
    assert!(ControlFlowValidator::validate_loop_termination(100).is_ok());
    assert!(ControlFlowValidator::validate_loop_termination(1_000_000).is_ok());
    assert!(ControlFlowValidator::validate_loop_termination(2_000_000).is_err());

    // 测试匹配完整性验证
    assert!(ControlFlowValidator::validate_match_coverage(Some(42)).is_ok());
    assert!(ControlFlowValidator::validate_match_coverage(Some(0)).is_ok());
    assert!(ControlFlowValidator::validate_match_coverage(Some(-1)).is_err());
    assert!(ControlFlowValidator::validate_match_coverage(None).is_err());
}

/// 测试新功能的集成场景
#[test]
fn test_new_features_integration() {
    // 场景：使用所有新功能进行复杂控制流处理
    let mut profiler = ControlFlowProfiler::new();
    let mut analyzer = ControlFlowAnalyzer::new();

    // 1. 使用模式匹配器
    let values = vec![-5, 0, 5, 50, 200];
    for value in &values {
        let result = ControlFlowMatcher::match_with_guard(*value);
        analyzer.analyze_branch(!result.is_empty());
        profiler.profile_branch(|| {
            let _ = ControlFlowMatcher::match_with_guard(*value);
        });
    }

    // 2. 使用组合器
    let valid_values = vec![10, 20, 30];
    profiler.profile_loop(|| {
        let _result = ControlFlowCombinator::chain_conditions(&valid_values);
    });

    // 3. 使用验证器
    for value in &valid_values {
        profiler.profile_match(|| {
            let _ = ControlFlowValidator::validate_branch(*value);
        });
    }

    // 4. 验证结果
    let (branches, _loops, _matches) = analyzer.get_statistics();
    assert!(branches > 0);

    let (branch_avg, loop_avg, match_avg) = profiler.get_stats();
    assert!(branch_avg >= 0.0);
    assert!(loop_avg >= 0.0);
    assert!(match_avg >= 0.0);
}

/// 测试控制流状态机
#[test]
fn test_state_machine_comprehensive() {
    let mut machine = ControlFlowStateMachine::new();

    // 测试完整工作流
    assert!(machine.execute_workflow(42).is_ok());
    assert_eq!(machine.current_state(), ControlFlowState::Completed);
    assert!(machine.transition_count() >= 3);

    // 测试错误工作流
    let mut machine2 = ControlFlowStateMachine::new();
    // 注意：execute_workflow 在 value <= 0 时会失败
    assert!(machine2.execute_workflow(-1).is_err());
}

/// 测试迭代器控制流扩展
#[test]
fn test_iterator_control_flow_comprehensive() {
    // 测试各种迭代器操作
    let numbers = vec![1, 2, 3, 4, 5];

    // 过滤测试
    let evens: Vec<_> = IteratorControlFlow::filter_with_control_flow(
        numbers.iter(),
        |&x| Ok(*x % 2 == 0),
    );
    assert_eq!(evens.len(), 2);

    // 映射测试
    let doubled = IteratorControlFlow::map_with_control_flow(numbers.iter(), |&x| {
        Ok(x * 2)
    });
    assert_eq!(doubled.unwrap(), vec![2, 4, 6, 8, 10]);

    // 折叠测试
    let sum = IteratorControlFlow::fold_with_control_flow(
        numbers.iter(),
        0,
        |acc, &x| Ok(acc + x),
    );
    assert_eq!(sum.unwrap(), 15);
}

/// 测试控制流可视化
#[test]
fn test_visualization_comprehensive() {
    let mut viz = ControlFlowVisualization::new();

    // 模拟一个完整的控制流过程
    viz.add_branch("检查输入");
    viz.add_branch("验证数据");
    viz.add_loop("处理数据");
    viz.add_match("模式匹配");
    viz.add_match("结果处理");

    let report = viz.generate_report();
    assert!(report.contains("分支数量: 2"));
    assert!(report.contains("循环数量: 1"));
    assert!(report.contains("匹配数量: 2"));

    let (branches, loops, matches, errors) = viz.statistics();
    assert_eq!(branches, 2);
    assert_eq!(loops, 1);
    assert_eq!(matches, 2);
    assert_eq!(errors, 0);
}

/// 测试异步控制流（如果启用）
#[cfg(feature = "async")]
#[tokio::test]
async fn test_async_features_comprehensive() {
    use c03_control_fn::rust_192_features::async_control_flow::*;

    // 测试异步组合器
    let values = vec![10, 20, 30, 40];
    let results = async_control_flow_combinator(&values).await;
    assert!(results.is_ok());
    assert_eq!(results.unwrap().len(), 4);
}

/// 测试并行控制流（如果启用）
#[cfg(feature = "std")]
#[test]
fn test_parallel_features_comprehensive() {
    use c03_control_fn::rust_192_features::parallel_control_flow::*;

    let values = vec![10, 20, -5, 30, 150, 50];
    let result = parallel_control_flow_branch(&values, 3);

    assert_eq!(result.all_results().len(), values.len());
    assert!(result.successes() + result.failures() == values.len());
}
