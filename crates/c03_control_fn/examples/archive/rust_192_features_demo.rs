#![doc(test(ignore))]
//! Rust 1.92.0 控制流特性演示示例
//!
//! 本示例展示了 Rust 1.92.0 在控制流和函数场景中的新特性应用：
//! - #[track_caller] 在控制流场景中的改进
//! - 更严格的 Never 类型 Lint
//! - Location API 在错误报告中的增强
//! - 改进的控制流分析
//! - 优化的错误处理和上下文捕获
//!
//! 运行方式:
//! ```bash
//! cargo run --example rust_192_features_demo
//! ```

use c03_control_fn::rust_192_features::{
    control_flow_check, control_flow_branch, control_flow_loop, control_flow_match,
    control_flow_with_never, LocatedError, ErrorContext,
    ControlFlowAnalyzer, ControlFlowOptimizer,
    ControlFlowMatcher, ControlFlowCombinator, ControlFlowProfiler, ControlFlowValidator,
    ControlFlowStateMachine, ControlFlowState,
    IteratorControlFlow,
    ControlFlowVisualization,
    demonstrate_rust_192_control_flow, get_rust_192_control_flow_info,
};

#[cfg(not(feature = "async"))]
fn main() -> anyhow::Result<()> {
    run_demo()
}

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    run_demo_async().await
}

#[cfg(not(feature = "async"))]
fn run_demo() -> anyhow::Result<()> {
    println!("🚀 Rust 1.92.0 控制流特性演示\n");
    println!("{}", "=".repeat(60));

    // 显示特性信息
    println!("\n📋 Rust 1.92.0 控制流特性列表:\n");
    println!("{}", get_rust_192_control_flow_info());

    println!("\n{}", "=".repeat(60));
    println!("\n🎯 综合演示\n");
    demonstrate_rust_192_control_flow();

    println!("\n{}", "=".repeat(60));
    println!("\n📊 实际应用场景演示\n");

    // 场景 1-9: 基础场景
    demonstrate_control_flow_analyzer();
    demonstrate_control_flow_optimizer();
    demonstrate_error_handling_with_location();
    demonstrate_never_type_usage();
    demonstrate_complex_control_flow();
    demonstrate_advanced_pattern_matching();
    demonstrate_control_flow_combinator();
    demonstrate_performance_profiling();
    demonstrate_control_flow_validation();

    // 场景 10-12: 高级场景
    demonstrate_state_machine();
    demonstrate_iterator_control_flow();
    demonstrate_visualization();

    // 场景 14: 并行控制流（如果启用）
    #[cfg(feature = "std")]
    demonstrate_parallel_control_flow();

    println!("\n✅ 所有演示完成！");
    println!("注意: 异步控制流演示需要启用 'async' 特性");

    Ok(())
}

#[cfg(feature = "async")]
async fn run_demo_async() -> anyhow::Result<()> {
    println!("🚀 Rust 1.92.0 控制流特性演示\n");
    println!("{}", "=".repeat(60));

    // 显示特性信息
    println!("\n📋 Rust 1.92.0 控制流特性列表:\n");
    println!("{}", get_rust_192_control_flow_info());

    println!("\n{}", "=".repeat(60));
    println!("\n🎯 综合演示\n");
    demonstrate_rust_192_control_flow();

    println!("\n{}", "=".repeat(60));
    println!("\n📊 实际应用场景演示\n");

    // 场景 1-9: 基础场景
    demonstrate_control_flow_analyzer();
    demonstrate_control_flow_optimizer();
    demonstrate_error_handling_with_location();
    demonstrate_never_type_usage();
    demonstrate_complex_control_flow();
    demonstrate_advanced_pattern_matching();
    demonstrate_control_flow_combinator();
    demonstrate_performance_profiling();
    demonstrate_control_flow_validation();

    // 场景 10-12: 高级场景
    demonstrate_state_machine();
    demonstrate_iterator_control_flow();
    demonstrate_visualization();

    // 场景 13: 异步控制流
    demonstrate_async_control_flow().await?;

    // 场景 14: 并行控制流（如果启用）
    #[cfg(feature = "std")]
    demonstrate_parallel_control_flow();

    println!("\n✅ 所有演示完成！");

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_async_control_flow() -> anyhow::Result<()> {
    use c03_control_fn::rust_192_features::async_control_flow::*;

    println!("\n⚡ 场景 13: 异步控制流");
    println!("{}", "-".repeat(60));

    // 异步分支
    println!("\n异步分支处理:");
    match async_control_flow_branch(42).await {
        Ok(result) => println!("  异步分支成功: {}", result),
        Err(e) => println!("  异步分支失败: {}", e),
    }

    // 异步循环
    println!("\n异步循环处理:");
    let count = async_control_flow_loop(5).await;
    println!("  异步循环完成，计数: {}", count);

    // 异步匹配
    println!("\n异步模式匹配:");
    let result = async_control_flow_match(Some(21)).await;
    println!("  异步匹配结果: {}", result);

    // 异步组合器
    println!("\n异步控制流组合:");
    let values = vec![10, 20, 30];
    match async_control_flow_combinator(&values).await {
        Ok(results) => {
            println!("  输入: {:?}", values);
            println!("  输出: {:?}", results);
        }
        Err(e) => println!("  异步组合失败: {}", e),
    }

    Ok(())
}

#[cfg(feature = "std")]
fn demonstrate_parallel_control_flow() {
    use c03_control_fn::rust_192_features::parallel_control_flow::*;

    println!("\n🔀 场景 14: 并行控制流");
    println!("{}", "-".repeat(60));

    let values = vec![10, 20, 30, -5, 50, 150, 40];
    println!("\n并行处理值: {:?}", values);

    let result = parallel_control_flow_branch(&values, 3);

    println!("\n并行处理结果:");
    println!("  成功数量: {}", result.successes());
    println!("  失败数量: {}", result.failures());
    println!("  总数量: {}", result.all_results().len());

    println!("\n详细结果:");
    for (i, res) in result.all_results().iter().enumerate() {
        match res {
            Ok(v) => println!("  值 {}: 成功 = {}", i, v),
            Err(e) => println!("  值 {}: 失败 = {}", i, e),
        }
    }
}

/// 演示控制流分析器
fn demonstrate_control_flow_analyzer() {
    println!("\n📈 场景 1: 控制流分析器");
    println!("{}", "-".repeat(60));

    let mut analyzer = ControlFlowAnalyzer::new();

    // 分析分支
    println!("\n分析分支结构:");
    for i in 0..5 {
        let result = analyzer.analyze_branch(i % 2 == 0);
        println!("  分支 {}: {}", i, if result { "真" } else { "假" });
    }

    // 分析循环
    println!("\n分析循环结构:");
    let count = analyzer.analyze_loop(10, |i| i % 3 == 0);
    println!("  符合条件的循环次数: {}", count);

    // 分析匹配
    println!("\n分析匹配结构:");
    analyzer.analyze_match(Some(42));
    analyzer.analyze_match(None::<i32>);
    analyzer.analyze_match(Some(100));

    let (branches, loops, matches) = analyzer.get_statistics();
    println!("\n控制流统计:");
    println!("  分支数: {}", branches);
    println!("  循环数: {}", loops);
    println!("  匹配数: {}", matches);
}

/// 演示控制流优化器
fn demonstrate_control_flow_optimizer() {
    println!("\n⚡ 场景 2: 控制流优化器");
    println!("{}", "-".repeat(60));

    // 优化循环
    println!("\n优化循环结构:");
    let result = ControlFlowOptimizer::optimize_loop(20);
    println!("  优化后的循环结果: {}", result);

    // 优化分支
    println!("\n优化分支结构:");
    match ControlFlowOptimizer::optimize_branch(42) {
        Ok(value) => println!("  优化后的分支结果: {}", value),
        Err(e) => println!("  分支错误: {}", e),
    }

    match ControlFlowOptimizer::optimize_branch(150) {
        Ok(value) => println!("  优化后的分支结果: {}", value),
        Err(e) => println!("  分支错误: {}", e),
    }

    // 优化匹配
    println!("\n优化匹配结构:");
    let result1 = ControlFlowOptimizer::optimize_match(Some(21));
    let result2 = ControlFlowOptimizer::optimize_match(Some(-21));
    let result3 = ControlFlowOptimizer::optimize_match(None);
    println!("  匹配结果 1: {}", result1);
    println!("  匹配结果 2: {}", result2);
    println!("  匹配结果 3: {}", result3);
}

/// 演示错误处理和位置追踪
fn demonstrate_error_handling_with_location() {
    println!("\n🔍 场景 3: 错误处理和位置追踪");
    println!("{}", "-".repeat(60));

    // 创建带位置的错误
    println!("\n创建带位置的错误:");
    let error1 = LocatedError::new("示例错误 1");
    println!("  错误 1: {}", error1);

    let error2 = LocatedError::new("示例错误 2");
    println!("  错误 2: {}", error2);

    // 获取错误上下文
    println!("\n获取错误上下文:");
    let context = ErrorContext::current();
    println!("  文件: {}", context.file);
    println!("  行号: {}", context.line);
    println!("  列号: {}", context.column);

    // 使用控制流分支和错误处理
    println!("\n控制流分支和错误处理:");
    for value in [-10, 42, 150] {
        match control_flow_branch(value) {
            Ok(result) => println!("  值 {} 处理成功: {}", value, result),
            Err(e) => println!("  值 {} 处理失败: {}", value, e),
        }
    }
}

/// 演示 Never 类型使用
fn demonstrate_never_type_usage() {
    println!("\n♾️  场景 4: Never 类型应用");
    println!("{}", "-".repeat(60));

    // 使用 Never 类型的控制流
    println!("\n使用 Never 类型的控制流:");
    let result1 = control_flow_with_never(Ok(42));
    println!("  成功结果: {}", result1);

    // 注意：control_flow_with_never(Err(...)) 会导致无限循环，所以不调用

    println!("\nNever 类型特点:");
    println!("  - Never 类型 (!) 表示函数永远不会返回");
    println!("  - 可以用于 panic、无限循环等场景");
    println!("  - Rust 1.92.0 对 Never 类型有更严格的 Lint 检查");
}

/// 演示复杂控制流组合
fn demonstrate_complex_control_flow() {
    println!("\n🎭 场景 5: 复杂控制流组合");
    println!("{}", "-".repeat(60));

    // 组合循环和分支
    println!("\n组合循环和分支:");
    let loop_result = control_flow_loop(10);
    println!("  循环计数: {}", loop_result);

    // 组合匹配和分支
    println!("\n组合匹配和分支:");
    let values = vec![Some(21), Some(-21), None, Some(0), Some(50)];
    for (i, value) in values.iter().enumerate() {
        let match_result = control_flow_match(*value);
        println!("  值 {}: 匹配结果 = {}", i, match_result);
    }

    // 组合分析和优化
    println!("\n组合分析和优化:");
    let mut analyzer = ControlFlowAnalyzer::new();
    let optimized_result = ControlFlowOptimizer::optimize_loop(15);
    analyzer.analyze_loop(15, |i| i % 2 == 0);

    let (branches, loops, matches) = analyzer.get_statistics();
    println!("  优化结果: {}", optimized_result);
    println!("  分析统计: 分支={}, 循环={}, 匹配={}", branches, loops, matches);

    // 控制流检查
    println!("\n控制流检查:");
    let check_results = vec![true, false, true, true];
    for (i, condition) in check_results.iter().enumerate() {
        let result = control_flow_check(*condition);
        println!("  检查 {}: 条件={}, 结果={}", i, condition, result);
    }
}

/// 演示高级模式匹配
fn demonstrate_advanced_pattern_matching() {
    println!("\n🎭 场景 6: 高级模式匹配");
    println!("{}", "-".repeat(60));

    // 带守卫的模式匹配
    println!("\n带守卫的模式匹配:");
    let test_values = vec![-5, 0, 5, 50, 200];
    for value in test_values {
        let result = ControlFlowMatcher::match_with_guard(value);
        println!("  值 {}: {}", value, result);
    }

    // 嵌套模式匹配
    println!("\n嵌套模式匹配:");
    let nested_values = vec![
        Some(Some(21)),
        Some(Some(-21)),
        Some(None),
        None,
    ];
    for (i, value) in nested_values.iter().enumerate() {
        let result = ControlFlowMatcher::nested_match(*value);
        println!("  嵌套值 {}: 结果 = {}", i, result);
    }

    // 元组模式匹配
    println!("\n元组模式匹配:");
    let tuples = vec![(3, 3, 3), (2, 2, 1), (1, 1, 2), (1, 2, 3)];
    for tuple in tuples {
        let result = ControlFlowMatcher::tuple_match(tuple);
        println!("  元组 {:?}: 结果 = {}", tuple, result);
    }

    // 范围模式匹配
    println!("\n范围模式匹配:");
    let range_values = vec![5, 42, 123, 1234, 12345];
    for value in range_values {
        let result = ControlFlowMatcher::range_match(value);
        println!("  值 {}: {}", value, result);
    }
}

/// 演示控制流组合器
fn demonstrate_control_flow_combinator() {
    println!("\n🔗 场景 7: 控制流组合器");
    println!("{}", "-".repeat(60));

    // 链式条件检查
    println!("\n链式条件检查:");
    let valid_values = vec![10, 20, 30, 40, 50];
    match ControlFlowCombinator::chain_conditions(&valid_values) {
        Ok(results) => {
            println!("  输入: {:?}", valid_values);
            println!("  输出: {:?}", results);
        }
        Err(e) => println!("  错误: {}", e),
    }

    let invalid_values = vec![10, -5, 30];
    match ControlFlowCombinator::chain_conditions(&invalid_values) {
        Ok(_) => println!("  意外成功"),
        Err(e) => println!("  预期的错误: {}", e),
    }

    // 组合循环和匹配
    println!("\n组合循环和匹配:");
    let items = vec![Some(21), Some(-21), None, Some(10), Some(0)];
    let results = ControlFlowCombinator::combine_loop_and_match(&items);
    println!("  输入: {:?}", items);
    println!("  输出: {:?}", results);

    // 组合分析和优化
    println!("\n组合分析和优化:");
    let items = vec![10, 20, 30, -5, 40];
    let (branches, loops, matches, optimized) = ControlFlowCombinator::analyze_and_optimize(&items);
    println!("  输入: {:?}", items);
    println!("  统计: 分支={}, 循环={}, 匹配={}, 优化成功={}", branches, loops, matches, optimized);
}

/// 演示性能分析
fn demonstrate_performance_profiling() {
    println!("\n⚡ 场景 8: 性能分析");
    println!("{}", "-".repeat(60));

    let mut profiler = ControlFlowProfiler::new();

    // 分析分支性能
    println!("\n分析分支性能:");
    for i in 0..10 {
        profiler.profile_branch(|| {
            let _ = control_flow_branch(i * 10);
        });
    }

    // 分析循环性能
    println!("\n分析循环性能:");
    for size in [10, 100, 1000] {
        profiler.profile_loop(|| {
            let _ = control_flow_loop(size);
        });
    }

    // 分析匹配性能
    println!("\n分析匹配性能:");
    let match_values = vec![Some(21), Some(-21), None, Some(10), Some(0)];
    for value in match_values {
        profiler.profile_match(|| {
            let _ = control_flow_match(value);
        });
    }

    // 获取统计信息
    let (branch_avg, loop_avg, match_avg) = profiler.get_stats();
    println!("\n性能统计 (纳秒):");
    println!("  分支平均: {:.2}", branch_avg);
    println!("  循环平均: {:.2}", loop_avg);
    println!("  匹配平均: {:.2}", match_avg);
}

/// 演示控制流验证
fn demonstrate_control_flow_validation() {
    println!("\n✅ 场景 9: 控制流验证");
    println!("{}", "-".repeat(60));

    // 验证分支逻辑
    println!("\n验证分支逻辑:");
    let branch_values = vec![42, -1, 1001, 500];
    for value in branch_values {
        match ControlFlowValidator::validate_branch(value) {
            Ok(v) => println!("  值 {}: 验证通过", v),
            Err(e) => println!("  值 {}: 验证失败 - {}", value, e),
        }
    }

    // 验证循环终止条件
    println!("\n验证循环终止条件:");
    let loop_sizes = vec![0, 100, 1_000_000, 2_000_000];
    for size in loop_sizes {
        match ControlFlowValidator::validate_loop_termination(size) {
            Ok(result) => println!("  大小 {}: 验证通过，结果 = {}", size, result),
            Err(e) => println!("  大小 {}: 验证失败 - {}", size, e),
        }
    }

    // 验证匹配完整性
    println!("\n验证匹配完整性:");
    let match_values = vec![Some(42), Some(-1), None, Some(0)];
    for value in match_values {
        match ControlFlowValidator::validate_match_coverage(value) {
            Ok(v) => println!("  值 {:?}: 验证通过，结果 = {}", value, v),
            Err(e) => println!("  值 {:?}: 验证失败 - {}", value, e),
        }
    }
}

/// 演示控制流状态机
fn demonstrate_state_machine() {
    println!("\n🔄 场景 10: 控制流状态机");
    println!("{}", "-".repeat(60));

    let mut machine = ControlFlowStateMachine::new();
    println!("\n初始状态: {:?}", machine.current_state());

    // 执行工作流
    println!("\n执行工作流 (值 = 42):");
    match machine.execute_workflow(42) {
        Ok(result) => {
            println!("  工作流成功完成");
            println!("  最终状态: {:?}", machine.current_state());
            println!("  结果值: {}", result);
            println!("  状态转换次数: {}", machine.transition_count());
        }
        Err(e) => println!("  工作流失败: {}", e),
    }

    // 手动状态转换
    println!("\n手动状态转换示例:");
    let mut machine2 = ControlFlowStateMachine::new();
    println!("  当前状态: {:?}", machine2.current_state());

    machine2.transition_to(ControlFlowState::Processing).unwrap();
    println!("  转换到 Processing: {:?}", machine2.current_state());

    machine2.transition_to(ControlFlowState::Validating).unwrap();
    println!("  转换到 Validating: {:?}", machine2.current_state());

    machine2.transition_to(ControlFlowState::Completed).unwrap();
    println!("  转换到 Completed: {:?}", machine2.current_state());

    // 测试重置
    machine2.reset();
    println!("  重置后状态: {:?}", machine2.current_state());
}

/// 演示迭代器控制流扩展
fn demonstrate_iterator_control_flow() {
    println!("\n🔄 场景 11: 迭代器控制流扩展");
    println!("{}", "-".repeat(60));

    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // 过滤示例
    println!("\n使用控制流过滤（偶数）:");
    let evens = IteratorControlFlow::filter_with_control_flow(numbers.iter(), |&x| {
        Ok(*x % 2 == 0)
    });
    println!("  输入: {:?}", numbers);
    println!("  输出: {:?}", evens);

    // 映射示例
    println!("\n使用控制流映射（乘以2）:");
    match IteratorControlFlow::map_with_control_flow(numbers.iter(), |&x| {
        control_flow_branch(x)
    }) {
        Ok(doubled) => {
            println!("  输入: {:?}", numbers);
            println!("  输出: {:?}", doubled);
        }
        Err(e) => println!("  映射失败: {}", e),
    }

    // 折叠示例
    println!("\n使用控制流折叠（求和）:");
    match IteratorControlFlow::fold_with_control_flow(
        numbers.iter(),
        0,
        |acc, &x| Ok(acc + x),
    ) {
        Ok(sum) => println!("  总和: {}", sum),
        Err(e) => println!("  折叠失败: {}", e),
    }

    // 查找示例
    println!("\n使用控制流查找（值为7）:");
    match IteratorControlFlow::find_with_control_flow(numbers.iter(), |&x| {
        Ok(*x == 7)
    }) {
        Some(found) => println!("  找到: {}", found),
        None => println!("  未找到"),
    }
}

/// 演示控制流可视化
fn demonstrate_visualization() {
    println!("\n📊 场景 12: 控制流可视化");
    println!("{}", "-".repeat(60));

    let mut viz = ControlFlowVisualization::new();

    // 模拟一个完整的控制流过程
    println!("\n收集控制流信息:");

    viz.add_branch("检查输入有效性");
    viz.add_branch("验证数据格式");
    viz.add_loop("处理数据列表");
    viz.add_match("匹配数据类型");
    viz.add_match("处理结果模式");
    viz.add_error("数据验证失败");

    // 生成报告
    println!("\n生成可视化报告:");
    let report = viz.generate_report();
    println!("{}", report);

    // 显示统计信息
    let (branches, loops, matches, errors) = viz.statistics();
    println!("\n统计摘要:");
    println!("  分支: {}", branches);
    println!("  循环: {}", loops);
    println!("  匹配: {}", matches);
    println!("  错误: {}", errors);
}
