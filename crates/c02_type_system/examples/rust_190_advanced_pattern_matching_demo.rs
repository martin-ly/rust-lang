//! Rust 1.90 高级模式匹配演示
//!
//! 本示例展示了 Rust 1.90 中的高级模式匹配特性

use c02_type_system::advanced_pattern_matching::*;
use std::collections::HashMap;

fn main() {
    println!("=== Rust 1.90 高级模式匹配演示程序 ===\n");
    
    // 运行所有高级模式匹配演示
    demonstrate_advanced_pattern_matching();
    
    // 运行交互式演示
    interactive_pattern_matching_demo();
    
    // 运行性能测试
    pattern_matching_performance_demo();
}

/// 交互式模式匹配演示
fn interactive_pattern_matching_demo() {
    println!("\n=== 交互式模式匹配演示 ===\n");
    
    // 1. 交互式表达式求值
    println!("1. 交互式表达式求值:");
    interactive_expression_evaluation();
    
    // 2. 交互式动态模式匹配
    println!("\n2. 交互式动态模式匹配:");
    interactive_dynamic_pattern_matching();
    
    // 3. 交互式模式优化
    println!("\n3. 交互式模式优化:");
    interactive_pattern_optimization();
    
    // 4. 交互式嵌套模式匹配
    println!("\n4. 交互式嵌套模式匹配:");
    interactive_nested_pattern_matching();
}

/// 交互式表达式求值
fn interactive_expression_evaluation() {
    let mut evaluator = ExpressionEvaluator::new();
    
    // 设置变量
    evaluator.set_variable("x".to_string(), LiteralValue::Integer(10));
    evaluator.set_variable("y".to_string(), LiteralValue::Integer(5));
    evaluator.set_variable("z".to_string(), LiteralValue::Float(3.14));
    evaluator.set_variable("flag".to_string(), LiteralValue::Boolean(true));
    
    println!("  设置的变量:");
    println!("    x = 10");
    println!("    y = 5");
    println!("    z = 3.14");
    println!("    flag = true");
    
    // 测试各种表达式
    let expressions = vec![
        ("x + y", ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Variable("x".to_string())),
            operator: BinaryOperator::Add,
            right: Box::new(ComplexExpression::Variable("y".to_string())),
        }),
        ("x * y", ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Variable("x".to_string())),
            operator: BinaryOperator::Mul,
            right: Box::new(ComplexExpression::Variable("y".to_string())),
        }),
        ("x > y", ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Variable("x".to_string())),
            operator: BinaryOperator::Gt,
            right: Box::new(ComplexExpression::Variable("y".to_string())),
        }),
        ("!flag", ComplexExpression::UnaryOp {
            operator: UnaryOperator::Not,
            operand: Box::new(ComplexExpression::Variable("flag".to_string())),
        }),
        ("max(x, y)", ComplexExpression::FunctionCall {
            name: "max".to_string(),
            arguments: vec![
                ComplexExpression::Variable("x".to_string()),
                ComplexExpression::Variable("y".to_string()),
            ],
        }),
        ("x > 5 ? 'big' : 'small'", ComplexExpression::Conditional {
            condition: Box::new(ComplexExpression::BinaryOp {
                left: Box::new(ComplexExpression::Variable("x".to_string())),
                operator: BinaryOperator::Gt,
                right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(5))),
            }),
            true_branch: Box::new(ComplexExpression::Literal(LiteralValue::String("big".to_string()))),
            false_branch: Box::new(ComplexExpression::Literal(LiteralValue::String("small".to_string()))),
        }),
    ];
    
    for (description, expr) in expressions {
        println!("  表达式: {}", description);
        println!("    展开: {}", expr);
        match evaluator.evaluate(&expr) {
            Ok(result) => println!("    结果: {}", result),
            Err(e) => println!("    错误: {}", e),
        }
        println!();
    }
}

/// 交互式动态模式匹配
fn interactive_dynamic_pattern_matching() {
    let mut dynamic_matcher = DynamicPatternMatcher::new();
    
    // 添加各种动态模式
    dynamic_matcher.add_pattern(
        "arithmetic_operations".to_string(),
        |expr| matches!(expr, ComplexExpression::BinaryOp { operator: BinaryOperator::Add | BinaryOperator::Sub | BinaryOperator::Mul | BinaryOperator::Div, .. }),
        |expr| {
            if let ComplexExpression::BinaryOp { operator, .. } = expr {
                Ok(LiteralValue::String(format!("Arithmetic operation: {}", operator)))
            } else {
                Err("Not an arithmetic operation".to_string())
            }
        },
    );
    
    dynamic_matcher.add_pattern(
        "comparison_operations".to_string(),
        |expr| matches!(expr, ComplexExpression::BinaryOp { operator: BinaryOperator::Eq | BinaryOperator::Ne | BinaryOperator::Lt | BinaryOperator::Le | BinaryOperator::Gt | BinaryOperator::Ge, .. }),
        |expr| {
            if let ComplexExpression::BinaryOp { operator, .. } = expr {
                Ok(LiteralValue::String(format!("Comparison operation: {}", operator)))
            } else {
                Err("Not a comparison operation".to_string())
            }
        },
    );
    
    dynamic_matcher.add_pattern(
        "function_calls".to_string(),
        |expr| matches!(expr, ComplexExpression::FunctionCall { .. }),
        |expr| {
            if let ComplexExpression::FunctionCall { name, arguments } = expr {
                Ok(LiteralValue::String(format!("Function call: {}({} args)", name, arguments.len())))
            } else {
                Err("Not a function call".to_string())
            }
        },
    );
    
    dynamic_matcher.add_pattern(
        "literals".to_string(),
        |expr| matches!(expr, ComplexExpression::Literal(_)),
        |expr| {
            if let ComplexExpression::Literal(lit) = expr {
                Ok(LiteralValue::String(format!("Literal: {}", lit)))
            } else {
                Err("Not a literal".to_string())
            }
        },
    );
    
    // 显示注册的模式
    let patterns = dynamic_matcher.get_pattern_names();
    println!("  注册的动态模式: {:?}", patterns);
    
    // 测试各种表达式
    let test_expressions = vec![
        ("加法", ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Literal(LiteralValue::Integer(10))),
            operator: BinaryOperator::Add,
            right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(20))),
        }),
        ("比较", ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Variable("x".to_string())),
            operator: BinaryOperator::Gt,
            right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(5))),
        }),
        ("函数调用", ComplexExpression::FunctionCall {
            name: "abs".to_string(),
            arguments: vec![ComplexExpression::Literal(LiteralValue::Integer(-10))],
        }),
        ("字面量", ComplexExpression::Literal(LiteralValue::String("Hello".to_string()))),
        ("变量", ComplexExpression::Variable("unknown".to_string())),
    ];
    
    for (description, expr) in test_expressions {
        println!("  测试表达式: {}", description);
        println!("    表达式: {}", expr);
        match dynamic_matcher.match_and_handle(&expr) {
            Ok(result) => println!("    匹配结果: {}", result),
            Err(e) => println!("    匹配错误: {}", e),
        }
        println!();
    }
}

/// 交互式模式优化
fn interactive_pattern_optimization() {
    let mut optimizer = PatternMatchingOptimizer::new();
    
    // 测试常量折叠
    let constant_folding_expr = ComplexExpression::BinaryOp {
        left: Box::new(ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Literal(LiteralValue::Integer(10))),
            operator: BinaryOperator::Add,
            right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(20))),
        }),
        operator: BinaryOperator::Mul,
        right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(2))),
    };
    
    println!("  常量折叠测试:");
    println!("    原始表达式: {}", constant_folding_expr);
    match optimizer.evaluate_optimized(&constant_folding_expr) {
        Ok(result) => println!("    优化结果: {}", result),
        Err(e) => println!("    优化错误: {}", e),
    }
    
    // 测试一元运算优化
    let unary_optimization_expr = ComplexExpression::UnaryOp {
        operator: UnaryOperator::Neg,
        operand: Box::new(ComplexExpression::Literal(LiteralValue::Integer(42))),
    };
    
    println!("  一元运算优化测试:");
    println!("    原始表达式: {}", unary_optimization_expr);
    match optimizer.evaluate_optimized(&unary_optimization_expr) {
        Ok(result) => println!("    优化结果: {}", result),
        Err(e) => println!("    优化错误: {}", e),
    }
    
    // 测试缓存效果
    println!("  缓存效果测试:");
    let cache_test_expr = ComplexExpression::BinaryOp {
        left: Box::new(ComplexExpression::Literal(LiteralValue::Integer(100))),
        operator: BinaryOperator::Add,
        right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(200))),
    };
    
    // 第一次求值
    let start = std::time::Instant::now();
    let _ = optimizer.evaluate_optimized(&cache_test_expr);
    let first_duration = start.elapsed();
    
    // 第二次求值（应该使用缓存）
    let start = std::time::Instant::now();
    let _ = optimizer.evaluate_optimized(&cache_test_expr);
    let second_duration = start.elapsed();
    
    println!("    第一次求值耗时: {:?}", first_duration);
    println!("    第二次求值耗时: {:?}", second_duration);
    
    let stats = optimizer.get_stats();
    println!("    优化统计: {:?}", stats);
}

/// 交互式嵌套模式匹配
fn interactive_nested_pattern_matching() {
    let nested_matcher = NestedPatternMatcher;
    
    // 创建复杂的嵌套数据结构
    let complex_nested_data = NestedData::Branch {
        name: "root".to_string(),
        children: vec![
            NestedData::Leaf("important_leaf".to_string()),
            NestedData::Branch {
                name: "section1".to_string(),
                children: vec![
                    NestedData::Leaf("leaf1".to_string()),
                    NestedData::Leaf("leaf2".to_string()),
                    NestedData::Array(vec![
                        NestedData::Leaf("array_item1".to_string()),
                        NestedData::Leaf("array_item2".to_string()),
                        NestedData::Branch {
                            name: "nested_branch".to_string(),
                            children: vec![
                                NestedData::Leaf("deep_leaf".to_string()),
                            ],
                        },
                    ]),
                ],
            },
            NestedData::Branch {
                name: "section2".to_string(),
                children: vec![
                    NestedData::Object({
                        let mut map = HashMap::new();
                        map.insert("key1".to_string(), NestedData::Leaf("value1".to_string()));
                        map.insert("key2".to_string(), NestedData::Leaf("value2".to_string()));
                        map.insert("nested_object".to_string(), NestedData::Object({
                            let mut nested_map = HashMap::new();
                            nested_map.insert("nested_key".to_string(), NestedData::Leaf("nested_value".to_string()));
                            nested_map
                        }));
                        map
                    }),
                ],
            },
        ],
    };
    
    println!("  复杂嵌套数据结构已创建");
    
    // 测试名称搜索
    let search_targets = vec!["important_leaf", "leaf1", "deep_leaf", "nested_key", "nonexistent"];
    
    for target in search_targets {
        let found_nodes = nested_matcher.find_by_name(&complex_nested_data, target);
        println!("  搜索 '{}': 找到 {} 个节点", target, found_nodes.len());
    }
    
    // 测试数据转换
    println!("  数据转换测试:");
    let transformed_data = nested_matcher.transform(&complex_nested_data, |data| {
        match data {
            NestedData::Leaf(name) => {
                NestedData::Leaf(format!("transformed_{}", name))
            },
            NestedData::Branch { name, children } => {
                NestedData::Branch {
                    name: format!("transformed_{}", name),
                    children: children.clone(),
                }
            },
            other => other.clone(),
        }
    });
    
    // 查找转换后的节点
    let transformed_found = nested_matcher.find_by_name(&transformed_data, "transformed_important_leaf");
    println!("  转换后找到的节点数量: {}", transformed_found.len());
    
    // 测试数据过滤
    println!("  数据过滤测试:");
    let filtered_data = nested_matcher.filter(&complex_nested_data, |data| {
        match data {
            NestedData::Leaf(name) => name.contains("leaf"),
            NestedData::Branch { name, .. } => name.contains("section"),
            _ => true,
        }
    });
    
    if let Some(filtered) = filtered_data {
        println!("  过滤后的数据结构: {:?}", filtered);
        
        // 在过滤后的数据中搜索
        let filtered_search = nested_matcher.find_by_name(&filtered, "leaf1");
        println!("  在过滤数据中搜索 'leaf1': 找到 {} 个节点", filtered_search.len());
    }
}

/// 模式匹配性能演示
fn pattern_matching_performance_demo() {
    println!("\n=== 模式匹配性能演示 ===\n");
    
    // 1. 表达式求值性能测试
    println!("1. 表达式求值性能测试:");
    let mut evaluator = ExpressionEvaluator::new();
    evaluator.set_variable("x".to_string(), LiteralValue::Integer(10));
    evaluator.set_variable("y".to_string(), LiteralValue::Integer(5));
    
    let test_expr = ComplexExpression::BinaryOp {
        left: Box::new(ComplexExpression::BinaryOp {
            left: Box::new(ComplexExpression::Variable("x".to_string())),
            operator: BinaryOperator::Add,
            right: Box::new(ComplexExpression::Variable("y".to_string())),
        }),
        operator: BinaryOperator::Mul,
        right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(2))),
    };
    
    let iterations = 10000;
    let start = std::time::Instant::now();
    
    for _ in 0..iterations {
        let _ = evaluator.evaluate(&test_expr);
    }
    
    let duration = start.elapsed();
    println!("  {} 次表达式求值耗时: {:?}", iterations, duration);
    println!("  平均每次求值: {:?}", duration / iterations);
    
    // 2. 优化器性能测试
    println!("\n2. 优化器性能测试:");
    let mut optimizer = PatternMatchingOptimizer::new();
    
    let optimizable_expr = ComplexExpression::BinaryOp {
        left: Box::new(ComplexExpression::Literal(LiteralValue::Integer(100))),
        operator: BinaryOperator::Add,
        right: Box::new(ComplexExpression::Literal(LiteralValue::Integer(200))),
    };
    
    let start = std::time::Instant::now();
    
    for _ in 0..iterations {
        let _ = optimizer.evaluate_optimized(&optimizable_expr);
    }
    
    let duration = start.elapsed();
    println!("  {} 次优化求值耗时: {:?}", iterations, duration);
    println!("  平均每次求值: {:?}", duration / iterations);
    
    let stats = optimizer.get_stats();
    println!("  优化统计: {:?}", stats);
    println!("  缓存命中率: {:.2}%", 
            stats.cache_hits as f64 / (stats.cache_hits + stats.cache_misses) as f64 * 100.0);
    
    // 3. 动态模式匹配性能测试
    println!("\n3. 动态模式匹配性能测试:");
    let mut dynamic_matcher = DynamicPatternMatcher::new();
    
    // 添加多个模式
    for i in 0..10 {
        dynamic_matcher.add_pattern(
            format!("pattern_{}", i),
            |expr| matches!(expr, ComplexExpression::Literal(_)),
            move |_| Ok(LiteralValue::Integer(i)),
        );
    }
    
    let test_expr = ComplexExpression::Literal(LiteralValue::Integer(42));
    
    let start = std::time::Instant::now();
    
    for _ in 0..iterations {
        let _ = dynamic_matcher.match_and_handle(&test_expr);
    }
    
    let duration = start.elapsed();
    println!("  {} 次动态模式匹配耗时: {:?}", iterations, duration);
    println!("  平均每次匹配: {:?}", duration / iterations);
    
    // 4. 嵌套模式匹配性能测试
    println!("\n4. 嵌套模式匹配性能测试:");
    let nested_matcher = NestedPatternMatcher;
    
    // 创建大型嵌套数据结构
    let large_nested_data = create_large_nested_data(100);
    
    let start = std::time::Instant::now();
    
    for _ in 0..100 {
        let _ = nested_matcher.find_by_name(&large_nested_data, "target_leaf");
    }
    
    let duration = start.elapsed();
    println!("  100 次嵌套搜索耗时: {:?}", duration);
    println!("  平均每次搜索: {:?}", duration / 100);
}

/// 创建大型嵌套数据结构用于性能测试
fn create_large_nested_data(size: usize) -> NestedData {
    let mut children = Vec::new();
    
    for i in 0..size {
        children.push(NestedData::Branch {
            name: format!("branch_{}", i),
            children: vec![
                NestedData::Leaf(format!("leaf_{}", i)),
                NestedData::Leaf(format!("target_leaf")), // 目标节点
                NestedData::Array(vec![
                    NestedData::Leaf(format!("array_leaf_{}", i)),
                    NestedData::Leaf(format!("array_leaf_{}", i + 1)),
                ]),
            ],
        });
    }
    
    NestedData::Branch {
        name: "root".to_string(),
        children,
    }
}

