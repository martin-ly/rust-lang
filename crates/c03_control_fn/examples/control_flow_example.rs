//! Rust 1.89 控制流特性示例
//!
//! 本示例展示了Rust 1.89版本中的控制流特性：
//! - 改进的模式匹配
//! - 控制流优化
//! - 新的控制结构
//! - 性能改进
use anyhow::Result;

/// Rust 1.89 改进的模式匹配示例
///
/// 模式匹配现在支持更复杂的模式和更好的性能
#[derive(Debug, Clone, PartialEq)]
enum Shape {
    Circle { radius: f64 },
    Rectangle { width: f64, height: f64 },
    Triangle { a: f64, b: f64, c: f64 },
    Polygon { sides: Vec<f64> },
}

impl Shape {
    /// 计算面积
    fn area(&self) -> f64 {
        match self {
            Shape::Circle { radius } => std::f64::consts::PI * radius * radius,
            Shape::Rectangle { width, height } => width * height,
            Shape::Triangle { a, b, c } => {
                // 海伦公式
                let s = (a + b + c) / 2.0;
                (s * (s - a) * (s - b) * (s - c)).sqrt()
            }
            Shape::Polygon { sides } => {
                // 简化计算，实际应该使用更复杂的算法
                sides.iter().sum::<f64>() * 0.5
            }
        }
    }

    /// 检查是否为规则形状
    fn is_regular(&self) -> bool {
        match self {
            Shape::Circle { .. } => true,
            Shape::Rectangle { width, height } => (width - height).abs() < f64::EPSILON,
            Shape::Triangle { a, b, c } => {
                (a - b).abs() < f64::EPSILON && (b - c).abs() < f64::EPSILON
            }
            Shape::Polygon { sides } => {
                if sides.len() < 3 {
                    return false;
                }
                let first = sides[0];
                sides
                    .iter()
                    .all(|&side| (side - first).abs() < f64::EPSILON)
            }
        }
    }
}

/// Rust 1.89 控制流优化示例
///
/// 控制流现在有了显著的性能改进
struct ControlFlowOptimizer;

impl ControlFlowOptimizer {
    /// 优化的条件判断
    #[inline(always)]
    fn optimized_condition_check(&self, value: i32) -> &'static str {
        // 编译器会优化这种连续的条件判断
        if value < 0 {
            "负数"
        } else if value == 0 {
            "零"
        } else if value < 100 {
            "小正数"
        } else if value < 1000 {
            "中等正数"
        } else {
            "大正数"
        }
    }

    /// 优化的循环控制
    #[inline(always)]
    fn optimized_loop_control(&self, items: &[i32]) -> (i32, i32, i32) {
        let mut sum = 0;
        let mut count = 0;
        let mut max = i32::MIN;

        // 编译器会优化这种循环
        for &item in items {
            sum += item;
            count += 1;
            if item > max {
                max = item;
            }
        }

        (sum, count, max)
    }

    /// 优化的迭代器链
    #[inline(always)]
    fn optimized_iterator_chain(&self, items: &[i32]) -> Vec<i32> {
        items
            .iter()
            .filter(|&&x| x > 0)
            .map(|&x| x * 2)
            .take(10)
            .collect()
    }
}

/// Rust 1.89 新的控制结构示例
///
/// 引入了新的控制结构来简化常见的编程模式
struct NewControlStructures;

impl NewControlStructures {
    /// 使用let-else模式（Rust 1.89中的改进）
    fn let_else_pattern(&self, input: Option<String>) -> Result<String> {
        let Some(value) = input else {
            return Err(anyhow::anyhow!("输入为空"));
        };

        if value.is_empty() {
            return Err(anyhow::anyhow!("输入字符串为空"));
        }

        Ok(value.to_uppercase())
    }

    /// 改进的if-let模式
    fn improved_if_let(&self, input: Option<i32>) -> String {
        if let Some(value) = input {
            if value > 0 {
                format!("正数: {}", value)
            } else if value < 0 {
                format!("负数: {}", value)
            } else {
                "零".to_string()
            }
        } else {
            "无值".to_string()
        }
    }

    /// 使用match表达式作为值
    fn match_as_expression(&self, input: &str) -> i32 {
        match input {
            "one" | "一" => 1,
            "two" | "二" => 2,
            "three" | "三" => 3,
            "four" | "四" => 4,
            "five" | "五" => 5,
            _ => -1,
        }
    }
}

/// Rust 1.89 控制流性能改进示例
///
/// 控制流现在有了显著的性能改进
struct PerformanceImprovements;

impl PerformanceImprovements {
    /// 分支预测友好的控制流
    #[inline(always)]
    fn branch_prediction_friendly(&self, data: &[i32]) -> Vec<i32> {
        let mut result = Vec::new();

        // 编译器会优化这种模式
        for &item in data {
            match item {
                0..=10 => result.push(item * 2),
                11..=50 => result.push(item + 10),
                51..=100 => result.push(item / 2),
                _ => result.push(item),
            }
        }

        result
    }

    /// 无分支控制流
    #[inline(always)]
    fn branchless_control_flow(&self, a: i32, b: i32) -> i32 {
        // 使用位运算避免分支
        let mask = (a > b) as i32;
        mask * a + (1 - mask) * b
    }

    /// 向量化友好的控制流
    #[inline(always)]
    fn vectorization_friendly(&self, data: &[f64]) -> Vec<f64> {
        data.iter()
            .map(|&x| if x > 0.0 { x.sqrt() } else { 0.0 })
            .collect()
    }
}

/// Rust 1.89 控制流错误处理改进示例
///
/// 错误处理现在更加优雅和高效
struct ErrorHandlingImprovements;

impl ErrorHandlingImprovements {
    /// 使用?操作符的改进
    fn improved_error_handling(&self, input: &str) -> Result<i32> {
        let parsed = input.parse::<i32>()?;

        if parsed < 0 {
            return Err(anyhow::anyhow!("不能处理负数"));
        }

        Ok(parsed * 2)
    }

    /// 使用map_or的改进
    fn map_or_improvement(&self, input: Option<String>) -> String {
        input
            .map(|s| s.to_uppercase())
            .unwrap_or_else(|| "默认值".to_string())
    }

    /// 使用and_then的改进
    fn and_then_improvement(&self, input: Option<i32>) -> Option<String> {
        input.filter(|&x| x > 0).map(|x| format!("正数: {}", x))
    }
}

/// 主函数
fn main() -> Result<()> {
    println!("🚀 Rust 1.89 控制流特性演示");
    println!("{}", "=".repeat(50));

    // 1. 改进的模式匹配示例
    println!("\n1. 改进的模式匹配示例");
    let shapes = vec![
        Shape::Circle { radius: 5.0 },
        Shape::Rectangle {
            width: 4.0,
            height: 6.0,
        },
        Shape::Triangle {
            a: 3.0,
            b: 4.0,
            c: 5.0,
        },
        Shape::Polygon {
            sides: vec![2.0, 2.0, 2.0, 2.0],
        },
    ];

    for shape in &shapes {
        println!(
            "形状: {:?}, 面积: {:.2}, 规则: {}",
            shape,
            shape.area(),
            shape.is_regular()
        );
    }

    // 2. 控制流优化示例
    println!("\n2. 控制流优化示例");
    let optimizer = ControlFlowOptimizer;
    let numbers = vec![1, -5, 0, 100, 500, 2000];

    for &num in &numbers {
        println!("{} -> {}", num, optimizer.optimized_condition_check(num));
    }

    let (sum, count, max) = optimizer.optimized_loop_control(&numbers);
    println!("统计: 总和={}, 数量={}, 最大值={}", sum, count, max);

    let filtered = optimizer.optimized_iterator_chain(&numbers);
    println!("过滤后: {:?}", filtered);

    // 3. 新的控制结构示例
    println!("\n3. 新的控制结构示例");
    let new_controls = NewControlStructures;

    let test_inputs = vec![Some("hello".to_string()), Some("".to_string()), None];

    for input in test_inputs {
        match new_controls.let_else_pattern(input.clone()) {
            Ok(result) => println!("输入 {:?} -> 成功: {}", input, result),
            Err(e) => println!("输入 {:?} -> 错误: {}", input, e),
        }
    }

    let number_inputs = vec![Some(5), Some(-3), Some(0), None];
    for input in number_inputs {
        println!(
            "输入 {:?} -> {}",
            input,
            new_controls.improved_if_let(input)
        );
    }

    let word_inputs = vec!["one", "二", "three", "unknown"];
    for input in word_inputs {
        println!(
            "单词 '{}' -> 数字 {}",
            input,
            new_controls.match_as_expression(input)
        );
    }

    // 4. 控制流性能改进示例
    println!("\n4. 控制流性能改进示例");
    let performance = PerformanceImprovements;
    let test_data = vec![5, 25, 75, 150, -10];

    let processed = performance.branch_prediction_friendly(&test_data);
    println!("分支预测友好处理: {:?}", processed);

    let max_value = performance.branchless_control_flow(10, 20);
    println!("无分支最大值: {}", max_value);

    let vector_data = vec![4.0, 9.0, 16.0, -1.0, 25.0];
    let vectorized = performance.vectorization_friendly(&vector_data);
    println!("向量化友好处理: {:?}", vectorized);

    // 5. 错误处理改进示例
    println!("\n5. 错误处理改进示例");
    let error_handler = ErrorHandlingImprovements;
    let test_strings = vec!["42", "-5", "abc", "100"];

    for s in test_strings {
        match error_handler.improved_error_handling(s) {
            Ok(result) => println!("'{}' -> 成功: {}", s, result),
            Err(e) => println!("'{}' -> 错误: {}", s, e),
        }
    }

    let option_inputs = vec![Some("hello".to_string()), None];

    for input in option_inputs {
        println!(
            "输入 {:?} -> map_or: {}",
            input,
            error_handler.map_or_improvement(input.clone())
        );
        println!(
            "输入 {:?} -> and_then: {:?}",
            input,
            error_handler.and_then_improvement(Some(42))
        );
    }

    println!("\n✅ Rust 1.89 控制流特性演示完成！");
    Ok(())
}
