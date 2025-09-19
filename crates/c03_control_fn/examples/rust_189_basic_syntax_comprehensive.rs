//! Rust 1.89 基础语法综合示例
//!
//! 本示例展示了 Rust 1.89 版本中基础语法的所有重要特性，包括：
//! - 变量声明与绑定
//! - 数据类型与类型推断
//! - 控制流结构
//! - 函数定义与调用
//! - 表达式与语句
//! - 模式匹配
//! - 错误处理
//! - let_chains 新特性
//! - cfg_boolean_literals 新特性
//! - 增强的模式匹配
//! - 改进的类型推断
//! - 新的控制流特性
//! - 改进的错误处理
//!
//! 运行方式：
//! ```bash
//! cargo run --example rust_189_basic_syntax_comprehensive
//! ```

use c03_control_fn::*;
use std::collections::HashMap;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

/// 主函数 - 运行所有基础语法演示
fn main() {
    println!("🚀 Rust 1.89 基础语法综合示例");
    println!("=====================================");
    println!("本示例将展示 Rust 1.89 版本中基础语法的所有重要特性");
    println!();

    // 运行基础语法演示
    run_basic_syntax_demos();
    
    // 运行 Rust 1.89 新特性演示
    run_rust_189_demos();
    
    // 运行综合应用示例
    run_comprehensive_examples();
    
    println!("\n🎉 所有演示完成！");
}

/// 运行基础语法演示
fn run_basic_syntax_demos() {
    println!("📚 第一部分：基础语法演示");
    println!("==========================");
    
    // 变量声明与绑定
    println!("\n1. 变量声明与绑定");
    basic_syntax::variable_binding::basic_variable_declaration();
    basic_syntax::variable_binding::complex_type_declaration();
    basic_syntax::variable_binding::pattern_matching_binding();
    
    // 数据类型与类型推断
    println!("\n2. 数据类型与类型推断");
    basic_syntax::type_system::basic_data_types();
    basic_syntax::type_system::compound_data_types();
    basic_syntax::type_system::type_inference();
    
    // 控制流结构
    println!("\n3. 控制流结构");
    basic_syntax::control_flow::conditional_statements();
    basic_syntax::control_flow::loop_statements();
    basic_syntax::control_flow::pattern_matching();
    
    // 函数定义与调用
    println!("\n4. 函数定义与调用");
    basic_syntax::functions::basic_functions();
    basic_syntax::functions::advanced_functions();
    basic_syntax::functions::generic_functions();
    
    // 错误处理
    println!("\n5. 错误处理");
    basic_syntax::error_handling::basic_error_handling();
    basic_syntax::error_handling::advanced_error_handling();
}

/// 运行 Rust 1.89 新特性演示
fn run_rust_189_demos() {
    println!("\n\n🆕 第二部分：Rust 1.89 新特性演示");
    println!("==================================");
    
    // let_chains 稳定化
    println!("\n1. let_chains 稳定化");
    let_chains::basic_let_chains();
    let_chains::advanced_let_chains();
    let_chains::while_let_chains();
    
    // cfg_boolean_literals 稳定化
    println!("\n2. cfg_boolean_literals 稳定化");
    cfg_boolean_literals::basic_cfg_boolean_literals();
    cfg_boolean_literals::advanced_cfg_boolean_literals();
    
    // 增强的模式匹配
    println!("\n3. 增强的模式匹配");
    enhanced_pattern_matching::basic_enhanced_pattern_matching();
    enhanced_pattern_matching::advanced_enhanced_pattern_matching();
    
    // 增强的类型推断
    println!("\n4. 增强的类型推断");
    enhanced_type_inference::basic_enhanced_type_inference();
    enhanced_type_inference::advanced_enhanced_type_inference();
    
    // 新的控制流特性
    println!("\n5. 新的控制流特性");
    new_control_flow::basic_new_control_flow();
    new_control_flow::advanced_new_control_flow();
    
    // 改进的错误处理
    println!("\n6. 改进的错误处理");
    improved_error_handling::basic_improved_error_handling();
    improved_error_handling::advanced_improved_error_handling();
}

/// 运行综合应用示例
fn run_comprehensive_examples() {
    println!("\n\n🎯 第三部分：综合应用示例");
    println!("==========================");
    
    // 数据处理示例
    data_processing_example();
    
    // 异步编程示例
    async_programming_example();
    
    // 错误处理示例
    error_handling_example();
    
    // 性能优化示例
    performance_optimization_example();
    
    // 并发编程示例
    concurrent_programming_example();
}

/// 数据处理示例
/// 
/// 展示如何使用 Rust 1.89 的基础语法进行数据处理
fn data_processing_example() {
    println!("\n📊 数据处理示例");
    println!("================");
    
    // 1. 基础数据处理
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    println!("原始数据: {:?}", numbers);
    
    // 使用 let_chains 进行复杂条件处理
    let processed_numbers: Vec<i32> = numbers
        .iter()
        .filter(|&&x| {
            // 使用 let_chains 进行复杂条件判断
            if let Some(square) = Some(x * x) && 
               let Some(cube) = Some(x * x * x) && 
               square < 100 && cube < 1000 {
                true
            } else {
                false
            }
        })
        .map(|&x| x * 2)
        .collect();
    
    println!("处理后的数据: {:?}", processed_numbers);
    
    // 2. 复杂数据结构处理
    let mut data_map = HashMap::new();
    data_map.insert("user1".to_string(), UserData::new("Alice", 25, "Engineer"));
    data_map.insert("user2".to_string(), UserData::new("Bob", 30, "Designer"));
    data_map.insert("user3".to_string(), UserData::new("Charlie", 35, "Manager"));
    
    println!("\n用户数据处理:");
    for (_id, user) in data_map {
        // 使用增强的模式匹配
        match user {
            UserData { name, age, job } if age >= 25 && age <= 35 => {
                println!("  {}: {} 岁的 {}", name, age, job);
            }
            UserData { name, age, job } => {
                println!("  {}: {} 岁的 {} (年龄范围外)", name, age, job);
            }
        }
    }
}

/// 异步编程示例
/// 
/// 展示如何使用 Rust 1.89 的基础语法进行异步编程
fn async_programming_example() {
    println!("\n⚡ 异步编程示例");
    println!("================");
    
    // 模拟异步操作
    let async_operations = vec![
        AsyncOperation::new("操作1", 100),
        AsyncOperation::new("操作2", 200),
        AsyncOperation::new("操作3", 150),
    ];
    
    println!("异步操作列表:");
    for op in async_operations {
        println!("  {}: 预计耗时 {}ms", op.name, op.duration_ms);
    }
    
    // 使用 let_chains 进行异步条件判断
    let async_result = simulate_async_operation("数据获取", 300);
    if let Some(result) = async_result && 
       let Some(processed) = process_async_result(result) && 
       processed.is_success {
        println!("异步操作成功: {}", processed.message);
    } else {
        println!("异步操作失败");
    }
}

/// 错误处理示例
/// 
/// 展示如何使用 Rust 1.89 的基础语法进行错误处理
fn error_handling_example() {
    println!("\n🛡️ 错误处理示例");
    println!("================");
    
    // 1. 基础错误处理
    let results = vec![
        "42".parse::<i32>(),
        "abc".parse::<i32>(),
        "100".parse::<i32>(),
        "xyz".parse::<i32>(),
    ];
    
    println!("解析结果:");
    for (i, result) in results.iter().enumerate() {
        match result {
            Ok(value) => println!("  结果 {}: 成功解析为 {}", i + 1, value),
            Err(error) => println!("  结果 {}: 解析失败 - {}", i + 1, error),
        }
    }
    
    // 2. 复杂错误处理
    let complex_operations = vec![
        ComplexOperation::new("操作1", OperationType::Success),
        ComplexOperation::new("操作2", OperationType::Warning("警告信息".to_string())),
        ComplexOperation::new("操作3", OperationType::Error("错误信息".to_string())),
    ];
    
    println!("\n复杂操作结果:");
    for op in complex_operations {
        match op.execute() {
            Ok(result) => println!("  {}: 成功 - {}", op.name, result),
            Err(error) => println!("  {}: 失败 - {}", op.name, error),
        }
    }
}

/// 性能优化示例
/// 
/// 展示如何使用 Rust 1.89 的基础语法进行性能优化
fn performance_optimization_example() {
    println!("\n🚀 性能优化示例");
    println!("================");
    
    // 1. 零拷贝数据处理
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let optimized_result = process_data_optimized(&data);
    println!("优化处理结果: {:?}", optimized_result);
    
    // 2. 内存高效的数据结构
    let mut efficient_map = HashMap::new();
    for i in 0..1000 {
        efficient_map.insert(i, i * 2);
    }
    println!("高效数据结构大小: {} 个元素", efficient_map.len());
    
    // 3. 编译时计算
    const COMPILE_TIME_CONSTANT: i32 = calculate_at_compile_time();
    println!("编译时常量: {}", COMPILE_TIME_CONSTANT);
}

/// 并发编程示例
/// 
/// 展示如何使用 Rust 1.89 的基础语法进行并发编程
fn concurrent_programming_example() {
    println!("\n🔄 并发编程示例");
    println!("================");
    
    // 1. 线程安全的数据共享
    let shared_data = Arc::new(SharedCounter::new());
    let mut handles = vec![];
    
    for i in 0..5 {
        let data = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            for _ in 0..10 {
                data.increment();
                thread::sleep(Duration::from_millis(1));
            }
            println!("线程 {} 完成", i);
        });
        handles.push(handle);
    }
    
    // 等待所有线程完成
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("最终计数: {}", shared_data.get_count());
    
    // 2. 异步任务处理
    let async_tasks = vec![
        AsyncTask::new("任务1", 100),
        AsyncTask::new("任务2", 200),
        AsyncTask::new("任务3", 150),
    ];
    
    println!("\n异步任务处理:");
    for task in async_tasks {
        let result = task.execute();
        println!("  {}: {}", task.name, result);
    }
}

// 辅助数据结构和函数

/// 用户数据结构
#[derive(Debug, Clone)]
struct UserData {
    name: String,
    age: u32,
    job: String,
}

impl UserData {
    fn new(name: &str, age: u32, job: &str) -> Self {
        Self {
            name: name.to_string(),
            age,
            job: job.to_string(),
        }
    }
}

/// 异步操作结构
#[derive(Debug)]
struct AsyncOperation {
    name: String,
    duration_ms: u64,
}

impl AsyncOperation {
    fn new(name: &str, duration_ms: u64) -> Self {
        Self {
            name: name.to_string(),
            duration_ms,
        }
    }
}

/// 异步结果结构
#[derive(Debug)]
struct AsyncResult {
    is_success: bool,
    message: String,
}

/// 复杂操作结构
#[derive(Debug)]
struct ComplexOperation {
    name: String,
    operation_type: OperationType,
}

#[derive(Debug)]
enum OperationType {
    Success,
    Warning(String),
    Error(String),
}

impl ComplexOperation {
    fn new(name: &str, operation_type: OperationType) -> Self {
        Self {
            name: name.to_string(),
            operation_type,
        }
    }
    
    fn execute(&self) -> Result<String, String> {
        match &self.operation_type {
            OperationType::Success => Ok("操作成功".to_string()),
            OperationType::Warning(msg) => Err(format!("警告: {}", msg)),
            OperationType::Error(msg) => Err(format!("错误: {}", msg)),
        }
    }
}

/// 共享计数器结构
#[derive(Debug)]
struct SharedCounter {
    count: std::sync::Mutex<i32>,
}

impl SharedCounter {
    fn new() -> Self {
        Self {
            count: std::sync::Mutex::new(0),
        }
    }
    
    fn increment(&self) {
        let mut count = self.count.lock().unwrap();
        *count += 1;
    }
    
    fn get_count(&self) -> i32 {
        *self.count.lock().unwrap()
    }
}

/// 异步任务结构
#[derive(Debug)]
struct AsyncTask {
    name: String,
    duration_ms: u64,
}

impl AsyncTask {
    fn new(name: &str, duration_ms: u64) -> Self {
        Self {
            name: name.to_string(),
            duration_ms,
        }
    }
    
    fn execute(&self) -> String {
        // 模拟异步执行
        thread::sleep(Duration::from_millis(self.duration_ms));
        format!("完成 (耗时 {}ms)", self.duration_ms)
    }
}

/// 模拟异步操作
fn simulate_async_operation(name: &str, duration_ms: u64) -> Option<String> {
    // 模拟异步操作
    thread::sleep(Duration::from_millis(duration_ms));
    Some(format!("{} 完成", name))
}

/// 处理异步结果
fn process_async_result(result: String) -> Option<AsyncResult> {
    Some(AsyncResult {
        is_success: true,
        message: result,
    })
}

/// 优化数据处理
fn process_data_optimized(data: &[i32]) -> Vec<i32> {
    data.iter()
        .filter(|&&x| x % 2 == 0)
        .map(|&x| x * 2)
        .collect()
}

/// 编译时计算
const fn calculate_at_compile_time() -> i32 {
    42 * 2 + 16
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_user_data_creation() {
        let user = UserData::new("Alice", 25, "Engineer");
        assert_eq!(user.name, "Alice");
        assert_eq!(user.age, 25);
        assert_eq!(user.job, "Engineer");
    }

    #[test]
    fn test_async_operation_creation() {
        let op = AsyncOperation::new("测试操作", 100);
        assert_eq!(op.name, "测试操作");
        assert_eq!(op.duration_ms, 100);
    }

    #[test]
    fn test_complex_operation_execution() {
        let success_op = ComplexOperation::new("成功操作", OperationType::Success);
        assert!(success_op.execute().is_ok());
        
        let error_op = ComplexOperation::new("错误操作", OperationType::Error("测试错误".to_string()));
        assert!(error_op.execute().is_err());
    }

    #[test]
    fn test_shared_counter() {
        let counter = SharedCounter::new();
        assert_eq!(counter.get_count(), 0);
        
        counter.increment();
        assert_eq!(counter.get_count(), 1);
    }

    #[test]
    fn test_compile_time_calculation() {
        assert_eq!(calculate_at_compile_time(), 100);
    }

    #[test]
    fn test_data_processing() {
        let data = vec![1, 2, 3, 4, 5];
        let result = process_data_optimized(&data);
        assert_eq!(result, vec![4, 8]); // 2*2, 4*2
    }
}
