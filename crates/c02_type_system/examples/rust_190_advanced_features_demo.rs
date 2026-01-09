//! Rust 1.90 高级特性演示 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features_demo.rs`
//!
//! 本示例展示了 Rust 1.90 中的高级语言特性，包括：
//! - 高级生命周期管理
//! - 复杂类型约束
//! - 高级宏系统
//! - 内存安全高级特性
//! - 并发编程高级模式
//! - 高级错误处理

use c02_type_system::rust_190_advanced_features::*;
use std::collections::HashMap;
use std::thread;
use std::time::Duration;

fn main() {
    println!("=== Rust 1.90 高级特性演示程序 ===\n");
    
    // 运行所有高级特性演示
    demonstrate_advanced_features();
    
    // 额外的交互式演示
    interactive_demonstrations();
}

/// 交互式演示
fn interactive_demonstrations() {
    println!("\n=== 交互式演示 ===\n");
    
    // 1. 高级生命周期管理交互演示
    println!("1. 高级生命周期管理交互演示:");
    interactive_lifetime_demo();
    
    // 2. 复杂类型约束交互演示
    println!("\n2. 复杂类型约束交互演示:");
    interactive_type_constraints_demo();
    
    // 3. 高级宏系统交互演示
    println!("\n3. 高级宏系统交互演示:");
    interactive_macro_demo();
    
    // 4. 内存安全高级特性交互演示
    println!("\n4. 内存安全高级特性交互演示:");
    interactive_memory_safety_demo();
    
    // 5. 并发编程高级模式交互演示
    println!("\n5. 并发编程高级模式交互演示:");
    interactive_concurrency_demo();
    
    // 6. 高级错误处理交互演示
    println!("\n6. 高级错误处理交互演示:");
    interactive_error_handling_demo();
}

/// 高级生命周期管理交互演示
fn interactive_lifetime_demo() {
    let data1 = String::from("第一个数据");
    let data2 = String::from("第二个数据");
    let metadata = "组合元数据";
    
    // 创建生命周期组合
    let composition = AdvancedLifetimeComposition::new(&data1, &data2, metadata);
    
    // 演示生命周期转换
    let transformed = composition.transform_lifetimes(|p, s, m| {
        format!("转换结果: {} + {} + {}", p, s, m)
    });
    
    println!("  原始数据1: {}", data1);
    println!("  原始数据2: {}", data2);
    println!("  元数据: {}", metadata);
    println!("  转换结果: {}", transformed);
    println!("  生命周期验证: {}", composition.validate_lifetimes());
    
    // 演示生命周期约束
    let (combined_p, combined_s) = composition.get_combined_data();
    println!("  组合数据: ({}, {})", combined_p, combined_s);
}

/// 复杂类型约束交互演示
fn interactive_type_constraints_demo() {
    // 创建不同类型的处理器
    let int_processor = ConstrainedProcessor::new(vec![1, 2, 3, 4, 5]);
    let string_processor = ConstrainedProcessor::new(vec!["a".to_string(), "b".to_string(), "c".to_string()]);
    
    // 演示整数处理
    let int_result = int_processor.process_with_constraints(|data| {
        let sum: i32 = data.iter().sum();
        format!("整数总和: {}", sum)
    });
    println!("  整数处理结果: {:?}", int_result);
    
    // 演示字符串处理
    let string_result = string_processor.process_with_constraints(|data| {
        format!("字符串连接: {}", data.join(""))
    });
    println!("  字符串处理结果: {:?}", string_result);
    
    // 演示类型转换
    let conversion_result = int_processor.convert_with_bounds(42i32);
    println!("  类型转换结果: {:?}", conversion_result);
}

/// 高级宏系统交互演示
fn interactive_macro_demo() {
    // 演示基础类型构建
    let mut metadata = HashMap::new();
    metadata.insert("version".to_string(), "1.0".to_string());
    metadata.insert("author".to_string(), "Rust Team".to_string());
    
    let advanced_struct = AdvancedStruct::new(
        1001,
        "高级结构体".to_string(),
        metadata,
    );
    println!("  高级结构体: {:?}", advanced_struct);
    
    // 演示带默认值的类型构建
    let configurable = ConfigurableStruct::new();
    println!("  可配置结构体(默认): {:?}", configurable);
    
    let configurable_custom = ConfigurableStruct::with_values(
        Duration::from_secs(60),
        5,
        false,
    );
    println!("  可配置结构体(自定义): {:?}", configurable_custom);
    
    // 演示泛型类型构建
    let generic_int = GenericStruct::new(42, 10);
    let generic_string = GenericStruct::new("Hello".to_string(), 5);
    println!("  泛型结构体(整数): {:?}", generic_int);
    println!("  泛型结构体(字符串): {:?}", generic_string);
}

/// 内存安全高级特性交互演示
fn interactive_memory_safety_demo() {
    // 创建内存安全类型
    let memory_safe = AdvancedMemorySafe::new("安全数据".to_string());
    
    // 演示多线程安全访问
    let memory_safe_clone = memory_safe.clone();
    let handle = thread::spawn(move || {
        for i in 0..5 {
            let data = memory_safe_clone.get_data();
            println!("    线程访问 {}: {:?}", i, data);
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    // 主线程也进行访问
    for i in 0..3 {
        let data = memory_safe.get_data();
        println!("  主线程访问 {}: {:?}", i, data);
        thread::sleep(Duration::from_millis(150));
    }
    
    // 等待子线程完成
    handle.join().unwrap();
    
    // 演示元数据操作
    let _ = memory_safe.update_metadata("key1".to_string(), "value1".to_string());
    let _ = memory_safe.update_metadata("key2".to_string(), "value2".to_string());
    
    let metadata1 = memory_safe.get_metadata("key1");
    let metadata2 = memory_safe.get_metadata("key2");
    let metadata3 = memory_safe.get_metadata("key3");
    
    println!("  元数据1: {:?}", metadata1);
    println!("  元数据2: {:?}", metadata2);
    println!("  元数据3: {:?}", metadata3);
    println!("  总访问次数: {}", memory_safe.get_access_count());
}

/// 并发编程高级模式交互演示
fn interactive_concurrency_demo() {
    println!("  创建并发处理器...");
    let processor = AdvancedConcurrentProcessor::new(3);
    
    // 添加任务
    println!("  添加任务...");
    for i in 0..10 {
        processor.add_task(format!("任务-{}", i));
    }
    
    // 等待处理
    println!("  等待处理完成...");
    thread::sleep(Duration::from_millis(1000));
    
    // 获取中间结果
    let intermediate_results = processor.get_results();
    println!("  中间结果数量: {}", intermediate_results.len());
    
    // 添加更多任务
    println!("  添加更多任务...");
    for i in 10..15 {
        processor.add_task(format!("任务-{}", i));
    }
    
    // 等待处理
    thread::sleep(Duration::from_millis(500));
    
    // 停止处理器并获取最终结果
    println!("  停止处理器...");
    let final_results = processor.stop();
    println!("  最终结果数量: {}", final_results.len());
    
    // 显示部分结果
    for (i, result) in final_results.iter().enumerate() {
        if i < 5 {
            println!("    结果 {}: {:?}", i, result);
        }
    }
    if final_results.len() > 5 {
        println!("    ... 还有 {} 个结果", final_results.len() - 5);
    }
}

/// 高级错误处理交互演示
fn interactive_error_handling_demo() {
    let error_handler = ErrorHandler::new();
    
    // 模拟不同类型的错误
    println!("  记录各种类型的错误...");
    
    error_handler.log_error(AdvancedError::Processing(ProcessingError {
        message: "处理任务时发生错误".to_string(),
    }));
    
    error_handler.log_error(AdvancedError::Concurrent("并发访问冲突".to_string()));
    
    error_handler.log_error(AdvancedError::Memory("内存分配失败".to_string()));
    
    error_handler.log_error(AdvancedError::Type("类型转换错误".to_string()));
    
    error_handler.log_error(AdvancedError::Lifetime("生命周期约束违反".to_string()));
    
    // 获取错误日志
    let errors = error_handler.get_errors();
    println!("  错误总数: {}", errors.len());
    
    // 显示错误详情
    for (i, error) in errors.iter().enumerate() {
        println!("    错误 {}: {}", i + 1, error);
    }
    
    // 清空错误日志
    println!("  清空错误日志...");
    error_handler.clear_errors();
    let cleared_errors = error_handler.get_errors();
    println!("  清空后错误数量: {}", cleared_errors.len());
}
