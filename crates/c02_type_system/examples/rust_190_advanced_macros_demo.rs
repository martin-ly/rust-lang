//! Rust 1.90 高级宏系统演示
//! 
//! 本示例展示了 Rust 1.90 中宏系统的高级用法，包括：
//! - 声明宏 (Declarative Macros)
//! - 过程宏 (Procedural Macros) 
//! - 属性宏 (Attribute Macros)
//! - 派生宏 (Derive Macros)
//! - 函数式宏 (Function-like Macros)
//! - 宏组合和嵌套
//! - 宏元编程
//! - 编译时计算宏

#![recursion_limit = "2048"]

use c02_type_system::advanced_macros::*;
use std::collections::HashMap;

// 导入所有宏
use c02_type_system::{
    create_vec, debug_print, factorial, measure_time, log_info, log_error, 
    assert_positive, cached, retry, profile,
    complex_operation, nested_macro, conditional_macro, generate_functions,
    generate_structs, generate_enum, compile_time_string, compile_time_math,
    type_info, macro_debug, macro_benchmark
};

fn main() {
    println!("🔧 Rust 1.90 高级宏系统演示");
    println!("=============================");
    
    // 运行基础演示
    demonstrate_advanced_macros();
    
    // 运行详细演示
    demonstrate_macro_details();
    
    // 额外的宏使用示例
    println!("\n🔧 额外宏使用示例");
    println!("==================");
    
    // 1. 使用 create_vec! 宏
    println!("\n--- 向量创建宏示例 ---");
    let numbers = create_vec![1, 2, 3, 4, 5];
    let empty: Vec<i32> = create_vec![];
    println!("  📊 数字向量: {:?}", numbers);
    println!("  📊 空向量: {:?}", empty);
    
    // 2. 使用 factorial! 宏
    println!("\n--- 阶乘宏示例 ---");
    for i in 1..=5 {
        println!("  🧮 {}! = {}", i, factorial!(i));
    }
    
    // 3. 使用 debug_print! 宏
    println!("\n--- 调试打印宏示例 ---");
    debug_print!("这是调试信息，只在 debug 模式下显示");
    debug_print!("当前时间: {:?}", std::time::SystemTime::now());
    
    // 4. 使用 measure_time! 宏
    println!("\n--- 时间测量宏示例 ---");
    let result = measure_time!("斐波那契计算", {
        fibonacci(10)
    });
    println!("  ⏱️  斐波那契(10) = {}", result);
    
    // 5. 使用 log_info! 和 log_error! 宏
    println!("\n--- 日志宏示例 ---");
    log_info!("应用程序启动完成");
    log_info!("用户登录: {}", "alice");
    log_error!("数据库连接失败");
    
    // 6. 使用 assert_positive! 宏
    println!("\n--- 断言宏示例 ---");
    let positive_value = 42;
    assert_positive!(positive_value);
    println!("  ✅ 断言通过: {} 是正数", positive_value);
    
    // 7. 使用 cached! 宏
    println!("\n--- 缓存宏示例 ---");
    let expensive_calc1 = cached!("expensive_calc", expensive_calculation());
    let expensive_calc2 = cached!("expensive_calc", expensive_calculation());
    println!("  💾 第一次计算: {}", expensive_calc1);
    println!("  💾 第二次计算 (缓存): {}", expensive_calc2);
    
    // 8. 使用 retry! 宏
    println!("\n--- 重试宏示例 ---");
    let retry_result = retry!(3, {
        simulate_network_call()
    });
    println!("  🔄 重试结果: {:?}", retry_result);
    
    // 9. 使用 profile! 宏
    println!("\n--- 性能监控宏示例 ---");
    let profiled_result = profile!("数据处理", {
        process_large_dataset()
    });
    println!("  📊 处理结果: {}", profiled_result);
    
    // 10. 使用 complex_operation! 宏
    println!("\n--- 复杂操作宏示例 ---");
    let complex_result = complex_operation!("复杂数据处理", {
        complex_data_processing()
    });
    println!("  🔗 复杂操作结果: {}", complex_result);
    
    // 11. 使用 nested_macro! 宏
    println!("\n--- 嵌套宏示例 ---");
    let nested_result = nested_macro!(15);
    println!("  🪆 嵌套宏结果: {}", nested_result);
    
    // 12. 使用 generate_functions! 宏
    println!("\n--- 生成函数宏示例 ---");
    generate_functions!(double: i32, triple: i32);
    println!("  ⚙️  double(7): {}", double(7));
    println!("  ⚙️  triple(5): {}", triple(5));
    
    // 13. 使用 generate_structs! 宏
    println!("\n--- 生成结构体宏示例 ---");
    generate_structs!(Point, Vector);
    let point = Point::new(10);
    let vector = Vector::new(20);
    println!("  🏗️  点: {:?}", point);
    println!("  🏗️  向量: {:?}", vector);
    
    // 14. 使用 generate_enum! 宏
    println!("\n--- 生成枚举宏示例 ---");
    generate_enum!(Status, Active, Inactive, Pending);
    println!("  📋 状态变体: {:?}", Status::all_variants());
    
    // 15. 使用 compile_time_string! 宏
    println!("\n--- 编译时字符串宏示例 ---");
    let compile_str = compile_time_string!("Rust");
    println!("  📝 编译时字符串: {}", compile_str);
    
    // 16. 使用 compile_time_math! 宏
    println!("\n--- 编译时数学宏示例 ---");
    let add = compile_time_math!(100 + 200);
    let mul = compile_time_math!(12 * 8);
    println!("  🧮 100 + 200 = {}", add);
    println!("  🧮 12 * 8 = {}", mul);
    
    // 17. 使用 type_info! 宏
    println!("\n--- 类型信息宏示例 ---");
    let i32_info = type_info!(i32);
    let f64_info = type_info!(f64);
    let vec_info = type_info!(Vec<i32>);
    println!("  📊 i32: {}", i32_info);
    println!("  📊 f64: {}", f64_info);
    println!("  📊 Vec<i32>: {}", vec_info);
    
    // 18. 使用 macro_debug! 宏
    println!("\n--- 宏调试宏示例 ---");
    macro_debug!("这是宏调试信息");
    macro_debug!("当前值: {}", 42);
    
    // 19. 使用 macro_benchmark! 宏
    println!("\n--- 宏性能测试示例 ---");
    macro_benchmark!("简单循环", 10000, {
        (1..100).sum::<i32>()
    });
    
    macro_benchmark!("复杂计算", 1000, {
        (1..1000).map(|x| x * x * x).sum::<i64>()
    });
    
    // 20. 使用 conditional_macro! 宏
    println!("\n--- 条件宏示例 ---");
    let condition = true;
    let _result = conditional_macro!(condition, log_info, log_error, "条件测试消息");
    
    println!("\n✅ 所有高级宏系统演示完成！");
}

/// 辅助函数：计算斐波那契数
fn fibonacci(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

/// 辅助函数：模拟昂贵计算
fn expensive_calculation() -> i32 {
    // 模拟一些计算
    std::thread::sleep(std::time::Duration::from_millis(10));
    42 * 42
}

/// 辅助函数：模拟网络调用
fn simulate_network_call() -> Result<i32, String> {
    // 模拟网络调用，有时成功有时失败
    if std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() % 2 == 0
    {
        Ok(200)
    } else {
        Err("网络超时".to_string())
    }
}

/// 辅助函数：处理大数据集
fn process_large_dataset() -> i32 {
    // 模拟处理大数据集
    (1..1000).map(|x| x * x).sum::<i32>() / 100
}

/// 辅助函数：复杂数据处理
fn complex_data_processing() -> i32 {
    // 模拟复杂数据处理
    let data: Vec<i32> = (1..1000).collect();
    data.iter()
        .filter(|&x| x % 2 == 0)
        .map(|&x| x * x)
        .sum::<i32>()
        / 100
}