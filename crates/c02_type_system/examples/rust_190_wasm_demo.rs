//! Rust 1.90 WebAssembly 演示
//!
//! 本示例展示了 Rust 1.90 中的 WebAssembly 支持特性

use c02_type_system::wasm_support::*;
use std::thread;

fn main() {
    println!("=== Rust 1.90 WebAssembly 演示程序 ===\n");
    
    // 运行所有 WASM 特性演示
    demonstrate_wasm_features();
    
    // 运行交互式演示
    interactive_wasm_demo();
    
    // 运行性能测试
    wasm_performance_demo();
}

/// 交互式 WASM 演示
fn interactive_wasm_demo() {
    println!("\n=== 交互式 WebAssembly 演示 ===\n");
    
    // 1. 交互式类型操作
    println!("1. 交互式类型操作:");
    interactive_type_operations();
    
    // 2. 交互式内存管理
    println!("\n2. 交互式内存管理:");
    interactive_memory_management();
    
    // 3. 交互式函数调用
    println!("\n3. 交互式函数调用:");
    interactive_function_calls();
    
    // 4. 交互式性能优化
    println!("\n4. 交互式性能优化:");
    interactive_performance_optimization();
    
    // 5. 交互式 JavaScript 互操作
    println!("\n5. 交互式 JavaScript 互操作:");
    interactive_js_interop();
}

/// 交互式类型操作
fn interactive_type_operations() {
    // 演示类型转换
    let int_val = WasmType::I32(42);
    let float_val = WasmType::F64(3.14159);
    
    println!("  整数类型: {:?}", int_val);
    println!("  浮点类型: {:?}", float_val);
    
    // 类型转换
    let int_to_float = int_val.convert_to(WasmTypeKind::F64);
    let float_to_int = float_val.convert_to(WasmTypeKind::I32);
    
    println!("  整数转浮点: {:?}", int_to_float);
    println!("  浮点转整数: {:?}", float_to_int);
    
    // 混合类型运算
    let mixed_add = WasmOperations::add(int_val, float_val);
    println!("  混合类型加法: {:?}", mixed_add);
    
    // 类型比较
    let comparison = WasmOperations::compare(
        WasmType::I32(10),
        WasmType::F32(10.0)
    );
    println!("  类型比较 (10 vs 10.0): {}", comparison);
}

/// 交互式内存管理
#[allow(unused_variables)]
fn interactive_memory_management() {
    let mut memory_manager = WasmMemoryManager::new(2, 20); // 2页初始，最大20页
    
    println!("  初始内存页数: {}", memory_manager.get_pages());
    
    // 分配多个内存块
    let mut allocations = Vec::new();
    for i in 0..5 {
        let size = (i + 1) * 50;
        if let Some(offset) = memory_manager.allocate(size) {
            allocations.push((offset, size));
            println!("  分配 {} 字节，偏移: {}", size, offset);
        }
    }
    
    // 写入数据到分配的内存
    for (i, (offset, size)) in allocations.iter().enumerate() {
        let data = format!("Data block {}", i).into_bytes();
        if data.len() <= *size {
            let _ = memory_manager.write(*offset, &data);
            println!("  写入数据到偏移 {}: {:?}", offset, data);
        }
    }
    
    // 读取数据
    for (i, (offset, size)) in allocations.iter().enumerate() {
        if let Ok(data) = memory_manager.read(*offset, *size) {
            println!("  从偏移 {} 读取: {:?}", offset, data);
        }
    }
    
    // 内存扩展
    let old_pages = memory_manager.grow_memory(3).unwrap();
    println!("  扩展内存: {} -> {} 页", old_pages, memory_manager.get_pages());
    
    // 显示统计信息
    let stats = memory_manager.get_usage_stats();
    println!("  内存使用统计: {:?}", stats);
}

/// 交互式函数调用
#[allow(unused_variables)]
fn interactive_function_calls() {
    let mut exporter = WasmFunctionExporter::new();
    
    // 导出数学函数
    let _ = exporter.export_function("square".to_string(), |args| {
        if args.len() != 1 {
            return Err("Expected 1 argument".to_string());
        }
        let val = args[0].to_f64();
        Ok(WasmType::F64(val * val))
    });
    
    let _ = exporter.export_function("factorial".to_string(), |args| {
        if args.len() != 1 {
            return Err("Expected 1 argument".to_string());
        }
        let n = args[0].to_i32();
        if n < 0 {
            return Err("Factorial not defined for negative numbers".to_string());
        }
        let result = (1..=n).product::<i32>();
        Ok(WasmType::I32(result))
    });
    
    let _ = exporter.export_function("fibonacci".to_string(), |args| {
        if args.len() != 1 {
            return Err("Expected 1 argument".to_string());
        }
        let n = args[0].to_i32();
        if n < 0 {
            return Err("Fibonacci not defined for negative numbers".to_string());
        }
        
        let result = if n <= 1 {
            n
        } else {
            let mut a = 0;
            let mut b = 1;
            for _ in 2..=n {
                let temp = a + b;
                a = b;
                b = temp;
            }
            b
        };
        
        Ok(WasmType::I32(result))
    });
    
    // 调用导出的函数
    let functions = vec![
        ("square", vec![WasmType::F64(5.0)]),
        ("factorial", vec![WasmType::I32(5)]),
        ("fibonacci", vec![WasmType::I32(10)]),
    ];
    
    for (func_name, args) in functions {
        match exporter.call_function(func_name, args.clone()) {
            Ok(result) => println!("  {}({:?}) = {:?}", func_name, args, result),
            Err(e) => println!("  {}({:?}) 错误: {}", func_name, args, e),
        }
    }
    
    // 显示所有导出的函数
    let exported_functions = exporter.get_exported_functions();
    println!("  导出的函数: {:?}", exported_functions);
}

/// 交互式性能优化
#[allow(unused_variables)]
fn interactive_performance_optimization() {
    let optimizer = WasmPerformanceOptimizer::new();
    
    // 优化函数调用
    let functions_to_test = vec![
        ("add", vec![WasmType::I32(10), WasmType::I32(20)]),
        ("multiply", vec![WasmType::F32(2.5), WasmType::F32(4.0)]),
        ("mixed", vec![WasmType::I32(5), WasmType::F64(3.14)]),
    ];
    
    for (name, args) in functions_to_test {
        let result = optimizer.optimize_function_call(|args| {
            match args.len() {
                2 => Ok(WasmOperations::add(args[0].clone(), args[1].clone())),
                _ => Err("Invalid arguments".to_string()),
            }
        }, args);
        
        println!("  优化函数调用 {}: {:?}", name, result);
    }
    
    // 优化内存访问
    let memory_accesses = vec![
        (15, 7),   // 不对齐
        (16, 8),   // 对齐
        (23, 12),  // 不对齐
        (32, 16),  // 对齐
    ];
    
    for (offset, size) in memory_accesses {
        let (aligned_offset, aligned_size) = optimizer.optimize_memory_access(offset, size);
        println!("  内存访问优化: ({}, {}) -> ({}, {})", 
                offset, size, aligned_offset, aligned_size);
    }
    
    // 显示优化统计
    let stats = optimizer.get_stats();
    println!("  优化统计: {:?}", stats);
}

/// 交互式 JavaScript 互操作
#[allow(unused_variables)]
fn interactive_js_interop() {
    let js_interop = JsInterop::new();
    
    // 注册回调函数
    let _ = js_interop.register_callback("uppercase".to_string(), |data| {
        data.to_uppercase()
    });
    
    let _ = js_interop.register_callback("reverse".to_string(), |data| {
        data.chars().rev().collect()
    });
    
    let _ = js_interop.register_callback("count_words".to_string(), |data| {
        let count = data.split_whitespace().count();
        format!("Word count: {}", count)
    });
    
    let _ = js_interop.register_callback("json_format".to_string(), |data| {
        format!("{{\"message\": \"{}\", \"length\": {}}}", data, data.len())
    });
    
    // 测试回调函数
    let test_data = "Hello World from Rust WASM";
    let callbacks = vec!["uppercase", "reverse", "count_words", "json_format"];
    
    for callback_name in callbacks {
        let result = js_interop.handle_js_call(callback_name, test_data.to_string());
        println!("  {}('{}') = {}", callback_name, test_data, result);
    }
    
    // 模拟调用 JavaScript 函数
    let js_functions = vec![
        ("console.log", "Hello from WASM"),
        ("alert", "WASM is working!"),
        ("document.getElementById", "myElement"),
    ];
    
    for (func_name, args) in js_functions {
        let result = js_interop.call_js_function(func_name, args);
        println!("  JS 函数调用: {}", result);
    }
    
    // 显示注册的回调
    let registered_callbacks = js_interop.get_registered_callbacks();
    println!("  注册的回调函数: {:?}", registered_callbacks);
}

/// WASM 性能演示
#[allow(unused_variables)]
#[allow(unused_mut)]
fn wasm_performance_demo() {
    println!("\n=== WebAssembly 性能演示 ===\n");
    
    // 1. 类型操作性能测试
    println!("1. 类型操作性能测试:");
    let start = std::time::Instant::now();
    
    for i in 0..10000 {
        let a = WasmType::I32(i);
        let b = WasmType::I32(i * 2);
        let _ = WasmOperations::add(a, b);
    }
    
    let duration = start.elapsed();
    println!("  10000次类型操作耗时: {:?}", duration);
    println!("  平均每次操作: {:?}", duration / 10000);
    
    // 2. 内存管理性能测试
    println!("\n2. 内存管理性能测试:");
    let mut memory_manager = WasmMemoryManager::new(10, 100);
    
    let start = std::time::Instant::now();
    let mut allocations = Vec::new();
    
    for i in 0..1000 {
        if let Some(offset) = memory_manager.allocate(100) {
            allocations.push(offset);
        }
    }
    
    let duration = start.elapsed();
    println!("  1000次内存分配耗时: {:?}", duration);
    println!("  平均每次分配: {:?}", duration / 1000);
    println!("  成功分配数量: {}", allocations.len());
    
    // 3. 函数调用性能测试
    println!("\n3. 函数调用性能测试:");
    let mut exporter = WasmFunctionExporter::new();
    let _ = exporter.export_function("test".to_string(), |args| {
        Ok(WasmType::I32(args.len() as i32))
    });
    
    let start = std::time::Instant::now();
    
    for i in 0..5000 {
        let args = vec![WasmType::I32(i), WasmType::I32(i * 2)];
        let _ = exporter.call_function("test", args);
    }
    
    let duration = start.elapsed();
    println!("  5000次函数调用耗时: {:?}", duration);
    println!("  平均每次调用: {:?}", duration / 5000);
    
    // 4. 性能优化效果测试
    println!("\n4. 性能优化效果测试:");
    let optimizer = WasmPerformanceOptimizer::new();
    
    // 未优化版本
    let start = std::time::Instant::now();
    for i in 0..1000 {
        let args = vec![WasmType::F32(i as f32), WasmType::F32((i * 2) as f32)];
        let _ = WasmOperations::add(args[0].clone(), args[1].clone());
    }
    let unoptimized_duration = start.elapsed();
    
    // 优化版本
    let start = std::time::Instant::now();
    for i in 0..1000 {
        let args = vec![WasmType::F32(i as f32), WasmType::F32((i * 2) as f32)];
        let _ = optimizer.optimize_function_call(|args| {
            Ok(WasmOperations::add(args[0].clone(), args[1].clone()))
        }, args);
    }
    let optimized_duration = start.elapsed();
    
    println!("  未优化版本耗时: {:?}", unoptimized_duration);
    println!("  优化版本耗时: {:?}", optimized_duration);
    println!("  性能提升: {:.2}x", 
            unoptimized_duration.as_nanos() as f64 / optimized_duration.as_nanos() as f64);
    
    let stats = optimizer.get_stats();
    println!("  优化统计: {:?}", stats);
}

/// 并发 WASM 演示
#[allow(unused_variables)]
#[allow(dead_code)]
fn concurrent_wasm_demo() {
    println!("\n=== 并发 WebAssembly 演示 ===\n");
    
    let memory_manager = std::sync::Arc::new(std::sync::Mutex::new(
        WasmMemoryManager::new(5, 50)
    ));
    
    let mut handles = Vec::new();
    
    // 创建多个线程同时进行内存操作
    for thread_id in 0..5 {
        let manager = memory_manager.clone();
        let handle = thread::spawn(move || {
            let mut local_allocations = Vec::new();
            
            for i in 0..100 {
                let mut manager = manager.lock().unwrap();
                if let Some(offset) = manager.allocate(50) {
                    local_allocations.push(offset);
                    
                    let data = format!("Thread {} data {}", thread_id, i).into_bytes();
                    let _ = manager.write(offset, &data);
                }
            }
            
            (thread_id, local_allocations.len())
        });
        
        handles.push(handle);
    }
    
    // 等待所有线程完成
    let mut total_allocations = 0;
    for handle in handles {
        if let Ok((thread_id, count)) = handle.join() {
            println!("  线程 {} 完成，分配了 {} 个内存块", thread_id, count);
            total_allocations += count;
        }
    }
    
    println!("  总分配数量: {}", total_allocations);
    
    let manager = memory_manager.lock().unwrap();
    let stats = manager.get_usage_stats();
    println!("  最终内存统计: {:?}", stats);
}
