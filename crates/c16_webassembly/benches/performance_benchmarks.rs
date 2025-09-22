//! # WebAssembly 2.0 + Rust 1.90 性能基准测试
//!
//! 本模块提供了全面的性能基准测试，用于评估 WebAssembly 2.0 和 Rust 1.90 新特性的性能表现。
//! This module provides comprehensive performance benchmarks to evaluate the performance of WebAssembly 2.0 and Rust 1.90 new features.

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use c16_webassembly::*;
use std::time::Duration;

/// 内存操作性能基准测试
/// Memory operation performance benchmarks
fn bench_memory_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_operations");
    group.measurement_time(Duration::from_secs(10));

    // 测试不同大小的内存操作
    // Test memory operations of different sizes
    for size in [1024, 4096, 16384, 65536].iter() {
        group.bench_with_input(BenchmarkId::new("bulk_memory_manager", size), size, |b, &size| {
            b.iter(|| {
                let mut manager = BulkMemoryManager::new(size);
                for i in 0..(size / 8) {
                    let offset = i * 8;
                    let data = (i as u64).to_le_bytes();
                    manager.write_memory(offset, &data).unwrap();
                }
                black_box(manager)
            })
        });

        group.bench_with_input(BenchmarkId::new("standard_memory", size), size, |b, &size| {
            b.iter(|| {
                let mut memory = Memory::new(0, size / 65536, Some(size / 65536));
                for i in 0..(size / 8) {
                    let offset = i * 8;
                    let data = (i as u64).to_le_bytes();
                    memory.write(offset, &data).unwrap();
                }
                black_box(memory)
            })
        });
    }

    group.finish();
}

/// SIMD操作性能基准测试
/// SIMD operation performance benchmarks
fn bench_simd_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("simd_operations");
    group.measurement_time(Duration::from_secs(10));

    // 测试不同数量的SIMD操作
    // Test different numbers of SIMD operations
    for count in [100, 1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("simd_add", count), count, |b, &count| {
            b.iter(|| {
                let mut processor = SimdProcessor::new();
                for i in 0..count {
                    let operands = [
                        Value::V128([i as u8; 16]),
                        Value::V128([(i + 1) as u8; 16])
                    ];
                    processor.execute_simd(SimdInstruction::V128Add, operands).unwrap();
                }
                black_box(processor)
            })
        });

        group.bench_with_input(BenchmarkId::new("simd_mul", count), count, |b, &count| {
            b.iter(|| {
                let mut processor = SimdProcessor::new();
                for i in 0..count {
                    let operands = [
                        Value::V128([i as u8; 16]),
                        Value::V128([(i + 1) as u8; 16])
                    ];
                    processor.execute_simd(SimdInstruction::V128Mul, operands).unwrap();
                }
                black_box(processor)
            })
        });

        group.bench_with_input(BenchmarkId::new("simd_eq", count), count, |b, &count| {
            b.iter(|| {
                let mut processor = SimdProcessor::new();
                for i in 0..count {
                    let operands = [
                        Value::V128([i as u8; 16]),
                        Value::V128([i as u8; 16])
                    ];
                    processor.execute_simd(SimdInstruction::V128Eq, operands).unwrap();
                }
                black_box(processor)
            })
        });
    }

    group.finish();
}

/// 尾调用优化性能基准测试
/// Tail call optimization performance benchmarks
fn bench_tail_call_optimization(c: &mut Criterion) {
    let mut group = c.benchmark_group("tail_call_optimization");
    group.measurement_time(Duration::from_secs(10));

    // 测试不同深度的尾调用
    // Test tail calls of different depths
    for depth in [10, 100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("tail_call", depth), depth, |b, &depth| {
            b.iter(|| {
                let mut optimizer = TailCallOptimizer::new();
                for i in 0..depth {
                    let args = vec![Value::I32(i), Value::I64(i as i64)];
                    optimizer.execute_tail_call(i % 10, args).unwrap();
                }
                black_box(optimizer)
            })
        });

        group.bench_with_input(BenchmarkId::new("regular_call", depth), depth, |b, &depth| {
            b.iter(|| {
                let mut call_stack = Vec::new();
                for i in 0..depth {
                    call_stack.push(Value::I32(i));
                }
                black_box(call_stack)
            })
        });
    }

    group.finish();
}

/// 宿主绑定性能基准测试
/// Host binding performance benchmarks
fn bench_host_bindings(c: &mut Criterion) {
    let mut group = c.benchmark_group("host_bindings");
    group.measurement_time(Duration::from_secs(10));

    // 测试不同数量的宿主绑定
    // Test different numbers of host bindings
    for count in [10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("register_bindings", count), count, |b, &count| {
            b.iter(|| {
                let mut manager = HostBindingManager::new();
                for i in 0..count {
                    manager.register_binding(
                        format!("function_{}", i),
                        HostBindingType::JavaScriptFunction,
                        "test".to_string(),
                    );
                }
                black_box(manager)
            })
        });

        group.bench_with_input(BenchmarkId::new("call_bindings", count), count, |b, &count| {
            b.iter(|| {
                let mut manager = HostBindingManager::new();
                for i in 0..count {
                    manager.register_binding(
                        format!("function_{}", i),
                        HostBindingType::JavaScriptFunction,
                        "test".to_string(),
                    );
                }
                for i in 0..count {
                    let args = vec![Value::I32(i)];
                    manager.call_javascript_function(&format!("function_{}", i), args).unwrap();
                }
                black_box(manager)
            })
        });
    }

    group.finish();
}

/// 接口类型性能基准测试
/// Interface type performance benchmarks
fn bench_interface_types(c: &mut Criterion) {
    let mut group = c.benchmark_group("interface_types");
    group.measurement_time(Duration::from_secs(10));

    // 测试不同数量的接口类型
    // Test different numbers of interface types
    for count in [10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("register_types", count), count, |b, &count| {
            b.iter(|| {
                let mut handler = InterfaceTypeHandler::new();
                for i in 0..count {
                    handler.register_type(
                        format!("type_{}", i),
                        InterfaceType::Basic(ValueType::I32),
                    );
                }
                black_box(handler)
            })
        });

        group.bench_with_input(BenchmarkId::new("validate_types", count), count, |b, &count| {
            b.iter(|| {
                let mut handler = InterfaceTypeHandler::new();
                for i in 0..count {
                    handler.register_type(
                        format!("type_{}", i),
                        InterfaceType::Basic(ValueType::I32),
                    );
                }
                for i in 0..count {
                    let value = Value::I32(i);
                    handler.validate_interface_type(&format!("type_{}", i), &value).unwrap();
                }
                black_box(handler)
            })
        });
    }

    group.finish();
}

/// Rust 1.90 新特性性能基准测试
/// Rust 1.90 new features performance benchmarks
fn bench_rust_190_features(c: &mut Criterion) {
    let mut group = c.benchmark_group("rust_190_features");
    group.measurement_time(Duration::from_secs(10));

    // 测试常量泛型推断性能
    // Test const generic inference performance
    group.bench_function("const_generic_inference", |b| {
        b.iter(|| {
            let array_8: [Value; 8] = create_wasm_array();
            let array_64: [Value; 64] = create_wasm_array();
            let array_512: [Value; 512] = create_wasm_array();
            black_box((array_8, array_64, array_512))
        })
    });

    // 测试128位整数操作性能
    // Test 128-bit integer operation performance
    group.bench_function("i128_operations", |b| {
        b.iter(|| {
            let mut sum = 0i128;
            for i in 0..1000 {
                let val = Value::I128(i);
                sum += val.as_i128().unwrap();
            }
            black_box(sum)
        })
    });

    group.bench_function("u128_operations", |b| {
        b.iter(|| {
            let mut sum = 0u128;
            for i in 0..1000 {
                let val = Value::U128(i);
                sum += val.as_u128().unwrap();
            }
            black_box(sum)
        })
    });

    // 测试生命周期语法检查性能
    // Test lifetime syntax check performance
    group.bench_function("lifetime_syntax_check", |b| {
        b.iter(|| {
            let data = "WebAssembly 2.0 with Rust 1.90";
            let result = lifetime_example(data);
            black_box(result)
        })
    });

    group.finish();
}

/// 综合性能基准测试
/// Comprehensive performance benchmarks
fn bench_comprehensive(c: &mut Criterion) {
    let mut group = c.benchmark_group("comprehensive");
    group.measurement_time(Duration::from_secs(30));

    // 测试完整的WebAssembly 2.0 + Rust 1.90集成
    // Test complete WebAssembly 2.0 + Rust 1.90 integration
    group.bench_function("full_integration", |b| {
        b.iter(|| {
            let mut integration = Rust190Wasm2Integration::new();
            integration.initialize().unwrap();
            let result = integration.run_comprehensive_test().unwrap();
            black_box(result)
        })
    });

    // 测试内存密集型操作
    // Test memory-intensive operations
    group.bench_function("memory_intensive", |b| {
        b.iter(|| {
            let mut memory_manager = BulkMemoryManager::new(65536);
            let mut simd_processor = SimdProcessor::new();
            
            // 执行大量内存操作
            // Execute large number of memory operations
            for i in 0..10000 {
                let offset = (i % 1000) * 8;
                let data = (i as u64).to_le_bytes();
                memory_manager.write_memory(offset, &data).unwrap();
            }
            
            // 执行大量SIMD操作
            // Execute large number of SIMD operations
            for i in 0..10000 {
                let operands = [
                    Value::V128([i as u8; 16]),
                    Value::V128([(i + 1) as u8; 16])
                ];
                simd_processor.execute_simd(SimdInstruction::V128Add, operands).unwrap();
            }
            
            black_box((memory_manager, simd_processor))
        })
    });

    // 测试计算密集型操作
    // Test compute-intensive operations
    group.bench_function("compute_intensive", |b| {
        b.iter(|| {
            let mut optimizer = TailCallOptimizer::new();
            let mut type_handler = InterfaceTypeHandler::new();
            
            // 执行大量尾调用
            // Execute large number of tail calls
            for i in 0..5000 {
                let args = vec![Value::I32(i), Value::I64(i as i64)];
                optimizer.execute_tail_call(i % 10, args).unwrap();
            }
            
            // 执行大量类型验证
            // Execute large number of type validations
            for i in 0..5000 {
                type_handler.register_type(
                    format!("type_{}", i),
                    InterfaceType::Basic(ValueType::I32),
                );
                let value = Value::I32(i);
                type_handler.validate_interface_type(&format!("type_{}", i), &value).unwrap();
            }
            
            black_box((optimizer, type_handler))
        })
    });

    group.finish();
}

/// 内存使用基准测试
/// Memory usage benchmarks
fn bench_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");
    group.measurement_time(Duration::from_secs(10));

    // 测试不同大小的内存分配
    // Test memory allocation of different sizes
    for size in [1024, 4096, 16384, 65536, 262144].iter() {
        group.bench_with_input(BenchmarkId::new("memory_allocation", size), size, |b, &size| {
            b.iter(|| {
                let memory = Memory::new(0, size / 65536, Some(size / 65536));
                black_box(memory)
            })
        });

        group.bench_with_input(BenchmarkId::new("bulk_memory_allocation", size), size, |b, &size| {
            b.iter(|| {
                let manager = BulkMemoryManager::new(size);
                black_box(manager)
            })
        });
    }

    group.finish();
}

/// 并发性能基准测试
/// Concurrency performance benchmarks
fn bench_concurrency(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrency");
    group.measurement_time(Duration::from_secs(10));

    use std::sync::Arc;
    use std::thread;

    // 测试多线程内存操作
    // Test multi-threaded memory operations
    for thread_count in [2, 4, 8].iter() {
        group.bench_with_input(BenchmarkId::new("multi_thread_memory", thread_count), thread_count, |b, &thread_count| {
            b.iter(|| {
                let memory_manager = Arc::new(std::sync::Mutex::new(BulkMemoryManager::new(8192)));
                let mut handles = vec![];

                for i in 0..thread_count {
                    let manager = Arc::clone(&memory_manager);
                    let handle = thread::spawn(move || {
                        let mut manager = manager.lock().unwrap();
                        for j in 0..100 {
                            let offset = (i * 100 + j) * 4;
                            let data = (offset as u32).to_le_bytes();
                            manager.write_memory(offset, &data).unwrap();
                        }
                    });
                    handles.push(handle);
                }

                for handle in handles {
                    handle.join().unwrap();
                }

                black_box(memory_manager)
            })
        });
    }

    group.finish();
}

/// 创建WebAssembly数组（使用常量泛型推断）
/// Create WebAssembly array (using const generic inference)
fn create_wasm_array<const LEN: usize>() -> [Value; LEN] {
    [Value::I32(0); LEN]
}

/// 生命周期示例
/// Lifetime example
fn lifetime_example<'a>(input: &'a str) -> &'a str {
    input
}

// 基准测试组配置
// Benchmark group configuration
criterion_group!(
    benches,
    bench_memory_operations,
    bench_simd_operations,
    bench_tail_call_optimization,
    bench_host_bindings,
    bench_interface_types,
    bench_rust_190_features,
    bench_comprehensive,
    bench_memory_usage,
    bench_concurrency
);

criterion_main!(benches);
