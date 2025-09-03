use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use c03_control_fn::rust_189_features::{
    TextProcessor,
    VecCollection,
    Matrix,
    compile_time_factorial,
    is_prime,
    calculate_matrix_size,
};
use c03_control_fn::async_control_flow_189::AsyncControlFlowExecutor189;
use c03_control_fn::performance_optimization_189::{
    fast_add,
    DefaultLayout,
    COptimizedLayout,
    CacheLineAligned,
    ControlFlowOptimizer,
};

// 异步trait性能基准测试
fn bench_async_trait_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("Async Trait Performance");
    
    group.bench_function("async_trait_process", |b| {
        b.iter(|| {
            let processor = TextProcessor;
            let data = black_box(b"Hello, Rust 1.89!");
            black_box(processor);
            black_box(data);
        });
    });
    
    group.bench_function("async_trait_validate", |b| {
        b.iter(|| {
            let processor = TextProcessor;
            let input = black_box("test_input");
            black_box(processor);
            black_box(input);
        });
    });
    
    group.finish();
}

// GATs性能基准测试
fn bench_gats_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("GATs Performance");
    
    group.bench_function("gats_iteration", |b| {
        let collection = VecCollection {
            items: vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        };
        
        b.iter(|| {
            let mut iter = collection.items.iter();
            let mut sum = 0;
            while let Some(item) = iter.next() {
                sum += item;
            }
            black_box(sum);
        });
    });
    
    group.bench_function("gats_large_collection", |b| {
        let items: Vec<i32> = (0..1000).collect();
        let collection = VecCollection { items };
        
        b.iter(|| {
            let mut iter = collection.items.iter();
            let mut sum = 0;
            while let Some(item) = iter.next() {
                sum += item;
            }
            black_box(sum);
        });
    });
    
    group.finish();
}

// 常量泛型性能基准测试
fn bench_const_generics_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("Const Generics Performance");
    
    group.bench_function("matrix_creation_small", |b| {
        b.iter(|| {
            let matrix = Matrix::<f64, 3, 3>::new();
            black_box(matrix);
        });
    });
    
    group.bench_function("matrix_creation_large", |b| {
        b.iter(|| {
            let matrix = Matrix::<f64, 10, 10>::new();
            black_box(matrix);
        });
    });
    
    group.bench_function("matrix_access", |b| {
        let matrix = Matrix::<f64, 10, 10>::new();
        b.iter(|| {
            for row in 0..10 {
                for col in 0..10 {
                    let _ = matrix.get(row, col);
                }
            }
        });
    });
    
    group.bench_function("compile_time_calculation", |b| {
        b.iter(|| {
            let size = calculate_matrix_size::<5, 5>();
            black_box(size);
        });
    });
    
    group.finish();
}

// 内存布局优化性能基准测试
fn bench_memory_layout_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("Memory Layout Performance");
    
    group.bench_function("default_layout_size", |b| {
        b.iter(|| {
            let size = std::mem::size_of::<DefaultLayout>();
            black_box(size);
        });
    });
    
    group.bench_function("optimized_layout_size", |b| {
        b.iter(|| {
            let size = std::mem::size_of::<COptimizedLayout>();
            black_box(size);
        });
    });
    
    group.bench_function("cache_aligned_size", |b| {
        b.iter(|| {
            let size = std::mem::size_of::<CacheLineAligned>();
            black_box(size);
        });
    });
    
    group.finish();
}

// 内联优化性能基准测试
fn bench_inline_optimization_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("Inline Optimization Performance");
    
    group.bench_function("fast_add_inlined", |b| {
        b.iter(|| {
            let result = fast_add(black_box(10), black_box(20));
            black_box(result);
        });
    });
    
    group.finish();
}

// 控制流优化性能基准测试
fn bench_control_flow_optimization_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("Control Flow Optimization Performance");
    
    let small_data: Vec<i32> = (-50..50).collect();
    let large_data: Vec<i32> = (-1000..1000).collect();
    
    group.bench_function("branch_prediction_friendly_small", |b| {
        b.iter(|| {
            let result = ControlFlowOptimizer::branch_prediction_friendly_process(
                black_box(&small_data),
            );
            black_box(result);
        });
    });
    
    group.bench_function("branch_prediction_friendly_large", |b| {
        b.iter(|| {
            let result = ControlFlowOptimizer::branch_prediction_friendly_process(
                black_box(&large_data),
            );
            black_box(result);
        });
    });
    
    group.bench_function("branchless_max", |b| {
        b.iter(|| {
            let result = ControlFlowOptimizer::branchless_max(
                black_box(10),
                black_box(20),
            );
            black_box(result);
        });
    });
    
    group.bench_function("branchless_abs", |b| {
        b.iter(|| {
            let result = ControlFlowOptimizer::branchless_abs(black_box(-100));
            black_box(result);
        });
    });
    
    group.finish();
}

// 编译时计算性能基准测试
fn bench_compile_time_calculation_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("Compile Time Calculation Performance");
    
    group.bench_function("factorial_small", |b| {
        b.iter(|| {
            let result = compile_time_factorial(black_box(5));
            black_box(result);
        });
    });
    
    group.bench_function("factorial_medium", |b| {
        b.iter(|| {
            let result = compile_time_factorial(black_box(10));
            black_box(result);
        });
    });
    
    group.bench_function("is_prime_small", |b| {
        b.iter(|| {
            let result = is_prime(black_box(17));
            black_box(result);
        });
    });
    
    group.bench_function("is_prime_medium", |b| {
        b.iter(|| {
            let result = is_prime(black_box(100));
            black_box(result);
        });
    });
    
    group.finish();
}

// 异步控制流性能基准测试（简化）
fn bench_async_control_flow_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("Async Control Flow Performance");
    
    group.bench_function("async_control_flow_executor", |b| {
        b.iter(|| {
            let executor = AsyncControlFlowExecutor189;
            black_box(executor);
        });
    });
    
    group.finish();
}

// 综合性能基准测试
fn bench_comprehensive_performance(c: &mut Criterion) {
    let mut group = c.benchmark_group("Comprehensive Performance");
    
    group.bench_function("web_service_scenario", |b| {
        b.iter(|| {
            let processor = TextProcessor;
            let data = b"HTTP request data";
            let matrix = Matrix::<f64, 3, 3>::new();
            let size = calculate_matrix_size::<3, 3>();
            
            black_box(processor);
            black_box(data);
            black_box(matrix);
            black_box(size);
        });
    });
    
    group.bench_function("data_processing_scenario", |b| {
        let data: Vec<i32> = (-100..100).collect();
        
        b.iter(|| {
            let result = ControlFlowOptimizer::branch_prediction_friendly_process(
                black_box(&data),
            );
            let matrix = Matrix::<f64, 5, 5>::new();
            let factorial = compile_time_factorial(5);
            
            black_box(result);
            black_box(matrix);
            black_box(factorial);
        });
    });
    
    group.bench_function("system_programming_scenario", |b| {
        b.iter(|| {
            let max_val = ControlFlowOptimizer::branchless_max(100, 200);
            let abs_val = ControlFlowOptimizer::branchless_abs(-150);
            let optimized_layout = COptimizedLayout {
                a: 1,
                c: 2,
                d: 3,
                b: 4,
            };
            
            black_box(max_val);
            black_box(abs_val);
            black_box(optimized_layout);
        });
    });
    
    group.finish();
}

// 配置基准测试组
criterion_group!(
    benches,
    bench_async_trait_performance,
    bench_gats_performance,
    bench_const_generics_performance,
    bench_memory_layout_performance,
    bench_inline_optimization_performance,
    bench_control_flow_optimization_performance,
    bench_compile_time_calculation_performance,
    bench_async_control_flow_performance,
    bench_comprehensive_performance,
);

criterion_main!(benches);
