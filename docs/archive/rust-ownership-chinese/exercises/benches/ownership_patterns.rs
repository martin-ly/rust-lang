use criterion::{black_box, criterion_group, criterion_main, Criterion};

// 基准测试：所有权转移 vs 借用
fn ownership_transfer_benchmark(c: &mut Criterion) {
    c.bench_function("vec_clone_transfer", |b| {
        let data: Vec<u8> = (0..1000).map(|x| x as u8).collect();
        b.iter(|| {
            let cloned = data.clone();
            black_box(cloned);
        });
    });
    
    c.bench_function("vec_borrow", |b| {
        let data: Vec<u8> = (0..1000).map(|x| x as u8).collect();
        b.iter(|| {
            let slice: &[u8] = &data;
            black_box(slice);
        });
    });
}

// 基准测试：Box vs 栈分配
fn box_vs_stack_benchmark(c: &mut Criterion) {
    c.bench_function("large_struct_stack", |b| {
        #[derive(Clone, Copy)]
        struct LargeStruct([u64; 128]);
        
        b.iter(|| {
            let s = LargeStruct([0; 128]);
            black_box(s);
        });
    });
    
    c.bench_function("large_struct_heap", |b| {
        #[derive(Clone, Copy)]
        struct LargeStruct([u64; 128]);
        
        b.iter(|| {
            let s = Box::new(LargeStruct([0; 128]));
            black_box(s);
        });
    });
}

// 基准测试：Rc vs Arc
fn rc_vs_arc_benchmark(c: &mut Criterion) {
    use std::rc::Rc;
    use std::sync::Arc;
    
    c.bench_function("rc_clone", |b| {
        let data = Rc::new(vec![0u8; 1000]);
        b.iter(|| {
            let cloned = Rc::clone(&data);
            black_box(cloned);
        });
    });
    
    c.bench_function("arc_clone", |b| {
        let data = Arc::new(vec![0u8; 1000]);
        b.iter(|| {
            let cloned = Arc::clone(&data);
            black_box(cloned);
        });
    });
}

// 基准测试：迭代器链
fn iterator_chain_benchmark(c: &mut Criterion) {
    let data: Vec<i32> = (0..10000).collect();
    
    c.bench_function("iterator_chain", |b| {
        b.iter(|| {
            let sum: i32 = data
                .iter()
                .filter(|&&x| x % 2 == 0)
                .map(|x| x * x)
                .take(100)
                .sum();
            black_box(sum);
        });
    });
    
    c.bench_function("manual_loop", |b| {
        b.iter(|| {
            let mut sum = 0;
            let mut count = 0;
            for &x in &data {
                if x % 2 == 0 {
                    sum += x * x;
                    count += 1;
                    if count >= 100 {
                        break;
                    }
                }
            }
            black_box(sum);
        });
    });
}

criterion_group!(
    benches,
    ownership_transfer_benchmark,
    box_vs_stack_benchmark,
    rc_vs_arc_benchmark,
    iterator_chain_benchmark
);
criterion_main!(benches);
