//! 性能基准测试
//! 
//! 使用criterion进行性能基准测试

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::time::Duration;

fn bench_ownership_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("ownership");
    
    group.bench_function("move_semantics", |b| {
        b.iter(|| {
            let data = vec![1, 2, 3, 4, 5];
            black_box(take_ownership(data))
        })
    });
    
    group.bench_function("borrow_semantics", |b| {
        let data = vec![1, 2, 3, 4, 5];
        b.iter(|| {
            black_box(borrow_data(&data))
        })
    });
    
    group.bench_function("clone_operation", |b| {
        let data = vec![1, 2, 3, 4, 5];
        b.iter(|| {
            black_box(data.clone())
        })
    });
    
    group.finish();
}

fn bench_type_system_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("type_system");
    
    group.bench_function("generic_instantiation", |b| {
        b.iter(|| {
            black_box(generic_function::<i32>(1000))
        })
    });
    
    group.bench_function("trait_dispatch", |b| {
        let data = create_trait_objects(1000);
        b.iter(|| {
            black_box(process_trait_objects(&data))
        })
    });
    
    group.bench_function("enum_matching", |b| {
        let enums = create_enums(1000);
        b.iter(|| {
            black_box(process_enums(&enums))
        })
    });
    
    group.finish();
}

fn bench_collection_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("collections");
    
    group.bench_function("vec_push", |b| {
        b.iter(|| {
            let mut vec = Vec::new();
            for i in 0..1000 {
                vec.push(i);
            }
            black_box(vec)
        })
    });
    
    group.bench_function("vec_with_capacity", |b| {
        b.iter(|| {
            let mut vec = Vec::with_capacity(1000);
            for i in 0..1000 {
                vec.push(i);
            }
            black_box(vec)
        })
    });
    
    group.bench_function("hashmap_insert", |b| {
        b.iter(|| {
            let mut map = std::collections::HashMap::new();
            for i in 0..1000 {
                map.insert(i, i * 2);
            }
            black_box(map)
        })
    });
    
    group.finish();
}

fn bench_string_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("strings");
    
    group.bench_function("string_concat", |b| {
        b.iter(|| {
            let mut s = String::new();
            for i in 0..100 {
                s.push_str(&i.to_string());
            }
            black_box(s)
        })
    });
    
    group.bench_function("string_format", |b| {
        b.iter(|| {
            let mut s = String::new();
            for i in 0..100 {
                s = format!("{}{}", s, i);
            }
            black_box(s)
        })
    });
    
    group.bench_function("string_join", |b| {
        let strings: Vec<String> = (0..100).map(|i| i.to_string()).collect();
        b.iter(|| {
            black_box(strings.join(""))
        })
    });
    
    group.finish();
}

fn bench_iteration_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("iteration");
    
    let data: Vec<i32> = (0..10000).collect();
    
    group.bench_function("for_loop", |b| {
        b.iter(|| {
            let mut sum = 0;
            for &item in &data {
                sum += item;
            }
            black_box(sum)
        })
    });
    
    group.bench_function("iterator_sum", |b| {
        b.iter(|| {
            let sum: i32 = data.iter().sum();
            black_box(sum)
        })
    });
    
    group.bench_function("iterator_fold", |b| {
        b.iter(|| {
            let sum = data.iter().fold(0, |acc, &x| acc + x);
            black_box(sum)
        })
    });
    
    group.finish();
}

fn bench_error_handling(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling");
    
    group.bench_function("result_ok", |b| {
        b.iter(|| {
            let result: Result<i32, String> = Ok(42);
            black_box(result.unwrap())
        })
    });
    
    group.bench_function("result_err", |b| {
        b.iter(|| {
            let result: Result<i32, String> = Err("error".to_string());
            black_box(result.is_err())
        })
    });
    
    group.bench_function("option_some", |b| {
        b.iter(|| {
            let option: Option<i32> = Some(42);
            black_box(option.unwrap())
        })
    });
    
    group.bench_function("option_none", |b| {
        b.iter(|| {
            let option: Option<i32> = None;
            black_box(option.is_none())
        })
    });
    
    group.finish();
}

// 配置基准测试组
criterion_group!(
    benches,
    bench_ownership_operations,
    bench_type_system_operations,
    bench_collection_operations,
    bench_string_operations,
    bench_iteration_operations,
    bench_error_handling
);

criterion_main!(benches);

// 辅助函数
fn take_ownership(data: Vec<i32>) -> Vec<i32> {
    data
}

fn borrow_data(data: &[i32]) -> i32 {
    data.iter().sum()
}

fn generic_function<T>(value: T) -> T {
    value
}

trait TestTrait {
    fn process(&self) -> i32;
}

struct TestStruct {
    value: i32,
}

impl TestTrait for TestStruct {
    fn process(&self) -> i32 {
        self.value * 2
    }
}

fn create_trait_objects(count: usize) -> Vec<Box<dyn TestTrait>> {
    (0..count)
        .map(|i| Box::new(TestStruct { value: i as i32 }) as Box<dyn TestTrait>)
        .collect()
}

fn process_trait_objects(objects: &[Box<dyn TestTrait>]) -> i32 {
    objects.iter().map(|obj| obj.process()).sum()
}

enum TestEnum {
    A(i32),
    B(String),
    C,
}

fn create_enums(count: usize) -> Vec<TestEnum> {
    (0..count)
        .map(|i| match i % 3 {
            0 => TestEnum::A(i as i32),
            1 => TestEnum::B(i.to_string()),
            _ => TestEnum::C,
        })
        .collect()
}

fn process_enums(enums: &[TestEnum]) -> i32 {
    enums.iter().map(|e| match e {
        TestEnum::A(x) => *x,
        TestEnum::B(s) => s.len() as i32,
        TestEnum::C => 0,
    }).sum()
}
