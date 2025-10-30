//! # 设计模式性能基准测试
//!
//! 测试不同设计模式实现的性能
//!
//! ## 运行方式
//!
//! ```bash
//! cargo bench --bench design_patterns_bench
//! ```

use c12_wasm::ecosystem_examples::design_patterns::strategy::SortStrategy;
use c12_wasm::ecosystem_examples::design_patterns::*;
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};

/// 测试工厂模式性能
fn bench_factory_pattern(c: &mut Criterion) {
    let mut group = c.benchmark_group("factory_pattern");

    group.bench_function("create_html_renderer", |b| {
        use factory::*;
        b.iter(|| {
            let renderer = create_renderer(black_box(RendererType::Html));
            renderer.render(black_box("test content"))
        });
    });

    group.bench_function("create_markdown_renderer", |b| {
        use factory::*;
        b.iter(|| {
            let renderer = create_renderer(black_box(RendererType::Markdown));
            renderer.render(black_box("test content"))
        });
    });

    group.finish();
}

/// 测试建造者模式性能
fn bench_builder_pattern(c: &mut Criterion) {
    let mut group = c.benchmark_group("builder_pattern");

    group.bench_function("build_simple_config", |b| {
        use builder::*;
        b.iter(|| {
            ConfigBuilder::new()
                .url(black_box("https://example.com".to_string()))
                .build()
        });
    });

    group.bench_function("build_complex_config", |b| {
        use builder::*;
        b.iter(|| {
            ConfigBuilder::new()
                .url(black_box("https://example.com".to_string()))
                .timeout(black_box(5000))
                .retries(black_box(3))
                .build()
        });
    });

    group.finish();
}

/// 测试策略模式性能 - 排序算法比较
fn bench_strategy_pattern(c: &mut Criterion) {
    let mut group = c.benchmark_group("strategy_pattern_sorting");

    // 小数据集
    let small_data: Vec<i32> = vec![5, 2, 8, 1, 9, 3, 7, 4, 6];

    group.bench_with_input(
        BenchmarkId::new("bubble_sort", "small"),
        &small_data,
        |b, data| {
            use strategy::BubbleSortStrategy;
            let strategy = BubbleSortStrategy;
            b.iter(|| {
                let mut data_clone = data.clone();
                strategy.sort(&mut data_clone);
                data_clone
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("quick_sort", "small"),
        &small_data,
        |b, data| {
            use strategy::QuickSortStrategy;
            let strategy = QuickSortStrategy;
            b.iter(|| {
                let mut data_clone = data.clone();
                strategy.sort(&mut data_clone);
                data_clone
            });
        },
    );

    // 大数据集
    let large_data: Vec<i32> = (0..1000).rev().collect();

    group.bench_with_input(
        BenchmarkId::new("bubble_sort", "large"),
        &large_data,
        |b, data| {
            use strategy::BubbleSortStrategy;
            let strategy = BubbleSortStrategy;
            b.iter(|| {
                let mut data_clone = data.clone();
                strategy.sort(&mut data_clone);
                data_clone
            });
        },
    );

    group.bench_with_input(
        BenchmarkId::new("quick_sort", "large"),
        &large_data,
        |b, data| {
            use strategy::QuickSortStrategy;
            let strategy = QuickSortStrategy;
            b.iter(|| {
                let mut data_clone = data.clone();
                strategy.sort(&mut data_clone);
                data_clone
            });
        },
    );

    group.finish();
}

/// 测试观察者模式性能
fn bench_observer_pattern(c: &mut Criterion) {
    let mut group = c.benchmark_group("observer_pattern");

    group.bench_function("notify_observers", |b| {
        use observer::*;

        let subject = EventSubject::new();

        // 添加10个观察者
        for _ in 0..10 {
            subject.attach(Box::new(ConsoleObserver));
        }

        b.iter(|| {
            subject.notify(black_box("test event"));
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_factory_pattern,
    bench_builder_pattern,
    bench_strategy_pattern,
    bench_observer_pattern
);

criterion_main!(benches);
