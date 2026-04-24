//! C09 设计模式搜索与查询性能基准测试
//!
//! 测试设计模式库的查询、过滤和匹配操作性能。

use c09_design_pattern::{
    ExecutionModel, PatternCategory, get_all_patterns, get_patterns_by_category,
    get_patterns_by_execution_model, search_patterns,
};
use criterion::{Criterion, criterion_group, criterion_main};

/// 基准测试：获取所有设计模式
fn bench_get_all_patterns(c: &mut Criterion) {
    c.bench_function("get_all_patterns", |b| {
        b.iter(|| {
            let patterns = get_all_patterns();
            std::hint::black_box(patterns);
        });
    });
}

/// 基准测试：按分类过滤
fn bench_filter_by_category(c: &mut Criterion) {
    c.bench_function("filter_by_category_creational", |b| {
        b.iter(|| {
            let patterns = get_patterns_by_category(PatternCategory::Creational);
            std::hint::black_box(patterns);
        });
    });

    c.bench_function("filter_by_category_behavioral", |b| {
        b.iter(|| {
            let patterns = get_patterns_by_category(PatternCategory::Behavioral);
            std::hint::black_box(patterns);
        });
    });
}

/// 基准测试：按执行模型过滤
fn bench_filter_by_execution_model(c: &mut Criterion) {
    c.bench_function("filter_by_execution_sync", |b| {
        b.iter(|| {
            let patterns = get_patterns_by_execution_model(ExecutionModel::Sync);
            std::hint::black_box(patterns);
        });
    });

    c.bench_function("filter_by_execution_async", |b| {
        b.iter(|| {
            let patterns = get_patterns_by_execution_model(ExecutionModel::Async);
            std::hint::black_box(patterns);
        });
    });
}

/// 基准测试：搜索设计模式
fn bench_search_patterns(c: &mut Criterion) {
    c.bench_function("search_patterns_hit", |b| {
        b.iter(|| {
            let results = search_patterns("singleton");
            std::hint::black_box(results);
        });
    });

    c.bench_function("search_patterns_miss", |b| {
        b.iter(|| {
            let results = search_patterns("nonexistent_pattern_query");
            std::hint::black_box(results);
        });
    });

    c.bench_function("search_patterns_partial", |b| {
        b.iter(|| {
            let results = search_patterns("proxy");
            std::hint::black_box(results);
        });
    });
}

/// 基准测试：枚举匹配（模拟运行时分发）
fn bench_enum_matching(c: &mut Criterion) {
    let categories = vec![
        PatternCategory::Creational,
        PatternCategory::Structural,
        PatternCategory::Behavioral,
        PatternCategory::Parallel,
        PatternCategory::Concurrency,
        PatternCategory::DomainSpecific,
    ];

    c.bench_function("enum_match_dispatch", |b| {
        b.iter(|| {
            let mut counts = [0usize; 6];
            for cat in &categories {
                let idx = match cat {
                    PatternCategory::Creational => 0,
                    PatternCategory::Structural => 1,
                    PatternCategory::Behavioral => 2,
                    PatternCategory::Parallel => 3,
                    PatternCategory::Concurrency => 4,
                    PatternCategory::DomainSpecific => 5,
                };
                counts[idx] += 1;
            }
            std::hint::black_box(counts);
        });
    });
}

criterion_group!(
    benches,
    bench_get_all_patterns,
    bench_filter_by_category,
    bench_filter_by_execution_model,
    bench_search_patterns,
    bench_enum_matching,
);
criterion_main!(benches);
