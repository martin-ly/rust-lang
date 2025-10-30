//! # 字符串操作性能基准测试
//!
//! 测试各种字符串操作的性能
//!
//! ## 运行方式
//!
//! ```bash
//! cargo bench --bench string_operations_bench
//! ```

use c12_wasm::string_examples::*;
use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};

/// 测试字符串反转性能
fn bench_reverse_string(c: &mut Criterion) {
    let mut group = c.benchmark_group("reverse_string");

    let short_str = "hello";
    let medium_str = "The quick brown fox jumps over the lazy dog";
    let long_str = "Lorem ipsum dolor sit amet, consectetur adipiscing elit. ".repeat(10);

    group.bench_with_input(BenchmarkId::new("short", 5), &short_str, |b, s| {
        b.iter(|| reverse_string(black_box(s)));
    });

    group.bench_with_input(BenchmarkId::new("medium", 44), &medium_str, |b, s| {
        b.iter(|| reverse_string(black_box(s)));
    });

    group.bench_with_input(
        BenchmarkId::new("long", long_str.len()),
        &long_str,
        |b, s| {
            b.iter(|| reverse_string(black_box(s)));
        },
    );

    group.finish();
}

/// 测试回文检测性能
fn bench_is_palindrome(c: &mut Criterion) {
    let mut group = c.benchmark_group("is_palindrome");

    group.bench_function("short_palindrome", |b| {
        b.iter(|| is_palindrome(black_box("racecar")));
    });

    group.bench_function("short_non_palindrome", |b| {
        b.iter(|| is_palindrome(black_box("hello")));
    });

    group.bench_function("long_palindrome", |b| {
        b.iter(|| is_palindrome(black_box("A man a plan a canal Panama")));
    });

    group.finish();
}

/// 测试单词计数性能
fn bench_count_words(c: &mut Criterion) {
    let mut group = c.benchmark_group("count_words");

    let long_text = "Lorem ipsum dolor sit amet. ".repeat(100);
    let texts = vec![
        ("short", "hello world"),
        ("medium", "The quick brown fox jumps over the lazy dog"),
        ("long", long_text.as_str()),
    ];

    for (name, text) in texts {
        group.bench_with_input(BenchmarkId::from_parameter(name), &text, |b, text| {
            b.iter(|| count_words(black_box(text)));
        });
    }

    group.finish();
}

/// 测试大小写转换性能
fn bench_case_conversion(c: &mut Criterion) {
    let mut group = c.benchmark_group("case_conversion");

    let text = "The Quick Brown Fox Jumps Over The Lazy Dog. ".repeat(100);

    group.bench_function("to_uppercase", |b| {
        b.iter(|| to_uppercase(black_box(&text)));
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_reverse_string,
    bench_is_palindrome,
    bench_count_words,
    bench_case_conversion
);

criterion_main!(benches);
