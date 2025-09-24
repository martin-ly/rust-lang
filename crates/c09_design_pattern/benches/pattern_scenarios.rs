use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::hint::black_box;

// 责任链：用函数链模拟
fn chain_process(input: &str) -> String {
    fn a(s: &str) -> String { format!("a:{}", s) }
    fn b(s: &str) -> String { format!("b:{}", s) }
    fn c(s: &str) -> String { format!("c:{}", s) }
    c(&b(&a(input)))
}

// 装饰器：包装函数
fn base(x: u64) -> u64 { x.wrapping_mul(3).wrapping_add(7) }
fn deco1(f: fn(u64) -> u64) -> impl Fn(u64) -> u64 { move |x| f(x).wrapping_mul(2) }
fn deco2(f: fn(u64) -> u64) -> impl Fn(u64) -> u64 { move |x| f(x).wrapping_add(11) }

// 代理：条件分派
fn proxy_call(flag: bool, x: u64) -> u64 {
    if flag { base(x) } else { x }
}

pub fn scenario_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pattern_scenarios");

    group.bench_with_input(BenchmarkId::new("chain", 1024), &1024, |b, &n| {
        b.iter(|| {
            let mut out = String::new();
            for i in 0..n { out = chain_process(black_box(&format!("{}", i))); }
            black_box(out)
        })
    });

    group.bench_with_input(BenchmarkId::new("decorator", 1_000), &1_000u64, |b, &n| {
        let f1 = deco1(base);
        let f2 = deco2(base);
        b.iter(|| {
            let mut acc = 0u64;
            for i in 0..n { acc = acc.wrapping_add(black_box(f1(i)) ^ black_box(f2(i))); }
            black_box(acc)
        })
    });

    group.bench_with_input(BenchmarkId::new("proxy", 1_000), &1_000u64, |b, &n| {
        b.iter(|| {
            let mut acc = 0u64;
            for i in 0..n { acc = acc.wrapping_add(black_box(proxy_call(i % 2 == 0, i))); }
            black_box(acc)
        })
    });

    group.finish();
}

criterion_group!(benches, scenario_benchmarks);
criterion_main!(benches);

