// benches/my_bench.rs
use criterion::{Criterion, black_box, criterion_group, criterion_main};

fn bench_example(c: &mut Criterion) {
    c.bench_function("example", |b| b.iter(|| black_box(42)));
}

criterion_group!(benches, bench_example);
criterion_main!(benches);
