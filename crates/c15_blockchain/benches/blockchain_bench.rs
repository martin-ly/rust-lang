use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

fn bench_noop(criterion: &mut Criterion) {
    criterion.bench_function("noop", |bencher| bencher.iter(|| black_box(1)));
}

criterion_group!(benches, bench_noop);
criterion_main!(benches);
