use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_noop(criterion: &mut Criterion) {
    criterion.bench_function("noop", |bencher| bencher.iter(|| black_box(1)));
}

criterion_group!(benches, bench_noop);
criterion_main!(benches);


