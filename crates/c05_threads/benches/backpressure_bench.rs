use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use c05_threads::message_passing::backpressure_handling as bp;

fn bench_blocking(c: &mut Criterion) {
    c.bench_function("blocking_backpressure_10k", |b| {
        b.iter(|| {
            let ch = bp::BlockingBackpressureChannel::new(1024);
            for i in 0..10_000 {
                let _ = ch.send(i);
            }
            let mut sum = 0u64;
            for _ in 0..10_000 {
                if let Some(v) = ch.recv() { sum = sum.wrapping_add(v as u64); }
            }
            black_box(sum)
        })
    });
}

fn bench_dropping(c: &mut Criterion) {
    c.bench_function("dropping_backpressure_10k", |b| {
        b.iter(|| {
            let ch = bp::DroppingBackpressureChannel::new(1024, 0.95);
            let mut sent = 0u64;
            for i in 0..10_000 {
                if ch.send(i).is_ok() { sent += 1; }
            }
            let mut sum = 0u64;
            for _ in 0..sent {
                if let Some(v) = ch.recv() { sum = sum.wrapping_add(v as u64); }
            }
            black_box((sent, sum))
        })
    });
}

criterion_group!(benches, bench_blocking, bench_dropping);
criterion_main!(benches);
