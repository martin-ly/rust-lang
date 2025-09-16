use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use std::sync::mpsc;
use std::thread;

fn mpsc_roundtrip(n: usize) {
    let (tx, rx) = mpsc::channel();
    let producer = thread::spawn(move || {
        for i in 0..n {
            tx.send(i).unwrap();
        }
    });
    let mut sum = 0usize;
    for _ in 0..n {
        sum += rx.recv().unwrap();
    }
    producer.join().unwrap();
    black_box(sum);
}

fn sync_mpsc_roundtrip(n: usize, cap: usize) {
    let (tx, rx) = mpsc::sync_channel(cap);
    let producer = thread::spawn(move || {
        for i in 0..n {
            tx.send(i).unwrap();
        }
    });
    let mut sum = 0usize;
    for _ in 0..n {
        sum += rx.recv().unwrap();
    }
    producer.join().unwrap();
    black_box(sum);
}

fn bench_mpsc(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrency_mpsc");
    for &n in &[1_000, 10_000] {
        group.bench_with_input(format!("roundtrip_{}", n), &n, |b, &n| b.iter(|| mpsc_roundtrip(n)));
    }
    for &cap in &[1, 8, 64] {
        group.bench_with_input(format!("sync_roundtrip_{}_cap{}", 10_000, cap), &cap, |b, &cap| b.iter(|| sync_mpsc_roundtrip(10_000, cap)));
    }
    group.finish();
}

criterion_group!(benches, bench_mpsc);
criterion_main!(benches);


