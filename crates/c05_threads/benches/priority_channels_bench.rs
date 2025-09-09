use criterion::{criterion_group, criterion_main, Criterion, black_box};
use c05_threads::message_passing::{priority_channels as full, priority_channels_simple as simple};

fn bench_simple(c: &mut Criterion) {
    c.bench_function("simple_priority_channel_send_recv_10k", |b| {
        b.iter(|| {
            let ch = simple::SimplePriorityChannel::new();
            for i in 0..10_000 {
                ch.send((i % 3) as u32, i);
            }
            let mut sum = 0u64;
            while let Some(v) = ch.recv() {
                sum = sum.wrapping_add(v as u64);
            }
            black_box(sum)
        })
    });
}

fn bench_full(c: &mut Criterion) {
    c.bench_function("full_priority_channel_send_recv_10k", |b| {
        b.iter(|| {
            let ch = full::PriorityChannel::new();
            for i in 0..10_000 {
                let _ = ch.send((i % 3) as u32, i);
            }
            let mut sum = 0u64;
            for _ in 0..10_000 {
                if let Some(v) = ch.try_recv() { sum = sum.wrapping_add(v as u64); }
            }
            black_box(sum)
        })
    });
}

fn bench_dynamic(c: &mut Criterion) {
    c.bench_function("dynamic_priority_channel_send_recv_10k", |b| {
        b.iter(|| {
            let ch = full::DynamicPriorityChannel::new(|data: &i32| {
                // 短小数据优先（示意）
                if *data < 1000 { 1 } else if *data < 5000 { 2 } else { 3 }
            });
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

fn bench_fair(c: &mut Criterion) {
    c.bench_function("fair_priority_channel_send_recv_10k", |b| {
        b.iter(|| {
            let ch = full::FairSchedulingPriorityChannel::new(2, 3);
            for i in 0..10_000 {
                let p = if i % 5 == 0 { 1 } else { 5 };
                let _ = ch.send(p, i);
            }
            let mut sum = 0u64;
            for _ in 0..10_000 {
                if let Some(v) = ch.recv() { sum = sum.wrapping_add(v as u64); }
            }
            black_box(sum)
        })
    });
}

criterion_group!(benches, bench_simple, bench_full, bench_dynamic, bench_fair);
criterion_main!(benches);
