use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use c20_distributed::replication::MajorityQuorum;
use c20_distributed::replication::QuorumPolicy;
use c20_distributed::consistency::ConsistencyLevel;

fn bench_ack(c: &mut Criterion) {
    c.bench_function("ack_quorum_table", |b| {
        b.iter(|| {
            let total = 5usize;
            for ok in 0..=total {
                let need = MajorityQuorum::required_acks(total, ConsistencyLevel::Quorum);
                black_box((ok, need, ok >= need));
            }
        })
    });
}

criterion_group!(benches, bench_ack);
criterion_main!(benches);


