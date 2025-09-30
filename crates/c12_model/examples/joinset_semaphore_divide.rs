#![allow(clippy::print_stdout)]

#[cfg(all(feature = "tokio-adapter"))]
#[tokio::main(flavor = "multi_thread")] 
async fn main() {
    use std::sync::Arc;
    use tokio::{sync::Semaphore, task::JoinSet};

    let items: Vec<u64> = (0..10_000).collect();
    let max_concurrency = 128usize;
    let batch = 64usize;
    let sem = Arc::new(Semaphore::new(max_concurrency));
    let mut set = JoinSet::new();

    for chunk in items.chunks(batch) {
        let permit = sem.clone().acquire_owned().await.expect("permit");
        let v = chunk.to_vec();
        set.spawn(async move {
            let _p = permit;
            // emulate CPU bound work per batch
            let s: u64 = v.into_iter().map(|x| x.wrapping_mul(2)).sum();
            Ok::<u64, ()>(s)
        });
    }

    let mut total = 0u64;
    while let Some(res) = set.join_next().await { 
        if let Ok(Ok(value)) = res {
            total += value;
        }
    }
    println!("joinset_semaphore_divide: max_concurrency={max_concurrency} total={total}");
}

#[cfg(not(all(feature = "tokio-adapter")))]
fn main() {
    eprintln!("Enable features: --features tokio-adapter\nExample: cargo run -p c12_model --example joinset_semaphore_divide --features tokio-adapter");
}


