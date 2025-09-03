use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let mut set = tokio::task::JoinSet::new();
    for i in 0..6u32 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_millis(50 * i as u64)).await;
            if i == 3 { anyhow::bail!("task {} failed", i); }
            Ok::<u32, _>(i)
        });
    }

    while let Some(res) = set.join_next().await {
        match res {
            Ok(Ok(v)) => println!("ok {v}"),
            Ok(Err(e)) => {
                eprintln!("task error: {e}");
                set.abort_all();
            }
            Err(e) => {
                eprintln!("join error: {e}");
                set.abort_all();
            }
        }
    }
}


