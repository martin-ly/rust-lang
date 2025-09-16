use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let mut set = tokio::task::JoinSet::new();
    for i in 0..5u32 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_millis(50 * i as u64)).await;
            i * i
        });
    }
    while let Some(res) = set.join_next().await {
        match res {
            Ok(v) => println!("got {}", v),
            Err(e) => eprintln!("task error: {:?}", e),
        }
    }
}
