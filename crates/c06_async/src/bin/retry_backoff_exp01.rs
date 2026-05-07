use c06_async::utils::retry_with_backoff;
use std::time::Duration;

async fn flaky(op_ok_after: u32) -> Result<&'static str, &'static str> {
    use std::sync::atomic::{AtomicU32, Ordering};
    static COUNT: AtomicU32 = AtomicU32::new(0);
    let current = COUNT.fetch_add(1, Ordering::Relaxed) + 1;
    if current >= op_ok_after {
        Ok("ok")
    } else {
        Err("err")
    }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let res = retry_with_backoff(
        |attempt| async move {
            match flaky(3).await {
                Ok(s) => Ok::<_, &'static str>((attempt, s)),
                Err(e) => Err(e),
            }
        },
        5,
        Duration::from_millis(50),
    )
    .await;
    match res {
        Ok((attempt, s)) => println!("success on attempt {}: {}", attempt, s),
        Err(_) => println!("give up"),
    }
}
