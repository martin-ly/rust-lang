use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let mut tick = tokio::time::interval(Duration::from_millis(100));
    let mut slow = tokio::time::interval(Duration::from_millis(250));

    let mut count = 0;
    loop {
        tokio::select! {
            _ = tick.tick() => {
                count += 1;
                println!("tick {}", count);
            }
            _ = slow.tick() => {
                println!("slow event");
            }
            _ = tokio::time::sleep(Duration::from_secs(1)) => {
                println!("timeout reached, break");
                break;
            }
        }
    }
}
