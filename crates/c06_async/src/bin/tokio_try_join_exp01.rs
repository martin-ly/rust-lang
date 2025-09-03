use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let f1 = async {
        tokio::time::sleep(Duration::from_millis(150)).await;
        Ok::<_, &'static str>(1)
    };
    let f2 = async {
        tokio::time::sleep(Duration::from_millis(100)).await;
        Ok::<_, &'static str>(2)
    };
    match tokio::try_join!(f1, f2) {
        Ok((a, b)) => println!("try_join ok: {} {}", a, b),
        Err(e) => eprintln!("try_join error: {}", e),
    }
}


