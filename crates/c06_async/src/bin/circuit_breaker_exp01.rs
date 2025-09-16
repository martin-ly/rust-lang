use c06_async::utils::circuit_breaker::CircuitBreaker;
use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let breaker = CircuitBreaker::new(3, Duration::from_secs(2));
    let client = reqwest::Client::new();

    for i in 0..10u32 {
        let b = breaker.clone();
        let c = client.clone();
        let res = b
            .run(async move {
                // 模拟请求：前几次访问一个 404，触发失败累计
                let url = if i < 4 {
                    "https://httpbin.org/status/404"
                } else {
                    "https://httpbin.org/get"
                };
                let r = c.get(url).send().await.map_err(|_| "send_err")?;
                if !r.status().is_success() {
                    return Err("status_err");
                }
                Ok::<_, &'static str>(r.status())
            })
            .await;
        match res {
            Ok(status) => println!("ok {status}"),
            Err(_) => println!("blocked or failed (i={i})"),
        }
        tokio::time::sleep(Duration::from_millis(300)).await;
    }
}
