// async fn in traits 示例（Rust 1.88 新特性）
trait AsyncJob {
    async fn run(&self);
}

struct MyJob;

#[tokio::main]
async fn main() {
    let job = MyJob;
    job.run().await;
}

impl AsyncJob for MyJob {
    async fn run(&self) {
        println!("Running async job!");
    }
} 