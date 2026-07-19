// 数据管道：异步处理器示例 Data Pipeline: Async Processor Example
trait Processor {
    async fn process(&self, input: i32) -> i32;
}

struct AddOne;

#[tokio::main]
async fn main() {
    let p = AddOne;
    let out = p.process(41).await;
    println!("Processed: {}", out);
}

impl Processor for AddOne {
    async fn process(&self, input: i32) -> i32 {
        input + 1
    }
} 