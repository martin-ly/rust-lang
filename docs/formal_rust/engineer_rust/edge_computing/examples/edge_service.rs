// 边缘计算：异步边缘服务处理示例 Edge Computing: Async Edge Service Example
trait EdgeService {
    async fn process(&self, input: i32) -> i32;
}

struct EdgeNode;

#[tokio::main]
async fn main() {
    let node = EdgeNode;
    let out = node.process(7).await;
    println!("Edge processed: {}", out);
}

impl EdgeService for EdgeNode {
    async fn process(&self, input: i32) -> i32 {
        input * 10
    }
} 