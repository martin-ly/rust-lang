// 区块链异步共识示例 Blockchain Async Consensus Example
trait Consensus {
    async fn propose(&self, block: u64) -> bool;
}

struct SimpleConsensus;

#[tokio::main]
async fn main() {
    let c = SimpleConsensus;
    let ok = c.propose(42).await;
    println!("Consensus result: {}", ok);
}

impl Consensus for SimpleConsensus {
    async fn propose(&self, block: u64) -> bool {
        println!("Proposing block: {}", block);
        true
    }
} 