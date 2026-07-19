// CI/CD 流水线步骤示例 CI/CD Pipeline Step Example
trait Step {
    async fn execute(&self) -> Result<(), String>;
}

struct TestStep;

#[tokio::main]
async fn main() {
    let s = TestStep;
    s.execute().await.unwrap();
}

impl Step for TestStep {
    async fn execute(&self) -> Result<(), String> {
        println!("Running tests...");
        Ok(())
    }
} 