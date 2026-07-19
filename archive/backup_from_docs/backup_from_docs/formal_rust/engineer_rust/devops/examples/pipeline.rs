// DevOps流水线任务示例 DevOps Pipeline Step Example
trait PipelineStep {
    async fn run(&self) -> Result<(), String>;
}

struct Build;

#[tokio::main]
async fn main() {
    let step = Build;
    step.run().await.unwrap();
}

impl PipelineStep for Build {
    async fn run(&self) -> Result<(), String> {
        println!("Building project...");
        Ok(())
    }
} 