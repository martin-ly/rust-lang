// 基础设施即代码：资源自动化配置示例
// Infrastructure as Code: Resource Provision Example
trait Resource {
    async fn provision(&self) -> Result<(), String>;
}

struct VM;

#[tokio::main]
async fn main() {
    let vm = VM;
    vm.provision().await.unwrap();
}

impl Resource for VM {
    async fn provision(&self) -> Result<(), String> {
        println!("Provisioning VM...");
        Ok(())
    }
} 