//! Azure Blob Storage 列容器示例
//!
//! 本示例演示如何使用 `azure_identity` 与 `azure_storage_blob` 列出存储账户中的容器。
//! 运行时需要有效的 Azure 凭证（例如通过 `az login` 或 Azure Developer CLI）。
//! 若凭证不可用，程序将干净地返回错误。
//!
//! 本示例主要用于编译检查，不依赖真实模型文件。

use azure_identity::DeveloperToolsCredential;
use azure_storage_blob::BlobServiceClient;
use futures::TryStreamExt;
use std::sync::Arc;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let account = std::env::var("AZURE_STORAGE_ACCOUNT").unwrap_or_else(|_| "example".into());

    // 使用本地开发凭证（会尝试 Azure CLI / Azure Developer CLI）。
    // DeveloperToolsCredential::new 已返回 Arc<DeveloperToolsCredential>，可直接作为 Arc<dyn TokenCredential>。
    let credential: Arc<dyn azure_core::credentials::TokenCredential> =
        DeveloperToolsCredential::new(None)?;

    let service_url = format!("https://{}.blob.core.windows.net/", account).parse()?;
    let service_client = BlobServiceClient::new(service_url, Some(credential), None)?;

    // 列出容器；Pager 会自动处理分页。
    let mut pager = service_client.list_containers(None)?;
    while let Some(container) = pager.try_next().await? {
        println!("📦 Container: {:?}", container.name);
    }

    Ok(())
}
