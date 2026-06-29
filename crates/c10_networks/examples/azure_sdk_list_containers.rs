//! Azure SDK for Rust —— 列出 Storage 容器示例
//!
//! 本示例演示如何使用 `azure_identity::DeveloperToolsCredential` 获取 Entra ID token，
//! 并通过 `azure_storage_blob::BlobServiceClient` 列出存储账户下的容器。
//!
//! 运行时需要有效的 Azure 凭证（如已登录的 Azure CLI / azd）。
//! 可通过 `AZURE_STORAGE_ACCOUNT` 环境变量指定存储账户名称。
//! 本示例主要用于编译检查，运行时若无凭证将连接失败。

use azure_core::http::Url;
use azure_identity::DeveloperToolsCredential;
use azure_storage_blob::BlobServiceClient;
use futures::TryStreamExt;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let account = std::env::var("AZURE_STORAGE_ACCOUNT").unwrap_or_else(|_| "myaccount".into());
    let endpoint = format!("https://{account}.blob.core.windows.net/");

    let credential = DeveloperToolsCredential::new(None)?;
    let service_client = BlobServiceClient::new(Url::parse(&endpoint)?, Some(credential), None)?;

    let mut pager = service_client.list_containers(None)?;
    while let Some(container) = pager.try_next().await? {
        println!("✅ 容器: {container:?}");
    }

    Ok(())
}
