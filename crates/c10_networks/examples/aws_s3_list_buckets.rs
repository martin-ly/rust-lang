//! AWS S3 列桶示例
//!
//! 本示例演示如何使用 `aws-config` 与 `aws-sdk-s3` 列出当前凭证可访问的 S3 Bucket。
//! 运行时需要有效的 AWS 凭证（例如通过环境变量或 `~/.aws/credentials` 配置）。
//! 若凭证不可用，程序将干净地返回错误。
//!
//! 本示例主要用于编译检查，不依赖真实模型文件。

use anyhow::Result;

#[tokio::main]
async fn main() -> Result<()> {
    // 从环境 / 配置文件加载默认凭证链与区域。
    let config = aws_config::load_defaults(aws_config::BehaviorVersion::latest()).await;
    let client = aws_sdk_s3::Client::new(&config);

    // 发送 ListBuckets 请求。
    let resp = client.list_buckets().send().await?;

    println!("📦 S3 Buckets:");
    for bucket in resp.buckets() {
        if let Some(name) = bucket.name() {
            println!("  - {}", name);
        }
    }

    Ok(())
}
