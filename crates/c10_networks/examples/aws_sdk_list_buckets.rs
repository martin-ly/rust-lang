//! AWS SDK for Rust —— 列出 S3 Bucket 示例
//!
//! 本示例演示如何使用 `aws-config` 加载默认凭证链与区域配置，
//! 并通过 `aws-sdk-s3` 调用 `list_buckets`。
//!
//! 运行时需要有效的 AWS 凭证（环境变量、~/.aws/credentials 或 IAM Role）。
//! 本示例主要用于编译检查，运行时若无凭证将连接失败。

use aws_config::meta::region::RegionProviderChain;
use aws_config::{BehaviorVersion, Region};
use aws_sdk_s3::Client;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let region_provider = RegionProviderChain::default_provider().or_else(Region::new("us-east-1"));
    let config = aws_config::defaults(BehaviorVersion::latest())
        .region(region_provider)
        .load()
        .await;
    let client = Client::new(&config);

    let resp = client.list_buckets().send().await?;
    println!("✅ 查询成功，Bucket 列表: {:?}", resp.buckets());

    Ok(())
}
