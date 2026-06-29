//! meilisearch-sdk 基本搜索示例
//!
//! 运行时需要 Meilisearch 服务。默认连接 `http://localhost:7700`；
//! 可通过 `MEILISEARCH_URL` 环境变量覆盖，通过 `MEILISEARCH_API_KEY` 设置密钥。
//! 本示例仅做编译检查用，运行时若无服务将连接失败。

use meilisearch_sdk::client::Client;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct Movie {
    id: u64,
    title: String,
    genres: Vec<String>,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let url = std::env::var("MEILISEARCH_URL").unwrap_or_else(|_| "http://localhost:7700".into());
    let api_key = std::env::var("MEILISEARCH_API_KEY").ok();

    let client = Client::new(&url, api_key.as_deref())?;
    let index = client.index("rust_learning_movies");

    // 配置可过滤字段（仅需执行一次，会触发索引重建）
    let task = index.set_filterable_attributes(&["genres"]).await?;
    let _ = client.wait_for_task(task, None, None).await?;

    // 添加文档，primary key 为 "id"
    let docs = vec![
        Movie {
            id: 1,
            title: "Carol".into(),
            genres: vec!["Romance".into(), "Drama".into()],
        },
        Movie {
            id: 2,
            title: "Wonder Woman".into(),
            genres: vec!["Action".into(), "Adventure".into()],
        },
        Movie {
            id: 3,
            title: "Mad Max: Fury Road".into(),
            genres: vec!["Adventure".into(), "Science Fiction".into()],
        },
    ];
    let task = index.add_documents(&docs, Some("id")).await?;
    let _ = client.wait_for_task(task, None, None).await?;

    // 基本搜索（Meilisearch 支持拼写容错）
    let results = index
        .search()
        .with_query("caorl")
        .execute::<Movie>()
        .await?;
    println!("typo-tolerant hits: {:?}", results.hits);

    // 带过滤条件的搜索
    let filtered = index
        .search()
        .with_query("wonder")
        .with_filter("genres = Action")
        .execute::<Movie>()
        .await?;
    println!("filtered hits: {:?}", filtered.hits);

    Ok(())
}
