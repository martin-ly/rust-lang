//! mongodb-rust-driver 3.x 聚合管道与变更流骨架示例
//!
//! 运行时需要 MongoDB 服务。默认连接 localhost:27017；可通过 MONGODB_URI 环境变量覆盖。
//! 变更流需要副本集或分片拓扑，单节点 mongod 不支持。
//! 本示例仅做编译检查用，运行时若无服务将连接失败。

use futures::stream::TryStreamExt;
use mongodb::{
    bson::{doc, Document},
    options::ClientOptions,
    Client,
};

#[tokio::main]
async fn main() -> mongodb::error::Result<()> {
    let uri = std::env::var("MONGODB_URI").unwrap_or_else(|_| "mongodb://localhost:27017".into());

    let client_options = ClientOptions::parse(uri).await?;
    let client = Client::with_options(client_options)?;
    let db = client.database("rust_learning");
    let coll: mongodb::Collection<Document> = db.collection("c10_networks_events");

    // Aggregation pipeline: match -> group -> sort
    let pipeline = vec![
        doc! { "$match": { "status": "active" } },
        doc! {
            "$group": {
                "_id": "$category",
                "total": { "$sum": "$amount" },
                "count": { "$sum": 1 },
            }
        },
        doc! { "$sort": { "total": -1 } },
    ];

    let mut cursor = coll.aggregate(pipeline).await?;
    while let Some(doc) = cursor.try_next().await? {
        println!("aggregation result: {:?}", doc);
    }

    // Change stream skeleton
    let mut change_stream = coll.watch().await?;
    println!("change stream started; waiting for events...");
    while let Some(event) = change_stream.next_if_any().await? {
        println!(
            "change event: op={:?}, full_document={:?}",
            event.operation_type, event.full_document
        );
    }

    Ok(())
}
