//! mongodb-rust-driver 3.x 基本 CRUD 示例
//!
//! 运行时需要 MongoDB 服务。默认连接 localhost:27017；可通过 MONGODB_URI 环境变量覆盖。
//! 本示例仅做编译检查用，运行时若无服务将连接失败。

use mongodb::{
    bson::{doc, Document},
    options::{ClientOptions, IndexOptions},
    Client, IndexModel,
};

#[tokio::main]
async fn main() -> mongodb::error::Result<()> {
    let uri = std::env::var("MONGODB_URI").unwrap_or_else(|_| "mongodb://localhost:27017".into());

    let client_options = ClientOptions::parse(uri).await?;
    let client = Client::with_options(client_options)?;
    let db = client.database("rust_learning");
    let coll: mongodb::Collection<Document> = db.collection("c10_networks_demo");

    // Insert
    coll.insert_one(doc! { "name": "rust", "score": 95 }).await?;

    // Find one
    if let Some(found) = coll.find_one(doc! { "name": "rust" }).await? {
        println!("found: {:?}", found);
    }

    // Update
    coll.update_one(
        doc! { "name": "rust" },
        doc! { "$set": { "score": 100 } },
    )
    .await?;

    // Create a unique index on `name`
    let index = IndexModel::builder()
        .keys(doc! { "name": 1 })
        .options(IndexOptions::builder().unique(true).build())
        .build();
    coll.create_index(index).await?;

    // Delete
    coll.delete_one(doc! { "name": "rust" }).await?;

    Ok(())
}
