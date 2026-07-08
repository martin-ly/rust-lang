//! surrealdb 远程文档-图数据库 CRUD 示例
//!
//! 运行时需要 SurrealDB 服务。默认连接 `ws://127.0.0.1:8000`；
//! 可通过 `SURREALDB_URL` 环境变量覆盖。
//! 默认使用 root/root 认证，可通过 `SURREALDB_USER` / `SURREALDB_PASS` 覆盖。
//! 本示例仅做编译检查用，运行时若无服务将连接失败。

use serde::{Deserialize, Serialize};
use surrealdb::Surreal;
use surrealdb::engine::remote::ws::Ws;
use surrealdb::opt::auth::Root;
use surrealdb::types::SurrealValue;

#[derive(Debug, Serialize, Deserialize, SurrealValue)]
struct Person {
    name: String,
    age: u8,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let url = std::env::var("SURREALDB_URL").unwrap_or_else(|_| "ws://127.0.0.1:8000".into());
    let username = std::env::var("SURREALDB_USER").unwrap_or_else(|_| "root".into());
    let password = std::env::var("SURREALDB_PASS").unwrap_or_else(|_| "root".into());

    let db = Surreal::new::<Ws>(&url).await?;

    db.signin(Root {
        username: username.clone(),
        password: password.clone(),
    })
    .await?;

    db.use_ns("rust_learning")
        .use_db("c10_networks_demo")
        .await?;

    // CREATE：插入一条随机 ID 的记录（surrealdb 2.x 返回 Option<T>）
    let created: Option<Person> = db
        .create("person")
        .content(Person {
            name: "Alice".into(),
            age: 30,
        })
        .await?;
    println!("created: {:?}", created);

    // SELECT：查询所有 person
    let people: Vec<Person> = db.select("person").await?;
    println!("selected: {:?}", people);

    // UPDATE：部分更新指定记录
    let updated: Option<Person> = db
        .update(("person", "alice"))
        .merge(serde_json::json!({ "age": 31 }))
        .await?;
    println!("updated: {:?}", updated);

    // QUERY：使用 SurrealQL 与参数化查询
    let mut result = db
        .query("SELECT * FROM person WHERE age > $min")
        .bind(("min", 25))
        .await?;
    let adults: Vec<Person> = result.take(0)?;
    println!("adults: {:?}", adults);

    Ok(())
}
