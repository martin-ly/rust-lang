# GraphQL - 现代化API查询语言

## 📋 目录

- [GraphQL - 现代化API查询语言](#graphql---现代化api查询语言)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [async-graphql](#async-graphql)
    - [基础 Schema](#基础-schema)
    - [Mutation](#mutation)
    - [与 Axum 集成](#与-axum-集成)
  - [Juniper](#juniper)
    - [基础示例](#基础示例)
  - [实战示例](#实战示例)
    - [完整的博客 API](#完整的博客-api)
  - [参考资源](#参考资源)

---

## 概述

GraphQL 是一种用于 API 的查询语言，允许客户端精确指定所需数据。

### 核心依赖

```toml
[dependencies]
# async-graphql - 现代化 GraphQL 服务器
async-graphql = "7.0"
async-graphql-axum = "7.0"

# Juniper - 成熟的 GraphQL 实现
juniper = "0.16"
juniper_axum = "0.1"
```

---

## async-graphql

### 基础 Schema

```rust
use async_graphql::*;

struct Query;

#[Object]
impl Query {
    async fn hello(&self) -> &str {
        "Hello, GraphQL!"
    }
    
    async fn user(&self, id: ID) -> Result<User> {
        Ok(User {
            id: id.clone(),
            name: format!("User {}", id),
            email: format!("user{}@example.com", id),
        })
    }
}

#[derive(SimpleObject)]
struct User {
    id: ID,
    name: String,
    email: String,
}

#[tokio::main]
async fn main() {
    let schema = Schema::new(Query, EmptyMutation, EmptySubscription);
    
    let query = r#"
        query {
            hello
            user(id: "1") {
                id
                name
                email
            }
        }
    "#;
    
    let result = schema.execute(query).await;
    println!("{}", serde_json::to_string_pretty(&result).unwrap());
}
```

### Mutation

```rust
use async_graphql::*;

struct Mutation;

#[Object]
impl Mutation {
    async fn create_user(&self, name: String, email: String) -> Result<User> {
        Ok(User {
            id: ID::from("new_id"),
            name,
            email,
        })
    }
}

#[derive(SimpleObject)]
struct User {
    id: ID,
    name: String,
    email: String,
}
```

### 与 Axum 集成

```rust
use axum::{
    Router,
    routing::get,
    extract::State,
};
use async_graphql::{
    EmptyMutation, EmptySubscription, Object, Schema, ID,
};
use async_graphql_axum::{GraphQLRequest, GraphQLResponse};
use std::sync::Arc;

struct Query;

#[Object]
impl Query {
    async fn hello(&self) -> &str {
        "Hello from GraphQL!"
    }
}

type MySchema = Schema<Query, EmptyMutation, EmptySubscription>;

async fn graphql_handler(
    State(schema): State<Arc<MySchema>>,
    req: GraphQLRequest,
) -> GraphQLResponse {
    schema.execute(req.into_inner()).await.into()
}

#[tokio::main]
async fn main() {
    let schema = Arc::new(Schema::new(Query, EmptyMutation, EmptySubscription));
    
    let app = Router::new()
        .route("/graphql", get(graphql_handler).post(graphql_handler))
        .with_state(schema);
    
    println!("GraphQL 服务器运行在 http://127.0.0.1:8000/graphql");
}
```

---

## Juniper

### 基础示例

```rust
use juniper::{graphql_object, EmptyMutation, EmptySubscription, RootNode};

struct Query;

#[graphql_object]
impl Query {
    fn api_version() -> &'static str {
        "1.0"
    }
}

type Schema = RootNode<'static, Query, EmptyMutation<()>, EmptySubscription<()>>;

fn main() {
    let schema = Schema::new(Query, EmptyMutation::new(), EmptySubscription::new());
    
    let query = r#"{ apiVersion }"#;
    let (result, _errors) = juniper::execute_sync(query, None, &schema, &juniper::Variables::new(), &()).unwrap();
    
    println!("{}", serde_json::to_string_pretty(&result).unwrap());
}
```

---

## 实战示例

### 完整的博客 API

```rust
use async_graphql::*;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

type DB = Arc<Mutex<HashMap<ID, Post>>>;

struct Query;

#[Object]
impl Query {
    async fn post(&self, ctx: &Context<'_>, id: ID) -> Result<Post> {
        let db = ctx.data::<DB>()?;
        db.lock()
            .await
            .get(&id)
            .cloned()
            .ok_or_else(|| "Post not found".into())
    }
    
    async fn posts(&self, ctx: &Context<'_>) -> Result<Vec<Post>> {
        let db = ctx.data::<DB>()?;
        Ok(db.lock().await.values().cloned().collect())
    }
}

struct Mutation;

#[Object]
impl Mutation {
    async fn create_post(
        &self,
        ctx: &Context<'_>,
        title: String,
        content: String,
    ) -> Result<Post> {
        let db = ctx.data::<DB>()?;
        let id = ID::from(uuid::Uuid::new_v4().to_string());
        
        let post = Post { id: id.clone(), title, content };
        db.lock().await.insert(id, post.clone());
        
        Ok(post)
    }
}

#[derive(Clone, SimpleObject)]
struct Post {
    id: ID,
    title: String,
    content: String,
}
```

---

## 参考资源

- [async-graphql 文档](https://async-graphql.github.io/async-graphql/)
- [Juniper 官网](https://graphql-rust.github.io/)
