use axum::{routing::get, Router, extract::State, Json};
use serde::{Deserialize, Serialize};
// use sqlx::{Pool, Postgres, postgres::PgPoolOptions}; // 暂时注释以避免链接冲突
use std::{net::SocketAddr, time::Duration};
use tokio::time::{timeout, sleep};
use tracing_subscriber::EnvFilter;
use reqwest::Client;

#[derive(Clone)]
struct AppState { 
    // db: Pool<Postgres>, // 暂时注释以避免链接冲突
    http_client: Client,
}

#[derive(Serialize, Deserialize)]
#[allow(dead_code)] // 暂时注释数据库功能时未使用
struct Item { id: i64, name: String }

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .init();

    // 数据库：暂时注释以避免链接冲突
    // 实际使用时需要配置真实的 PostgreSQL 连接字符串
    // let db_url = std::env::var("DATABASE_URL")
    //     .unwrap_or_else(|_| "postgresql://user:pass@localhost/db".to_string());
    // let db = PgPoolOptions::new()
    //     .max_connections(5)
    //     .connect(&db_url).await?;
    // sqlx::query("CREATE TABLE IF NOT EXISTS items (id SERIAL PRIMARY KEY, name TEXT NOT NULL)")
    //     .execute(&db).await?;

    let http_client = Client::builder()
        .timeout(Duration::from_secs(10))
        .build()?;

    let app = Router::new()
        .route("/health", get(health))
        // .route("/items", get(list_items).post(create_item)) // 暂时注释数据库相关路由
        .route("/external", get(fetch_external_data))
        .with_state(AppState { http_client });

    let addr: SocketAddr = "127.0.0.1:3000".parse().unwrap();
    tracing::info!(%addr, "listening");
    let listener = tokio::net::TcpListener::bind(&addr).await?;
    axum::serve(listener, app).await?;
    Ok(())
}

async fn health() -> &'static str { "ok" }

// 暂时注释数据库相关函数以避免链接冲突
// async fn list_items(State(state): State<AppState>) -> anyhow::Result<Json<Vec<Item>>, axum::http::StatusCode> {
//     let fut = async {
//         let rows = sqlx::query_as::<_, Item>("SELECT id, name FROM items ORDER BY id")
//             .fetch_all(&state.db).await?;
//         Ok::<_, anyhow::Error>(Json(rows))
//     };
//     match timeout(Duration::from_secs(2), fut).await {
//         Ok(Ok(json)) => Ok(json),
//         Ok(Err(_)) => Err(axum::http::StatusCode::INTERNAL_SERVER_ERROR),
//         Err(_) => Err(axum::http::StatusCode::GATEWAY_TIMEOUT),
//     }
// }

// async fn create_item(State(state): State<AppState>, Json(mut item): Json<Item>) -> anyhow::Result<Json<Item>, axum::http::StatusCode> {
//     let fut = async {
//         let rec = sqlx::query!("INSERT INTO items(name) VALUES ($1) RETURNING id", item.name)
//             .fetch_one(&state.db).await?;
//         let id: i64 = rec.get("id");
//         item.id = id;
//         Ok::<_, anyhow::Error>(Json(item))
//     };
//     match timeout(Duration::from_secs(2), fut).await {
//         Ok(Ok(json)) => Ok(json),
//         Ok(Err(_)) => Err(axum::http::StatusCode::INTERNAL_SERVER_ERROR),
//         Err(_) => Err(axum::http::StatusCode::GATEWAY_TIMEOUT),
//     }
// }

/// 外部 HTTP 请求示例：带重试与指数退避
async fn fetch_external_data(State(state): State<AppState>) -> anyhow::Result<Json<serde_json::Value>, axum::http::StatusCode> {
    let fut = async {
        let url = "https://httpbin.org/json";
        let mut retries = 3;
        let mut delay = Duration::from_millis(100);
        
        loop {
            match state.http_client.get(url).send().await {
                Ok(resp) => {
                    if resp.status().is_success() {
                        let json: serde_json::Value = resp.json().await?;
                        tracing::info!("external fetch success");
                        return Ok(Json(json));
                    } else {
                        tracing::warn!(status = %resp.status(), "external fetch failed");
                    }
                }
                Err(e) => {
                    tracing::warn!(error = %e, "external fetch error");
                }
            }
            
            if retries == 0 {
                return Err(anyhow::anyhow!("max retries exceeded"));
            }
            
            retries -= 1;
            sleep(delay).await;
            delay *= 2; // 指数退避
        }
    };
    
    match timeout(Duration::from_secs(15), fut).await {
        Ok(Ok(json)) => Ok(json),
        Ok(Err(_)) => Err(axum::http::StatusCode::BAD_GATEWAY),
        Err(_) => Err(axum::http::StatusCode::GATEWAY_TIMEOUT),
    }
}


