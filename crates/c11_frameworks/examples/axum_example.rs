// Axum 示例
// 运行命令: cargo run --example axum_example --features axum

use axum::{
    extract::{Path, State},
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::net::TcpListener;

#[derive(Deserialize, Serialize, Clone)]
struct User {
    id: u32,
    name: String,
    email: String,
}

#[derive(Deserialize)]
struct CreateUser {
    name: String,
    email: String,
}

// 应用状态
#[derive(Clone)]
struct AppState {
    users: Arc<Mutex<HashMap<u32, User>>>,
}

impl AppState {
    fn new() -> Self {
        Self {
            users: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

async fn get_user(Path(id): Path<u32>, State(state): State<AppState>) -> Result<Json<User>, StatusCode> {
    let users = state.users.lock().unwrap();
    match users.get(&id) {
        Some(user) => Ok(Json(user.clone())),
        None => Err(StatusCode::NOT_FOUND),
    }
}

async fn create_user(State(state): State<AppState>, Json(payload): Json<CreateUser>) -> Result<Json<User>, StatusCode> {
    let mut users = state.users.lock().unwrap();
    let id = users.len() as u32 + 1;
    let user = User {
        id,
        name: payload.name,
        email: payload.email,
    };
    users.insert(id, user.clone());
    Ok(Json(user))
}

async fn list_users(State(state): State<AppState>) -> Json<Vec<User>> {
    let users = state.users.lock().unwrap();
    Json(users.values().cloned().collect())
}

async fn health_check() -> &'static str {
    "服务健康"
}

#[tokio::main]
async fn main() {
    let app_state = AppState::new();
    
    let app = Router::new()
        .route("/api/v1/users/:id", get(get_user))
        .route("/api/v1/users", post(create_user))
        .route("/api/v1/users", get(list_users))
        .route("/api/v1/health", get(health_check))
        .with_state(app_state);

    let listener = TcpListener::bind("0.0.0.0:3000").await.unwrap();
    println!("启动 Axum 服务器在 http://0.0.0.0:3000");
    
    axum::serve(listener, app).await.unwrap();
}
