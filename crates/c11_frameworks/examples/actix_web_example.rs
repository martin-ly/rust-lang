// Actix Web 示例
// 运行命令: cargo run --example actix_web_example --features actix-web

use actix_web::{web, App, HttpServer, Result, middleware::Logger, HttpResponse};
use serde::{Deserialize, Serialize};
use std::sync::Mutex;
use std::collections::HashMap;

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

// 简单的内存存储
type UserStorage = Mutex<HashMap<u32, User>>;

async fn get_user(path: web::Path<u32>, data: web::Data<UserStorage>) -> Result<HttpResponse> {
    let users = data.lock().unwrap();
    match users.get(&path.into_inner()) {
        Some(user) => Ok(HttpResponse::Ok().json(user)),
        None => Ok(HttpResponse::NotFound().json("用户不存在")),
    }
}

async fn create_user(user: web::Json<CreateUser>, data: web::Data<UserStorage>) -> Result<HttpResponse> {
    let mut users = data.lock().unwrap();
    let id = users.len() as u32 + 1;
    let new_user = User {
        id,
        name: user.name.clone(),
        email: user.email.clone(),
    };
    users.insert(id, new_user.clone());
    Ok(HttpResponse::Created().json(new_user))
}

async fn list_users(data: web::Data<UserStorage>) -> Result<HttpResponse> {
    let users = data.lock().unwrap();
    let user_list: Vec<User> = users.values().cloned().collect();
    Ok(HttpResponse::Ok().json(user_list))
}

async fn health_check() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json("服务健康"))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    // env_logger::init(); // 需要启用logging特性
    
    let user_storage = web::Data::new(UserStorage::new(HashMap::new()));
    
    println!("启动 Actix Web 服务器在 http://127.0.0.1:8080");
    
    HttpServer::new(move || {
        App::new()
            .app_data(user_storage.clone())
            .wrap(Logger::default())
            .service(
                web::scope("/api/v1")
                    .route("/users/{id}", web::get().to(get_user))
                    .route("/users", web::post().to(create_user))
                    .route("/users", web::get().to(list_users))
                    .route("/health", web::get().to(health_check))
            )
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
