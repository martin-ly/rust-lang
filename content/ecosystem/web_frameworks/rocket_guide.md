# Rocket 框架指南

> **定位**: Rust 声明式 Web 框架，宏驱动开发的典范
> **版本**: Rocket 0.5.x (兼容 Rust 1.96.0+)
> **适用场景**: 快速 API 开发、类型安全路由、学术/原型项目

---

## 📋 目录

- [Rocket 框架指南](#rocket-框架指南)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [路由 (Route)](#路由-route)
    - [守卫 (Guard)](#守卫-guard)
    - [公平器 (Fairing)](#公平器-fairing)
  - [🚀 宏驱动的声明式路由](#-宏驱动的声明式路由)
    - [动态参数](#动态参数)
    - [请求方法](#请求方法)
    - [数据获取](#数据获取)
  - [📝 表单验证](#-表单验证)
  - [🗄️ 状态管理](#️-状态管理)
  - [📊 与 Axum / Actix-web 对比](#-与-axum--actix-web-对比)
  - [📐 选择决策树](#-选择决策树)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 核心概念

Rocket 的设计哲学是**通过宏将声明式语法嵌入 Rust**，让路由、验证和中间件看起来像配置而非代码：

```text
┌─────────────────────────────────────────┐
│           Rocket Application            │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐    │
│  │ #[get]  │ │ #[post] │ │ #[put]  │    │  ← 路由宏
│  │  路由   │ │  路由   │ │  路由    │    │
│  └────┬────┘ └────┬────┘ └────┬────┘    │
│       └─────────────┴─────────────┘     │
│              ↓ Guard 类型检查            │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐│
│  │ Form<T> │   │ Json<T> │   │ State<T>││  ← 请求守卫
│  └────┬────┘   └────┬────┘   └────┬────┘│
│       └─────────────┴─────────────┘     │
│              ↓ Fairing 生命周期          │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐    │
│  │ Attach  │ │ Launch  │ │ Request │    │  ← 公平器
│  │ (挂载)  │ │ (启动)   │ │ (请求)  │    │
│  └─────────┘ └─────────┘ └─────────┘    │
└─────────────────────────────────────────┘
```
### 路由 (Route)

使用属性宏直接标注在 Handler 函数上：

```rust
#[macro_use] extern crate rocket;

#[get("/")]
fn index() -> &'static str {
    "Hello, Rocket!"
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/", routes![index])
}
```
**特点**:

- 路由即代码，编译时验证路径格式
- 自动推导 Content-Type
- 函数签名即 API 契约

### 守卫 (Guard)

Guard 是实现 `FromRequest` 的类型，用于**安全地提取请求信息**：

```rust
use rocket::request::{FromRequest, Outcome, Request};
use rocket::http::Status;

// 自定义认证守卫
pub struct ApiKey<'r>(&'r str);

#[derive(Debug)]
pub enum ApiKeyError {
    Missing,
    Invalid,
}

#[rocket::async_trait]
impl<'r> FromRequest<'r> for ApiKey<'r> {
    type Error = ApiKeyError;

    async fn from_request(req: &'r Request<'_>) -> Outcome<Self, Self::Error> {
        match req.headers().get_one("x-api-key") {
            None => Outcome::Error((Status::Unauthorized, ApiKeyError::Missing)),
            Some(key) if is_valid(key) => Outcome::Success(ApiKey(key)),
            Some(_) => Outcome::Error((Status::Unauthorized, ApiKeyError::Invalid)),
        }
    }
}

// 使用守卫
#[get("/protected")]
fn protected(key: ApiKey<'_>) -> String {
    format!("Access granted with key: {}", key.0)
}
```
### 公平器 (Fairing)

Fairing 是 Rocket 的中间件机制，在应用生命周期特定点介入：

```rust
use rocket::{ fairing::{Fairing, Info, Kind}, Request, Response, Data };
use rocket::http::Status;

pub struct RequestTimer;

#[rocket::async_trait]
impl Fairing for RequestTimer {
    fn info(&self) -> Info {
        Info {
            name: "Request Timer",
            kind: Kind::Request | Kind::Response,
        }
    }

    async fn on_request(&self, req: &mut Request<'_>, _data: &mut Data<'_>) {
        req.local_cache(|| std::time::Instant::now());
    }

    async fn on_response<'r>(&self, req: &'r Request<'_>, res: &mut Response<'r>) {
        let start = req.local_cache(|| std::time::Instant::now());
        let duration = start.elapsed();
        println!("Request took: {:?}", duration);
    }
}

// 挂载 Fairing
#[launch]
fn rocket() -> _ {
    rocket::build()
        .attach(RequestTimer)
        .attach(rocket::fairing::AdHoc::on_response("CORS", |_req, res| {
            Box::pin(async move {
                res.set_header(rocket::http::Header::new(
                    "Access-Control-Allow-Origin", "*"
                ));
            })
        }))
}
```
---

## 🚀 宏驱动的声明式路由

### 动态参数

```rust
#[get("/user/<id>")]
fn user(id: u64) -> String {
    format!("User ID: {}", id)
}

// 多个参数
#[get("/user/<id>/post/<slug>")]
fn user_post(id: u64, slug: String) -> String {
    format!("User {} - Post: {}", id, slug)
}

// 可选参数 + 正则约束
#[get("/files/<path..>")]
fn files(path: PathBuf) -> String {
    format!("Path: {:?}", path)
}

// 参数守卫: 仅匹配数字
#[get("/item/<id>")]
fn item(id: u32) -> String {
    format!("Item: {}", id)
}
```
### 请求方法

```rust
#[post("/users", data = "<user>")]
async fn create_user(user: Form<UserInput<'_>>) -> Status {
    // 创建用户
    Status::Created
}

#[put("/users/<id>", data = "<user>")]
async fn update_user(id: u64, user: Json<UpdateUser>) -> Json<User> {
    // 更新用户
    Json(User { id, name: user.name.clone() })
}

#[delete("/users/<id>")]
fn delete_user(id: u64) -> Status {
    // 删除用户
    Status::NoContent
}

#[patch("/users/<id>", data = "<patch>")]
fn patch_user(id: u64, patch: Json<PatchUser>) -> Json<User> {
    // 部分更新
    Json(User { id, ..Default::default() })
}
```
### 数据获取

```rust
use rocket::serde::{Deserialize, Serialize, json::Json};
use rocket::form::Form;

#[derive(Deserialize)]
#[serde(crate = "rocket::serde")]
struct LoginRequest<'r> {
    username: &'r str,
    password: &'r str,
}

#[derive(Serialize)]
#[serde(crate = "rocket::serde")]
struct LoginResponse {
    token: String,
}

// JSON 请求体
#[post("/login", format = "json", data = "<req>")]
async fn login(req: Json<LoginRequest<'_>>) -> Json<LoginResponse> {
    Json(LoginResponse {
        token: generate_token(req.username),
    })
}

// 查询参数
#[get("/search?term&limit")]
fn search(term: &str, limit: Option<u8>) -> String {
    let limit = limit.unwrap_or(10);
    format!("Search {} with limit {}", term, limit)
}
```
---

## 📝 表单验证

```rust
use rocket::form::{Form, FromForm, validation};

#[derive(FromForm)]
struct Registration<'r> {
    #[field(validate = len(3..20))]
    username: &'r str,
    #[field(validate = contains('@').or_else(msg!("must be an email")))]
    email: &'r str,
    #[field(validate = len(8..).or_else(msg!("too short")))]
    password: &'r str,
    #[field(validate = eq(self.password))]
    confirm_password: &'r str,
}

#[post("/register", data = "<form>")]
fn register(form: Form<Registration<'_>>) -> String {
    format!("Registered: {}", form.username)
}
```
**自定义验证器**:

```rust
use rocket::form::Error;

fn strong_password<'v>(password: &str) -> form::Result<'v, ()> {
    if password.len() < 12 {
        return Err(Error::validation("password must be at least 12 characters"))?;
    }
    if !password.chars().any(|c| c.is_ascii_uppercase()) {
        return Err(Error::validation("must contain uppercase letter"))?;
    }
    Ok(())
}
```
---

## 🗄️ 状态管理

Rocket 使用 `State` 管理全局共享状态：

```rust
use rocket::State;
use std::sync::atomic::{AtomicU64, Ordering};

struct HitCount {
    count: AtomicU64,
}

#[get("/count")]
fn count(hit_count: &State<HitCount>) -> String {
    let count = hit_count.count.fetch_add(1, Ordering::Relaxed);
    format!("Hits: {}", count)
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .manage(HitCount { count: AtomicU64::new(0) })
        .mount("/", routes![count])
}
```
**数据库状态** (使用 sqlx):

```rust
struct Db(sqlx::PgPool);

#[get("/users/<id>")]
async fn get_user(db: &State<Db>, id: i64) -> Option<Json<User>> {
    sqlx::query_as!(User, "SELECT * FROM users WHERE id = $1", id)
        .fetch_one(&db.0)
        .await
        .ok()
        .map(Json)
}

#[launch]
async fn rocket() -> _ {
    let pool = sqlx::PgPool::connect(&std::env::var("DATABASE_URL").unwrap())
        .await
        .unwrap();

    rocket::build()
        .manage(Db(pool))
        .mount("/", routes![get_user])
}
```
---

## 📊 与 Axum / Actix-web 对比

| 维度 | Rocket | Axum | Actix-web |
|------|--------|------|-----------|
| **路由风格** | 宏驱动 (声明式) | 函数式 (编程式) | 配置式 |
| **学习曲线** | 低 (直觉性强) | 中等 | 中等 |
| **编译速度** | 较慢 (宏展开复杂) | 较快 | 中等 |
| **中间件** | Fairing (有限) | Tower Layer (丰富) | Transform (丰富) |
| **异步运行时** | tokio (内置) | tokio (原生) | actix-rt |
| **Handler 签名** | 多种类型自动推导 | 函数 + Extractor | 多种类型 |
| **生态成熟度** | 良好 | 快速增长 | 非常成熟 |
| **生产部署** | 适合中小型 | 适合中大型 | 适合所有规模 |

---

## 📐 选择决策树

```text
偏好声明式 / 宏驱动语法? ──是──→ Rocket
                └──否──→ 需要深度 Tower 生态集成? ──是──→ Axum
                                      └──否──→ 需要最高成熟度 / Actor 模型? ──是──→ Actix-web
                                                        └──否──→ Axum (默认推荐)
```
**何时选 Rocket**:

- ✅ 喜欢声明式、接近其他语言框架的 API 风格
- ✅ 快速原型开发或学术项目
- ✅ 团队有 Ruby on Rails / Laravel 背景
- ✅ 需要编译时路由验证但不想处理复杂类型体操

**何时不选 Rocket**:

- ❌ 极度关注编译速度
- ❌ 需要复杂的中间件链
- ❌ 需要与 Tower/gRPC 生态深度整合

---

## 🔗 参考资源

- [Rocket 官方文档](https://rocket.rs/)
- [Rocket GitHub](https://github.com/SergioBenitez/Rocket)
- [Rocket 指南 - 状态管理](https://rocket.rs/guide/v0.5/state/)
- [Actix-web vs Axum 对比](actix_web_vs_axum.md)
- [项目 C10 网络模块](../../crates/c10_networks)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
