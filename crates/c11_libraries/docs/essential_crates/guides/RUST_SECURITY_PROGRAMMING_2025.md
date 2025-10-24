# Rust 安全编程实战指南 (2025版)

> 从零信任到纵深防御：构建安全可靠的 Rust 应用

## 📊 目录

- [Rust 安全编程实战指南 (2025版)](#rust-安全编程实战指南-2025版)
  - [📊 目录](#-目录)
  - [概述](#概述)
    - [安全原则](#安全原则)
    - [核心依赖](#核心依赖)
  - [密码学基础](#密码学基础)
    - [1. 密码哈希 (Argon2id)](#1-密码哈希-argon2id)
    - [2. 加密与解密 (AES-256-GCM)](#2-加密与解密-aes-256-gcm)
    - [3. 数字签名 (Ed25519)](#3-数字签名-ed25519)
  - [身份认证](#身份认证)
    - [1. JWT 认证 (完整实现)](#1-jwt-认证-完整实现)
    - [2. OAuth2 集成 (GitHub 示例)](#2-oauth2-集成-github-示例)
  - [授权与访问控制](#授权与访问控制)
    - [RBAC (基于角色的访问控制)](#rbac-基于角色的访问控制)
  - [输入验证](#输入验证)
    - [使用 `validator` crate](#使用-validator-crate)
  - [SQL 注入防护](#sql-注入防护)
    - [✅ 安全：参数化查询 (sqlx)](#-安全参数化查询-sqlx)
  - [XSS 防护](#xss-防护)
    - [输出转义](#输出转义)
    - [Content Security Policy (CSP)](#content-security-policy-csp)
  - [CSRF 防护](#csrf-防护)
    - [CSRF Token 实现](#csrf-token-实现)
  - [安全通信](#安全通信)
    - [HTTPS/TLS (rustls)](#httpstls-rustls)
    - [生成自签名证书 (开发环境)](#生成自签名证书-开发环境)
  - [敏感数据保护](#敏感数据保护)
    - [1. 数据库加密 (透明加密)](#1-数据库加密-透明加密)
    - [2. 敏感数据擦除](#2-敏感数据擦除)
  - [安全审计](#安全审计)
    - [1. cargo-audit (依赖漏洞扫描)](#1-cargo-audit-依赖漏洞扫描)
    - [2. cargo-deny (License + 漏洞检查)](#2-cargo-deny-license--漏洞检查)
  - [漏洞扫描](#漏洞扫描)
    - [1. 静态分析 (Clippy + 自定义 Lints)](#1-静态分析-clippy--自定义-lints)
    - [2. 动态分析 (AddressSanitizer)](#2-动态分析-addresssanitizer)
    - [3. Fuzzing (cargo-fuzz)](#3-fuzzing-cargo-fuzz)
  - [最佳实践](#最佳实践)
    - [✅ 推荐做法](#-推荐做法)
  - [常见陷阱](#常见陷阱)
    - [❌ 避免的错误](#-避免的错误)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [核心库文档](#核心库文档)
    - [工具](#工具)
    - [学习资源](#学习资源)
  - [总结](#总结)

---

## 概述

### 安全原则

**OWASP Top 10 (2023) 对应的 Rust 解决方案：**

| OWASP 风险 | Rust 解决方案 | 核心库 |
|-----------|--------------|--------|
| **A01: Broken Access Control** | RBAC/ABAC | `casbin`, `oso` |
| **A02: Cryptographic Failures** | 现代加密算法 | `ring`, `rustls` |
| **A03: Injection** | 参数化查询 | `sqlx`, `diesel` |
| **A04: Insecure Design** | 类型安全 | Rust 类型系统 |
| **A05: Security Misconfiguration** | 安全默认值 | `config`, `dotenvy` |
| **A06: Vulnerable Components** | 依赖审计 | `cargo-audit`, `cargo-deny` |
| **A07: Authentication Failures** | JWT/OAuth2 | `jsonwebtoken`, `oauth2` |
| **A08: Data Integrity Failures** | 签名验证 | `ed25519-dalek` |
| **A09: Logging Failures** | 结构化日志 | `tracing` |
| **A10: SSRF** | URL 白名单 | `url`, `reqwest` |

### 核心依赖

```toml
[dependencies]
# 密码学
ring = "0.17"
rustls = "0.23"
argon2 = "0.5"
sha2 = "0.10"
blake3 = "1.5"

# 认证与授权
jsonwebtoken = "9.3"
oauth2 = "4.4"
tower-sessions = "0.13"

# 输入验证
validator = { version = "0.18", features = ["derive"] }
garde = "0.20"

# SQL 安全
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres"] }

# 防护中间件
tower = "0.4"
tower-http = { version = "0.5", features = ["cors", "trace"] }

# 审计工具
cargo-audit = "0.20"
cargo-deny = "0.16"
```

---

## 密码学基础

### 1. 密码哈希 (Argon2id)

**为什么选择 Argon2id？**

- ✅ 2015年密码哈希竞赛冠军
- ✅ 抵抗 GPU/ASIC 破解
- ✅ 内存密集型算法
- ✅ 参数可调 (时间/内存成本)

```rust
use argon2::{
    password_hash::{rand_core::OsRng, PasswordHash, PasswordHasher, PasswordVerifier, SaltString},
    Argon2,
};

/// 密码哈希配置 (生产环境推荐)
pub fn get_argon2() -> Argon2<'static> {
    Argon2::default()
}

/// 哈希密码
pub fn hash_password(password: &str) -> Result<String, argon2::password_hash::Error> {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = get_argon2();
    
    let password_hash = argon2
        .hash_password(password.as_bytes(), &salt)?
        .to_string();
    
    Ok(password_hash)
}

/// 验证密码
pub fn verify_password(password: &str, password_hash: &str) -> Result<bool, argon2::password_hash::Error> {
    let parsed_hash = PasswordHash::new(password_hash)?;
    let argon2 = get_argon2();
    
    match argon2.verify_password(password.as_bytes(), &parsed_hash) {
        Ok(_) => Ok(true),
        Err(argon2::password_hash::Error::Password) => Ok(false),
        Err(e) => Err(e),
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 注册用户
    let password = "SuperSecret123!";
    let hash = hash_password(password)?;
    println!("Hash: {}", hash);
    
    // 登录验证
    let is_valid = verify_password(password, &hash)?;
    println!("Valid: {}", is_valid);  // true
    
    let is_invalid = verify_password("WrongPassword", &hash)?;
    println!("Invalid: {}", is_invalid);  // false
    
    Ok(())
}
```

**哈希示例：**

```text
$argon2id$v=19$m=19456,t=2,p=1$Bph+GhH0qLzE6XzA5jd7Lg$
  XZdZ9+jdZzQgJqQJqQJqQJqQJqQJqQJqQJqQJqQJqQJqQ
  
参数解释：
- m=19456: 内存成本 (19MB)
- t=2: 时间成本 (迭代次数)
- p=1: 并行度
```

### 2. 加密与解密 (AES-256-GCM)

```rust
use ring::aead::{Aad, BoundKey, Nonce, NonceSequence, OpeningKey, SealingKey, UnboundKey, AES_256_GCM};
use ring::error::Unspecified;
use ring::rand::{SecureRandom, SystemRandom};

/// 自定义 Nonce 序列 (生产环境需要更复杂的实现)
struct CounterNonceSequence(u32);

impl NonceSequence for CounterNonceSequence {
    fn advance(&mut self) -> Result<Nonce, Unspecified> {
        let mut nonce_bytes = vec![0u8; 12];
        nonce_bytes[8..].copy_from_slice(&self.0.to_be_bytes());
        self.0 = self.0.wrapping_add(1);
        Nonce::try_assume_unique_for_key(&nonce_bytes)
    }
}

/// 加密数据
pub fn encrypt(key: &[u8], plaintext: &[u8]) -> Result<Vec<u8>, Unspecified> {
    let unbound_key = UnboundKey::new(&AES_256_GCM, key)?;
    let nonce_sequence = CounterNonceSequence(0);
    let mut sealing_key = SealingKey::new(unbound_key, nonce_sequence);
    
    let mut in_out = plaintext.to_vec();
    sealing_key.seal_in_place_append_tag(Aad::empty(), &mut in_out)?;
    
    Ok(in_out)
}

/// 解密数据
pub fn decrypt(key: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>, Unspecified> {
    let unbound_key = UnboundKey::new(&AES_256_GCM, key)?;
    let nonce_sequence = CounterNonceSequence(0);
    let mut opening_key = OpeningKey::new(unbound_key, nonce_sequence);
    
    let mut in_out = ciphertext.to_vec();
    let plaintext = opening_key.open_in_place(Aad::empty(), &mut in_out)?;
    
    Ok(plaintext.to_vec())
}

// 使用示例
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let rng = SystemRandom::new();
    
    // 生成 256-bit 密钥
    let mut key = vec![0u8; 32];
    rng.fill(&mut key)?;
    
    // 加密
    let plaintext = b"Sensitive data";
    let ciphertext = encrypt(&key, plaintext)?;
    println!("Encrypted: {:?}", ciphertext);
    
    // 解密
    let decrypted = decrypt(&key, &ciphertext)?;
    println!("Decrypted: {}", String::from_utf8_lossy(&decrypted));
    
    Ok(())
}
```

### 3. 数字签名 (Ed25519)

```rust
use ed25519_dalek::{Keypair, Signature, Signer, Verifier};
use rand::rngs::OsRng;

fn main() {
    let mut csprng = OsRng;
    
    // 生成密钥对
    let keypair: Keypair = Keypair::generate(&mut csprng);
    
    // 签名
    let message = b"This is a test message";
    let signature: Signature = keypair.sign(message);
    
    // 验证签名
    assert!(keypair.verify(message, &signature).is_ok());
    
    // 验证失败示例
    let bad_message = b"Wrong message";
    assert!(keypair.verify(bad_message, &signature).is_err());
}
```

---

## 身份认证

### 1. JWT 认证 (完整实现)

```rust
use axum::{
    extract::{Request, State},
    http::{header, StatusCode},
    middleware::Next,
    response::{IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
use jsonwebtoken::{decode, encode, DecodingKey, EncodingKey, Header, Validation};
use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// JWT Claims
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,        // Subject (user ID)
    pub exp: u64,           // Expiration time
    pub iat: u64,           // Issued at
    pub roles: Vec<String>, // User roles
}

impl Claims {
    pub fn new(user_id: String, roles: Vec<String>) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        Self {
            sub: user_id,
            exp: now + 3600, // 1 hour
            iat: now,
            roles,
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Token 生成
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
pub fn generate_token(claims: &Claims, secret: &str) -> Result<String, jsonwebtoken::errors::Error> {
    encode(
        &Header::default(),
        claims,
        &EncodingKey::from_secret(secret.as_ref()),
    )
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Token 验证
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
pub fn verify_token(token: &str, secret: &str) -> Result<Claims, jsonwebtoken::errors::Error> {
    let token_data = decode::<Claims>(
        token,
        &DecodingKey::from_secret(secret.as_ref()),
        &Validation::default(),
    )?;
    
    Ok(token_data.claims)
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 登录请求
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Deserialize)]
struct LoginRequest {
    username: String,
    password: String,
}

#[derive(Serialize)]
struct LoginResponse {
    token: String,
}

async fn login(Json(req): Json<LoginRequest>) -> Result<Json<LoginResponse>, StatusCode> {
    // 1. 验证用户名和密码 (实际应该查数据库)
    if req.username != "admin" || req.password != "password" {
        return Err(StatusCode::UNAUTHORIZED);
    }
    
    // 2. 生成 JWT
    let claims = Claims::new("user_123".to_string(), vec!["admin".to_string()]);
    let token = generate_token(&claims, "your-secret-key")
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    Ok(Json(LoginResponse { token }))
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// JWT 中间件
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn jwt_middleware(
    State(secret): State<String>,
    mut req: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 1. 提取 Authorization header
    let auth_header = req
        .headers()
        .get(header::AUTHORIZATION)
        .and_then(|v| v.to_str().ok())
        .ok_or(StatusCode::UNAUTHORIZED)?;
    
    // 2. 检查 Bearer token
    let token = auth_header
        .strip_prefix("Bearer ")
        .ok_or(StatusCode::UNAUTHORIZED)?;
    
    // 3. 验证 token
    let claims = verify_token(token, &secret).map_err(|_| StatusCode::UNAUTHORIZED)?;
    
    // 4. 将 claims 存入 request extensions
    req.extensions_mut().insert(claims);
    
    Ok(next.run(req).await)
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 受保护的路由
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn protected_route(req: Request) -> impl IntoResponse {
    let claims = req.extensions().get::<Claims>().unwrap();
    
    Json(serde_json::json!({
        "message": "Access granted",
        "user_id": claims.sub,
        "roles": claims.roles,
    }))
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 应用路由
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[tokio::main]
async fn main() {
    let secret = "your-secret-key".to_string();
    
    let app = Router::new()
        .route("/login", post(login))
        .route("/protected", get(protected_route))
        .route_layer(axum::middleware::from_fn_with_state(
            secret.clone(),
            jwt_middleware,
        ))
        .with_state(secret);
    
    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080")
        .await
        .unwrap();
    
    println!("Server running on http://0.0.0.0:8080");
    axum::serve(listener, app).await.unwrap();
}
```

**测试 JWT 认证：**

```bash
# 1. 登录获取 token
curl -X POST http://localhost:8080/login \
  -H "Content-Type: application/json" \
  -d '{"username": "admin", "password": "password"}'

# 响应:
# {"token": "eyJ0eXAiOiJKV1QiLCJhbGc..."}

# 2. 使用 token 访问受保护路由
curl -X GET http://localhost:8080/protected \
  -H "Authorization: Bearer eyJ0eXAiOiJKV1QiLCJhbGc..."

# 响应:
# {"message": "Access granted", "user_id": "user_123", "roles": ["admin"]}
```

### 2. OAuth2 集成 (GitHub 示例)

```rust
use oauth2::{
    basic::BasicClient, AuthUrl, AuthorizationCode, ClientId, ClientSecret, CsrfToken,
    RedirectUrl, Scope, TokenResponse, TokenUrl,
};

async fn oauth2_login() -> Result<String, Box<dyn std::error::Error>> {
    // 1. 配置 OAuth2 客户端
    let client = BasicClient::new(
        ClientId::new("your-client-id".to_string()),
        Some(ClientSecret::new("your-client-secret".to_string())),
        AuthUrl::new("https://github.com/login/oauth/authorize".to_string())?,
        Some(TokenUrl::new("https://github.com/login/oauth/access_token".to_string())?),
    )
    .set_redirect_uri(RedirectUrl::new("http://localhost:8080/auth/callback".to_string())?);
    
    // 2. 生成授权 URL
    let (auth_url, csrf_token) = client
        .authorize_url(CsrfToken::new_random)
        .add_scope(Scope::new("user:email".to_string()))
        .url();
    
    println!("Open this URL: {}", auth_url);
    
    // 3. 用户授权后，GitHub 会重定向到 /auth/callback?code=xxx&state=yyy
    // (这里省略回调处理代码)
    
    // 4. 交换授权码获取 access token
    let code = AuthorizationCode::new("authorization_code_from_callback".to_string());
    let token_result = client.exchange_code(code).request_async(oauth2::reqwest::async_http_client).await?;
    
    let access_token = token_result.access_token().secret();
    println!("Access token: {}", access_token);
    
    Ok(access_token.clone())
}
```

---

## 授权与访问控制

### RBAC (基于角色的访问控制)

```rust
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct User {
    pub id: String,
    pub roles: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Permission {
    pub resource: String,
    pub action: String,
}

pub struct RBAC {
    role_permissions: HashMap<String, HashSet<Permission>>,
}

impl RBAC {
    pub fn new() -> Self {
        let mut role_permissions = HashMap::new();
        
        // 定义角色权限
        let mut admin_perms = HashSet::new();
        admin_perms.insert(Permission { resource: "users".to_string(), action: "read".to_string() });
        admin_perms.insert(Permission { resource: "users".to_string(), action: "write".to_string() });
        admin_perms.insert(Permission { resource: "users".to_string(), action: "delete".to_string() });
        role_permissions.insert("admin".to_string(), admin_perms);
        
        let mut user_perms = HashSet::new();
        user_perms.insert(Permission { resource: "users".to_string(), action: "read".to_string() });
        role_permissions.insert("user".to_string(), user_perms);
        
        Self { role_permissions }
    }
    
    pub fn check_permission(&self, user: &User, resource: &str, action: &str) -> bool {
        for role in &user.roles {
            if let Some(perms) = self.role_permissions.get(role) {
                for perm in perms {
                    if perm.resource == resource && perm.action == action {
                        return true;
                    }
                }
            }
        }
        false
    }
}

// 中间件：权限检查
async fn permission_middleware(
    user: User,
    resource: String,
    action: String,
) -> Result<(), StatusCode> {
    let rbac = RBAC::new();
    
    if rbac.check_permission(&user, &resource, &action) {
        Ok(())
    } else {
        Err(StatusCode::FORBIDDEN)
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    let admin = User {
        id: "1".to_string(),
        roles: vec!["admin".to_string()],
    };
    
    let regular_user = User {
        id: "2".to_string(),
        roles: vec!["user".to_string()],
    };
    
    let rbac = RBAC::new();
    
    // admin 可以删除用户
    assert!(rbac.check_permission(&admin, "users", "delete"));
    
    // regular_user 不能删除用户
    assert!(!rbac.check_permission(&regular_user, "users", "delete"));
}
```

---

## 输入验证

### 使用 `validator` crate

```rust
use validator::{Validate, ValidationError};
use serde::Deserialize;

#[derive(Debug, Deserialize, Validate)]
pub struct RegisterRequest {
    #[validate(length(min = 3, max = 20))]
    pub username: String,
    
    #[validate(email)]
    pub email: String,
    
    #[validate(length(min = 8), custom(function = "validate_password_strength"))]
    pub password: String,
    
    #[validate(range(min = 18, max = 120))]
    pub age: u8,
}

fn validate_password_strength(password: &str) -> Result<(), ValidationError> {
    let has_uppercase = password.chars().any(|c| c.is_uppercase());
    let has_lowercase = password.chars().any(|c| c.is_lowercase());
    let has_digit = password.chars().any(|c| c.is_numeric());
    
    if has_uppercase && has_lowercase && has_digit {
        Ok(())
    } else {
        Err(ValidationError::new("password_weak"))
    }
}

// 在 handler 中使用
async fn register(Json(req): Json<RegisterRequest>) -> Result<StatusCode, (StatusCode, String)> {
    // 验证输入
    req.validate().map_err(|e| {
        (StatusCode::BAD_REQUEST, format!("Validation error: {:?}", e))
    })?;
    
    // 处理注册逻辑...
    Ok(StatusCode::CREATED)
}
```

---

## SQL 注入防护

### ✅ 安全：参数化查询 (sqlx)

```rust
use sqlx::{PgPool, query_as};

#[derive(sqlx::FromRow)]
struct User {
    id: i64,
    username: String,
    email: String,
}

// ✅ 安全：使用参数化查询
async fn get_user_by_username(pool: &PgPool, username: &str) -> Result<Option<User>, sqlx::Error> {
    let user = query_as!(
        User,
        "SELECT id, username, email FROM users WHERE username = $1",
        username
    )
    .fetch_optional(pool)
    .await?;
    
    Ok(user)
}

// ❌ 危险：永远不要这样做！
async fn get_user_unsafe(pool: &PgPool, username: &str) -> Result<Option<User>, sqlx::Error> {
    // 如果 username = "admin' OR '1'='1"，会返回所有用户！
    let query = format!("SELECT id, username, email FROM users WHERE username = '{}'", username);
    // ...
    unimplemented!()
}
```

---

## XSS 防护

### 输出转义

```rust
use askama::Template;

#[derive(Template)]
#[template(path = "user.html")]
struct UserTemplate<'a> {
    username: &'a str,
}

// templates/user.html:
// <h1>Welcome, {{ username }}</h1>
// Askama 会自动转义 HTML

// 如果 username = "<script>alert('XSS')</script>"
// 渲染结果: <h1>Welcome, &lt;script&gt;alert('XSS')&lt;/script&gt;</h1>
```

### Content Security Policy (CSP)

```rust
use tower_http::set_header::SetResponseHeaderLayer;
use http::header;

let app = Router::new()
    .route("/", get(handler))
    .layer(SetResponseHeaderLayer::if_not_present(
        header::CONTENT_SECURITY_POLICY,
        HeaderValue::from_static(
            "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'"
        ),
    ));
```

---

## CSRF 防护

### CSRF Token 实现

```rust
use axum::{
    extract::{Request, State},
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use tower_sessions::{Session, SessionManagerLayer};
use uuid::Uuid;

// 生成 CSRF Token
async fn generate_csrf_token(session: Session) -> Result<String, StatusCode> {
    let token = Uuid::new_v4().to_string();
    session
        .insert("csrf_token", token.clone())
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    Ok(token)
}

// 验证 CSRF Token
async fn verify_csrf_token(
    session: Session,
    provided_token: &str,
) -> Result<(), StatusCode> {
    let stored_token: Option<String> = session
        .get("csrf_token")
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    match stored_token {
        Some(token) if token == provided_token => Ok(()),
        _ => Err(StatusCode::FORBIDDEN),
    }
}

// CSRF 中间件
async fn csrf_middleware(
    session: Session,
    req: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 只检查 POST/PUT/DELETE 请求
    if matches!(req.method(), &http::Method::POST | &http::Method::PUT | &http::Method::DELETE) {
        let csrf_token = req
            .headers()
            .get("X-CSRF-Token")
            .and_then(|v| v.to_str().ok())
            .ok_or(StatusCode::FORBIDDEN)?;
        
        verify_csrf_token(session, csrf_token).await?;
    }
    
    Ok(next.run(req).await)
}
```

---

## 安全通信

### HTTPS/TLS (rustls)

```rust
use axum_server::tls_rustls::RustlsConfig;
use std::net::SocketAddr;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let app = Router::new().route("/", get(|| async { "Hello, HTTPS!" }));
    
    // TLS 配置
    let config = RustlsConfig::from_pem_file("cert.pem", "key.pem").await?;
    
    let addr = SocketAddr::from(([0, 0, 0, 0], 443));
    
    axum_server::bind_rustls(addr, config)
        .serve(app.into_make_service())
        .await?;
    
    Ok(())
}
```

### 生成自签名证书 (开发环境)

```bash
# 使用 openssl
openssl req -x509 -newkey rsa:4096 -nodes \
  -keyout key.pem -out cert.pem -days 365 \
  -subj "/CN=localhost"

# 或使用 mkcert (推荐)
mkcert -install
mkcert localhost 127.0.0.1 ::1
```

---

## 敏感数据保护

### 1. 数据库加密 (透明加密)

```rust
use ring::aead::{Aad, BoundKey, Nonce, NonceSequence, SealingKey, UnboundKey, AES_256_GCM};

#[derive(sqlx::FromRow)]
struct User {
    id: i64,
    username: String,
    #[sqlx(default)]
    ssn_encrypted: Vec<u8>,  // 加密的社会安全号
}

// 存储前加密
async fn create_user(pool: &PgPool, username: &str, ssn: &str) -> Result<(), sqlx::Error> {
    let encrypted_ssn = encrypt_sensitive_data(ssn.as_bytes());
    
    sqlx::query!(
        "INSERT INTO users (username, ssn_encrypted) VALUES ($1, $2)",
        username,
        encrypted_ssn
    )
    .execute(pool)
    .await?;
    
    Ok(())
}

// 读取后解密
async fn get_user_ssn(pool: &PgPool, user_id: i64) -> Result<String, sqlx::Error> {
    let user = sqlx::query_as!(
        User,
        "SELECT id, username, ssn_encrypted FROM users WHERE id = $1",
        user_id
    )
    .fetch_one(pool)
    .await?;
    
    let decrypted_ssn = decrypt_sensitive_data(&user.ssn_encrypted);
    Ok(String::from_utf8_lossy(&decrypted_ssn).to_string())
}
```

### 2. 敏感数据擦除

```rust
use zeroize::Zeroize;

fn process_password(mut password: String) {
    // 使用密码...
    
    // 离开作用域前擦除内存
    password.zeroize();
}
```

---

## 安全审计

### 1. cargo-audit (依赖漏洞扫描)

```bash
# 安装
cargo install cargo-audit

# 扫描项目依赖
cargo audit

# 示例输出:
# Crate:     tokio
# Version:   1.28.0
# Warning:   unsoundness
# Title:     tokio::io::ReadHalf<T>::unsplit is Unsound
# Date:      2023-05-10
# ID:        RUSTSEC-2023-0001
# URL:       https://rustsec.org/advisories/RUSTSEC-2023-0001
# Dependency tree:
# tokio 1.28.0
# └── myapp 1.0.0
```

**CI 集成：**

```yaml
# .github/workflows/security-audit.yml
name: Security Audit
on:
  schedule:
    - cron: '0 0 * * *'  # 每天运行
  push:
    branches: [main]

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo install cargo-audit
      - run: cargo audit
```

### 2. cargo-deny (License + 漏洞检查)

```toml
# deny.toml
[advisories]
vulnerability = "deny"
unmaintained = "warn"
notice = "warn"

[licenses]
unlicensed = "deny"
allow = ["MIT", "Apache-2.0", "BSD-3-Clause"]
deny = ["GPL-3.0"]

[bans]
multiple-versions = "warn"
```

```bash
# 安装
cargo install cargo-deny

# 检查
cargo deny check
```

---

## 漏洞扫描

### 1. 静态分析 (Clippy + 自定义 Lints)

```bash
# 启用所有 Clippy lints
cargo clippy --all-targets --all-features -- \
  -D warnings \
  -D clippy::all \
  -D clippy::pedantic \
  -D clippy::nursery

# 安全相关 lints
rustc -W unsafe-code src/main.rs
```

### 2. 动态分析 (AddressSanitizer)

```bash
# 检测内存错误 (use-after-free, buffer overflow)
RUSTFLAGS="-Z sanitizer=address" cargo +nightly run

# 检测数据竞争 (data race)
RUSTFLAGS="-Z sanitizer=thread" cargo +nightly run

# 检测未初始化内存
RUSTFLAGS="-Z sanitizer=memory" cargo +nightly run
```

### 3. Fuzzing (cargo-fuzz)

```bash
# 安装
cargo install cargo-fuzz

# 初始化 fuzzing 项目
cargo fuzz init

# 运行 fuzzing
cargo fuzz run fuzz_target_1
```

**Fuzz Target 示例：**

```rust
// fuzz/fuzz_targets/fuzz_target_1.rs
#![no_main]
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        // 测试你的解析函数
        let _ = my_parser(s);
    }
});
```

---

## 最佳实践

### ✅ 推荐做法

1. **使用 Argon2id 哈希密码**

   ```rust
   // ✅ 安全的密码存储
   let hash = argon2::hash_password(password)?;
   ```

2. **所有外部输入都要验证**

   ```rust
   // ✅ 使用 validator
   #[derive(Validate)]
   struct Input {
       #[validate(email)]
       email: String,
   }
   ```

3. **使用参数化查询**

   ```rust
   // ✅ 防止 SQL 注入
   query!("SELECT * FROM users WHERE id = $1", id)
   ```

4. **启用 HTTPS/TLS**

   ```rust
   // ✅ 加密通信
   RustlsConfig::from_pem_file("cert.pem", "key.pem")
   ```

5. **实施 CSRF 保护**

   ```rust
   // ✅ 防止跨站请求伪造
   verify_csrf_token(session, token).await?;
   ```

6. **输出转义**

   ```html
   <!-- ✅ Askama 自动转义 -->
   {{ user_input }}
   ```

7. **定期运行安全审计**

   ```bash
   # ✅ 每天自动运行
   cargo audit && cargo deny check
   ```

8. **最小权限原则**

   ```rust
   // ✅ 只授予必要权限
   if !rbac.check_permission(&user, "admin", "delete") {
       return Err(StatusCode::FORBIDDEN);
   }
   ```

9. **使用 Secrets 管理敏感信息**

   ```rust
   // ✅ 从环境变量读取
   let jwt_secret = env::var("JWT_SECRET")?;
   ```

10. **启用安全头部**

    ```rust
    // ✅ CSP, HSTS, X-Frame-Options
    .layer(SetResponseHeaderLayer::...)
    ```

---

## 常见陷阱

### ❌ 避免的错误

1. **使用弱密码哈希 (MD5/SHA1)**

   ```rust
   // ❌ 不安全！
   let hash = md5::compute(password);
   
   // ✅ 使用 Argon2id
   let hash = argon2::hash_password(password)?;
   ```

2. **字符串拼接 SQL**

   ```rust
   // ❌ SQL 注入风险！
   let query = format!("SELECT * FROM users WHERE name = '{}'", name);
   
   // ✅ 参数化查询
   query!("SELECT * FROM users WHERE name = $1", name)
   ```

3. **未验证用户输入**

   ```rust
   // ❌ 直接使用用户输入
   let age = req.age;
   
   // ✅ 先验证
   req.validate()?;
   let age = req.age;
   ```

4. **使用 HTTP 而非 HTTPS**

   ```rust
   // ❌ 明文传输
   .bind("0.0.0.0:80")
   
   // ✅ HTTPS 加密
   .bind_rustls(addr, tls_config)
   ```

5. **硬编码密钥**

   ```rust
   // ❌ 泄露风险！
   let secret = "hardcoded-secret-key";
   
   // ✅ 环境变量
   let secret = env::var("JWT_SECRET")?;
   ```

6. **忽略依赖漏洞**

   ```bash
   # ❌ 从不运行审计
   
   # ✅ 定期审计
   cargo audit
   ```

7. **缺少 CSRF 保护**

   ```rust
   // ❌ 直接处理 POST 请求
   async fn delete_user(req: Request) { ... }
   
   // ✅ 验证 CSRF token
   verify_csrf_token(session, token).await?;
   ```

8. **未转义输出**

   ```html
   <!-- ❌ XSS 风险！ -->
   <div>{{ user_input | safe }}</div>
   
   <!-- ✅ 自动转义 -->
   <div>{{ user_input }}</div>
   ```

9. **过度授权**

   ```rust
   // ❌ 所有用户都有管理员权限
   if user.is_authenticated() { ... }
   
   // ✅ 检查具体权限
   if rbac.check_permission(&user, "admin", "delete") { ... }
   ```

10. **不安全的随机数生成**

    ```rust
    // ❌ 不安全！
    use rand::random;
    let token = random::<u64>();
    
    // ✅ 密码学安全的随机数
    use ring::rand::{SystemRandom, SecureRandom};
    let rng = SystemRandom::new();
    let mut token = [0u8; 32];
    rng.fill(&mut token)?;
    ```

---

## 参考资源

### 官方文档

- [OWASP Top 10](https://owasp.org/www-project-top-ten/)
- [RustSec Advisory Database](https://rustsec.org/)
- [Rust Secure Code Guidelines](https://anssi-fr.github.io/rust-guide/)

### 核心库文档

- [ring](https://docs.rs/ring/) - 密码学库
- [rustls](https://docs.rs/rustls/) - TLS 库
- [jsonwebtoken](https://docs.rs/jsonwebtoken/) - JWT 库
- [validator](https://docs.rs/validator/) - 输入验证

### 工具

- [cargo-audit](https://github.com/RustSec/rustsec/tree/main/cargo-audit) - 依赖审计
- [cargo-deny](https://github.com/EmbarkStudios/cargo-deny) - License + 漏洞检查
- [cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz) - Fuzzing 工具

### 学习资源

- [OWASP Cheat Sheet Series](https://cheatsheetseries.owasp.org/)
- [Secure Rust Guidelines](https://anssi-fr.github.io/rust-guide/)
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) - Unsafe Rust

---

## 总结

Rust 安全编程的**核心要素**：

1. ✅ **密码安全**：Argon2id 哈希
2. ✅ **认证**：JWT + OAuth2
3. ✅ **授权**：RBAC/ABAC
4. ✅ **输入验证**：validator + garde
5. ✅ **SQL 安全**：参数化查询
6. ✅ **XSS 防护**：自动转义 + CSP
7. ✅ **CSRF 防护**：Token 验证
8. ✅ **通信加密**：HTTPS/TLS
9. ✅ **数据加密**：AES-256-GCM
10. ✅ **安全审计**：cargo-audit + cargo-deny

🔒 **记住**：安全是一个持续的过程，不是一次性的任务！定期审计、更新依赖、监控漏洞是保持系统安全的关键。
