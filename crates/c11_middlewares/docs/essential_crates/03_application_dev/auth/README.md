# 认证与授权 - Rust Web 安全解决方案

> **核心库**: jsonwebtoken, oauth2, argon2, tower-sessions, tower-cookies  
> **适用场景**: JWT认证、OAuth2授权、密码哈希、会话管理、权限控制

---

## 📋 目录

- [认证与授权 - Rust Web 安全解决方案](#认证与授权---rust-web-安全解决方案)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心概念](#核心概念)
    - [认证vs授权](#认证vs授权)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
  - [jsonwebtoken - JWT认证](#jsonwebtoken---jwt认证)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
      - [安装](#安装)
      - [快速开始](#快速开始)
    - [高级特性](#高级特性)
      - [1. 自定义声明](#1-自定义声明)
      - [2. 刷新令牌](#2-刷新令牌)
      - [3. 多密钥管理](#3-多密钥管理)
  - [oauth2 - OAuth2授权](#oauth2---oauth2授权)
    - [核心特性1](#核心特性1)
    - [基础用法1](#基础用法1)
      - [安装1](#安装1)
      - [授权码流程](#授权码流程)
  - [argon2 - 密码哈希](#argon2---密码哈希)
    - [核心特性2](#核心特性2)
    - [基础用法2](#基础用法2)
      - [安装2](#安装2)
      - [密码哈希与验证](#密码哈希与验证)
  - [使用场景](#使用场景)
    - [场景1: JWT认证中间件](#场景1-jwt认证中间件)
    - [场景2: OAuth2第三方登录](#场景2-oauth2第三方登录)
    - [场景3: 基于角色的访问控制(RBAC)](#场景3-基于角色的访问控制rbac)
  - [最佳实践](#最佳实践)
    - [1. 安全密钥管理](#1-安全密钥管理)
    - [2. Token过期策略](#2-token过期策略)
    - [3. 密码存储](#3-密码存储)
    - [4. CSRF防护](#4-csrf防护)
    - [5. 速率限制](#5-速率限制)
  - [常见陷阱](#常见陷阱)
    - [⚠️ 陷阱1: 硬编码密钥](#️-陷阱1-硬编码密钥)
    - [⚠️ 陷阱2: 不验证JWT签名](#️-陷阱2-不验证jwt签名)
    - [⚠️ 陷阱3: 弱密码策略](#️-陷阱3-弱密码策略)
    - [⚠️ 陷阱4: 缺少Token撤销机制](#️-陷阱4-缺少token撤销机制)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程与文章](#教程与文章)
    - [示例项目](#示例项目)
    - [相关文档](#相关文档)

---

## 概述

认证与授权是Web应用安全的核心，保护用户数据和系统资源免受未授权访问。

**核心价值**:

- **身份验证**: 确认用户身份
- **访问控制**: 限制资源访问权限
- **会话管理**: 维护用户登录状态
- **安全通信**: 防止中间人攻击和数据泄露

### 核心概念

```text
认证授权流程：

┌─────────────────┐
│   用户登录       │
│   (Credentials) │
└────────┬────────┘
         │
         ↓
┌─────────────────────────────┐
│   认证 (Authentication)      │
│   - 验证用户名/密码          │
│   - 验证第三方OAuth Token   │
└────────┬────────────────────┘
         │
         ↓ 生成Token/Session
         │
┌─────────────────────────────┐
│   授权 (Authorization)       │
│   - 检查用户角色             │
│   - 验证资源访问权限         │
└────────┬────────────────────┘
         │
         ↓
┌─────────────────────────────┐
│   访问资源 (Access)          │
│   - API端点                  │
│   - 数据库记录               │
└─────────────────────────────┘
```

### 认证vs授权

| 维度 | 认证 (Authentication) | 授权 (Authorization) |
|------|----------------------|---------------------|
| **目的** | 验证"你是谁" | 验证"你能做什么" |
| **时机** | 登录时 | 每次请求时 |
| **方法** | 密码、OAuth、生物识别 | 角色、权限、策略 |
| **结果** | Token/Session | 允许/拒绝访问 |
| **示例** | 用户登录 | 访问管理员页面 |

---

## 核心库对比

### 功能矩阵

| 特性 | jsonwebtoken | oauth2 | argon2 | tower-sessions | tower-cookies |
|------|--------------|--------|--------|----------------|---------------|
| **JWT生成** | ✅ | ❌ | ❌ | ❌ | ❌ |
| **JWT验证** | ✅ | ❌ | ❌ | ❌ | ❌ |
| **OAuth2流程** | ❌ | ✅ | ❌ | ❌ | ❌ |
| **密码哈希** | ❌ | ❌ | ✅ | ❌ | ❌ |
| **会话管理** | ❌ | ❌ | ❌ | ✅ | ✅ |
| **多种算法** | ✅ | ✅ | ✅ | ❌ | ❌ |
| **安全性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **易用性** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

### 选择指南

| 场景 | 推荐库 | 理由 |
|------|--------|------|
| **无状态API** | jsonwebtoken | JWT适合微服务和移动端 |
| **第三方登录** | oauth2 | GitHub/Google等OAuth2集成 |
| **密码存储** | argon2 | 业界推荐的密码哈希算法 |
| **传统Web应用** | tower-sessions | 服务端会话管理 |
| **简单Cookie** | tower-cookies | 轻量级Cookie操作 |
| **企业应用** | jsonwebtoken + RBAC | JWT + 角色权限控制 |

---

## jsonwebtoken - JWT认证

### 核心特性

- ✅ **多种算法**: HS256, HS384, HS512, RS256, RS384, RS512, ES256, ES384
- ✅ **标准声明**: iss, sub, aud, exp, nbf, iat, jti
- ✅ **自定义声明**: 支持任意JSON结构
- ✅ **验证规则**: 自定义验证逻辑
- ✅ **零依赖**: 核心功能无外部依赖

### 基础用法

#### 安装

```toml
[dependencies]
jsonwebtoken = "9.2"
serde = { version = "1.0", features = ["derive"] }
chrono = "0.4"
```

#### 快速开始

```rust
use jsonwebtoken::{encode, decode, Header, Algorithm, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};
use chrono::{Utc, Duration};

#[derive(Debug, Serialize, Deserialize)]
struct Claims {
    sub: String,           // 用户ID
    exp: i64,              // 过期时间
    iat: i64,              // 签发时间
    role: String,          // 自定义：用户角色
}

fn create_jwt(user_id: &str, role: &str) -> Result<String, jsonwebtoken::errors::Error> {
    let expiration = Utc::now()
        .checked_add_signed(Duration::hours(24))
        .expect("valid timestamp")
        .timestamp();

    let claims = Claims {
        sub: user_id.to_owned(),
        exp: expiration,
        iat: Utc::now().timestamp(),
        role: role.to_owned(),
    };

    let token = encode(
        &Header::default(),
        &claims,
        &EncodingKey::from_secret("your-secret-key".as_ref()),
    )?;

    Ok(token)
}

fn verify_jwt(token: &str) -> Result<Claims, jsonwebtoken::errors::Error> {
    let token_data = decode::<Claims>(
        token,
        &DecodingKey::from_secret("your-secret-key".as_ref()),
        &Validation::default(),
    )?;

    Ok(token_data.claims)
}

fn main() {
    // 创建Token
    let token = create_jwt("user123", "admin").unwrap();
    println!("Token: {}", token);

    // 验证Token
    let claims = verify_jwt(&token).unwrap();
    println!("User: {}, Role: {}", claims.sub, claims.role);
}
```

### 高级特性

#### 1. 自定义声明

```rust
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct CustomClaims {
    // 标准声明
    sub: String,
    exp: i64,
    
    // 自定义声明
    user_id: u32,
    username: String,
    email: String,
    roles: Vec<String>,
    permissions: Vec<String>,
    
    // 业务特定
    tenant_id: Option<String>,
    session_id: String,
}

fn create_custom_jwt(user: &User) -> String {
    let claims = CustomClaims {
        sub: user.id.to_string(),
        exp: get_expiration(),
        user_id: user.id,
        username: user.username.clone(),
        email: user.email.clone(),
        roles: user.roles.clone(),
        permissions: user.get_permissions(),
        tenant_id: user.tenant_id.clone(),
        session_id: generate_session_id(),
    };

    encode(&Header::default(), &claims, &get_encoding_key()).unwrap()
}
```

#### 2. 刷新令牌

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

struct TokenPair {
    access_token: String,
    refresh_token: String,
    expires_in: i64,
}

struct TokenManager {
    refresh_tokens: Arc<Mutex<HashMap<String, String>>>,  // refresh_token -> user_id
}

impl TokenManager {
    fn issue_tokens(&self, user_id: &str) -> TokenPair {
        let access_token = create_jwt(user_id, "user").unwrap();
        let refresh_token = uuid::Uuid::new_v4().to_string();

        // 存储refresh_token
        self.refresh_tokens.lock().unwrap()
            .insert(refresh_token.clone(), user_id.to_string());

        TokenPair {
            access_token,
            refresh_token,
            expires_in: 3600,  // 1小时
        }
    }

    fn refresh(&self, refresh_token: &str) -> Option<TokenPair> {
        let tokens = self.refresh_tokens.lock().unwrap();
        let user_id = tokens.get(refresh_token)?;

        Some(self.issue_tokens(user_id))
    }

    fn revoke(&self, refresh_token: &str) {
        self.refresh_tokens.lock().unwrap().remove(refresh_token);
    }
}
```

#### 3. 多密钥管理

```rust
use jsonwebtoken::{Algorithm, Header};

enum KeyType {
    Development,
    Production,
    Staging,
}

struct KeyManager {
    keys: HashMap<KeyType, (EncodingKey, DecodingKey)>,
}

impl KeyManager {
    fn new() -> Self {
        let mut keys = HashMap::new();
        
        // 不同环境使用不同密钥
        keys.insert(
            KeyType::Development,
            (
                EncodingKey::from_secret(b"dev-secret"),
                DecodingKey::from_secret(b"dev-secret"),
            ),
        );
        
        keys.insert(
            KeyType::Production,
            (
                EncodingKey::from_rsa_pem(include_bytes!("prod-private.pem")).unwrap(),
                DecodingKey::from_rsa_pem(include_bytes!("prod-public.pem")).unwrap(),
            ),
        );

        Self { keys }
    }

    fn encode(&self, claims: &Claims, key_type: &KeyType) -> String {
        let (encoding_key, _) = self.keys.get(key_type).unwrap();
        encode(&Header::new(Algorithm::RS256), claims, encoding_key).unwrap()
    }
}
```

---

## oauth2 - OAuth2授权

### 核心特性1

- ✅ **OAuth2流程**: 授权码、隐式、密码、客户端凭证
- ✅ **PKCE支持**: 防止授权码拦截
- ✅ **多提供商**: GitHub, Google, Microsoft等
- ✅ **Token刷新**: 自动刷新访问令牌
- ✅ **作用域管理**: 细粒度权限控制

### 基础用法1

#### 安装1

```toml
[dependencies]
oauth2 = "4.4"
reqwest = { version = "0.11", features = ["json"] }
tokio = { version = "1", features = ["full"] }
```

#### 授权码流程

```rust
use oauth2::{
    AuthorizationCode, AuthUrl, ClientId, ClientSecret, CsrfToken,
    RedirectUrl, Scope, TokenResponse, TokenUrl,
};
use oauth2::basic::BasicClient;
use oauth2::reqwest::async_http_client;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 配置OAuth2客户端
    let client = BasicClient::new(
        ClientId::new("your-client-id".to_string()),
        Some(ClientSecret::new("your-client-secret".to_string())),
        AuthUrl::new("https://github.com/login/oauth/authorize".to_string())?,
        Some(TokenUrl::new("https://github.com/login/oauth/access_token".to_string())?),
    )
    .set_redirect_uri(RedirectUrl::new("http://localhost:8080/callback".to_string())?);

    // 2. 生成授权URL
    let (auth_url, csrf_token) = client
        .authorize_url(CsrfToken::new_random)
        .add_scope(Scope::new("user:email".to_string()))
        .add_scope(Scope::new("repo".to_string()))
        .url();

    println!("访问此URL进行授权: {}", auth_url);

    // 3. 用户授权后，从回调URL获取授权码
    let code = AuthorizationCode::new("authorization-code-from-callback".to_string());

    // 4. 交换授权码获取访问令牌
    let token_result = client
        .exchange_code(code)
        .request_async(async_http_client)
        .await?;

    let access_token = token_result.access_token();
    let refresh_token = token_result.refresh_token();

    println!("Access Token: {}", access_token.secret());
    if let Some(refresh) = refresh_token {
        println!("Refresh Token: {}", refresh.secret());
    }

    Ok(())
}
```

---

## argon2 - 密码哈希

### 核心特性2

- ✅ **Argon2算法**: 2015年密码哈希竞赛冠军
- ✅ **抗GPU攻击**: 内存密集型算法
- ✅ **自动盐值**: 随机生成安全盐值
- ✅ **参数可调**: 内存、时间、并行度
- ✅ **PHC格式**: 标准密码哈希格式

### 基础用法2

#### 安装2

```toml
[dependencies]
argon2 = "0.5"
```

#### 密码哈希与验证

```rust
use argon2::{
    Argon2,
    PasswordHasher, PasswordVerifier, PasswordHash,
    password_hash::{rand_core::OsRng, SaltString},
};

fn hash_password(password: &[u8]) -> Result<String, argon2::password_hash::Error> {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default();
    
    let password_hash = argon2.hash_password(password, &salt)?;
    Ok(password_hash.to_string())
}

fn verify_password(password: &[u8], hash: &str) -> Result<bool, argon2::password_hash::Error> {
    let parsed_hash = PasswordHash::new(hash)?;
    let argon2 = Argon2::default();
    
    match argon2.verify_password(password, &parsed_hash) {
        Ok(()) => Ok(true),
        Err(_) => Ok(false),
    }
}

fn main() {
    let password = b"my-secure-password";
    
    // 哈希密码
    let hash = hash_password(password).unwrap();
    println!("Hash: {}", hash);
    
    // 验证密码
    let is_valid = verify_password(password, &hash).unwrap();
    println!("Valid: {}", is_valid);
    
    // 错误密码
    let is_valid = verify_password(b"wrong-password", &hash).unwrap();
    println!("Valid: {}", is_valid);
}
```

---

## 使用场景

### 场景1: JWT认证中间件

**需求描述**: Axum Web应用需要JWT认证保护路由

**推荐方案**:

```rust
use axum::{
    Router, routing::get,
    extract::State,
    http::{Request, StatusCode},
    middleware::{self, Next},
    response::{IntoResponse, Response},
};
use jsonwebtoken::{decode, DecodingKey, Validation};
use std::sync::Arc;

#[derive(Clone)]
struct AppState {
    jwt_secret: String,
}

// JWT认证中间件
async fn auth_middleware<B>(
    State(state): State<Arc<AppState>>,
    mut req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    let auth_header = req.headers()
        .get("Authorization")
        .and_then(|h| h.to_str().ok())
        .ok_or(StatusCode::UNAUTHORIZED)?;

    let token = auth_header
        .strip_prefix("Bearer ")
        .ok_or(StatusCode::UNAUTHORIZED)?;

    let token_data = decode::<Claims>(
        token,
        &DecodingKey::from_secret(state.jwt_secret.as_bytes()),
        &Validation::default(),
    )
    .map_err(|_| StatusCode::UNAUTHORIZED)?;

    // 将用户信息添加到请求扩展
    req.extensions_mut().insert(token_data.claims);

    Ok(next.run(req).await)
}

// 受保护的路由
async fn protected_route() -> impl IntoResponse {
    "This is a protected route"
}

#[tokio::main]
async fn main() {
    let state = Arc::new(AppState {
        jwt_secret: "your-secret-key".to_string(),
    });

    let app = Router::new()
        .route("/protected", get(protected_route))
        .route_layer(middleware::from_fn_with_state(state.clone(), auth_middleware))
        .with_state(state);

    let listener = tokio::net::TcpListener::bind("127.0.0.1:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

### 场景2: OAuth2第三方登录

**需求描述**: 实现GitHub OAuth登录

**推荐方案**:

```rust
use axum::{Router, routing::get, extract::Query, response::Redirect};
use oauth2::basic::BasicClient;
use serde::Deserialize;

#[derive(Deserialize)]
struct CallbackParams {
    code: String,
    state: String,
}

async fn login() -> Redirect {
    // 生成授权URL并重定向
    let (auth_url, _csrf) = oauth_client()
        .authorize_url(CsrfToken::new_random)
        .add_scope(Scope::new("user:email".to_string()))
        .url();

    Redirect::to(auth_url.as_str())
}

async fn callback(Query(params): Query<CallbackParams>) -> impl IntoResponse {
    // 交换授权码获取Token
    let token = oauth_client()
        .exchange_code(AuthorizationCode::new(params.code))
        .request_async(async_http_client)
        .await
        .unwrap();

    // 使用Token获取用户信息
    let user_info = fetch_github_user(token.access_token()).await;

    // 创建本地会话/JWT
    let jwt = create_jwt(&user_info.id, "user").unwrap();

    format!("Login successful! JWT: {}", jwt)
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/login", get(login))
        .route("/callback", get(callback));

    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

### 场景3: 基于角色的访问控制(RBAC)

**需求描述**: 实现用户角色权限管理

**推荐方案**:

```rust
use axum::{extract::Extension, http::StatusCode};

#[derive(Debug, Clone)]
enum Role {
    Admin,
    User,
    Guest,
}

impl Role {
    fn has_permission(&self, permission: &str) -> bool {
        match (self, permission) {
            (Role::Admin, _) => true,  // 管理员有所有权限
            (Role::User, "read") => true,
            (Role::User, "write") => true,
            (Role::Guest, "read") => true,
            _ => false,
        }
    }
}

// 权限检查中间件
async fn require_permission(
    Extension(claims): Extension<Claims>,
    permission: &'static str,
) -> Result<(), StatusCode> {
    let role = match claims.role.as_str() {
        "admin" => Role::Admin,
        "user" => Role::User,
        _ => Role::Guest,
    };

    if role.has_permission(permission) {
        Ok(())
    } else {
        Err(StatusCode::FORBIDDEN)
    }
}

// 使用
async fn admin_only_route(Extension(claims): Extension<Claims>) -> Result<String, StatusCode> {
    require_permission(Extension(claims.clone()), "admin").await?;
    Ok("Admin content".to_string())
}
```

---

## 最佳实践

### 1. 安全密钥管理

**描述**: 永远不要硬编码密钥

✅ **正确做法**:

```rust
use std::env;

fn get_jwt_secret() -> String {
    env::var("JWT_SECRET")
        .expect("JWT_SECRET must be set")
}

// 使用环境变量
let secret = get_jwt_secret();
```

❌ **避免**:

```rust
// 不要硬编码！
let secret = "my-secret-key";  // 危险！
```

### 2. Token过期策略

```rust
use chrono::{Duration, Utc};

// 访问令牌：短期(15分钟-1小时)
let access_exp = Utc::now()
    .checked_add_signed(Duration::minutes(15))
    .unwrap()
    .timestamp();

// 刷新令牌：长期(7-30天)
let refresh_exp = Utc::now()
    .checked_add_signed(Duration::days(7))
    .unwrap()
    .timestamp();
```

### 3. 密码存储

```rust
// 使用Argon2而非bcrypt或MD5
use argon2::Argon2;

let argon2 = Argon2::default();
let hash = argon2.hash_password(password, &salt).unwrap();
```

### 4. CSRF防护

```rust
use axum::http::header;

// 设置CSRF Token
response.headers_mut().insert(
    "X-CSRF-Token",
    generate_csrf_token().parse().unwrap(),
);

// 验证CSRF Token
fn validate_csrf(request: &Request) -> bool {
    let header_token = request.headers().get("X-CSRF-Token");
    let cookie_token = get_csrf_from_cookie(request);
    
    header_token == cookie_token
}
```

### 5. 速率限制

```rust
use tower_governor::{GovernorLayer, governor::GovernorConfigBuilder};

// 限制登录尝试
let governor_conf = Box::new(
    GovernorConfigBuilder::default()
        .per_second(2)
        .burst_size(5)
        .finish()
        .unwrap(),
);

let app = Router::new()
    .route("/login", post(login))
    .layer(GovernorLayer { config: Box::leak(governor_conf) });
```

---

## 常见陷阱

### ⚠️ 陷阱1: 硬编码密钥

**问题描述**: 密钥泄露导致安全风险

❌ **错误示例**:

```rust
let secret = "my-secret-key";  // 提交到Git！
```

✅ **正确做法**:

```rust
let secret = std::env::var("JWT_SECRET").expect("JWT_SECRET required");
```

### ⚠️ 陷阱2: 不验证JWT签名

❌ **错误示例**:

```rust
// 危险：不验证签名
let mut validation = Validation::default();
validation.insecure_disable_signature_validation();  // 不要这样做！
```

✅ **正确做法**:

```rust
let validation = Validation::default();  // 始终验证签名
decode::<Claims>(token, &key, &validation)?;
```

### ⚠️ 陷阱3: 弱密码策略

❌ **错误示例**:

```rust
// 不检查密码强度
fn register(password: &str) {
    let hash = hash_password(password.as_bytes()).unwrap();
    save_user(hash);
}
```

✅ **正确做法**:

```rust
fn validate_password(password: &str) -> Result<(), String> {
    if password.len() < 8 {
        return Err("Password must be at least 8 characters".to_string());
    }
    
    let has_uppercase = password.chars().any(|c| c.is_uppercase());
    let has_lowercase = password.chars().any(|c| c.is_lowercase());
    let has_digit = password.chars().any(|c| c.is_digit(10));
    
    if !(has_uppercase && has_lowercase && has_digit) {
        return Err("Password must contain uppercase, lowercase, and digit".to_string());
    }
    
    Ok(())
}
```

### ⚠️ 陷阱4: 缺少Token撤销机制

**问题描述**: 用户登出后Token仍然有效

✅ **正确做法**:

```rust
use std::collections::HashSet;
use std::sync::{Arc, Mutex};

struct TokenBlacklist {
    tokens: Arc<Mutex<HashSet<String>>>,
}

impl TokenBlacklist {
    fn revoke(&self, token: &str) {
        self.tokens.lock().unwrap().insert(token.to_string());
    }

    fn is_revoked(&self, token: &str) -> bool {
        self.tokens.lock().unwrap().contains(token)
    }
}

// 在中间件中检查
if blacklist.is_revoked(token) {
    return Err(StatusCode::UNAUTHORIZED);
}
```

---

## 参考资源

### 官方文档

- 📚 [jsonwebtoken文档](https://docs.rs/jsonwebtoken/)
- 📚 [oauth2文档](https://docs.rs/oauth2/)
- 📚 [argon2文档](https://docs.rs/argon2/)
- 📚 [JWT.io](https://jwt.io/)

### 教程与文章

- 📖 [OAuth2 RFC 6749](https://tools.ietf.org/html/rfc6749)
- 📖 [OWASP认证备忘单](https://cheatsheetseries.owasp.org/cheatsheets/Authentication_Cheat_Sheet.html)
- 📖 [Rust Web认证指南](https://blog.logrocket.com/jwt-authentication-in-rust/)

### 示例项目

- 💻 [Realworld Axum](https://github.com/launchbadge/realworld-axum-sqlx) - JWT认证实战
- 💻 [rust-web-api-example](https://github.com/davidpdrsn/realworld-axum-sqlx) - 完整认证流程

### 相关文档

- 🔗 [Web框架](../web_frameworks/README.md)
- 🔗 [会话管理](../session/README.md)
- 🔗 [安全最佳实践](../../cross_cutting/security/README.md)
- 🔗 [数据库](../databases/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区  
**文档长度**: 800+ 行
