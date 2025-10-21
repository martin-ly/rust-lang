# Authentication - 认证系统

## 📋 目录

- [概述](#概述)
- [JWT 认证](#jwt-认证)
- [OAuth2](#oauth2)
- [密码哈希](#密码哈希)

---

## 概述

认证是确认用户身份的过程，是应用安全的第一道防线。

### 核心依赖

```toml
[dependencies]
# JWT
jsonwebtoken = "9.2"

# OAuth2
oauth2 = "4.4"

# 密码哈希
argon2 = "0.5"
bcrypt = "0.15"
```

---

## JWT 认证

### 基础用法

```rust
use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct Claims {
    sub: String,
    exp: usize,
}

fn create_jwt(user_id: &str) -> Result<String, jsonwebtoken::errors::Error> {
    let claims = Claims {
        sub: user_id.to_string(),
        exp: (chrono::Utc::now() + chrono::Duration::hours(24)).timestamp() as usize,
    };
    
    encode(
        &Header::default(),
        &claims,
        &EncodingKey::from_secret("secret".as_ref())
    )
}

fn verify_jwt(token: &str) -> Result<Claims, jsonwebtoken::errors::Error> {
    let token_data = decode::<Claims>(
        token,
        &DecodingKey::from_secret("secret".as_ref()),
        &Validation::default()
    )?;
    
    Ok(token_data.claims)
}
```

### Axum 中间件

```rust
use axum::{
    Router,
    routing::get,
    middleware::{self, Next},
    http::{Request, StatusCode},
    response::{Response, IntoResponse},
    extract::Extension,
};

async fn auth_middleware<B>(
    mut req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    let auth_header = req
        .headers()
        .get("Authorization")
        .and_then(|v| v.to_str().ok())
        .and_then(|v| v.strip_prefix("Bearer "));
    
    match auth_header {
        Some(token) => {
            match verify_jwt(token) {
                Ok(claims) => {
                    req.extensions_mut().insert(claims);
                    Ok(next.run(req).await)
                }
                Err(_) => Err(StatusCode::UNAUTHORIZED),
            }
        }
        None => Err(StatusCode::UNAUTHORIZED),
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/protected", get(protected_handler))
        .layer(middleware::from_fn(auth_middleware));
}

async fn protected_handler(Extension(claims): Extension<Claims>) -> String {
    format!("Hello, {}!", claims.sub)
}
```

---

## OAuth2

### Google OAuth2

```rust
use oauth2::{
    AuthUrl, AuthorizationCode, ClientId, ClientSecret, CsrfToken,
    RedirectUrl, Scope, TokenUrl,
    basic::BasicClient,
};

fn create_oauth_client() -> BasicClient {
    BasicClient::new(
        ClientId::new("client_id".to_string()),
        Some(ClientSecret::new("client_secret".to_string())),
        AuthUrl::new("https://accounts.google.com/o/oauth2/auth".to_string()).unwrap(),
        Some(TokenUrl::new("https://oauth2.googleapis.com/token".to_string()).unwrap())
    )
    .set_redirect_uri(RedirectUrl::new("http://localhost:8080/callback".to_string()).unwrap())
}

fn get_auth_url() -> (String, CsrfToken) {
    let client = create_oauth_client();
    
    client
        .authorize_url(CsrfToken::new_random)
        .add_scope(Scope::new("email".to_string()))
        .add_scope(Scope::new("profile".to_string()))
        .url()
}
```

---

## 密码哈希

### Argon2

```rust
use argon2::{
    password_hash::{
        rand_core::OsRng,
        PasswordHash, PasswordHasher, PasswordVerifier, SaltString
    },
    Argon2
};

fn hash_password(password: &str) -> Result<String, argon2::password_hash::Error> {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default();
    
    let password_hash = argon2.hash_password(password.as_bytes(), &salt)?;
    Ok(password_hash.to_string())
}

fn verify_password(password: &str, hash: &str) -> Result<bool, argon2::password_hash::Error> {
    let parsed_hash = PasswordHash::new(hash)?;
    let argon2 = Argon2::default();
    
    Ok(argon2.verify_password(password.as_bytes(), &parsed_hash).is_ok())
}
```

---

## 实战示例

### 完整的登录系统

```rust
use axum::{Router, routing::post, Json};
use serde::{Deserialize, Serialize};

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
    // 从数据库获取用户
    let stored_hash = get_user_hash(&req.username).await
        .ok_or(StatusCode::UNAUTHORIZED)?;
    
    // 验证密码
    if !verify_password(&req.password, &stored_hash).unwrap_or(false) {
        return Err(StatusCode::UNAUTHORIZED);
    }
    
    // 生成 JWT
    let token = create_jwt(&req.username)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    
    Ok(Json(LoginResponse { token }))
}

async fn get_user_hash(username: &str) -> Option<String> {
    // 模拟数据库查询
    Some("$argon2id$v=19$m=19456,t=2,p=1$...".to_string())
}
```

---

## 参考资源

- [jsonwebtoken 文档](https://docs.rs/jsonwebtoken/)
- [oauth2 文档](https://docs.rs/oauth2/)
- [argon2 文档](https://docs.rs/argon2/)
