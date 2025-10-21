# 密码学 (Cryptography)

**类别**: 横切关注点  
**重要程度**: ⭐⭐⭐⭐⭐ (必备)  
**更新日期**: 2025-10-20

---

## 📋 概述

密码学是保护应用程序安全的基础。Rust 生态提供了高质量、经过审计的密码学库，涵盖加密、哈希、签名、TLS 等所有核心需求。

**⚠️ 安全警告**: 密码学实现极其敏感，务必使用经过审计的库，避免自己实现！

---

## 🔧 核心工具

### 1. ring (通用密码学 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add ring`  
**用途**: 高性能、安全的密码学原语

#### 核心特性

- ✅ 基于 BoringSSL (Google)
- ✅ 经过安全审计
- ✅ 零unsafe代码暴露
- ✅ 高性能实现

#### HMAC 签名

```rust
use ring::{hmac, rand};

// 生成密钥
let rng = rand::SystemRandom::new();
let key = hmac::Key::generate(hmac::HMAC_SHA256, &rng).unwrap();

// 签名
let message = b"Hello, World!";
let signature = hmac::sign(&key, message);

// 验证
hmac::verify(&key, message, signature.as_ref()).unwrap();
```

#### AES-GCM 加密

```rust
use ring::{aead, rand};

fn encrypt_data(data: &[u8], key: &[u8]) -> Vec<u8> {
    let rng = rand::SystemRandom::new();
    
    // 创建加密密钥
    let unbound_key = aead::UnboundKey::new(&aead::AES_256_GCM, key).unwrap();
    let key = aead::LessSafeKey::new(unbound_key);
    
    // 生成 nonce
    let mut nonce_bytes = [0u8; 12];
    rng.fill(&mut nonce_bytes).unwrap();
    let nonce = aead::Nonce::assume_unique_for_key(nonce_bytes);
    
    // 加密
    let mut in_out = data.to_vec();
    key.seal_in_place_append_tag(nonce, aead::Aad::empty(), &mut in_out)
        .unwrap();
    
    // 返回 nonce + ciphertext
    [&nonce_bytes[..], &in_out[..]].concat()
}

fn decrypt_data(encrypted: &[u8], key: &[u8]) -> Result<Vec<u8>, aead::Error> {
    // 分离 nonce 和 ciphertext
    let (nonce_bytes, ciphertext) = encrypted.split_at(12);
    
    let unbound_key = aead::UnboundKey::new(&aead::AES_256_GCM, key)?;
    let key = aead::LessSafeKey::new(unbound_key);
    
    let nonce = aead::Nonce::assume_unique_for_key(*array_ref![nonce_bytes, 0, 12]);
    
    let mut in_out = ciphertext.to_vec();
    let plaintext = key.open_in_place(nonce, aead::Aad::empty(), &mut in_out)?;
    
    Ok(plaintext.to_vec())
}
```

#### Ed25519 签名

```rust
use ring::signature::{Ed25519KeyPair, KeyPair, UnparsedPublicKey, ED25519};
use ring::rand::SystemRandom;

// 生成密钥对
let rng = SystemRandom::new();
let pkcs8 = Ed25519KeyPair::generate_pkcs8(&rng).unwrap();
let key_pair = Ed25519KeyPair::from_pkcs8(pkcs8.as_ref()).unwrap();

// 签名
let message = b"Important message";
let signature = key_pair.sign(message);

// 验证
let public_key = UnparsedPublicKey::new(&ED25519, key_pair.public_key());
public_key.verify(message, signature.as_ref()).unwrap();
```

---

### 2. rustls (TLS 实现 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add rustls rustls-pemfile`  
**用途**: 纯 Rust 的 TLS 库，替代 OpenSSL

#### 核心优势

- ✅ 纯 Rust，无 C 依赖
- ✅ 内存安全
- ✅ 现代 TLS 1.2/1.3
- ✅ 高性能

#### TLS 客户端

```rust
use rustls::{ClientConfig, RootCertStore};
use rustls_pemfile;
use std::sync::Arc;

fn create_tls_client() -> Arc<ClientConfig> {
    let mut root_store = RootCertStore::empty();
    
    // 加载系统根证书
    root_store.add_server_trust_anchors(
        webpki_roots::TLS_SERVER_ROOTS
            .0
            .iter()
            .map(|ta| {
                rustls::OwnedTrustAnchor::from_subject_spki_name_constraints(
                    ta.subject,
                    ta.spki,
                    ta.name_constraints,
                )
            }),
    );
    
    Arc::new(
        ClientConfig::builder()
            .with_safe_defaults()
            .with_root_certificates(root_store)
            .with_no_client_auth()
    )
}

// 与 reqwest 集成
use reqwest::Client;

let tls_config = create_tls_client();
let client = Client::builder()
    .use_preconfigured_tls(tls_config)
    .build()
    .unwrap();
```

#### TLS 服务器 (Axum)

```rust
use axum::{Router, routing::get};
use axum_server::tls_rustls::RustlsConfig;
use std::net::SocketAddr;

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello, HTTPS!" }));
    
    // 配置 TLS
    let config = RustlsConfig::from_pem_file(
        "cert.pem",
        "key.pem"
    ).await.unwrap();
    
    let addr = SocketAddr::from(([0, 0, 0, 0], 3000));
    
    axum_server::bind_rustls(addr, config)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

---

### 3. argon2 (密码哈希 ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add argon2`  
**用途**: 安全的密码哈希算法

#### 核心特性3

- ✅ 2015 密码哈希竞赛冠军
- ✅ 抗 GPU 攻击
- ✅ 可配置的资源消耗
- ✅ PHC 标准格式

#### 基础用法

```rust
use argon2::{
    password_hash::{
        rand_core::OsRng,
        PasswordHash, PasswordHasher, PasswordVerifier, SaltString
    },
    Argon2
};

// 注册：哈希密码
pub fn hash_password(password: &str) -> Result<String, argon2::password_hash::Error> {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default();
    
    let password_hash = argon2.hash_password(password.as_bytes(), &salt)?;
    
    Ok(password_hash.to_string())
}

// 登录：验证密码
pub fn verify_password(password: &str, hash: &str) -> Result<bool, argon2::password_hash::Error> {
    let parsed_hash = PasswordHash::new(hash)?;
    let argon2 = Argon2::default();
    
    match argon2.verify_password(password.as_bytes(), &parsed_hash) {
        Ok(()) => Ok(true),
        Err(_) => Ok(false),
    }
}
```

#### 高级配置

```rust
use argon2::{
    Argon2, 
    Algorithm, 
    Version, 
    Params
};

// 生产环境配置
let params = Params::new(
    65536,      // m_cost (64 MiB)
    3,          // t_cost (3 iterations)
    4,          // p_cost (4 parallel threads)
    None        // output length
).unwrap();

let argon2 = Argon2::new(
    Algorithm::Argon2id,
    Version::V0x13,
    params
);
```

---

### 4. sha2 (哈希函数 ⭐⭐⭐⭐)

**添加依赖**: `cargo add sha2`  
**用途**: SHA-2 系列哈希函数

```rust
use sha2::{Sha256, Sha512, Digest};

// SHA-256
let mut hasher = Sha256::new();
hasher.update(b"hello world");
let result = hasher.finalize();
println!("SHA-256: {:x}", result);

// SHA-512
let result = Sha512::digest(b"hello world");
println!("SHA-512: {:x}", result);
```

---

### 5. blake3 (现代哈希 💡)

**添加依赖**: `cargo add blake3`  
**用途**: 极快的密码学哈希

```rust
use blake3;

// 简单哈希
let hash = blake3::hash(b"hello world");
println!("BLAKE3: {}", hash);

// 流式哈希
let mut hasher = blake3::Hasher::new();
hasher.update(b"hello");
hasher.update(b" ");
hasher.update(b"world");
let hash = hasher.finalize();
```

---

### 6. jsonwebtoken (JWT ⭐⭐⭐⭐)

**添加依赖**: `cargo add jsonwebtoken serde`  
**用途**: JSON Web Token 实现

#### 生成 JWT

```rust
use jsonwebtoken::{encode, decode, Header, Algorithm, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct Claims {
    sub: String,
    exp: usize,
    iat: usize,
}

fn create_token(user_id: &str, secret: &[u8]) -> String {
    let claims = Claims {
        sub: user_id.to_string(),
        exp: (chrono::Utc::now() + chrono::Duration::hours(24)).timestamp() as usize,
        iat: chrono::Utc::now().timestamp() as usize,
    };
    
    encode(
        &Header::default(),
        &claims,
        &EncodingKey::from_secret(secret)
    ).unwrap()
}

fn verify_token(token: &str, secret: &[u8]) -> Result<Claims, jsonwebtoken::errors::Error> {
    let token_data = decode::<Claims>(
        token,
        &DecodingKey::from_secret(secret),
        &Validation::new(Algorithm::HS256)
    )?;
    
    Ok(token_data.claims)
}
```

---

### 7. oauth2 (OAuth 2.0 💡)

**添加依赖**: `cargo add oauth2`  
**用途**: OAuth 2.0 客户端实现

```rust
use oauth2::{
    AuthUrl, ClientId, ClientSecret, TokenUrl,
    basic::BasicClient,
    AuthorizationCode,
    CsrfToken,
    PkceCodeChallenge,
    RedirectUrl,
    Scope,
};

// 创建 OAuth 客户端
let client = BasicClient::new(
    ClientId::new("client_id".to_string()),
    Some(ClientSecret::new("client_secret".to_string())),
    AuthUrl::new("https://auth.example.com/authorize".to_string()).unwrap(),
    Some(TokenUrl::new("https://auth.example.com/token".to_string()).unwrap())
)
.set_redirect_uri(RedirectUrl::new("http://localhost:8080/callback".to_string()).unwrap());

// 生成授权 URL
let (pkce_challenge, pkce_verifier) = PkceCodeChallenge::new_random_sha256();

let (auth_url, csrf_token) = client
    .authorize_url(CsrfToken::new_random)
    .add_scope(Scope::new("read".to_string()))
    .add_scope(Scope::new("write".to_string()))
    .set_pkce_challenge(pkce_challenge)
    .url();
```

---

## 💡 最佳实践

### 1. 密钥管理

```rust
use std::env;

// ❌ 错误：硬编码密钥
const SECRET_KEY: &[u8] = b"my-secret-key";

// ✅ 正确：环境变量
fn get_secret_key() -> Vec<u8> {
    env::var("SECRET_KEY")
        .expect("SECRET_KEY must be set")
        .into_bytes()
}

// ✅ 更好：专用密钥管理
use aws_sdk_secretsmanager::Client;

async fn get_secret_from_aws(secret_name: &str) -> String {
    let config = aws_config::load_from_env().await;
    let client = Client::new(&config);
    
    let response = client
        .get_secret_value()
        .secret_id(secret_name)
        .send()
        .await
        .unwrap();
    
    response.secret_string().unwrap().to_string()
}
```

### 2. 密码存储

```rust
use argon2::{Argon2, PasswordHasher, PasswordVerifier};
use argon2::password_hash::{SaltString, PasswordHash};
use rand_core::OsRng;

pub struct PasswordService;

impl PasswordService {
    // 注册时：哈希密码
    pub fn hash_password(password: &str) -> Result<String, argon2::password_hash::Error> {
        let salt = SaltString::generate(&mut OsRng);
        let argon2 = Argon2::default();
        
        let hash = argon2.hash_password(password.as_bytes(), &salt)?;
        Ok(hash.to_string())
    }
    
    // 登录时：验证密码
    pub fn verify_password(password: &str, hash: &str) -> Result<bool, argon2::password_hash::Error> {
        let parsed_hash = PasswordHash::new(hash)?;
        let argon2 = Argon2::default();
        
        match argon2.verify_password(password.as_bytes(), &parsed_hash) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }
}
```

### 3. API 认证

```rust
use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey};
use serde::{Serialize, Deserialize};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Serialize, Deserialize)]
struct TokenClaims {
    sub: String,      // 用户 ID
    exp: u64,         // 过期时间
    iat: u64,         // 签发时间
    role: String,     // 用户角色
}

pub struct JwtService {
    secret: Vec<u8>,
}

impl JwtService {
    pub fn new(secret: Vec<u8>) -> Self {
        Self { secret }
    }
    
    pub fn create_token(&self, user_id: &str, role: &str, ttl_hours: u64) -> String {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let claims = TokenClaims {
            sub: user_id.to_string(),
            exp: now + (ttl_hours * 3600),
            iat: now,
            role: role.to_string(),
        };
        
        encode(
            &Header::default(),
            &claims,
            &EncodingKey::from_secret(&self.secret)
        ).unwrap()
    }
    
    pub fn verify_token(&self, token: &str) -> Result<TokenClaims, jsonwebtoken::errors::Error> {
        let token_data = decode::<TokenClaims>(
            token,
            &DecodingKey::from_secret(&self.secret),
            &Validation::default()
        )?;
        
        Ok(token_data.claims)
    }
}
```

---

## 📊 工具对比

### 加密库对比

| 工具 | 场景 | 性能 | 安全性 | 易用性 | 推荐度 |
|------|------|------|--------|--------|--------|
| **ring** | 通用加密 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | 🌟 强推 |
| **RustCrypto** | 纯 Rust 生态 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 💡 推荐 |
| **sodiumoxide** | libsodium 绑定 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 💡 推荐 |

### TLS 库对比

| 工具 | 优势 | 劣势 | 推荐度 |
|------|------|------|--------|
| **rustls** | 纯 Rust, 内存安全 | 生态较小 | 🌟 首选 |
| **openssl** | 成熟, 生态大 | C 依赖, 不安全 | 💡 兼容性 |
| **native-tls** | 系统原生 | 平台差异 | 💡 特定场景 |

---

## 🔗 相关资源

- [RustCrypto Organization](https://github.com/RustCrypto)
- [rustls Documentation](https://docs.rs/rustls/)
- [OWASP Cryptographic Storage](https://cheatsheetseries.owasp.org/cheatsheets/Cryptographic_Storage_Cheat_Sheet.html)
- [NIST Cryptographic Standards](https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines)

---

**导航**: [返回横切关注点](../README.md) | [下一类别：可观测性](../observability/README.md)
