# Rust安全指南

## 概述

本文档提供了Rust应用程序的安全最佳实践和防护策略，适用于各个软件行业领域。

## 1. 内存安全

### 避免不安全代码

```rust
// 不安全的代码 - 避免使用
unsafe fn dangerous_function(ptr: *mut i32) {
    *ptr = 42; // 可能导致段错误
}

// 安全的替代方案
fn safe_function(data: &mut i32) {
    *data = 42; // 编译器保证安全
}

// 使用智能指针
use std::rc::Rc;
use std::sync::Arc;

pub struct SafeData {
    data: Arc<String>,
}

impl SafeData {
    pub fn new(data: String) -> Self {
        Self {
            data: Arc::new(data),
        }
    }
    
    pub fn get_data(&self) -> Arc<String> {
        Arc::clone(&self.data)
    }
}
```

### 边界检查

```rust
// 安全的数组访问
pub fn safe_array_access(arr: &[i32], index: usize) -> Option<&i32> {
    arr.get(index) // 返回Option，避免越界
}

// 安全的字符串操作
pub fn safe_string_operation(s: &str, start: usize, end: usize) -> Option<&str> {
    if start <= end && end <= s.len() {
        Some(&s[start..end])
    } else {
        None
    }
}

// 安全的数值转换
pub fn safe_conversion(value: i64) -> Option<i32> {
    value.try_into().ok() // 使用try_into避免溢出
}
```

## 2. 密码学安全

### 加密实现

```rust
use ring::aead;
use ring::rand::SystemRandom;

pub struct CryptoService {
    key: aead::UnboundKey,
    rng: SystemRandom,
}

impl CryptoService {
    pub fn new() -> Result<Self, ring::error::Unspecified> {
        let rng = SystemRandom::new();
        let key_bytes = ring::aead::CHACHA20_POLY1305.key_len();
        let mut key_material = vec![0u8; key_bytes];
        rng.fill(&mut key_material)?;
        
        let key = aead::UnboundKey::new(&aead::CHACHA20_POLY1305, &key_material)?;
        
        Ok(Self { key, rng })
    }
    
    pub fn encrypt(&self, data: &[u8]) -> Result<Vec<u8>, ring::error::Unspecified> {
        let nonce_bytes = ring::aead::CHACHA20_POLY1305.nonce_len();
        let mut nonce = vec![0u8; nonce_bytes];
        self.rng.fill(&mut nonce)?;
        
        let nonce = aead::Nonce::assume_unique_for_key(nonce.try_into().unwrap());
        let aad = aead::Aad::empty();
        
        let mut ciphertext = data.to_vec();
        let tag = aead::seal_in_place_separate_tag(&self.key, nonce, aad, &mut ciphertext)?;
        
        // 将nonce和tag附加到密文
        let mut result = nonce.as_ref().to_vec();
        result.extend_from_slice(&ciphertext);
        result.extend_from_slice(tag.as_ref());
        
        Ok(result)
    }
    
    pub fn decrypt(&self, ciphertext: &[u8]) -> Result<Vec<u8>, ring::error::Unspecified> {
        let nonce_len = ring::aead::CHACHA20_POLY1305.nonce_len();
        let tag_len = ring::aead::CHACHA20_POLY1305.tag_len();
        
        if ciphertext.len() < nonce_len + tag_len {
            return Err(ring::error::Unspecified);
        }
        
        let nonce = aead::Nonce::assume_unique_for_key(
            ciphertext[..nonce_len].try_into().unwrap()
        );
        let aad = aead::Aad::empty();
        
        let mut plaintext = ciphertext[nonce_len..ciphertext.len() - tag_len].to_vec();
        let tag = aead::Tag::from_slice(&ciphertext[ciphertext.len() - tag_len..]);
        
        aead::open_in_place(&self.key, nonce, aad, &mut plaintext, tag)?;
        Ok(plaintext)
    }
}
```

### 哈希和签名

```rust
use ring::digest;
use ring::signature::{self, Ed25519KeyPair, KeyPair};

pub struct SignatureService {
    keypair: Ed25519KeyPair,
}

impl SignatureService {
    pub fn new() -> Result<Self, ring::error::Unspecified> {
        let rng = ring::rand::SystemRandom::new();
        let pkcs8_bytes = Ed25519KeyPair::generate_pkcs8(&rng)?;
        let keypair = Ed25519KeyPair::from_pkcs8(pkcs8_bytes.as_ref())?;
        
        Ok(Self { keypair })
    }
    
    pub fn sign(&self, message: &[u8]) -> Result<Vec<u8>, ring::error::Unspecified> {
        let signature = self.keypair.sign(message);
        Ok(signature.as_ref().to_vec())
    }
    
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<bool, ring::error::Unspecified> {
        let public_key = self.keypair.public_key();
        let signature = signature::UnparsedPublicKey::new(
            &signature::ED25519,
            public_key.as_ref(),
        );
        
        match signature.verify(message, signature) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }
}

pub fn secure_hash(data: &[u8]) -> Vec<u8> {
    let hash = digest::digest(&digest::SHA256, data);
    hash.as_ref().to_vec()
}
```

## 3. 输入验证

### 数据验证

```rust
use validator::{Validate, ValidationError};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, Validate)]
pub struct UserInput {
    #[validate(length(min = 3, max = 50))]
    #[validate(regex(path = "USERNAME_REGEX", message = "Invalid username format"))]
    pub username: String,
    
    #[validate(email)]
    pub email: String,
    
    #[validate(length(min = 8))]
    pub password: String,
    
    #[validate(range(min = 0, max = 150))]
    pub age: u8,
}

lazy_static! {
    static ref USERNAME_REGEX: regex::Regex = regex::Regex::new(r"^[a-zA-Z0-9_]+$").unwrap();
}

impl UserInput {
    pub fn validate(&self) -> Result<(), Vec<ValidationError>> {
        self.validate()
    }
    
    pub fn sanitize(&mut self) {
        // 移除危险字符
        self.username = self.username.replace(['<', '>', '"', '\'', '&'], "");
        self.email = self.email.trim().to_lowercase();
    }
}
```

### SQL注入防护

```rust
use sqlx::{PgPool, Row};

pub struct UserRepository {
    pool: PgPool,
}

impl UserRepository {
    pub async fn find_user_by_username(&self, username: &str) -> Result<Option<User>, sqlx::Error> {
        // 使用参数化查询防止SQL注入
        let user = sqlx::query_as!(
            User,
            "SELECT id, username, email FROM users WHERE username = $1",
            username
        )
        .fetch_optional(&self.pool)
        .await?;
        
        Ok(user)
    }
    
    pub async fn create_user(&self, user: &User) -> Result<User, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            "INSERT INTO users (username, email, password_hash) VALUES ($1, $2, $3) RETURNING id, username, email",
            user.username,
            user.email,
            user.password_hash
        )
        .fetch_one(&self.pool)
        .await?;
        
        Ok(user)
    }
}
```

## 4. 认证和授权

### JWT认证

```rust
use jsonwebtoken::{decode, encode, DecodingKey, EncodingKey, Header, Validation};
use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String, // 用户ID
    pub exp: usize,  // 过期时间
    pub iat: usize,  // 签发时间
    pub role: String, // 用户角色
}

pub struct AuthService {
    secret: String,
}

impl AuthService {
    pub fn new(secret: String) -> Self {
        Self { secret }
    }
    
    pub fn generate_token(&self, user_id: &str, role: &str) -> Result<String, jsonwebtoken::errors::Error> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs() as usize;
        
        let claims = Claims {
            sub: user_id.to_string(),
            exp: now + 3600, // 1小时过期
            iat: now,
            role: role.to_string(),
        };
        
        encode(
            &Header::default(),
            &claims,
            &EncodingKey::from_secret(self.secret.as_ref()),
        )
    }
    
    pub fn verify_token(&self, token: &str) -> Result<Claims, jsonwebtoken::errors::Error> {
        let token_data = decode::<Claims>(
            token,
            &DecodingKey::from_secret(self.secret.as_ref()),
            &Validation::default(),
        )?;
        
        Ok(token_data.claims)
    }
}
```

### 基于角色的访问控制

```rust
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Permission {
    Read,
    Write,
    Delete,
    Admin,
}

#[derive(Debug, Clone)]
pub struct Role {
    name: String,
    permissions: Vec<Permission>,
}

pub struct RBACService {
    roles: HashMap<String, Role>,
}

impl RBACService {
    pub fn new() -> Self {
        let mut roles = HashMap::new();
        
        // 定义角色和权限
        roles.insert("user".to_string(), Role {
            name: "user".to_string(),
            permissions: vec![Permission::Read],
        });
        
        roles.insert("admin".to_string(), Role {
            name: "admin".to_string(),
            permissions: vec![Permission::Read, Permission::Write, Permission::Delete, Permission::Admin],
        });
        
        Self { roles }
    }
    
    pub fn has_permission(&self, role: &str, permission: &Permission) -> bool {
        if let Some(role_def) = self.roles.get(role) {
            role_def.permissions.contains(permission)
        } else {
            false
        }
    }
    
    pub fn check_access(&self, user_role: &str, required_permission: &Permission) -> bool {
        self.has_permission(user_role, required_permission)
    }
}
```

## 5. 网络安全

### HTTPS配置

```rust
use tokio_rustls::TlsAcceptor;
use rustls::{ServerConfig, PrivateKey, Certificate};
use std::fs::File;
use std::io::BufReader;

pub struct SecureServer {
    tls_config: ServerConfig,
}

impl SecureServer {
    pub fn new(cert_path: &str, key_path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        // 加载证书
        let cert_file = File::open(cert_path)?;
        let mut cert_reader = BufReader::new(cert_file);
        let certs = rustls_pemfile::certs(&mut cert_reader)?;
        let certs: Vec<Certificate> = certs.into_iter().map(Certificate).collect();
        
        // 加载私钥
        let key_file = File::open(key_path)?;
        let mut key_reader = BufReader::new(key_file);
        let keys = rustls_pemfile::pkcs8_private_keys(&mut key_reader)?;
        let key = PrivateKey(keys[0].clone());
        
        // 创建TLS配置
        let config = ServerConfig::builder()
            .with_safe_defaults()
            .with_no_client_auth()
            .with_single_cert(certs, key)?;
        
        Ok(Self { tls_config: config })
    }
    
    pub async fn start(&self, addr: &str) -> Result<(), Box<dyn std::error::Error>> {
        let acceptor = TlsAcceptor::from(Arc::new(self.tls_config.clone()));
        let listener = tokio::net::TcpListener::bind(addr).await?;
        
        loop {
            let (stream, _) = listener.accept().await?;
            let acceptor = acceptor.clone();
            
            tokio::spawn(async move {
                if let Ok(tls_stream) = acceptor.accept(stream).await {
                    // 处理安全的TLS连接
                    Self::handle_connection(tls_stream).await;
                }
            });
        }
    }
    
    async fn handle_connection(stream: tokio_rustls::TlsStream<tokio::net::TcpStream>) {
        // 处理连接逻辑
    }
}
```

### 请求限流

```rust
use std::collections::HashMap;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;

pub struct RateLimiter {
    requests: Arc<Mutex<HashMap<String, Vec<Instant>>>>,
    max_requests: usize,
    window: Duration,
}

impl RateLimiter {
    pub fn new(max_requests: usize, window: Duration) -> Self {
        Self {
            requests: Arc::new(Mutex::new(HashMap::new())),
            max_requests,
            window,
        }
    }
    
    pub async fn is_allowed(&self, client_id: &str) -> bool {
        let mut requests = self.requests.lock().await;
        let now = Instant::now();
        
        // 清理过期的请求记录
        if let Some(client_requests) = requests.get_mut(client_id) {
            client_requests.retain(|&time| now.duration_since(time) < self.window);
            
            if client_requests.len() < self.max_requests {
                client_requests.push(now);
                true
            } else {
                false
            }
        } else {
            // 新客户端
            requests.insert(client_id.to_string(), vec![now]);
            true
        }
    }
}
```

## 6. 安全配置

### 环境变量管理

```rust
use config::{Config, ConfigError, Environment, File};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct SecurityConfig {
    pub jwt_secret: String,
    pub database_url: String,
    pub redis_url: String,
    pub cors_origins: Vec<String>,
    pub rate_limit_requests: usize,
    pub rate_limit_window_seconds: u64,
}

impl SecurityConfig {
    pub fn load() -> Result<Self, ConfigError> {
        let config = Config::builder()
            // 默认配置
            .add_source(File::with_name("config/default"))
            // 环境特定配置
            .add_source(File::with_name(&format!("config/{}", std::env::var("ENV").unwrap_or("development".to_string()))))
            // 环境变量覆盖
            .add_source(Environment::with_prefix("APP"))
            .build()?;
        
        config.try_deserialize()
    }
}
```

### 安全中间件

```rust
use actix_web::{middleware, web, App, HttpServer};
use actix_web::middleware::{Logger, DefaultHeaders};

pub fn create_secure_app() -> App<()> {
    App::new()
        // 安全头部
        .wrap(DefaultHeaders::new()
            .add(("X-Content-Type-Options", "nosniff"))
            .add(("X-Frame-Options", "DENY"))
            .add(("X-XSS-Protection", "1; mode=block"))
            .add(("Strict-Transport-Security", "max-age=31536000; includeSubDomains"))
            .add(("Content-Security-Policy", "default-src 'self'"))
        )
        // CORS配置
        .wrap(middleware::Cors::default()
            .allowed_origin("https://example.com")
            .allowed_methods(vec!["GET", "POST", "PUT", "DELETE"])
            .allowed_headers(vec![http::header::AUTHORIZATION, http::header::ACCEPT])
            .max_age(3600)
        )
        // 请求日志
        .wrap(Logger::default())
        // 压缩
        .wrap(middleware::Compress::default())
        // 服务路由
        .service(web::scope("/api/v1")
            .service(user_routes())
            .service(admin_routes())
        )
}
```

## 7. 安全测试

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_password_validation() {
        let weak_password = "123456";
        assert!(!is_strong_password(weak_password));
        
        let strong_password = "MySecureP@ssw0rd!";
        assert!(is_strong_password(strong_password));
    }
    
    #[test]
    fn test_sql_injection_prevention() {
        let malicious_input = "'; DROP TABLE users; --";
        let sanitized = sanitize_input(malicious_input);
        assert!(!sanitized.contains("DROP TABLE"));
    }
    
    #[test]
    fn test_jwt_token_validation() {
        let auth_service = AuthService::new("secret".to_string());
        let token = auth_service.generate_token("user123", "user").unwrap();
        let claims = auth_service.verify_token(&token).unwrap();
        
        assert_eq!(claims.sub, "user123");
        assert_eq!(claims.role, "user");
    }
}

fn is_strong_password(password: &str) -> bool {
    password.len() >= 8 &&
    password.chars().any(|c| c.is_uppercase()) &&
    password.chars().any(|c| c.is_lowercase()) &&
    password.chars().any(|c| c.is_numeric()) &&
    password.chars().any(|c| !c.is_alphanumeric())
}

fn sanitize_input(input: &str) -> String {
    input.replace(['<', '>', '"', '\'', '&', ';'], "")
}
```

### 集成测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use actix_web::test;
    
    #[actix_web::test]
    async fn test_secure_endpoint() {
        let app = test::init_service(create_secure_app()).await;
        
        // 测试未认证访问
        let req = test::TestRequest::get()
            .uri("/api/v1/admin/users")
            .to_request();
        let resp = test::call_service(&app, req).await;
        assert_eq!(resp.status(), 401);
        
        // 测试认证访问
        let token = generate_test_token();
        let req = test::TestRequest::get()
            .uri("/api/v1/admin/users")
            .insert_header(("Authorization", format!("Bearer {}", token)))
            .to_request();
        let resp = test::call_service(&app, req).await;
        assert_eq!(resp.status(), 200);
    }
}
```

## 8. 安全监控

### 安全日志

```rust
use tracing::{info, warn, error, instrument};
use serde_json::json;

pub struct SecurityLogger;

impl SecurityLogger {
    pub fn log_login_attempt(user_id: &str, success: bool, ip: &str) {
        if success {
            info!(
                event = "login_success",
                user_id = user_id,
                ip = ip,
                timestamp = chrono::Utc::now().to_rfc3339(),
            );
        } else {
            warn!(
                event = "login_failed",
                user_id = user_id,
                ip = ip,
                timestamp = chrono::Utc::now().to_rfc3339(),
            );
        }
    }
    
    pub fn log_security_violation(event: &str, details: &str, severity: &str) {
        error!(
            event = "security_violation",
            violation_type = event,
            details = details,
            severity = severity,
            timestamp = chrono::Utc::now().to_rfc3339(),
        );
    }
    
    #[instrument(skip(self))]
    pub fn log_sensitive_operation(&self, operation: &str, user_id: &str) {
        info!(
            event = "sensitive_operation",
            operation = operation,
            user_id = user_id,
            timestamp = chrono::Utc::now().to_rfc3339(),
        );
    }
}
```

### 异常检测

```rust
use std::collections::HashMap;
use std::time::{Duration, Instant};

pub struct AnomalyDetector {
    patterns: HashMap<String, Vec<Instant>>,
    thresholds: HashMap<String, usize>,
}

impl AnomalyDetector {
    pub fn new() -> Self {
        let mut thresholds = HashMap::new();
        thresholds.insert("login_attempts".to_string(), 5);
        thresholds.insert("api_requests".to_string(), 100);
        
        Self {
            patterns: HashMap::new(),
            thresholds,
        }
    }
    
    pub fn record_event(&mut self, event_type: &str, client_id: &str) -> bool {
        let key = format!("{}:{}", event_type, client_id);
        let now = Instant::now();
        
        let events = self.patterns.entry(key.clone()).or_insert_with(Vec::new);
        
        // 清理1小时前的记录
        events.retain(|&time| now.duration_since(time) < Duration::from_secs(3600));
        events.push(now);
        
        // 检查是否超过阈值
        if let Some(&threshold) = self.thresholds.get(event_type) {
            if events.len() > threshold {
                SecurityLogger::log_security_violation(
                    "rate_limit_exceeded",
                    &format!("{} exceeded threshold of {}", event_type, threshold),
                    "high"
                );
                return false;
            }
        }
        
        true
    }
}
```

## 总结

安全是一个持续的过程，需要：

1. **防御深度**: 多层安全防护
2. **最小权限**: 只授予必要的权限
3. **安全编码**: 遵循安全编码实践
4. **持续监控**: 实时监控安全事件
5. **定期审计**: 定期安全评估

通过遵循这些安全最佳实践，可以构建出安全可靠的Rust应用程序。
