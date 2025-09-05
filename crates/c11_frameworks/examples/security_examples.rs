//! 安全相关示例
//! 
//! 展示Rust Web应用的安全特性，包括：
//! - JWT认证和授权
//! - 密码加密和验证
//! - API密钥管理
//! - 请求限流和安全头
//! - 输入验证和清理
//! - 会话管理
//! - 加密通信

use axum::{
    extract::{Request, State},
    http::{HeaderMap, StatusCode, HeaderValue},
    middleware,
    response::{IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
use jsonwebtoken::{decode, encode, Algorithm, DecodingKey, EncodingKey, Header, Validation};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::sync::RwLock;
use tower::ServiceBuilder;
use tower_http::{
    cors::CorsLayer,
    limit::RequestBodyLimitLayer,
    set_header::SetResponseHeaderLayer,
};
use tracing::{info, warn, error, debug};
use uuid::Uuid;
use argon2::{Argon2, PasswordHash, PasswordHasher, PasswordVerifier};
use argon2::password_hash::{rand_core::OsRng, SaltString};
use base64::{Engine as _, engine::general_purpose};
use hmac::{Hmac, Mac};
use sha2::{Sha256, Sha512};
use aes_gcm::{Aes256Gcm, Key, Nonce};
use aes_gcm::aead::{Aead, NewAead};
use rand::Rng;

/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub users: Arc<RwLock<HashMap<String, User>>>,
    pub sessions: Arc<RwLock<HashMap<String, Session>>>,
    pub api_keys: Arc<RwLock<HashMap<String, ApiKey>>>,
    pub rate_limiter: Arc<RwLock<HashMap<String, RateLimitInfo>>>,
    pub jwt_secret: String,
    pub encryption_key: [u8; 32],
}

/// 用户模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub username: String,
    pub email: String,
    pub password_hash: String,
    pub role: UserRole,
    pub is_active: bool,
    pub created_at: u64,
    pub last_login: Option<u64>,
}

/// 用户角色
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum UserRole {
    Admin,
    User,
    Guest,
}

/// 会话模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Session {
    pub id: String,
    pub user_id: String,
    pub created_at: u64,
    pub expires_at: u64,
    pub ip_address: String,
    pub user_agent: String,
    pub is_active: bool,
}

/// API密钥模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApiKey {
    pub id: String,
    pub key_hash: String,
    pub user_id: String,
    pub name: String,
    pub permissions: Vec<String>,
    pub created_at: u64,
    pub expires_at: Option<u64>,
    pub last_used: Option<u64>,
    pub is_active: bool,
}

/// 限流信息
#[derive(Debug, Clone)]
pub struct RateLimitInfo {
    pub requests: u32,
    pub window_start: u64,
    pub blocked_until: Option<u64>,
}

/// JWT声明
#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String, // 用户ID
    pub username: String,
    pub role: String,
    pub exp: u64,    // 过期时间
    pub iat: u64,    // 签发时间
    pub jti: String, // JWT ID
}

/// 登录请求
#[derive(Debug, Deserialize)]
pub struct LoginRequest {
    pub username: String,
    pub password: String,
    pub remember_me: Option<bool>,
}

/// 注册请求
#[derive(Debug, Deserialize)]
pub struct RegisterRequest {
    pub username: String,
    pub email: String,
    pub password: String,
}

/// 用户响应
#[derive(Debug, Serialize)]
pub struct UserResponse {
    pub id: String,
    pub username: String,
    pub email: String,
    pub role: UserRole,
    pub created_at: u64,
}

/// 登录响应
#[derive(Debug, Serialize)]
pub struct LoginResponse {
    pub access_token: String,
    pub refresh_token: String,
    pub user: UserResponse,
    pub expires_in: u64,
}

/// 错误响应
#[derive(Debug, Serialize)]
pub struct ErrorResponse {
    pub error: String,
    pub message: String,
    pub code: String,
}

/// 密码管理器
pub struct PasswordManager;

impl PasswordManager {
    /// 哈希密码
    pub fn hash_password(password: &str) -> Result<String, String> {
        let salt = SaltString::generate(&mut OsRng);
        let argon2 = Argon2::default();
        
        let password_hash = argon2
            .hash_password(password.as_bytes(), &salt)
            .map_err(|e| format!("密码哈希失败: {}", e))?;
        
        Ok(password_hash.to_string())
    }
    
    /// 验证密码
    pub fn verify_password(password: &str, hash: &str) -> Result<bool, String> {
        let parsed_hash = PasswordHash::new(hash)
            .map_err(|e| format!("密码哈希解析失败: {}", e))?;
        
        let argon2 = Argon2::default();
        let is_valid = argon2.verify_password(password.as_bytes(), &parsed_hash).is_ok();
        
        Ok(is_valid)
    }
}

/// JWT管理器
pub struct JwtManager {
    encoding_key: EncodingKey,
    decoding_key: DecodingKey,
    validation: Validation,
}

impl JwtManager {
    pub fn new(secret: &str) -> Self {
        let encoding_key = EncodingKey::from_secret(secret.as_ref());
        let decoding_key = DecodingKey::from_secret(secret.as_ref());
        let mut validation = Validation::new(Algorithm::HS256);
        validation.validate_exp = true;
        validation.validate_iat = true;
        
        Self {
            encoding_key,
            decoding_key,
            validation,
        }
    }
    
    /// 生成访问令牌
    pub fn generate_access_token(&self, user: &User) -> Result<String, String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let claims = Claims {
            sub: user.id.clone(),
            username: user.username.clone(),
            role: format!("{:?}", user.role),
            exp: now + 3600, // 1小时过期
            iat: now,
            jti: Uuid::new_v4().to_string(),
        };
        
        encode(&Header::default(), &claims, &self.encoding_key)
            .map_err(|e| format!("JWT编码失败: {}", e))
    }
    
    /// 生成刷新令牌
    pub fn generate_refresh_token(&self, user: &User) -> Result<String, String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let claims = Claims {
            sub: user.id.clone(),
            username: user.username.clone(),
            role: format!("{:?}", user.role),
            exp: now + 86400 * 7, // 7天过期
            iat: now,
            jti: Uuid::new_v4().to_string(),
        };
        
        encode(&Header::default(), &claims, &self.encoding_key)
            .map_err(|e| format!("JWT编码失败: {}", e))
    }
    
    /// 验证令牌
    pub fn verify_token(&self, token: &str) -> Result<Claims, String> {
        decode::<Claims>(token, &self.decoding_key, &self.validation)
            .map(|data| data.claims)
            .map_err(|e| format!("JWT验证失败: {}", e))
    }
}

/// 加密管理器
pub struct EncryptionManager {
    key: [u8; 32],
}

impl EncryptionManager {
    pub fn new(key: [u8; 32]) -> Self {
        Self { key }
    }
    
    /// 加密数据
    pub fn encrypt(&self, data: &str) -> Result<String, String> {
        let cipher = Aes256Gcm::new(Key::from_slice(&self.key));
        let nonce = Nonce::from_slice(&[0u8; 12]); // 在实际应用中应该使用随机nonce
        
        let ciphertext = cipher
            .encrypt(nonce, data.as_bytes())
            .map_err(|e| format!("加密失败: {}", e))?;
        
        Ok(general_purpose::STANDARD.encode(ciphertext))
    }
    
    /// 解密数据
    pub fn decrypt(&self, encrypted_data: &str) -> Result<String, String> {
        let ciphertext = general_purpose::STANDARD
            .decode(encrypted_data)
            .map_err(|e| format!("Base64解码失败: {}", e))?;
        
        let cipher = Aes256Gcm::new(Key::from_slice(&self.key));
        let nonce = Nonce::from_slice(&[0u8; 12]);
        
        let plaintext = cipher
            .decrypt(nonce, ciphertext.as_ref())
            .map_err(|e| format!("解密失败: {}", e))?;
        
        String::from_utf8(plaintext)
            .map_err(|e| format!("UTF-8解码失败: {}", e))
    }
}

/// API密钥管理器
pub struct ApiKeyManager;

impl ApiKeyManager {
    /// 生成API密钥
    pub fn generate_api_key() -> String {
        let mut rng = rand::thread_rng();
        let key_bytes: [u8; 32] = rng.gen();
        general_purpose::STANDARD.encode(key_bytes)
    }
    
    /// 哈希API密钥
    pub fn hash_api_key(key: &str) -> String {
        let mut mac = Hmac::<Sha256>::new_from_slice(b"api_key_secret")
            .expect("HMAC密钥长度错误");
        mac.update(key.as_bytes());
        let result = mac.finalize();
        general_purpose::STANDARD.encode(result.into_bytes())
    }
    
    /// 验证API密钥
    pub fn verify_api_key(key: &str, hash: &str) -> bool {
        let computed_hash = Self::hash_api_key(key);
        computed_hash == hash
    }
}

/// 输入验证器
pub struct InputValidator;

impl InputValidator {
    /// 验证用户名
    pub fn validate_username(username: &str) -> Result<(), String> {
        if username.len() < 3 || username.len() > 20 {
            return Err("用户名长度必须在3-20个字符之间".to_string());
        }
        
        if !username.chars().all(|c| c.is_alphanumeric() || c == '_' || c == '-') {
            return Err("用户名只能包含字母、数字、下划线和连字符".to_string());
        }
        
        Ok(())
    }
    
    /// 验证邮箱
    pub fn validate_email(email: &str) -> Result<(), String> {
        if !email.contains('@') || !email.contains('.') {
            return Err("邮箱格式无效".to_string());
        }
        
        if email.len() > 254 {
            return Err("邮箱长度不能超过254个字符".to_string());
        }
        
        Ok(())
    }
    
    /// 验证密码
    pub fn validate_password(password: &str) -> Result<(), String> {
        if password.len() < 8 {
            return Err("密码长度至少8个字符".to_string());
        }
        
        if password.len() > 128 {
            return Err("密码长度不能超过128个字符".to_string());
        }
        
        let has_lowercase = password.chars().any(|c| c.is_lowercase());
        let has_uppercase = password.chars().any(|c| c.is_uppercase());
        let has_digit = password.chars().any(|c| c.is_digit(10));
        let has_special = password.chars().any(|c| "!@#$%^&*()_+-=[]{}|;:,.<>?".contains(c));
        
        if !has_lowercase {
            return Err("密码必须包含小写字母".to_string());
        }
        
        if !has_uppercase {
            return Err("密码必须包含大写字母".to_string());
        }
        
        if !has_digit {
            return Err("密码必须包含数字".to_string());
        }
        
        if !has_special {
            return Err("密码必须包含特殊字符".to_string());
        }
        
        Ok(())
    }
    
    /// 清理输入
    pub fn sanitize_input(input: &str) -> String {
        input
            .chars()
            .filter(|c| !c.is_control() || *c == '\n' || *c == '\r' || *c == '\t')
            .collect()
    }
}

/// 限流管理器
pub struct RateLimitManager;

impl RateLimitManager {
    /// 检查限流
    pub fn check_rate_limit(
        rate_limits: &mut HashMap<String, RateLimitInfo>,
        identifier: &str,
        limit: u32,
        window: Duration,
    ) -> bool {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let rate_limit = rate_limits.entry(identifier.to_string()).or_insert(RateLimitInfo {
            requests: 0,
            window_start: now,
            blocked_until: None,
        });
        
        // 检查是否在阻塞期内
        if let Some(blocked_until) = rate_limit.blocked_until {
            if now < blocked_until {
                return false;
            } else {
                rate_limit.blocked_until = None;
            }
        }
        
        // 检查窗口是否过期
        if now - rate_limit.window_start > window.as_secs() {
            rate_limit.requests = 0;
            rate_limit.window_start = now;
        }
        
        // 检查是否超过限制
        if rate_limit.requests >= limit {
            rate_limit.blocked_until = Some(now + 3600); // 阻塞1小时
            return false;
        }
        
        rate_limit.requests += 1;
        true
    }
}

/// 安全头中间件
pub async fn security_headers_middleware(
    request: Request,
    next: middleware::Next,
) -> Response {
    let mut response = next.run(request).await;
    
    // 添加安全头
    let headers = response.headers_mut();
    headers.insert("X-Content-Type-Options", HeaderValue::from_static("nosniff"));
    headers.insert("X-Frame-Options", HeaderValue::from_static("DENY"));
    headers.insert("X-XSS-Protection", HeaderValue::from_static("1; mode=block"));
    headers.insert("Strict-Transport-Security", HeaderValue::from_static("max-age=31536000; includeSubDomains"));
    headers.insert("Content-Security-Policy", HeaderValue::from_static("default-src 'self'"));
    headers.insert("Referrer-Policy", HeaderValue::from_static("strict-origin-when-cross-origin"));
    
    response
}

/// 认证中间件
pub async fn auth_middleware(
    State(state): State<AppState>,
    headers: HeaderMap,
    request: Request,
    next: middleware::Next,
) -> Result<Response, (StatusCode, Json<ErrorResponse>)> {
    let auth_header = headers.get("Authorization");
    
    if let Some(auth_header) = auth_header {
        if let Ok(auth_str) = auth_header.to_str() {
            if auth_str.starts_with("Bearer ") {
                let token = &auth_str[7..];
                let jwt_manager = JwtManager::new(&state.jwt_secret);
                
                match jwt_manager.verify_token(token) {
                    Ok(claims) => {
                        // 验证用户是否存在且活跃
                        let users = state.users.read().await;
                        if let Some(user) = users.get(&claims.sub) {
                            if user.is_active {
                                // 将用户信息添加到请求头中
                                let mut request = request;
                                request.headers_mut().insert(
                                    "X-User-ID",
                                    HeaderValue::from_str(&user.id).unwrap(),
                                );
                                request.headers_mut().insert(
                                    "X-User-Role",
                                    HeaderValue::from_str(&format!("{:?}", user.role)).unwrap(),
                                );
                                
                                return Ok(next.run(request).await);
                            }
                        }
                    }
                    Err(_) => {
                        return Err((
                            StatusCode::UNAUTHORIZED,
                            Json(ErrorResponse {
                                error: "INVALID_TOKEN".to_string(),
                                message: "无效的访问令牌".to_string(),
                                code: "AUTH_ERROR".to_string(),
                            }),
                        ));
                    }
                }
            }
        }
    }
    
    Err((
        StatusCode::UNAUTHORIZED,
        Json(ErrorResponse {
            error: "MISSING_TOKEN".to_string(),
            message: "缺少访问令牌".to_string(),
            code: "AUTH_ERROR".to_string(),
        }),
    ))
}

/// 授权中间件
pub async fn authorization_middleware(
    required_role: UserRole,
    headers: HeaderMap,
    request: Request,
    next: middleware::Next,
) -> Result<Response, (StatusCode, Json<ErrorResponse>)> {
    let user_role_header = headers.get("X-User-Role");
    
    if let Some(role_header) = user_role_header {
        if let Ok(role_str) = role_header.to_str() {
            let user_role = match role_str {
                "Admin" => UserRole::Admin,
                "User" => UserRole::User,
                "Guest" => UserRole::Guest,
                _ => {
                    return Err((
                        StatusCode::FORBIDDEN,
                        Json(ErrorResponse {
                            error: "INVALID_ROLE".to_string(),
                            message: "无效的用户角色".to_string(),
                            code: "AUTHZ_ERROR".to_string(),
                        }),
                    ));
                }
            };
            
            // 检查权限
            let has_permission = match (&user_role, &required_role) {
                (UserRole::Admin, _) => true,
                (UserRole::User, UserRole::User) => true,
                (UserRole::User, UserRole::Guest) => true,
                (UserRole::Guest, UserRole::Guest) => true,
                _ => false,
            };
            
            if has_permission {
                return Ok(next.run(request).await);
            }
        }
    }
    
    Err((
        StatusCode::FORBIDDEN,
        Json(ErrorResponse {
            error: "INSUFFICIENT_PERMISSIONS".to_string(),
            message: "权限不足".to_string(),
            code: "AUTHZ_ERROR".to_string(),
        }),
    ))
}

/// 限流中间件
pub async fn rate_limit_middleware(
    State(state): State<AppState>,
    headers: HeaderMap,
    request: Request,
    next: middleware::Next,
) -> Result<Response, (StatusCode, Json<ErrorResponse>)> {
    let client_ip = headers
        .get("X-Forwarded-For")
        .or_else(|| headers.get("X-Real-IP"))
        .and_then(|h| h.to_str().ok())
        .unwrap_or("unknown");
    
    let mut rate_limits = state.rate_limiter.write().await;
    
    if !RateLimitManager::check_rate_limit(
        &mut rate_limits,
        client_ip,
        100, // 每小时100个请求
        Duration::from_secs(3600),
    ) {
        return Err((
            StatusCode::TOO_MANY_REQUESTS,
            Json(ErrorResponse {
                error: "RATE_LIMIT_EXCEEDED".to_string(),
                message: "请求频率过高".to_string(),
                code: "RATE_LIMIT_ERROR".to_string(),
            }),
        ));
    }
    
    Ok(next.run(request).await)
}

/// 用户注册
async fn register(
    State(state): State<AppState>,
    Json(payload): Json<RegisterRequest>,
) -> Result<Json<UserResponse>, (StatusCode, Json<ErrorResponse>)> {
    // 验证输入
    if let Err(e) = InputValidator::validate_username(&payload.username) {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "INVALID_USERNAME".to_string(),
                message: e,
                code: "VALIDATION_ERROR".to_string(),
            }),
        ));
    }
    
    if let Err(e) = InputValidator::validate_email(&payload.email) {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "INVALID_EMAIL".to_string(),
                message: e,
                code: "VALIDATION_ERROR".to_string(),
            }),
        ));
    }
    
    if let Err(e) = InputValidator::validate_password(&payload.password) {
        return Err((
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse {
                error: "INVALID_PASSWORD".to_string(),
                message: e,
                code: "VALIDATION_ERROR".to_string(),
            }),
        ));
    }
    
    // 清理输入
    let username = InputValidator::sanitize_input(&payload.username);
    let email = InputValidator::sanitize_input(&payload.email);
    
    // 检查用户是否已存在
    let mut users = state.users.write().await;
    if users.values().any(|u| u.username == username || u.email == email) {
        return Err((
            StatusCode::CONFLICT,
            Json(ErrorResponse {
                error: "USER_EXISTS".to_string(),
                message: "用户名或邮箱已存在".to_string(),
                code: "CONFLICT_ERROR".to_string(),
            }),
        ));
    }
    
    // 创建用户
    let user_id = Uuid::new_v4().to_string();
    let password_hash = PasswordManager::hash_password(&payload.password)
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(ErrorResponse {
                    error: "HASH_ERROR".to_string(),
                    message: e,
                    code: "INTERNAL_ERROR".to_string(),
                }),
            )
        })?;
    
    let user = User {
        id: user_id.clone(),
        username: username.clone(),
        email: email.clone(),
        password_hash,
        role: UserRole::User,
        is_active: true,
        created_at: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        last_login: None,
    };
    
    users.insert(user_id.clone(), user.clone());
    drop(users);
    
    let response = UserResponse {
        id: user.id,
        username: user.username,
        email: user.email,
        role: user.role,
        created_at: user.created_at,
    };
    
    info!("用户注册成功: {}", username);
    Ok(Json(response))
}

/// 用户登录
async fn login(
    State(state): State<AppState>,
    Json(payload): Json<LoginRequest>,
) -> Result<Json<LoginResponse>, (StatusCode, Json<ErrorResponse>)> {
    // 查找用户
    let users = state.users.read().await;
    let user = users.values().find(|u| u.username == payload.username);
    
    if let Some(user) = user {
        if !user.is_active {
            return Err((
                StatusCode::FORBIDDEN,
                Json(ErrorResponse {
                    error: "ACCOUNT_DISABLED".to_string(),
                    message: "账户已被禁用".to_string(),
                    code: "AUTH_ERROR".to_string(),
                }),
            ));
        }
        
        // 验证密码
        if PasswordManager::verify_password(&payload.password, &user.password_hash)
            .map_err(|e| {
                (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    Json(ErrorResponse {
                        error: "VERIFY_ERROR".to_string(),
                        message: e,
                        code: "INTERNAL_ERROR".to_string(),
                    }),
                )
            })?
        {
            // 生成令牌
            let jwt_manager = JwtManager::new(&state.jwt_secret);
            let access_token = jwt_manager.generate_access_token(user)
                .map_err(|e| {
                    (
                        StatusCode::INTERNAL_SERVER_ERROR,
                        Json(ErrorResponse {
                            error: "TOKEN_ERROR".to_string(),
                            message: e,
                            code: "INTERNAL_ERROR".to_string(),
                        }),
                    )
                })?;
            
            let refresh_token = jwt_manager.generate_refresh_token(user)
                .map_err(|e| {
                    (
                        StatusCode::INTERNAL_SERVER_ERROR,
                        Json(ErrorResponse {
                            error: "TOKEN_ERROR".to_string(),
                            message: e,
                            code: "INTERNAL_ERROR".to_string(),
                        }),
                    )
                })?;
            
            // 创建会话
            let session_id = Uuid::new_v4().to_string();
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs();
            
            let session = Session {
                id: session_id,
                user_id: user.id.clone(),
                created_at: now,
                expires_at: now + 86400 * 7, // 7天
                ip_address: "127.0.0.1".to_string(), // 在实际应用中从请求中获取
                user_agent: "test".to_string(), // 在实际应用中从请求中获取
                is_active: true,
            };
            
            let mut sessions = state.sessions.write().await;
            sessions.insert(session.id.clone(), session);
            drop(sessions);
            
            // 更新最后登录时间
            let mut users = state.users.write().await;
            if let Some(user) = users.get_mut(&user.id) {
                user.last_login = Some(now);
            }
            drop(users);
            
            let response = LoginResponse {
                access_token,
                refresh_token,
                user: UserResponse {
                    id: user.id.clone(),
                    username: user.username.clone(),
                    email: user.email.clone(),
                    role: user.role.clone(),
                    created_at: user.created_at,
                },
                expires_in: 3600,
            };
            
            info!("用户登录成功: {}", user.username);
            Ok(Json(response))
        } else {
            Err((
                StatusCode::UNAUTHORIZED,
                Json(ErrorResponse {
                    error: "INVALID_CREDENTIALS".to_string(),
                    message: "用户名或密码错误".to_string(),
                    code: "AUTH_ERROR".to_string(),
                }),
            ))
        }
    } else {
        Err((
            StatusCode::UNAUTHORIZED,
            Json(ErrorResponse {
                error: "INVALID_CREDENTIALS".to_string(),
                message: "用户名或密码错误".to_string(),
                code: "AUTH_ERROR".to_string(),
            }),
        ))
    }
}

/// 获取当前用户信息
async fn get_current_user(
    State(state): State<AppState>,
    headers: HeaderMap,
) -> Result<Json<UserResponse>, (StatusCode, Json<ErrorResponse>)> {
    let user_id = headers
        .get("X-User-ID")
        .and_then(|h| h.to_str().ok())
        .ok_or_else(|| {
            (
                StatusCode::UNAUTHORIZED,
                Json(ErrorResponse {
                    error: "MISSING_USER_ID".to_string(),
                    message: "缺少用户ID".to_string(),
                    code: "AUTH_ERROR".to_string(),
                }),
            )
        })?;
    
    let users = state.users.read().await;
    let user = users.get(user_id).ok_or_else(|| {
        (
            StatusCode::NOT_FOUND,
            Json(ErrorResponse {
                error: "USER_NOT_FOUND".to_string(),
                message: "用户不存在".to_string(),
                code: "NOT_FOUND_ERROR".to_string(),
            }),
        )
    })?;
    
    let response = UserResponse {
        id: user.id.clone(),
        username: user.username.clone(),
        email: user.email.clone(),
        role: user.role.clone(),
        created_at: user.created_at,
    };
    
    Ok(Json(response))
}

/// 创建API密钥
async fn create_api_key(
    State(state): State<AppState>,
    headers: HeaderMap,
    Json(payload): Json<serde_json::Value>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let user_id = headers
        .get("X-User-ID")
        .and_then(|h| h.to_str().ok())
        .ok_or_else(|| {
            (
                StatusCode::UNAUTHORIZED,
                Json(ErrorResponse {
                    error: "MISSING_USER_ID".to_string(),
                    message: "缺少用户ID".to_string(),
                    code: "AUTH_ERROR".to_string(),
                }),
            )
        })?;
    
    let name = payload["name"].as_str().unwrap_or("API Key");
    let permissions = payload["permissions"]
        .as_array()
        .map(|arr| arr.iter().filter_map(|v| v.as_str().map(|s| s.to_string())).collect())
        .unwrap_or_else(|| vec!["read".to_string()]);
    
    let api_key = ApiKeyManager::generate_api_key();
    let key_hash = ApiKeyManager::hash_api_key(&api_key);
    
    let api_key_record = ApiKey {
        id: Uuid::new_v4().to_string(),
        key_hash,
        user_id: user_id.to_string(),
        name: name.to_string(),
        permissions,
        created_at: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        expires_at: None,
        last_used: None,
        is_active: true,
    };
    
    let mut api_keys = state.api_keys.write().await;
    api_keys.insert(api_key_record.id.clone(), api_key_record);
    drop(api_keys);
    
    let response = serde_json::json!({
        "api_key": api_key,
        "id": api_key_record.id,
        "name": name,
        "permissions": permissions,
        "created_at": api_key_record.created_at
    });
    
    info!("API密钥创建成功: {}", name);
    Ok(Json(response))
}

/// 加密数据
async fn encrypt_data(
    State(state): State<AppState>,
    Json(payload): Json<serde_json::Value>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let data = payload["data"].as_str().unwrap_or("");
    
    let encryption_manager = EncryptionManager::new(state.encryption_key);
    let encrypted = encryption_manager.encrypt(data)
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(ErrorResponse {
                    error: "ENCRYPTION_ERROR".to_string(),
                    message: e,
                    code: "INTERNAL_ERROR".to_string(),
                }),
            )
        })?;
    
    let response = serde_json::json!({
        "encrypted_data": encrypted
    });
    
    Ok(Json(response))
}

/// 解密数据
async fn decrypt_data(
    State(state): State<AppState>,
    Json(payload): Json<serde_json::Value>,
) -> Result<Json<serde_json::Value>, (StatusCode, Json<ErrorResponse>)> {
    let encrypted_data = payload["encrypted_data"].as_str().unwrap_or("");
    
    let encryption_manager = EncryptionManager::new(state.encryption_key);
    let decrypted = encryption_manager.decrypt(encrypted_data)
        .map_err(|e| {
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(ErrorResponse {
                    error: "DECRYPTION_ERROR".to_string(),
                    message: e,
                    code: "INTERNAL_ERROR".to_string(),
                }),
            )
        })?;
    
    let response = serde_json::json!({
        "decrypted_data": decrypted
    });
    
    Ok(Json(response))
}

/// 创建应用路由
fn create_app(state: AppState) -> Router {
    Router::new()
        .route("/register", post(register))
        .route("/login", post(login))
        .route("/user", get(get_current_user))
        .route("/api-keys", post(create_api_key))
        .route("/encrypt", post(encrypt_data))
        .route("/decrypt", post(decrypt_data))
        .layer(
            ServiceBuilder::new()
                .layer(SetResponseHeaderLayer::overriding(
                    "X-Content-Type-Options",
                    HeaderValue::from_static("nosniff"),
                ))
                .layer(SetResponseHeaderLayer::overriding(
                    "X-Frame-Options",
                    HeaderValue::from_static("DENY"),
                ))
                .layer(SetResponseHeaderLayer::overriding(
                    "X-XSS-Protection",
                    HeaderValue::from_static("1; mode=block"),
                ))
                .layer(RequestBodyLimitLayer::new(1024 * 1024)) // 1MB限制
                .layer(CorsLayer::permissive())
        )
        .layer(middleware::from_fn_with_state(
            state.clone(),
            rate_limit_middleware,
        ))
        .layer(middleware::from_fn(security_headers_middleware))
        .with_state(state)
}

/// 创建受保护的路由
fn create_protected_app(state: AppState) -> Router {
    Router::new()
        .route("/user", get(get_current_user))
        .route("/api-keys", post(create_api_key))
        .layer(middleware::from_fn_with_state(
            state.clone(),
            auth_middleware,
        ))
        .layer(middleware::from_fn_with_state(
            UserRole::User,
            authorization_middleware,
        ))
        .with_state(state)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    // 创建应用状态
    let state = AppState {
        users: Arc::new(RwLock::new(HashMap::new())),
        sessions: Arc::new(RwLock::new(HashMap::new())),
        api_keys: Arc::new(RwLock::new(HashMap::new())),
        rate_limiter: Arc::new(RwLock::new(HashMap::new())),
        jwt_secret: "your-secret-key".to_string(),
        encryption_key: [0u8; 32], // 在实际应用中应该使用安全的随机密钥
    };
    
    // 创建应用
    let app = create_app(state);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    info!("安全服务器启动在 http://0.0.0.0:3000");
    
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_password_manager() {
        let password = "TestPassword123!";
        let hash = PasswordManager::hash_password(password).unwrap();
        assert!(PasswordManager::verify_password(password, &hash).unwrap());
        assert!(!PasswordManager::verify_password("wrong", &hash).unwrap());
    }
    
    #[test]
    fn test_jwt_manager() {
        let jwt_manager = JwtManager::new("test-secret");
        let user = User {
            id: "test-id".to_string(),
            username: "testuser".to_string(),
            email: "test@example.com".to_string(),
            password_hash: "hash".to_string(),
            role: UserRole::User,
            is_active: true,
            created_at: 0,
            last_login: None,
        };
        
        let token = jwt_manager.generate_access_token(&user).unwrap();
        let claims = jwt_manager.verify_token(&token).unwrap();
        assert_eq!(claims.sub, "test-id");
        assert_eq!(claims.username, "testuser");
    }
    
    #[test]
    fn test_encryption_manager() {
        let key = [0u8; 32];
        let manager = EncryptionManager::new(key);
        let data = "test data";
        
        let encrypted = manager.encrypt(data).unwrap();
        let decrypted = manager.decrypt(&encrypted).unwrap();
        assert_eq!(data, decrypted);
    }
    
    #[test]
    fn test_api_key_manager() {
        let key = ApiKeyManager::generate_api_key();
        let hash = ApiKeyManager::hash_api_key(&key);
        assert!(ApiKeyManager::verify_api_key(&key, &hash));
        assert!(!ApiKeyManager::verify_api_key("wrong", &hash));
    }
    
    #[test]
    fn test_input_validator() {
        assert!(InputValidator::validate_username("valid_user").is_ok());
        assert!(InputValidator::validate_username("invalid user").is_err());
        
        assert!(InputValidator::validate_email("test@example.com").is_ok());
        assert!(InputValidator::validate_email("invalid-email").is_err());
        
        assert!(InputValidator::validate_password("ValidPass123!").is_ok());
        assert!(InputValidator::validate_password("weak").is_err());
    }
    
    #[test]
    fn test_rate_limit_manager() {
        let mut rate_limits = HashMap::new();
        
        // 第一次请求应该通过
        assert!(RateLimitManager::check_rate_limit(
            &mut rate_limits,
            "test",
            1,
            Duration::from_secs(1)
        ));
        
        // 第二次请求应该被限制
        assert!(!RateLimitManager::check_rate_limit(
            &mut rate_limits,
            "test",
            1,
            Duration::from_secs(1)
        ));
    }
}
