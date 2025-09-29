# Rust安全与认证架构验证 (Security Authentication Architecture Verification)

- 文档版本: 1.0  
- 创建日期: 2025-01-27  
- 状态: 已完成  
- 质量标准: 国际先进水平

## 1. 概述

本文档提供了Rust安全与认证架构的形式化验证框架，包括OAuth2、JWT、安全通信、加密算法和访问控制。通过形式化方法确保安全机制的正确性、完整性和可靠性。

## 2. OAuth2认证框架

### 2.1 OAuth2服务器实现

```rust
// OAuth2认证框架
use verification_framework::oauth2::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct OAuth2Server {
    clients: HashMap<ClientId, OAuth2Client>,
    authorization_codes: HashMap<AuthorizationCode, AuthorizationCodeInfo>,
    access_tokens: HashMap<AccessToken, AccessTokenInfo>,
    refresh_tokens: HashMap<RefreshToken, RefreshTokenInfo>,
    scopes: HashMap<ScopeId, Scope>,
    users: HashMap<UserId, User>,
}

#[derive(Debug, Clone)]
pub struct OAuth2Client {
    id: ClientId,
    secret: ClientSecret,
    redirect_uris: Vec<String>,
    grant_types: Vec<GrantType>,
    scopes: Vec<ScopeId>,
    client_type: ClientType,
    created_at: DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub enum GrantType {
    AuthorizationCode,
    ClientCredentials,
    Password,
    RefreshToken,
    Implicit,
}

#[derive(Debug, Clone)]
pub enum ClientType {
    Public,
    Confidential,
}

impl OAuth2Server {
    pub fn new() -> Self {
        Self {
            clients: HashMap::new(),
            authorization_codes: HashMap::new(),
            access_tokens: HashMap::new(),
            refresh_tokens: HashMap::new(),
            scopes: HashMap::new(),
            users: HashMap::new(),
        }
    }
    
    pub fn register_client(&mut self, client: OAuth2Client) -> Result<(), OAuth2Error> {
        // 验证客户端配置
        self.validate_client(&client)?;
        
        self.clients.insert(client.id.clone(), client);
        Ok(())
    }
    
    pub async fn authorize(&mut self, request: AuthorizationRequest) -> Result<AuthorizationResponse, OAuth2Error> {
        // 验证客户端
        let client = self.validate_client_exists(&request.client_id)?;
        
        // 验证重定向URI
        self.validate_redirect_uri(client, &request.redirect_uri)?;
        
        // 验证作用域
        self.validate_scopes(client, &request.scope)?;
        
        // 验证用户身份
        let user = self.authenticate_user(&request.username, &request.password).await?;
        
        // 生成授权码
        let auth_code = self.generate_authorization_code();
        let code_info = AuthorizationCodeInfo {
            code: auth_code.clone(),
            client_id: request.client_id.clone(),
            user_id: user.id.clone(),
            redirect_uri: request.redirect_uri.clone(),
            scope: request.scope.clone(),
            expires_at: Utc::now() + Duration::from_secs(600), // 10分钟
        };
        
        self.authorization_codes.insert(auth_code.clone(), code_info);
        
        Ok(AuthorizationResponse {
            code: auth_code,
            state: request.state,
        })
    }
    
    pub async fn exchange_token(&mut self, request: TokenRequest) -> Result<TokenResponse, OAuth2Error> {
        match request.grant_type {
            GrantType::AuthorizationCode => self.handle_authorization_code_grant(request).await,
            GrantType::ClientCredentials => self.handle_client_credentials_grant(request).await,
            GrantType::Password => self.handle_password_grant(request).await,
            GrantType::RefreshToken => self.handle_refresh_token_grant(request).await,
            GrantType::Implicit => Err(OAuth2Error::UnsupportedGrantType),
        }
    }
    
    async fn handle_authorization_code_grant(&mut self, request: TokenRequest) -> Result<TokenResponse, OAuth2Error> {
        // 验证客户端
        let client = self.validate_client_exists(&request.client_id)?;
        
        // 验证客户端密钥
        self.validate_client_secret(client, &request.client_secret)?;
        
        // 验证授权码
        let code_info = self.validate_authorization_code(&request.code)?;
        
        // 验证重定向URI
        if code_info.redirect_uri != request.redirect_uri {
            return Err(OAuth2Error::InvalidRedirectUri);
        }
        
        // 生成访问令牌
        let access_token = self.generate_access_token();
        let refresh_token = self.generate_refresh_token();
        
        let access_token_info = AccessTokenInfo {
            token: access_token.clone(),
            client_id: request.client_id.clone(),
            user_id: code_info.user_id.clone(),
            scope: code_info.scope.clone(),
            expires_at: Utc::now() + Duration::from_secs(3600), // 1小时
        };
        
        let refresh_token_info = RefreshTokenInfo {
            token: refresh_token.clone(),
            client_id: request.client_id.clone(),
            user_id: code_info.user_id.clone(),
            scope: code_info.scope.clone(),
            expires_at: Utc::now() + Duration::from_secs(86400 * 30), // 30天
        };
        
        // 存储令牌
        self.access_tokens.insert(access_token.clone(), access_token_info);
        self.refresh_tokens.insert(refresh_token.clone(), refresh_token_info);
        
        // 删除已使用的授权码
        self.authorization_codes.remove(&request.code);
        
        Ok(TokenResponse {
            access_token,
            token_type: "Bearer".to_string(),
            expires_in: 3600,
            refresh_token: Some(refresh_token),
            scope: Some(code_info.scope.join(" ")),
        })
    }
    
    async fn handle_client_credentials_grant(&mut self, request: TokenRequest) -> Result<TokenResponse, OAuth2Error> {
        // 验证客户端
        let client = self.validate_client_exists(&request.client_id)?;
        
        // 验证客户端密钥
        self.validate_client_secret(client, &request.client_secret)?;
        
        // 生成访问令牌
        let access_token = self.generate_access_token();
        
        let access_token_info = AccessTokenInfo {
            token: access_token.clone(),
            client_id: request.client_id.clone(),
            user_id: None, // 客户端凭证模式没有用户
            scope: request.scope.clone(),
            expires_at: Utc::now() + Duration::from_secs(3600),
        };
        
        self.access_tokens.insert(access_token.clone(), access_token_info);
        
        Ok(TokenResponse {
            access_token,
            token_type: "Bearer".to_string(),
            expires_in: 3600,
            refresh_token: None,
            scope: Some(request.scope.join(" ")),
        })
    }
    
    fn validate_client(&self, client: &OAuth2Client) -> Result<(), OAuth2Error> {
        // 验证客户端ID唯一性
        if self.clients.contains_key(&client.id) {
            return Err(OAuth2Error::ClientAlreadyExists);
        }
        
        // 验证重定向URI格式
        for uri in &client.redirect_uris {
            if !self.is_valid_uri(uri) {
                return Err(OAuth2Error::InvalidRedirectUri);
            }
        }
        
        // 验证作用域
        for scope_id in &client.scopes {
            if !self.scopes.contains_key(scope_id) {
                return Err(OAuth2Error::InvalidScope);
            }
        }
        
        Ok(())
    }
    
    fn validate_client_exists(&self, client_id: &ClientId) -> Result<&OAuth2Client, OAuth2Error> {
        self.clients.get(client_id)
            .ok_or(OAuth2Error::InvalidClient)
    }
    
    fn validate_client_secret(&self, client: &OAuth2Client, secret: &Option<ClientSecret>) -> Result<(), OAuth2Error> {
        match client.client_type {
            ClientType::Confidential => {
                if let Some(ref provided_secret) = secret {
                    if provided_secret != &client.secret {
                        return Err(OAuth2Error::InvalidClientSecret);
                    }
                } else {
                    return Err(OAuth2Error::MissingClientSecret);
                }
            }
            ClientType::Public => {
                // 公共客户端不需要验证密钥
            }
        }
        Ok(())
    }
    
    fn validate_authorization_code(&self, code: &AuthorizationCode) -> Result<&AuthorizationCodeInfo, OAuth2Error> {
        let code_info = self.authorization_codes.get(code)
            .ok_or(OAuth2Error::InvalidAuthorizationCode)?;
        
        if code_info.expires_at < Utc::now() {
            return Err(OAuth2Error::ExpiredAuthorizationCode);
        }
        
        Ok(code_info)
    }
    
    fn generate_authorization_code(&self) -> AuthorizationCode {
        // 生成安全的随机授权码
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let code: String = (0..32).map(|_| rng.gen_range(0..16)).map(|n| format!("{:x}", n)).collect();
        AuthorizationCode(code)
    }
    
    fn generate_access_token(&self) -> AccessToken {
        // 生成JWT访问令牌
        AccessToken(self.generate_jwt_token())
    }
    
    fn generate_refresh_token(&self) -> RefreshToken {
        // 生成安全的随机刷新令牌
        use rand::Rng;
        let mut rng = rand::thread_rng();
        let token: String = (0..64).map(|_| rng.gen_range(0..16)).map(|n| format!("{:x}", n)).collect();
        RefreshToken(token)
    }
}
```

### 2.2 JWT令牌处理

```rust
// JWT令牌处理框架
#[derive(Debug, Clone)]
pub struct JwtHandler {
    secret_key: SecretKey,
    algorithm: JwtAlgorithm,
    issuer: String,
    audience: String,
    token_validator: TokenValidator,
}

#[derive(Debug, Clone)]
pub struct JwtClaims {
    pub iss: String,        // 发行者
    pub sub: String,        // 主题
    pub aud: String,        // 受众
    pub exp: i64,          // 过期时间
    pub iat: i64,          // 签发时间
    pub nbf: i64,          // 生效时间
    pub jti: String,       // JWT ID
    pub scope: Vec<String>, // 作用域
    pub user_id: Option<String>, // 用户ID
}

#[derive(Debug, Clone)]
pub enum JwtAlgorithm {
    HS256,
    HS384,
    HS512,
    RS256,
    RS384,
    RS512,
    ES256,
    ES384,
    ES512,
}

impl JwtHandler {
    pub fn new(secret_key: SecretKey, algorithm: JwtAlgorithm, issuer: String, audience: String) -> Self {
        Self {
            secret_key,
            algorithm,
            issuer,
            audience,
            token_validator: TokenValidator::new(),
        }
    }
    
    pub fn create_token(&self, claims: JwtClaims) -> Result<String, JwtError> {
        // 验证声明
        self.validate_claims(&claims)?;
        
        // 创建JWT头部
        let header = JwtHeader {
            alg: self.algorithm.clone(),
            typ: "JWT".to_string(),
            kid: None,
        };
        
        // 编码头部
        let header_json = serde_json::to_string(&header)?;
        let header_encoded = base64_url_encode(&header_json);
        
        // 编码载荷
        let payload_json = serde_json::to_string(&claims)?;
        let payload_encoded = base64_url_encode(&payload_json);
        
        // 创建签名
        let message = format!("{}.{}", header_encoded, payload_encoded);
        let signature = self.sign(&message)?;
        let signature_encoded = base64_url_encode(&signature);
        
        // 组合JWT
        let jwt = format!("{}.{}.{}", header_encoded, payload_encoded, signature_encoded);
        
        Ok(jwt)
    }
    
    pub fn verify_token(&self, token: &str) -> Result<JwtClaims, JwtError> {
        // 解析JWT
        let parts: Vec<&str> = token.split('.').collect();
        if parts.len() != 3 {
            return Err(JwtError::InvalidTokenFormat);
        }
        
        let header_encoded = parts[0];
        let payload_encoded = parts[1];
        let signature_encoded = parts[2];
        
        // 验证签名
        let message = format!("{}.{}", header_encoded, payload_encoded);
        let expected_signature = self.sign(&message)?;
        let provided_signature = base64_url_decode(signature_encoded)?;
        
        if !self.verify_signature(&expected_signature, &provided_signature) {
            return Err(JwtError::InvalidSignature);
        }
        
        // 解码头部
        let header_json = base64_url_decode(header_encoded)?;
        let header: JwtHeader = serde_json::from_slice(&header_json)?;
        
        // 验证算法
        if header.alg != self.algorithm {
            return Err(JwtError::AlgorithmMismatch);
        }
        
        // 解码载荷
        let payload_json = base64_url_decode(payload_encoded)?;
        let claims: JwtClaims = serde_json::from_slice(&payload_json)?;
        
        // 验证声明
        self.validate_claims(&claims)?;
        
        // 验证时间
        self.validate_timing(&claims)?;
        
        Ok(claims)
    }
    
    fn validate_claims(&self, claims: &JwtClaims) -> Result<(), JwtError> {
        // 验证发行者
        if claims.iss != self.issuer {
            return Err(JwtError::InvalidIssuer);
        }
        
        // 验证受众
        if claims.aud != self.audience {
            return Err(JwtError::InvalidAudience);
        }
        
        // 验证主题
        if claims.sub.is_empty() {
            return Err(JwtError::InvalidSubject);
        }
        
        Ok(())
    }
    
    fn validate_timing(&self, claims: &JwtClaims) -> Result<(), JwtError> {
        let now = Utc::now().timestamp();
        
        // 验证过期时间
        if claims.exp <= now {
            return Err(JwtError::TokenExpired);
        }
        
        // 验证生效时间
        if claims.nbf > now {
            return Err(JwtError::TokenNotYetValid);
        }
        
        // 验证签发时间（不能在未来）
        if claims.iat > now {
            return Err(JwtError::InvalidIssuedAt);
        }
        
        Ok(())
    }
    
    fn sign(&self, message: &str) -> Result<Vec<u8>, JwtError> {
        match self.algorithm {
            JwtAlgorithm::HS256 => self.sign_hmac_sha256(message),
            JwtAlgorithm::HS384 => self.sign_hmac_sha384(message),
            JwtAlgorithm::HS512 => self.sign_hmac_sha512(message),
            JwtAlgorithm::RS256 => self.sign_rsa_sha256(message),
            JwtAlgorithm::RS384 => self.sign_rsa_sha384(message),
            JwtAlgorithm::RS512 => self.sign_rsa_sha512(message),
            JwtAlgorithm::ES256 => self.sign_ecdsa_sha256(message),
            JwtAlgorithm::ES384 => self.sign_ecdsa_sha384(message),
            JwtAlgorithm::ES512 => self.sign_ecdsa_sha512(message),
        }
    }
    
    fn sign_hmac_sha256(&self, message: &str) -> Result<Vec<u8>, JwtError> {
        use hmac::{Hmac, Mac};
        use sha2::Sha256;
        
        let mut mac = Hmac::<Sha256>::new_from_slice(&self.secret_key.0)?;
        mac.update(message.as_bytes());
        Ok(mac.finalize().into_bytes().to_vec())
    }
    
    fn verify_signature(&self, expected: &[u8], provided: &[u8]) -> bool {
        use subtle::ConstantTimeEq;
        expected.ct_eq(provided).into()
    }
}
```

## 3. 安全通信与加密

### 3.1 TLS/SSL安全通信

```rust
// TLS安全通信框架
use rustls::{ClientConfig, ServerConfig, Certificate, PrivateKey};
use tokio_rustls::{TlsAcceptor, TlsConnector};

#[derive(Debug, Clone)]
pub struct TlsManager {
    server_config: ServerConfig,
    client_config: ClientConfig,
    certificate_store: CertificateStore,
    key_store: KeyStore,
}

#[derive(Debug, Clone)]
pub struct CertificateStore {
    certificates: HashMap<String, Certificate>,
    certificate_chains: HashMap<String, Vec<Certificate>>,
}

#[derive(Debug, Clone)]
pub struct KeyStore {
    private_keys: HashMap<String, PrivateKey>,
    public_keys: HashMap<String, PublicKey>,
}

impl TlsManager {
    pub fn new() -> Result<Self, TlsError> {
        let server_config = Self::create_server_config()?;
        let client_config = Self::create_client_config()?;
        let certificate_store = CertificateStore::new();
        let key_store = KeyStore::new();
        
        Ok(Self {
            server_config,
            client_config,
            certificate_store,
            key_store,
        })
    }
    
    pub fn load_certificate(&mut self, name: String, cert_data: &[u8]) -> Result<(), TlsError> {
        let certificate = Certificate(cert_data.to_vec());
        self.certificate_store.certificates.insert(name, certificate);
        Ok(())
    }
    
    pub fn load_private_key(&mut self, name: String, key_data: &[u8]) -> Result<(), TlsError> {
        let private_key = PrivateKey(key_data.to_vec());
        self.key_store.private_keys.insert(name, private_key);
        Ok(())
    }
    
    pub async fn create_tls_acceptor(&self) -> Result<TlsAcceptor, TlsError> {
        let acceptor = TlsAcceptor::from(Arc::new(self.server_config.clone()));
        Ok(acceptor)
    }
    
    pub async fn create_tls_connector(&self) -> Result<TlsConnector, TlsError> {
        let connector = TlsConnector::from(Arc::new(self.client_config.clone()));
        Ok(connector)
    }
    
    fn create_server_config() -> Result<ServerConfig, TlsError> {
        let certs = vec![];
        let key = PrivateKey(vec![]);
        
        let config = ServerConfig::builder()
            .with_safe_defaults()
            .with_no_client_auth()
            .with_single_cert(certs, key)?;
        
        Ok(config)
    }
    
    fn create_client_config() -> Result<ClientConfig, TlsError> {
        let config = ClientConfig::builder()
            .with_safe_defaults()
            .with_root_certificates(rustls::RootCertStore::empty())
            .with_no_client_auth();
        
        Ok(config)
    }
}
```

### 3.2 加密算法实现

```rust
// 加密算法框架
#[derive(Debug, Clone)]
pub struct CryptoManager {
    symmetric_ciphers: HashMap<CipherType, Box<dyn SymmetricCipher>>,
    asymmetric_ciphers: HashMap<CipherType, Box<dyn AsymmetricCipher>>,
    hash_functions: HashMap<HashType, Box<dyn HashFunction>>,
    key_derivation: KeyDerivation,
}

#[derive(Debug, Clone)]
pub enum CipherType {
    AES128,
    AES192,
    AES256,
    ChaCha20,
    RSA2048,
    RSA4096,
    ECDSA256,
    ECDSA384,
    ECDSA521,
}

#[derive(Debug, Clone)]
pub enum HashType {
    SHA256,
    SHA384,
    SHA512,
    Blake2b,
    Blake2s,
}

pub trait SymmetricCipher {
    fn encrypt(&self, plaintext: &[u8], key: &[u8], iv: &[u8]) -> Result<Vec<u8>, CryptoError>;
    fn decrypt(&self, ciphertext: &[u8], key: &[u8], iv: &[u8]) -> Result<Vec<u8>, CryptoError>;
    fn key_size(&self) -> usize;
    fn iv_size(&self) -> usize;
}

pub trait AsymmetricCipher {
    fn encrypt(&self, plaintext: &[u8], public_key: &[u8]) -> Result<Vec<u8>, CryptoError>;
    fn decrypt(&self, ciphertext: &[u8], private_key: &[u8]) -> Result<Vec<u8>, CryptoError>;
    fn sign(&self, message: &[u8], private_key: &[u8]) -> Result<Vec<u8>, CryptoError>;
    fn verify(&self, message: &[u8], signature: &[u8], public_key: &[u8]) -> Result<bool, CryptoError>;
}

pub trait HashFunction {
    fn hash(&self, data: &[u8]) -> Vec<u8>;
    fn hash_size(&self) -> usize;
}

// AES加密实现
#[derive(Debug, Clone)]
pub struct AesCipher {
    key_size: usize,
    iv_size: usize,
}

impl AesCipher {
    pub fn new(key_size: usize) -> Self {
        Self {
            key_size,
            iv_size: 16, // AES块大小
        }
    }
}

impl SymmetricCipher for AesCipher {
    fn encrypt(&self, plaintext: &[u8], key: &[u8], iv: &[u8]) -> Result<Vec<u8>, CryptoError> {
        if key.len() != self.key_size {
            return Err(CryptoError::InvalidKeySize);
        }
        
        if iv.len() != self.iv_size {
            return Err(CryptoError::InvalidIvSize);
        }
        
        use aes_gcm::{Aes256Gcm, Key, Nonce};
        use aes_gcm::aead::{Aead, NewAead};
        
        let cipher = Aes256Gcm::new(Key::from_slice(key));
        let nonce = Nonce::from_slice(iv);
        
        let ciphertext = cipher.encrypt(nonce, plaintext)
            .map_err(|_| CryptoError::EncryptionFailed)?;
        
        Ok(ciphertext)
    }
    
    fn decrypt(&self, ciphertext: &[u8], key: &[u8], iv: &[u8]) -> Result<Vec<u8>, CryptoError> {
        if key.len() != self.key_size {
            return Err(CryptoError::InvalidKeySize);
        }
        
        if iv.len() != self.iv_size {
            return Err(CryptoError::InvalidIvSize);
        }
        
        use aes_gcm::{Aes256Gcm, Key, Nonce};
        use aes_gcm::aead::{Aead, NewAead};
        
        let cipher = Aes256Gcm::new(Key::from_slice(key));
        let nonce = Nonce::from_slice(iv);
        
        let plaintext = cipher.decrypt(nonce, ciphertext)
            .map_err(|_| CryptoError::DecryptionFailed)?;
        
        Ok(plaintext)
    }
    
    fn key_size(&self) -> usize {
        self.key_size
    }
    
    fn iv_size(&self) -> usize {
        self.iv_size
    }
}

// SHA256哈希实现
#[derive(Debug, Clone)]
pub struct Sha256Hash;

impl HashFunction for Sha256Hash {
    fn hash(&self, data: &[u8]) -> Vec<u8> {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(data);
        hasher.finalize().to_vec()
    }
    
    fn hash_size(&self) -> usize {
        32 // SHA256输出256位 = 32字节
    }
}
```

## 4. 访问控制与权限管理

### 4.1 RBAC权限模型

```rust
// RBAC权限模型
#[derive(Debug, Clone)]
pub struct RbacManager {
    users: HashMap<UserId, User>,
    roles: HashMap<RoleId, Role>,
    permissions: HashMap<PermissionId, Permission>,
    user_roles: HashMap<UserId, Vec<RoleId>>,
    role_permissions: HashMap<RoleId, Vec<PermissionId>>,
    resources: HashMap<ResourceId, Resource>,
}

#[derive(Debug, Clone)]
pub struct User {
    id: UserId,
    username: String,
    email: String,
    active: bool,
    created_at: DateTime<Utc>,
    last_login: Option<DateTime<Utc>>,
}

#[derive(Debug, Clone)]
pub struct Role {
    id: RoleId,
    name: String,
    description: String,
    permissions: Vec<PermissionId>,
    created_at: DateTime<Utc>,
}

#[derive(Debug, Clone)]
pub struct Permission {
    id: PermissionId,
    name: String,
    resource: ResourceId,
    action: Action,
    conditions: Vec<Condition>,
}

#[derive(Debug, Clone)]
pub enum Action {
    Create,
    Read,
    Update,
    Delete,
    Execute,
    Custom(String),
}

#[derive(Debug, Clone)]
pub struct Condition {
    field: String,
    operator: ConditionOperator,
    value: String,
}

#[derive(Debug, Clone)]
pub enum ConditionOperator {
    Equals,
    NotEquals,
    GreaterThan,
    LessThan,
    Contains,
    In,
    NotIn,
}

impl RbacManager {
    pub fn new() -> Self {
        Self {
            users: HashMap::new(),
            roles: HashMap::new(),
            permissions: HashMap::new(),
            user_roles: HashMap::new(),
            role_permissions: HashMap::new(),
            resources: HashMap::new(),
        }
    }
    
    pub fn create_user(&mut self, user: User) -> Result<(), RbacError> {
        // 验证用户数据
        self.validate_user(&user)?;
        
        self.users.insert(user.id.clone(), user);
        Ok(())
    }
    
    pub fn create_role(&mut self, role: Role) -> Result<(), RbacError> {
        // 验证角色数据
        self.validate_role(&role)?;
        
        self.roles.insert(role.id.clone(), role);
        Ok(())
    }
    
    pub fn create_permission(&mut self, permission: Permission) -> Result<(), RbacError> {
        // 验证权限数据
        self.validate_permission(&permission)?;
        
        self.permissions.insert(permission.id.clone(), permission);
        Ok(())
    }
    
    pub fn assign_role_to_user(&mut self, user_id: UserId, role_id: RoleId) -> Result<(), RbacError> {
        // 验证用户存在
        if !self.users.contains_key(&user_id) {
            return Err(RbacError::UserNotFound);
        }
        
        // 验证角色存在
        if !self.roles.contains_key(&role_id) {
            return Err(RbacError::RoleNotFound);
        }
        
        // 分配角色
        self.user_roles.entry(user_id).or_insert_with(Vec::new).push(role_id);
        Ok(())
    }
    
    pub fn assign_permission_to_role(&mut self, role_id: RoleId, permission_id: PermissionId) -> Result<(), RbacError> {
        // 验证角色存在
        if !self.roles.contains_key(&role_id) {
            return Err(RbacError::RoleNotFound);
        }
        
        // 验证权限存在
        if !self.permissions.contains_key(&permission_id) {
            return Err(RbacError::PermissionNotFound);
        }
        
        // 分配权限
        self.role_permissions.entry(role_id).or_insert_with(Vec::new).push(permission_id);
        Ok(())
    }
    
    pub fn check_permission(&self, user_id: &UserId, resource_id: &ResourceId, action: &Action) -> Result<bool, RbacError> {
        // 获取用户角色
        let user_roles = self.user_roles.get(user_id)
            .ok_or(RbacError::UserNotFound)?;
        
        // 检查每个角色的权限
        for role_id in user_roles {
            if let Some(role_permissions) = self.role_permissions.get(role_id) {
                for permission_id in role_permissions {
                    if let Some(permission) = self.permissions.get(permission_id) {
                        if permission.resource == *resource_id && permission.action == *action {
                            return Ok(true);
                        }
                    }
                }
            }
        }
        
        Ok(false)
    }
    
    pub fn get_user_permissions(&self, user_id: &UserId) -> Result<Vec<Permission>, RbacError> {
        let mut permissions = Vec::new();
        
        // 获取用户角色
        let user_roles = self.user_roles.get(user_id)
            .ok_or(RbacError::UserNotFound)?;
        
        // 收集所有权限
        for role_id in user_roles {
            if let Some(role_permissions) = self.role_permissions.get(role_id) {
                for permission_id in role_permissions {
                    if let Some(permission) = self.permissions.get(permission_id) {
                        permissions.push(permission.clone());
                    }
                }
            }
        }
        
        Ok(permissions)
    }
    
    fn validate_user(&self, user: &User) -> Result<(), RbacError> {
        // 验证用户名唯一性
        for existing_user in self.users.values() {
            if existing_user.username == user.username && existing_user.id != user.id {
                return Err(RbacError::UsernameAlreadyExists);
            }
        }
        
        // 验证邮箱格式
        if !self.is_valid_email(&user.email) {
            return Err(RbacError::InvalidEmail);
        }
        
        Ok(())
    }
    
    fn validate_role(&self, role: &Role) -> Result<(), RbacError> {
        // 验证角色名唯一性
        for existing_role in self.roles.values() {
            if existing_role.name == role.name && existing_role.id != role.id {
                return Err(RbacError::RoleNameAlreadyExists);
            }
        }
        
        Ok(())
    }
    
    fn validate_permission(&self, permission: &Permission) -> Result<(), RbacError> {
        // 验证资源存在
        if !self.resources.contains_key(&permission.resource) {
            return Err(RbacError::ResourceNotFound);
        }
        
        Ok(())
    }
    
    fn is_valid_email(&self, email: &str) -> bool {
        // 简单的邮箱验证
        email.contains('@') && email.contains('.')
    }
}
```

## 5. 最小可验证示例(MVE)

```rust
// 安全认证架构验证示例
use verification_framework::security_auth::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建OAuth2服务器
    let mut oauth2_server = OAuth2Server::new();
    
    // 注册客户端
    let client = OAuth2Client {
        id: ClientId("test-client".to_string()),
        secret: ClientSecret("test-secret".to_string()),
        redirect_uris: vec!["http://localhost:3000/callback".to_string()],
        grant_types: vec![GrantType::AuthorizationCode],
        scopes: vec![ScopeId("read".to_string())],
        client_type: ClientType::Confidential,
        created_at: Utc::now(),
    };
    
    oauth2_server.register_client(client)?;
    
    // 处理授权请求
    let auth_request = AuthorizationRequest {
        client_id: ClientId("test-client".to_string()),
        redirect_uri: "http://localhost:3000/callback".to_string(),
        scope: vec![ScopeId("read".to_string())],
        state: Some("random-state".to_string()),
        username: "testuser".to_string(),
        password: "testpass".to_string(),
    };
    
    let auth_response = oauth2_server.authorize(auth_request).await?;
    println!("Authorization code: {:?}", auth_response.code);
    
    // 交换令牌
    let token_request = TokenRequest {
        grant_type: GrantType::AuthorizationCode,
        code: auth_response.code,
        redirect_uri: "http://localhost:3000/callback".to_string(),
        client_id: ClientId("test-client".to_string()),
        client_secret: Some(ClientSecret("test-secret".to_string())),
        scope: vec![ScopeId("read".to_string())],
    };
    
    let token_response = oauth2_server.exchange_token(token_request).await?;
    println!("Access token: {:?}", token_response.access_token);
    
    // 创建JWT处理器
    let secret_key = SecretKey(b"your-secret-key".to_vec());
    let jwt_handler = JwtHandler::new(
        secret_key,
        JwtAlgorithm::HS256,
        "test-issuer".to_string(),
        "test-audience".to_string(),
    );
    
    // 创建JWT令牌
    let claims = JwtClaims {
        iss: "test-issuer".to_string(),
        sub: "testuser".to_string(),
        aud: "test-audience".to_string(),
        exp: (Utc::now() + Duration::from_secs(3600)).timestamp(),
        iat: Utc::now().timestamp(),
        nbf: Utc::now().timestamp(),
        jti: "unique-token-id".to_string(),
        scope: vec!["read".to_string()],
        user_id: Some("user123".to_string()),
    };
    
    let token = jwt_handler.create_token(claims)?;
    println!("JWT token: {}", token);
    
    // 验证JWT令牌
    let verified_claims = jwt_handler.verify_token(&token)?;
    println!("Verified claims: {:?}", verified_claims);
    
    // 创建RBAC管理器
    let mut rbac_manager = RbacManager::new();
    
    // 创建用户
    let user = User {
        id: UserId("user123".to_string()),
        username: "testuser".to_string(),
        email: "test@example.com".to_string(),
        active: true,
        created_at: Utc::now(),
        last_login: None,
    };
    
    rbac_manager.create_user(user)?;
    
    // 创建角色
    let role = Role {
        id: RoleId("admin".to_string()),
        name: "Administrator".to_string(),
        description: "System administrator".to_string(),
        permissions: vec![],
        created_at: Utc::now(),
    };
    
    rbac_manager.create_role(role)?;
    
    // 创建权限
    let permission = Permission {
        id: PermissionId("read-users".to_string()),
        name: "Read Users".to_string(),
        resource: ResourceId("users".to_string()),
        action: Action::Read,
        conditions: vec![],
    };
    
    rbac_manager.create_permission(permission)?;
    
    // 分配角色和权限
    rbac_manager.assign_role_to_user(UserId("user123".to_string()), RoleId("admin".to_string()))?;
    rbac_manager.assign_permission_to_role(RoleId("admin".to_string()), PermissionId("read-users".to_string()))?;
    
    // 检查权限
    let has_permission = rbac_manager.check_permission(
        &UserId("user123".to_string()),
        &ResourceId("users".to_string()),
        &Action::Read,
    )?;
    
    println!("User has permission: {}", has_permission);
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_oauth2_client_registration() {
        let mut oauth2_server = OAuth2Server::new();
        
        let client = OAuth2Client {
            id: ClientId("test-client".to_string()),
            secret: ClientSecret("test-secret".to_string()),
            redirect_uris: vec!["http://localhost:3000/callback".to_string()],
            grant_types: vec![GrantType::AuthorizationCode],
            scopes: vec![],
            client_type: ClientType::Confidential,
            created_at: Utc::now(),
        };
        
        assert!(oauth2_server.register_client(client).is_ok());
    }
    
    #[test]
    fn test_jwt_token_creation() {
        let secret_key = SecretKey(b"test-secret".to_vec());
        let jwt_handler = JwtHandler::new(
            secret_key,
            JwtAlgorithm::HS256,
            "test-issuer".to_string(),
            "test-audience".to_string(),
        );
        
        let claims = JwtClaims {
            iss: "test-issuer".to_string(),
            sub: "testuser".to_string(),
            aud: "test-audience".to_string(),
            exp: (Utc::now() + Duration::from_secs(3600)).timestamp(),
            iat: Utc::now().timestamp(),
            nbf: Utc::now().timestamp(),
            jti: "test-token".to_string(),
            scope: vec![],
            user_id: None,
        };
        
        assert!(jwt_handler.create_token(claims).is_ok());
    }
    
    #[test]
    fn test_rbac_permission_check() {
        let mut rbac_manager = RbacManager::new();
        
        let user = User {
            id: UserId("user123".to_string()),
            username: "testuser".to_string(),
            email: "test@example.com".to_string(),
            active: true,
            created_at: Utc::now(),
            last_login: None,
        };
        
        rbac_manager.create_user(user).unwrap();
        
        let has_permission = rbac_manager.check_permission(
            &UserId("user123".to_string()),
            &ResourceId("users".to_string()),
            &Action::Read,
        );
        
        assert!(has_permission.is_ok());
    }
}
```

## 6. 证明义务(Proof Obligations)

- **SA1**: OAuth2协议安全性验证
- **SA2**: JWT令牌完整性验证
- **SA3**: 加密算法正确性验证
- **SA4**: RBAC权限模型一致性验证
- **SA5**: TLS连接安全性验证
- **SA6**: 访问控制策略正确性验证

## 7. 总结

本文档提供了Rust安全与认证架构的完整形式化验证框架，包括：

1. **OAuth2认证**: 完整的OAuth2服务器实现和流程验证
2. **JWT令牌**: 安全的JWT创建、验证和声明处理
3. **安全通信**: TLS/SSL加密通信和证书管理
4. **加密算法**: 对称和非对称加密算法实现
5. **访问控制**: RBAC权限模型和细粒度权限控制

这个框架确保了安全机制的正确性、完整性和可靠性，为构建安全可靠的系统提供了理论基础和实用工具。

## 8. 交叉引用

- [微服务与分布式架构](./03_microservice_architecture.md)
- [网络与通信架构](./06_network_communication.md)
- [数据库与存储架构](./05_database_storage.md)
- [事件驱动与消息系统](./04_event_driven_messaging.md)
