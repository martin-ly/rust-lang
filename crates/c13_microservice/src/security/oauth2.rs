//! OAuth2认证模块
//!
//! 提供OAuth2认证和授权功能

use std::collections::HashMap;
use std::time::{Duration, SystemTime};
use serde::{Deserialize, Serialize};
use thiserror::Error;
use reqwest::Client;
use url::Url;

/// OAuth2配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OAuth2Config {
    pub providers: HashMap<String, OAuth2Provider>,
    pub default_provider: Option<String>,
    pub token_cache_ttl: Duration,
    pub client_timeout: Duration,
}

impl Default for OAuth2Config {
    fn default() -> Self {
        Self {
            providers: HashMap::new(),
            default_provider: None,
            token_cache_ttl: Duration::from_secs(3600), // 1小时
            client_timeout: Duration::from_secs(30),
        }
    }
}

/// OAuth2提供商配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OAuth2Provider {
    pub name: String,
    pub client_id: String,
    pub client_secret: String,
    pub auth_url: String,
    pub token_url: String,
    pub user_info_url: String,
    pub redirect_uri: String,
    pub scopes: Vec<String>,
    pub response_type: String,
}

impl OAuth2Provider {
    /// 创建新的OAuth2提供商
    pub fn new(
        name: String,
        client_id: String,
        client_secret: String,
        auth_url: String,
        token_url: String,
        user_info_url: String,
        redirect_uri: String,
    ) -> Self {
        Self {
            name,
            client_id,
            client_secret,
            auth_url,
            token_url,
            user_info_url,
            redirect_uri,
            scopes: vec!["openid".to_string(), "profile".to_string(), "email".to_string()],
            response_type: "code".to_string(),
        }
    }

    /// 获取授权URL
    pub fn get_auth_url(&self, state: &str) -> Result<String, OAuth2Error> {
        let mut url = Url::parse(&self.auth_url)?;
        url.query_pairs_mut()
            .append_pair("client_id", &self.client_id)
            .append_pair("redirect_uri", &self.redirect_uri)
            .append_pair("response_type", &self.response_type)
            .append_pair("scope", &self.scopes.join(" "))
            .append_pair("state", state);
        
        Ok(url.to_string())
    }

    /// 交换授权码获取令牌
    pub async fn exchange_code_for_token(
        &self,
        code: &str,
        client: &Client,
    ) -> Result<OAuth2Token, OAuth2Error> {
        let mut params = HashMap::new();
        params.insert("grant_type", "authorization_code");
        params.insert("client_id", &self.client_id);
        params.insert("client_secret", &self.client_secret);
        params.insert("code", code);
        params.insert("redirect_uri", &self.redirect_uri);

        let response = client
            .post(&self.token_url)
            .form(&params)
            .send()
            .await?;

        if !response.status().is_success() {
            let error_text = response.text().await?;
            return Err(OAuth2Error::TokenExchangeFailed(error_text));
        }

        let token: OAuth2Token = response.json().await?;
        Ok(token)
    }

    /// 获取用户信息
    pub async fn get_user_info(
        &self,
        access_token: &str,
        client: &Client,
    ) -> Result<OAuth2User, OAuth2Error> {
        let response = client
            .get(&self.user_info_url)
            .bearer_auth(access_token)
            .send()
            .await?;

        if !response.status().is_success() {
            let error_text = response.text().await?;
            return Err(OAuth2Error::UserInfoFailed(error_text));
        }

        let user: OAuth2User = response.json().await?;
        Ok(user)
    }
}

/// OAuth2客户端
#[derive(Debug, Clone)]
pub struct OAuth2Client {
    pub id: String,
    pub name: String,
    pub redirect_uris: Vec<String>,
    pub scopes: Vec<String>,
    pub client_type: ClientType,
    pub created_at: SystemTime,
}

/// 客户端类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ClientType {
    Public,
    Confidential,
}

/// OAuth2令牌
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OAuth2Token {
    pub access_token: String,
    pub token_type: String,
    pub expires_in: Option<u64>,
    pub refresh_token: Option<String>,
    pub scope: Option<String>,
    pub id_token: Option<String>,
    pub created_at: SystemTime,
}

impl OAuth2Token {
    /// 创建新的OAuth2令牌
    pub fn new(access_token: String, token_type: String) -> Self {
        Self {
            access_token,
            token_type,
            expires_in: None,
            refresh_token: None,
            scope: None,
            id_token: None,
            created_at: SystemTime::now(),
        }
    }

    /// 检查令牌是否过期
    pub fn is_expired(&self) -> bool {
        if let Some(expires_in) = self.expires_in {
            let expiry_time = self.created_at + Duration::from_secs(expires_in);
            SystemTime::now() > expiry_time
        } else {
            false
        }
    }

    /// 获取过期时间
    pub fn expires_at(&self) -> Option<SystemTime> {
        self.expires_in.map(|expires_in| self.created_at + Duration::from_secs(expires_in))
    }
}

/// OAuth2用户信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OAuth2User {
    pub id: String,
    pub username: Option<String>,
    pub email: Option<String>,
    pub name: Option<String>,
    pub given_name: Option<String>,
    pub family_name: Option<String>,
    pub picture: Option<String>,
    pub locale: Option<String>,
    pub verified: Option<bool>,
    pub provider: String,
    pub created_at: SystemTime,
}

impl OAuth2User {
    /// 创建新的OAuth2用户
    pub fn new(id: String, provider: String) -> Self {
        Self {
            id,
            username: None,
            email: None,
            name: None,
            given_name: None,
            family_name: None,
            picture: None,
            locale: None,
            verified: None,
            provider,
            created_at: SystemTime::now(),
        }
    }

    /// 获取显示名称
    pub fn get_display_name(&self) -> String {
        self.name
            .clone()
            .or_else(|| self.username.clone())
            .or_else(|| self.email.clone())
            .unwrap_or_else(|| "Unknown User".to_string())
    }
}

/// OAuth2管理器
#[derive(Debug)]
pub struct OAuth2Manager {
    config: OAuth2Config,
    client: Client,
    token_cache: HashMap<String, (OAuth2Token, SystemTime)>,
    user_cache: HashMap<String, (OAuth2User, SystemTime)>,
}

impl OAuth2Manager {
    /// 创建新的OAuth2管理器
    pub fn new(config: OAuth2Config) -> Self {
        let client = Client::builder()
            .timeout(config.client_timeout)
            .build()
            .unwrap_or_else(|_| Client::new());

        Self {
            config,
            client,
            token_cache: HashMap::new(),
            user_cache: HashMap::new(),
        }
    }

    /// 获取提供商
    pub fn get_provider(&self, name: &str) -> Option<&OAuth2Provider> {
        self.config.providers.get(name)
    }

    /// 获取默认提供商
    pub fn get_default_provider(&self) -> Option<&OAuth2Provider> {
        self.config.default_provider.as_ref()
            .and_then(|name| self.get_provider(name))
    }

    /// 生成授权URL
    pub fn generate_auth_url(&self, provider_name: &str, state: &str) -> Result<String, OAuth2Error> {
        let provider = self.get_provider(provider_name)
            .ok_or_else(|| OAuth2Error::ProviderNotFound(provider_name.to_string()))?;
        
        provider.get_auth_url(state)
    }

    /// 交换授权码获取令牌
    pub async fn exchange_code_for_token(
        &mut self,
        provider_name: &str,
        code: &str,
    ) -> Result<OAuth2Token, OAuth2Error> {
        let provider = self.get_provider(provider_name)
            .ok_or_else(|| OAuth2Error::ProviderNotFound(provider_name.to_string()))?;
        
        let token = provider.exchange_code_for_token(code, &self.client).await?;
        
        // 缓存令牌
        let cache_key = format!("{}:{}", provider_name, code);
        self.token_cache.insert(cache_key, (token.clone(), SystemTime::now()));
        
        Ok(token)
    }

    /// 验证令牌
    pub async fn validate_token(&mut self, token: &str) -> Result<OAuth2User, OAuth2Error> {
        // 检查缓存
        if let Some((cached_user, cached_time)) = self.user_cache.get(token) {
            if SystemTime::now().duration_since(*cached_time).unwrap_or_default() < self.config.token_cache_ttl {
                return Ok(cached_user.clone());
            }
        }

        // 从令牌中提取提供商信息（这里简化处理，实际应该从JWT或其他方式获取）
        let provider = self.get_default_provider()
            .ok_or_else(|| OAuth2Error::NoDefaultProvider)?;

        // 获取用户信息
        let user = provider.get_user_info(token, &self.client).await?;
        
        // 缓存用户信息
        self.user_cache.insert(token.to_string(), (user.clone(), SystemTime::now()));
        
        Ok(user)
    }

    /// 刷新令牌
    pub async fn refresh_token(
        &mut self,
        provider_name: &str,
        refresh_token: &str,
    ) -> Result<OAuth2Token, OAuth2Error> {
        let provider = self.get_provider(provider_name)
            .ok_or_else(|| OAuth2Error::ProviderNotFound(provider_name.to_string()))?;

        let mut params = HashMap::new();
        params.insert("grant_type", "refresh_token");
        params.insert("client_id", &provider.client_id);
        params.insert("client_secret", &provider.client_secret);
        params.insert("refresh_token", refresh_token);

        let response = self.client
            .post(&provider.token_url)
            .form(&params)
            .send()
            .await?;

        if !response.status().is_success() {
            let error_text = response.text().await?;
            return Err(OAuth2Error::TokenRefreshFailed(error_text));
        }

        let token: OAuth2Token = response.json().await?;
        Ok(token)
    }

    /// 撤销令牌
    pub async fn revoke_token(&self, provider_name: &str, token: &str) -> Result<(), OAuth2Error> {
        let provider = self.get_provider(provider_name)
            .ok_or_else(|| OAuth2Error::ProviderNotFound(provider_name.to_string()))?;

        let mut params = HashMap::new();
        params.insert("token", token);

        let response = self.client
            .post(&provider.token_url.replace("/token", "/revoke"))
            .form(&params)
            .send()
            .await?;

        if !response.status().is_success() {
            let error_text = response.text().await?;
            return Err(OAuth2Error::TokenRevocationFailed(error_text));
        }

        Ok(())
    }

    /// 清理过期缓存
    pub fn cleanup_expired_cache(&mut self) {
        let now = SystemTime::now();
        
        // 清理过期的令牌缓存
        self.token_cache.retain(|_, (_, cached_time)| {
            now.duration_since(*cached_time).unwrap_or_default() < self.config.token_cache_ttl
        });
        
        // 清理过期的用户缓存
        self.user_cache.retain(|_, (_, cached_time)| {
            now.duration_since(*cached_time).unwrap_or_default() < self.config.token_cache_ttl
        });
    }

    /// 获取缓存统计信息
    pub fn get_cache_stats(&self) -> OAuth2CacheStats {
        OAuth2CacheStats {
            token_cache_size: self.token_cache.len(),
            user_cache_size: self.user_cache.len(),
            cache_ttl: self.config.token_cache_ttl,
        }
    }
}

/// OAuth2缓存统计信息
#[derive(Debug, Clone)]
pub struct OAuth2CacheStats {
    pub token_cache_size: usize,
    pub user_cache_size: usize,
    pub cache_ttl: Duration,
}

/// OAuth2错误
#[derive(Error, Debug)]
pub enum OAuth2Error {
    #[error("提供商未找到: {0}")]
    ProviderNotFound(String),
    #[error("没有默认提供商")]
    NoDefaultProvider,
    #[error("令牌交换失败: {0}")]
    TokenExchangeFailed(String),
    #[error("令牌刷新失败: {0}")]
    TokenRefreshFailed(String),
    #[error("令牌撤销失败: {0}")]
    TokenRevocationFailed(String),
    #[error("用户信息获取失败: {0}")]
    UserInfoFailed(String),
    #[error("URL解析错误: {0}")]
    UrlError(#[from] url::ParseError),
    #[error("HTTP请求错误: {0}")]
    HttpError(#[from] reqwest::Error),
    #[error("JSON解析错误: {0}")]
    JsonError(#[from] serde_json::Error),
}

/// OAuth2结果类型别名
pub type OAuth2Result<T> = Result<T, OAuth2Error>;
