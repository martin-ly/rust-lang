//! 安全功能演示程序
//!
//! 展示OAuth2、TLS、输入验证、CORS和速率限制功能

use std::collections::HashMap;
use std::time::Duration;
use tokio::time::sleep;
use c13_microservice::security::{
    SecurityManager, SecurityConfig, SecurityRequest, InputData,
    OAuth2Config, OAuth2Provider, TlsConfig, CorsConfig, RateLimitConfig, RateLimit,
    TlsVersion,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🔐 安全功能演示程序");
    println!("==================");

    // 创建安全配置
    let security_config = create_security_config();
    
    // 创建安全管理器
    let mut security_manager = SecurityManager::new(security_config);

    // 演示输入验证
    demo_input_validation(&security_manager).await?;

    // 演示CORS验证
    demo_cors_validation(&security_manager).await?;

    // 演示速率限制
    demo_rate_limiting(&security_manager).await?;

    // 演示TLS功能
    demo_tls_features(&security_manager).await?;

    // 演示OAuth2功能
    demo_oauth2_features(&mut security_manager).await?;

    // 获取安全统计信息
    let stats = security_manager.get_security_stats().await;
    println!("\n📊 安全统计信息:");
    println!("  OAuth2启用: {}", stats.oauth2_enabled);
    println!("  TLS启用: {}", stats.tls_enabled);
    println!("  CORS启用: {}", stats.cors_enabled);
    println!("  速率限制启用: {}", stats.rate_limiting_enabled);
    println!("  输入验证启用: {}", stats.input_validation_enabled);
    println!("  总检查次数: {}", stats.total_requests_checked);
    println!("  被阻止请求数: {}", stats.blocked_requests);

    println!("\n✅ 安全功能演示完成！");
    Ok(())
}

/// 创建安全配置
fn create_security_config() -> SecurityConfig {
    // OAuth2配置
    let mut oauth2_providers = HashMap::new();
    oauth2_providers.insert(
        "google".to_string(),
        OAuth2Provider::new(
            "google".to_string(),
            "your-google-client-id".to_string(),
            "your-google-client-secret".to_string(),
            "https://accounts.google.com/o/oauth2/auth".to_string(),
            "https://oauth2.googleapis.com/token".to_string(),
            "https://www.googleapis.com/oauth2/v1/userinfo".to_string(),
            "http://localhost:3000/auth/callback".to_string(),
        ),
    );

    let oauth2_config = OAuth2Config {
        providers: oauth2_providers,
        default_provider: Some("google".to_string()),
        token_cache_ttl: Duration::from_secs(3600),
        client_timeout: Duration::from_secs(30),
    };

    // TLS配置
    let tls_config = TlsConfig {
        enabled: true,
        cert_path: Some("certs/server.crt".to_string()),
        key_path: Some("certs/server.key".to_string()),
        ca_cert_path: None,
        min_tls_version: TlsVersion::Tls12,
        cipher_suites: vec![
            "TLS_AES_256_GCM_SHA384".to_string(),
            "TLS_CHACHA20_POLY1305_SHA256".to_string(),
        ],
        require_client_cert: false,
        verify_peer: true,
        session_timeout: 3600,
        session_cache_size: 1000,
    };

    // CORS配置
    let cors_config = CorsConfig {
        enabled: true,
        allowed_origins: vec![
            "http://localhost:3000".to_string(),
            "https://localhost:3000".to_string(),
            "http://127.0.0.1:3000".to_string(),
        ],
        allowed_methods: vec![
            "GET".to_string(),
            "POST".to_string(),
            "PUT".to_string(),
            "DELETE".to_string(),
            "OPTIONS".to_string(),
        ],
        allowed_headers: vec![
            "Content-Type".to_string(),
            "Authorization".to_string(),
            "X-Requested-With".to_string(),
        ],
        exposed_headers: vec![
            "X-Total-Count".to_string(),
        ],
        allow_credentials: true,
        max_age: 86400,
        allow_wildcard: false,
    };

    // 速率限制配置
    let rate_limit_config = RateLimitConfig {
        enabled: true,
        default_limit: RateLimit {
            requests_per_window: 100,
            window_size: Duration::from_secs(60),
            burst_size: 10,
        },
        endpoint_limits: HashMap::new(),
        client_limits: HashMap::new(),
        window_size: Duration::from_secs(60),
        cleanup_interval: Duration::from_secs(300),
        max_entries: 10000,
    };

    SecurityConfig {
        oauth2: Some(oauth2_config),
        tls: Some(tls_config),
        cors: cors_config,
        rate_limit: rate_limit_config,
    }
}

/// 演示输入验证
async fn demo_input_validation(security_manager: &SecurityManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔍 输入验证演示");
    println!("================");

    // 创建测试请求
    let mut input_data = InputData {
        query_params: HashMap::new(),
        path_params: HashMap::new(),
        headers: HashMap::new(),
        body: None,
    };

    // 测试有效输入
    input_data.query_params.insert("email".to_string(), "user@example.com".to_string());
    input_data.query_params.insert("username".to_string(), "valid_user123".to_string());
    
    let security_request = SecurityRequest {
        client_id: "test_client".to_string(),
        endpoint: "/api/users".to_string(),
        method: "POST".to_string(),
        path: "/api/users".to_string(),
        origin: Some("http://localhost:3000".to_string()),
        input: input_data,
        is_https: true,
    };

    match security_manager.validate_request(&security_request).await {
        c13_microservice::security::SecurityResult::Allowed => {
            println!("✅ 有效输入验证通过");
        }
        c13_microservice::security::SecurityResult::Blocked(reasons) => {
            println!("❌ 输入验证失败: {:?}", reasons);
        }
    }

    // 测试恶意输入
    let mut malicious_input_data = InputData {
        query_params: HashMap::new(),
        path_params: HashMap::new(),
        headers: HashMap::new(),
        body: None,
    };
    malicious_input_data.query_params.insert("email".to_string(), "<script>alert('xss')</script>".to_string());
    malicious_input_data.query_params.insert("username".to_string(), "'; DROP TABLE users; --".to_string());
    
    let malicious_request = SecurityRequest {
        client_id: "malicious_client".to_string(),
        endpoint: "/api/users".to_string(),
        method: "POST".to_string(),
        path: "/api/users".to_string(),
        origin: Some("http://evil.com".to_string()),
        input: malicious_input_data,
        is_https: false,
    };

    match security_manager.validate_request(&malicious_request).await {
        c13_microservice::security::SecurityResult::Allowed => {
            println!("❌ 恶意输入验证失败");
        }
        c13_microservice::security::SecurityResult::Blocked(reasons) => {
            println!("✅ 恶意输入被正确阻止: {:?}", reasons);
        }
    }

    Ok(())
}

/// 演示CORS验证
async fn demo_cors_validation(security_manager: &SecurityManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🌐 CORS验证演示");
    println!("================");

    // 测试允许的Origin
    let input_data = InputData {
        query_params: HashMap::new(),
        path_params: HashMap::new(),
        headers: HashMap::new(),
        body: None,
    };

    let allowed_request = SecurityRequest {
        client_id: "web_client".to_string(),
        endpoint: "/api/data".to_string(),
        method: "GET".to_string(),
        path: "/api/data".to_string(),
        origin: Some("http://localhost:3000".to_string()),
        input: input_data.clone(),
        is_https: true,
    };

    match security_manager.validate_request(&allowed_request).await {
        c13_microservice::security::SecurityResult::Allowed => {
            println!("✅ 允许的Origin验证通过");
        }
        c13_microservice::security::SecurityResult::Blocked(reasons) => {
            println!("❌ 允许的Origin验证失败: {:?}", reasons);
        }
    }

    // 测试不允许的Origin
    let blocked_request = SecurityRequest {
        client_id: "web_client".to_string(),
        endpoint: "/api/data".to_string(),
        method: "GET".to_string(),
        path: "/api/data".to_string(),
        origin: Some("http://evil.com".to_string()),
        input: input_data,
        is_https: false,
    };

    match security_manager.validate_request(&blocked_request).await {
        c13_microservice::security::SecurityResult::Allowed => {
            println!("❌ 不允许的Origin验证失败");
        }
        c13_microservice::security::SecurityResult::Blocked(reasons) => {
            println!("✅ 不允许的Origin被正确阻止: {:?}", reasons);
        }
    }

    Ok(())
}

/// 演示速率限制
async fn demo_rate_limiting(security_manager: &SecurityManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚡ 速率限制演示");
    println!("================");

    let client_id = "rate_limit_client";
    let endpoint = "/api/limited";

    // 模拟正常请求
    for i in 1..=5 {
        let input_data = InputData {
            query_params: HashMap::new(),
            path_params: HashMap::new(),
            headers: HashMap::new(),
            body: None,
        };

        let request = SecurityRequest {
            client_id: client_id.to_string(),
            endpoint: endpoint.to_string(),
            method: "GET".to_string(),
            path: endpoint.to_string(),
            origin: Some("http://localhost:3000".to_string()),
            input: input_data,
            is_https: true,
        };

        match security_manager.validate_request(&request).await {
            c13_microservice::security::SecurityResult::Allowed => {
                println!("✅ 请求 {} 被允许", i);
            }
            c13_microservice::security::SecurityResult::Blocked(reasons) => {
                println!("❌ 请求 {} 被阻止: {:?}", i, reasons);
            }
        }

        sleep(Duration::from_millis(100)).await;
    }

    println!("💡 速率限制器会自动清理过期的计数器");

    Ok(())
}

/// 演示TLS功能
async fn demo_tls_features(security_manager: &SecurityManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔒 TLS功能演示");
    println!("===============");

    if let Some(tls_manager) = &security_manager.tls {
        println!("✅ TLS已启用");
        println!("  最小TLS版本: {:?}", tls_manager.get_config().min_tls_version);
        println!("  密码套件数量: {}", tls_manager.get_config().cipher_suites.len());
        println!("  需要客户端证书: {}", tls_manager.get_config().require_client_cert);
        
        // 模拟证书验证
        if let Ok(validation) = tls_manager.validate_certificate("certs/server.crt") {
            println!("  证书验证结果:");
            println!("    有效: {}", validation.valid);
            println!("    过期: {}", validation.expired);
            println!("    自签名: {}", validation.self_signed);
        }

        // 获取会话统计
        let stats = tls_manager.get_session_stats();
        println!("  活跃会话数: {}", stats.active_sessions);
        println!("  会话超时: {}秒", stats.session_timeout);
    } else {
        println!("❌ TLS未启用");
    }

    Ok(())
}

/// 演示OAuth2功能
async fn demo_oauth2_features(security_manager: &mut SecurityManager) -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔑 OAuth2功能演示");
    println!("==================");

    if let Some(oauth2_manager) = &security_manager.oauth2 {
        println!("✅ OAuth2已配置");
        
        // 获取提供商信息
        if let Some(provider) = oauth2_manager.get_provider("google") {
            println!("  提供商: {}", provider.name);
            println!("  授权URL: {}", provider.auth_url);
            println!("  令牌URL: {}", provider.token_url);
            println!("  用户信息URL: {}", provider.user_info_url);
        }

        // 模拟生成授权URL
        if let Ok(auth_url) = oauth2_manager.generate_auth_url("google", "test_state") {
            println!("  授权URL示例: {}", auth_url);
        }

        // 获取缓存统计
        let cache_stats = oauth2_manager.get_cache_stats();
        println!("  令牌缓存大小: {}", cache_stats.token_cache_size);
        println!("  用户缓存大小: {}", cache_stats.user_cache_size);
        println!("  缓存TTL: {}秒", cache_stats.cache_ttl.as_secs());

        // 模拟令牌验证（使用假令牌）
        let fake_token = "fake_access_token_123";
        match security_manager.validate_oauth2_token(fake_token).await {
            Ok(user) => {
                println!("✅ 令牌验证成功: {}", user.get_display_name());
            }
            Err(e) => {
                println!("❌ 令牌验证失败: {}", e);
            }
        }
    } else {
        println!("❌ OAuth2未配置");
    }

    Ok(())
}
