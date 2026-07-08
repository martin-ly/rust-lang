> **内容分级**: [专家级]
> **代码状态**: ✅ 含可编译示例
>
# 网络安全
>
> **EN**: Network Security in Rust
> **Summary**: Securing network applications in Rust: TLS configuration, certificate management, authentication, rate limiting, input validation, and common attack mitigations.
>
> **受众**: [专家]
> **层级**: L6 应用主题
> **A/S/P 标记**: **A+S+P** — Application + Structure + Procedure
> **前置概念**: [Async/Await](../../03_advanced/01_async/02_async.md) · [Rust 网络编程](../../03_advanced/06_low_level_patterns/18_network_programming.md) · [Security & Cryptography](../07_security_and_cryptography/43_security_cryptography.md)
> **后置概念**: [高级网络协议](01_advanced_network_protocols.md) · [分布式系统](../04_web_and_networking/18_distributed_systems.md)
>
> **来源**: [rustls](https://docs.rs/rustls/) · [tokio-rustls](https://docs.rs/tokio-rustls/) · [RFC 8446 — TLS 1.3](https://tools.ietf.org/html/rfc8446)

---

## 1. TLS/SSL 安全配置

生产环境应优先使用 TLS 1.3 并限制加密套件：

```rust
use tokio_rustls::{TlsAcceptor, rustls};
use std::sync::Arc;
use std::fs;

pub fn create_tls_config() -> Result<rustls::ServerConfig, Box<dyn std::error::Error>> {
    let cert = fs::read("cert.pem")?;
    let key = fs::read("key.pem")?;

    let certs: Vec<rustls::Certificate> = rustls_pemfile::certs(&mut &cert[..])
        .map(|mut certs| certs.drain(..).map(rustls::Certificate).collect())
        .unwrap();

    let keys: Vec<rustls::PrivateKey> = rustls_pemfile::pkcs8_private_keys(&mut &key[..])
        .map(|mut keys| keys.drain(..).map(rustls::PrivateKey).collect())
        .unwrap();

    let mut config = rustls::ServerConfig::builder()
        .with_safe_default_cipher_suites()
        .with_safe_default_kx_groups()
        .with_protocol_versions(&[&rustls::version::TLS13])?
        .with_no_client_auth()
        .with_single_cert(certs, keys.into_iter().next().ok_or("缺少私钥")?)?;

    config.alpn_protocols = vec![b"h2".to_vec(), b"http/1.1".to_vec()];
    Ok(config)
}
```

## 2. 证书管理

### 2.1 自签名证书（仅开发与测试）

```rust
use rcgen::{Certificate, CertificateParams, DistinguishedName};

pub fn generate_self_signed_cert() -> Result<Certificate, Box<dyn std::error::Error>> {
    let mut params = CertificateParams::new(vec!["localhost".to_string()]);
    params.distinguished_name = DistinguishedName::new();
    params.distinguished_name.push(rcgen::DnType::CommonName, "My Server");

    let cert = Certificate::from_params(params)?;
    std::fs::write("cert.pem", cert.serialize_pem()?)?;
    std::fs::write("key.pem", cert.serialize_private_key_pem())?;
    Ok(cert)
}
```

### 2.2 生产证书

- 使用 Let's Encrypt 等公共 CA 签发的证书。
- 配置证书自动续期。
- 验证证书链和主机名，不要禁用验证。

## 3. 认证与授权

### 3.1 JWT

```rust
use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct Claims {
    sub: String,
    exp: usize,
    role: String,
}

fn generate_jwt(user_id: &str, role: &str, secret: &str) -> Result<String, jsonwebtoken::errors::Error> {
    let exp = jsonwebtoken::get_current_timestamp() as usize + 24 * 3600;
    let claims = Claims { sub: user_id.to_owned(), exp, role: role.to_owned() };
    encode(&Header::default(), &claims, &EncodingKey::from_secret(secret.as_ref()))
}
```

### 3.2 OAuth2 / OpenID Connect

生产环境建议使用 `oauth2` crate 实现标准 OAuth2 / OIDC 流程，避免自行设计认证协议。

## 4. 输入验证与过滤

- 对所有外部输入进行长度、类型和范围校验。
- 使用参数化查询或 ORM 防止 SQL 注入。
- 对输出进行 HTML 转义防止 XSS。
- 校验文件上传类型和大小。

## 5. DoS 防护

### 5.1 速率限制

```rust
use std::collections::HashMap;
use std::time::{Duration, Instant};

struct RateLimiter {
    requests: HashMap<String, Vec<Instant>>,
    max_requests: usize,
    window: Duration,
}

impl RateLimiter {
    fn is_allowed(&mut self, key: &str) -> bool {
        let now = Instant::now();
        let window_start = now - self.window;
        let timestamps = self.requests.entry(key.to_string()).or_default();
        timestamps.retain(|&t| t > window_start);

        if timestamps.len() < self.max_requests {
            timestamps.push(now);
            true
        } else {
            false
        }
    }
}
```

### 5.2 连接限制

- 限制单 IP 并发连接数。
- 设置请求体大小上限。
- 使用超时防止慢速攻击。

## 6. 安全响应头

| 头部 | 作用 |
| :--- | :--- |
| `Strict-Transport-Security` | 强制 HTTPS |
| `Content-Security-Policy` | 防止 XSS |
| `X-Frame-Options` | 防止点击劫持 |
| `X-Content-Type-Options` | 防止 MIME 嗅探 |

## 7. 最佳实践

- 默认启用 TLS，禁用不安全的协议版本和加密套件。
- 不要自行实现密码学原语，使用 `ring` / `rustls`。
- 最小权限原则：服务只暴露必要的端口和权限。
- 记录安全事件并设置告警。
- 定期进行依赖审计（`cargo audit`）。

> **L5 对比**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)

---

## 相关概念

- [Security & Cryptography](../07_security_and_cryptography/43_security_cryptography.md)
- [高级网络协议](01_advanced_network_protocols.md)
- [HTTP 客户端开发](../04_web_and_networking/41_http_client_development.md)

---

> **来源**: [rustls](https://docs.rs/rustls/) · [RFC 8446](https://tools.ietf.org/html/rfc8446) · [OWASP Rust Security](https://owasp.org/www-project-web-security-testing-guide/)
