# 05_security - 安全

本文件夹包含Rust 1.90版本在IoT安全领域的最新成熟方案和开源库。

## 🔐 加密和认证

### 1. 加密库

#### ring

- **描述**: 高性能加密库
- **特点**:
  - 基于BoringSSL构建
  - 支持AES、RSA、ECDSA等算法
  - 内存安全，无unsafe代码
- **GitHub**: <https://github.com/briansmith/ring>
- **文档**: <https://docs.rs/ring>

#### rustls

- **描述**: 纯Rust TLS实现
- **特点**:
  - 支持TLS 1.2和1.3
  - 高性能、内存安全
  - 支持客户端和服务器
- **GitHub**: <https://github.com/rustls/rustls>
- **文档**: <https://docs.rs/rustls>

#### openssl

- **描述**: OpenSSL的Rust绑定
- **特点**:
  - 支持DTLS
  - 完整的OpenSSL功能
  - 适用于需要OpenSSL兼容性的场景
- **GitHub**: <https://github.com/sfackler/rust-openssl>
- **文档**: <https://docs.rs/openssl>

### 2. 哈希和摘要

#### sha2

- **描述**: SHA-2哈希函数实现
- **特点**:
  - 支持SHA-224、SHA-256、SHA-384、SHA-512
  - 高性能实现
  - 适用于密码学应用
- **GitHub**: <https://github.com/RustCrypto/hashes>
- **文档**: <https://docs.rs/sha2>

#### blake3

- **描述**: BLAKE3哈希函数
- **特点**:
  - 高性能哈希函数
  - 支持并行计算
  - 适用于大文件哈希
- **GitHub**: <https://github.com/BLAKE3-team/BLAKE3>
- **文档**: <https://docs.rs/blake3>

#### argon2

- **描述**: Argon2密码哈希函数
- **特点**:
  - 抗ASIC和GPU攻击
  - 适用于密码存储
  - 支持多种变体
- **GitHub**: <https://github.com/RustCrypto/password-hashes>
- **文档**: <https://docs.rs/argon2>

### 3. 数字签名

#### ed25519-dalek

- **描述**: Ed25519数字签名实现
- **特点**:
  - 高性能椭圆曲线签名
  - 支持批量验证
  - 适用于身份认证
- **GitHub**: <https://github.com/dalek-cryptography/ed25519-dalek>
- **文档**: <https://docs.rs/ed25519-dalek>

#### ecdsa

- **描述**: ECDSA数字签名实现
- **特点**:
  - 支持多种椭圆曲线
  - 与现有系统兼容
  - 适用于证书签名
- **GitHub**: <https://github.com/RustCrypto/signatures>
- **文档**: <https://docs.rs/ecdsa>

## 🔑 密钥管理

### 1. 密钥生成和存储

#### rand

- **描述**: 随机数生成库
- **特点**:
  - 密码学安全的随机数
  - 支持多种随机数生成器
  - 适用于密钥生成
- **GitHub**: <https://github.com/rust-random/rand>
- **文档**: <https://docs.rs/rand>

#### secrecy

- **描述**: 安全密钥管理
- **特点**:
  - 防止密钥泄露
  - 自动内存清理
  - 适用于敏感数据
- **GitHub**: <https://github.com/iqlusioninc/crates/tree/main/secrecy>
- **文档**: <https://docs.rs/secrecy>

### 2. 证书管理

#### x509-parser

- **描述**: X.509证书解析器
- **特点**:
  - 支持X.509证书解析
  - 验证证书链
  - 适用于PKI系统
- **GitHub**: <https://github.com/rusticata/x509-parser>
- **文档**: <https://docs.rs/x509-parser>

#### rcgen

- **描述**: X.509证书生成器
- **特点**:
  - 生成自签名证书
  - 支持CSR生成
  - 适用于测试和开发
- **GitHub**: <https://github.com/est31/rcgen>
- **文档**: <https://docs.rs/rcgen>

## 🛡️ 安全协议

### 1. TLS/DTLS

#### tokio-rustls

- **描述**: 基于tokio的TLS实现
- **特点**:
  - 异步TLS支持
  - 与tokio生态系统集成
  - 适用于高并发应用
- **GitHub**: <https://github.com/rustls/tokio-rustls>
- **文档**: <https://docs.rs/tokio-rustls>

#### quinn

- **描述**: QUIC协议实现
- **特点**:
  - 基于QUIC的可靠传输
  - 内置TLS 1.3支持
  - 适用于低延迟应用
- **GitHub**: <https://github.com/quinn-rs/quinn>
- **文档**: <https://docs.rs/quinn>

### 2. 身份认证

#### jsonwebtoken

- **描述**: JWT令牌处理
- **特点**:
  - 支持JWT创建和验证
  - 多种签名算法
  - 适用于API认证
- **GitHub**: <https://github.com/Keats/jsonwebtoken>
- **文档**: <https://docs.rs/jsonwebtoken>

#### oauth2

- **描述**: OAuth 2.0客户端
- **特点**:
  - 支持OAuth 2.0流程
  - 多种授权类型
  - 适用于第三方认证
- **GitHub**: <https://github.com/ramosbugs/oauth2-rs>
- **文档**: <https://docs.rs/oauth2>

## 🔒 设备安全

### 1. 安全启动

#### uefi-rs

- **描述**: UEFI的Rust绑定
- **特点**:
  - 支持UEFI固件
  - 安全启动支持
  - 适用于x86_64平台
- **GitHub**: <https://github.com/rust-osdev/uefi-rs>
- **文档**: <https://docs.rs/uefi>

### 2. 硬件安全模块

#### pkcs11

- **描述**: PKCS#11接口
- **特点**:
  - 支持HSM设备
  - 硬件密钥保护
  - 适用于高安全要求场景
- **GitHub**: <https://github.com/parallaxsecond/rust-pkcs11>
- **文档**: <https://docs.rs/pkcs11>

#### tpm2-rs

- **描述**: TPM 2.0接口
- **特点**:
  - 支持TPM 2.0设备
  - 硬件密钥保护
  - 适用于可信计算
- **GitHub**: <https://github.com/parallaxsecond/tpm2-rs>
- **文档**: <https://docs.rs/tpm2-rs>

## 🚨 安全监控

### 1. 入侵检测

#### suricata

- **描述**: 网络入侵检测系统
- **特点**:
  - 实时网络监控
  - 规则引擎
  - 适用于网络安全
- **GitHub**: <https://github.com/OISF/suricata>

### 2. 日志分析

#### serde

- **描述**: 序列化框架
- **特点**:
  - 结构化日志
  - 高性能序列化
  - 适用于日志分析
- **GitHub**: <https://github.com/serde-rs/serde>
- **文档**: <https://docs.rs/serde>

#### tracing

- **描述**: 结构化日志和追踪
- **特点**:
  - 异步日志支持
  - 分布式追踪
  - 适用于微服务架构
- **GitHub**: <https://github.com/tokio-rs/tracing>
- **文档**: <https://docs.rs/tracing>

## 📊 安全性能对比

| 功能 | 库 | 性能 | 内存使用 | 适用场景 |
|------|----|----|---------|---------|
| AES加密 | ring | 1GB/s | 10MB | 高速加密 |
| RSA签名 | ring | 1000 ops/sec | 5MB | 数字签名 |
| TLS握手 | rustls | 1000 handshakes/sec | 20MB | 安全通信 |
| 哈希计算 | blake3 | 2GB/s | 5MB | 快速哈希 |
| JWT验证 | jsonwebtoken | 10,000 tokens/sec | 2MB | API认证 |

## 🚀 快速开始

### TLS服务器示例

```rust
use rustls::{ServerConfig, ServerConnection};
use std::sync::Arc;
use tokio::net::TcpListener;
use tokio_rustls::TlsAcceptor;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 加载证书和私钥
    let certs = load_certs("cert.pem")?;
    let key = load_private_key("key.pem")?;
    
    // 创建TLS配置
    let config = ServerConfig::builder()
        .with_safe_defaults()
        .with_no_client_auth()
        .with_single_cert(certs, key)?;
    
    let acceptor = TlsAcceptor::from(Arc::new(config));
    
    // 监听连接
    let listener = TcpListener::bind("0.0.0.0:443").await?;
    
    while let Some((stream, _)) = listener.accept().await? {
        let acceptor = acceptor.clone();
        
        tokio::spawn(async move {
            let tls_stream = acceptor.accept(stream).await?;
            // 处理TLS连接
            handle_connection(tls_stream).await
        });
    }
    
    Ok(())
}
```

### JWT认证示例

```rust
use jsonwebtoken::{decode, encode, Algorithm, DecodingKey, EncodingKey, Header, Validation};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct Claims {
    sub: String,
    exp: usize,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let secret = "your-secret-key";
    let encoding_key = EncodingKey::from_secret(secret.as_ref());
    let decoding_key = DecodingKey::from_secret(secret.as_ref());
    
    // 创建JWT令牌
    let claims = Claims {
        sub: "user123".to_string(),
        exp: (chrono::Utc::now() + chrono::Duration::hours(1)).timestamp() as usize,
    };
    
    let token = encode(&Header::default(), &claims, &encoding_key)?;
    println!("JWT令牌: {}", token);
    
    // 验证JWT令牌
    let validation = Validation::new(Algorithm::HS256);
    let token_data = decode::<Claims>(&token, &decoding_key, &validation)?;
    
    println!("验证成功: {:?}", token_data.claims);
    
    Ok(())
}
```

### 加密数据示例

```rust
use ring::aead::{Aad, LessSafeKey, Nonce, UnboundKey, AES_256_GCM};
use ring::rand::{SecureRandom, SystemRandom};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let rng = SystemRandom::new();
    
    // 生成密钥
    let mut key_bytes = [0u8; 32];
    rng.fill(&mut key_bytes)?;
    let key = LessSafeKey::new(UnboundKey::new(&AES_256_GCM, &key_bytes)?);
    
    // 生成随机数
    let mut nonce_bytes = [0u8; 12];
    rng.fill(&mut nonce_bytes)?;
    let nonce = Nonce::assume_unique_for_key(nonce_bytes);
    
    // 加密数据
    let plaintext = b"Hello, World!";
    let mut ciphertext = plaintext.to_vec();
    let aad = Aad::empty();
    
    key.seal_in_place(nonce, aad, &mut ciphertext)?;
    
    println!("加密数据: {:?}", ciphertext);
    
    // 解密数据
    let key = LessSafeKey::new(UnboundKey::new(&AES_256_GCM, &key_bytes)?);
    let nonce = Nonce::assume_unique_for_key(nonce_bytes);
    
    key.open_in_place(nonce, aad, &mut ciphertext)?;
    
    println!("解密数据: {:?}", String::from_utf8(ciphertext)?);
    
    Ok(())
}
```

## 📚 学习资源

### 官方文档

- [ring Documentation](https://docs.rs/ring)
- [rustls Documentation](https://docs.rs/rustls)
- [RustCrypto Documentation](https://docs.rs/ring)

### 安全指南

- [Rust Security Guidelines](https://github.com/rust-lang/rust-security)
- [Cryptography in Rust](https://github.com/RustCrypto)
- [IoT Security Best Practices](https://github.com/iot-security/best-practices)

## 🔄 持续更新

本文件夹将持续跟踪：

- 新安全漏洞和修复
- 加密算法的发展
- 安全协议标准更新
- 最佳实践和指南

## 📝 贡献指南

欢迎提交：

- 新安全库的信息
- 安全漏洞报告
- 最佳实践和指南
- 性能测试和基准数据
