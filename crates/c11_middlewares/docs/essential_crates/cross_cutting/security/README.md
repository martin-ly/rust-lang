# Security - 安全工具

## 📋 目录

- [Security - 安全工具](#security---安全工具)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [安全审计](#安全审计)
    - [cargo-audit](#cargo-audit)
    - [cargo-deny](#cargo-deny)
  - [密码学](#密码学)
    - [ring](#ring)
    - [rustls (TLS)](#rustls-tls)
  - [最佳实践](#最佳实践)
    - [1. 输入验证](#1-输入验证)
    - [2. SQL 注入防护](#2-sql-注入防护)
    - [3. XSS 防护](#3-xss-防护)
  - [参考资源](#参考资源)

---

## 概述

安全是应用开发的核心关注点，Rust 提供强大的安全工具链。

---

## 安全审计

### cargo-audit

```bash
# 安装
cargo install cargo-audit

# 检查漏洞
cargo audit

# 修复漏洞
cargo audit fix
```

### cargo-deny

```bash
# 安装
cargo install cargo-deny

# 初始化配置
cargo deny init

# 检查
cargo deny check
cargo deny check advisories
cargo deny check licenses
```

配置文件 `deny.toml`:

```toml
[advisories]
vulnerability = "deny"
unmaintained = "warn"
unsound = "warn"
yanked = "warn"

[licenses]
unlicensed = "deny"
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
]

[bans]
multiple-versions = "warn"
```

---

## 密码学

### ring

```rust
use ring::{digest, pbkdf2, rand};
use ring::rand::SecureRandom;

fn hash_with_sha256(data: &[u8]) -> Vec<u8> {
    digest::digest(&digest::SHA256, data).as_ref().to_vec()
}

fn generate_random_bytes() -> [u8; 32] {
    let rng = rand::SystemRandom::new();
    let mut bytes = [0u8; 32];
    rng.fill(&mut bytes).unwrap();
    bytes
}
```

### rustls (TLS)

```rust
use rustls::{ClientConfig, RootCertStore};

fn create_tls_config() -> ClientConfig {
    let mut root_store = RootCertStore::empty();
    root_store.add_trust_anchors(
        webpki_roots::TLS_SERVER_ROOTS.iter().map(|ta| {
            rustls::OwnedTrustAnchor::from_subject_spki_name_constraints(
                ta.subject,
                ta.spki,
                ta.name_constraints,
            )
        })
    );
    
    ClientConfig::builder()
        .with_safe_defaults()
        .with_root_certificates(root_store)
        .with_no_client_auth()
}
```

---

## 最佳实践

### 1. 输入验证

```rust
use validator::Validate;

#[derive(Validate)]
struct UserInput {
    #[validate(email)]
    email: String,
    
    #[validate(length(min = 8, max = 100))]
    password: String,
    
    #[validate(range(min = 18, max = 120))]
    age: u32,
}
```

### 2. SQL 注入防护

```rust
// ✅ 使用参数化查询
let user = sqlx::query_as!(
    User,
    "SELECT * FROM users WHERE id = $1",
    user_id
)
.fetch_one(&pool)
.await?;

// ❌ 永远不要拼接 SQL
// let query = format!("SELECT * FROM users WHERE id = {}", user_id);
```

### 3. XSS 防护

```rust
use askama::Template;

#[derive(Template)]
#[template(path = "user.html")]
struct UserTemplate {
    name: String,  // 自动转义
}
```

---

## 参考资源

- [cargo-audit GitHub](https://github.com/rustsec/rustsec)
- [cargo-deny GitHub](https://github.com/EmbarkStudios/cargo-deny)
- [ring 文档](https://docs.rs/ring/)
