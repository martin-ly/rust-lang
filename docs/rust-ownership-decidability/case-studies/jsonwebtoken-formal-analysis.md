# jsonwebtoken JWT形式化分析

> **主题**: JWT签名与验证安全
>
> **形式化框架**: 密码学验证 + 时间约束
>
> **参考**: jsonwebtoken crate Documentation; RFC 7519

---

## 目录

- [jsonwebtoken JWT形式化分析](#jsonwebtoken-jwt形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Token结构](#2-token结构)
    - [定理 2.1 (JWT三段式)](#定理-21-jwt三段式)
  - [3. 验证约束](#3-验证约束)
    - [定理 3.1 (验证时约束)](#定理-31-验证时约束)
  - [4. 算法安全](#4-算法安全)
    - [定理 4.1 (算法拒绝)](#定理-41-算法拒绝)
    - [定理 4.2 (None算法)](#定理-42-none算法)
  - [5. 时间验证](#5-时间验证)
    - [定理 5.1 (时间窗口)](#定理-51-时间窗口)
  - [6. 反例](#6-反例)
    - [反例 6.1 (密钥混淆)](#反例-61-密钥混淆)
    - [反例 6.2 (忽略验证)](#反例-62-忽略验证)

---

## 1. 引言

jsonwebtoken提供:

- JWT编码/解码
- 多种算法支持
- 验证约束
- 时间检查

---

## 2. Token结构

### 定理 2.1 (JWT三段式)

> JWT = Base64(Header) + "." + Base64(Claims) + "." + Signature

```rust
pub struct TokenData<T> {
    pub claims: T,      // 自定义声明
    pub header: Header, // 算法元数据
}
```

∎

---

## 3. 验证约束

### 定理 3.1 (验证时约束)

> 可配置多种验证规则。

```rust
let validation = Validation::new(Algorithm::HS256);
validation.sub = Some("user123".to_string());  // 主题验证
validation.aud = Some(HashSet::from(["my_app"])); // 受众验证
```

∎

---

## 4. 算法安全

### 定理 4.1 (算法拒绝)

> 不明算法拒绝验证。

```rust
validation.algorithms = vec![Algorithm::EdDSA];  // 仅允许EdDSA
// 如果token使用HS256，验证失败
```

∎

### 定理 4.2 (None算法)

> 默认拒绝无签名算法。

```rust
// 防止攻击: {"alg": "none"}
validation.required_spec_claims.insert("alg".to_string());
```

∎

---

## 5. 时间验证

### 定理 5.1 (时间窗口)

> exp(过期)和nbf(生效前)自动验证。

```rust
#[derive(Serialize, Deserialize)]
struct Claims {
    exp: usize,  // 过期时间戳
    nbf: usize,  // 生效时间戳
    iat: usize,  // 签发时间
}

// 当前时间必须在[nbf, exp]内
```

∎

---

## 6. 反例

### 反例 6.1 (密钥混淆)

```rust
// 危险: RS256使用公钥验证，但误用私钥
let token = decode::<Claims>(
    token,
    &EncodingKey::from_rsa_pem(private_key)?,  // 错误!
    &validation
);

// 正确: 使用公钥验证
let token = decode::<Claims>(
    token,
    &DecodingKey::from_rsa_pem(public_key)?,
    &validation
);
```

### 反例 6.2 (忽略验证)

```rust
// 危险: 禁用所有验证
let mut validation = Validation::default();
validation.validate_exp = false;
validation.validate_nbf = false;
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
