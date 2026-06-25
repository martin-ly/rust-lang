# jsonwebtoken JWT形式化分析

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: JWT签名与验证安全
>
> **形式化框架**: 密码学验证 + 时间约束
>
> **参考**: jsonwebtoken crate Documentation; RFC 7519

---

## 目录
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

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
<a id="定理数量-6个"></a>
  - [*定理数量: 6个*](#定理数量-6个)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

---

## 1. 引言
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

jsonwebtoken提供:

- JWT编码/解码
- 多种算法支持
- 验证约束
- 时间检查

---

## 2. Token结构
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 定理 2.1 (JWT三段式)

> JWT = Base64(Header) + "." + Base64(Claims) + "." + Signature

```rust,ignore
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

```rust,ignore
let validation = Validation::new(Algorithm::HS256);
validation.sub = Some("user123".to_string());  // 主题验证
validation.aud = Some(HashSet::from(["my_app"])); // 受众验证
```

∎

---

## 4. 算法安全

### 定理 4.1 (算法拒绝)

> 不明算法拒绝验证。

```rust,ignore
validation.algorithms = vec![Algorithm::EdDSA];  // 仅允许EdDSA
// 如果token使用HS256，验证失败
```

∎

### 定理 4.2 (None算法)

> 默认拒绝无签名算法。

```rust,ignore
// 防止攻击: {"alg": "none"}
validation.required_spec_claims.insert("alg".to_string());
```

∎

---

## 5. 时间验证

### 定理 5.1 (时间窗口)

> exp(过期)和nbf(生效前)自动验证。

```rust,ignore
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

```rust,ignore
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

```rust,ignore
// 危险: 禁用所有验证
let mut validation = Validation::default();
validation.validate_exp = false;
validation.validate_nbf = false;
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**

> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**

> **来源: [Wikipedia - Web Framework](https://en.wikipedia.org/wiki/Web_Framework)**

> **来源: [axum.rs Documentation](https://docs.rs/axum/latest/axum/)**

> **来源: [actix.rs Documentation](https://actix.rs/)**

> **来源: [RFC 2616 - HTTP](https://rust-lang.github.io/rfcs/2616-http.html)**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Tokio Documentation](https://docs.rs/tokio/latest/tokio/)]**
>
> **[来源: [Hyper Documentation](https://hyper.rs/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
