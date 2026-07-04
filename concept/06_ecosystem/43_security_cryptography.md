> **内容分级**: [综述级]
> [专家级]
> **代码状态**: ✅ 含可编译示例
>
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
# Security & Cryptography（安全与密码学）
>
> **EN**: Security Practices
> **Summary**: Security Practices. Guide to 43 Security Cryptography.
>
> **受众**: [进阶]
> **Bloom 层级**: 应用 → 评价
> **A/S/P 标记**: **A+S+P** — Application + Structure + Procedure
> **双维定位**: P×Eva — 评价密码学实现的安全性
> **前置依赖**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [Trait](../02_intermediate/00_traits/01_traits.md) · [类型系统（Type System）](../01_foundation/02_type_system/04_type_system.md) · 安全实践
> **后置延伸**: [区块链与智能合约安全](06_blockchain.md) · [网络协议](38_network_protocols.md) · [TLS/QUIC](38_network_protocols.md)
>
> **来源**: [ring](https://docs.rs/ring/) · [rustls](https://docs.rs/rustls/) · [Rust Crypto](https://github.com/RustCrypto) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
> **前置概念**: N/A
---

> **来源**: [NIST FIPS 197](https://csrc.nist.gov/publications/detail/fips/197/final) ·
> [NIST FIPS 180-4](https://csrc.nist.gov/publications/detail/fips/180/4/final) ·
> [NIST FIPS 186-5](https://csrc.nist.gov/publications/detail/fips/186/5/final) ·
> [RFC 8439 — ChaCha20-Poly1305](https://tools.ietf.org/html/rfc8439) ·
> [RFC 8446 — TLS 1.3](https://tools.ietf.org/html/rfc8446) ·
> [RFC 9106 — Argon2](https://tools.ietf.org/html/rfc9106) ·
> [ring crate](https://briansmith.org/rustdoc/ring/) ·
> [rustls](https://docs.rs/rustls/latest/rustls/) ·
> [dalek-cryptography](https://docs.rs/ed25519-dalek/latest/ed25519_dalek/)
> **后置概念**: [Future Roadmap](../07_future/24_roadmap.md)
> **前置依赖**: [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)

## 📑 目录

- [Security \& Cryptography（安全与密码学）](#security--cryptography安全与密码学)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 Kerckhoffs 原则](#11-kerckhoffs-原则)
    - [1.2 密码学原语分类](#12-密码学原语分类)
    - [1.3 威胁模型](#13-威胁模型)
  - [二、概念属性矩阵](#二概念属性矩阵)
  - [三、对称加密](#三对称加密)
    - [3.1 AES-GCM](#31-aes-gcm)
    - [3.2 ChaCha20-Poly1305](#32-chacha20-poly1305)
  - [四、非对称加密与数字签名](#四非对称加密与数字签名)
    - [4.1 ECC 与 Ed25519](#41-ecc-与-ed25519)
    - [4.2 X25519 密钥交换](#42-x25519-密钥交换)
  - [五、哈希与消息认证](#五哈希与消息认证)
    - [5.1 哈希函数](#51-哈希函数)
    - [5.2 HMAC](#52-hmac)
    - [5.3 密钥派生（KDF）](#53-密钥派生kdf)
  - [六、Rust 密码学生态](#六rust-密码学生态)
    - [6.1 ring：安全原语聚合](#61-ring安全原语聚合)
    - [6.2 rustls：纯 Rust TLS](#62-rustls纯-rust-tls)
    - [6.3 dalek-cryptography：零知识友好](#63-dalek-cryptography零知识友好)
  - [七、常量时间操作与侧信道防护](#七常量时间操作与侧信道防护)
  - [八、后量子密码学预览](#八后量子密码学预览)
  - [九、反命题与边界](#九反命题与边界)
    - [9.1 反命题树](#91-反命题树)
    - [9.2 边界极限](#92-边界极限)
  - [十、边界测试](#十边界测试)
    - [10.1 边界测试：非常量时间比较导致定时攻击（运行时信息泄露）](#101-边界测试非常量时间比较导致定时攻击运行时信息泄露)
    - [10.2 边界测试：Nonce 复用破坏 AES-GCM 机密性（逻辑错误）](#102-边界测试nonce-复用破坏-aes-gcm-机密性逻辑错误)
    - [10.3 边界测试：低迭代次数 KDF 导致暴力破解（安全漏洞）](#103-边界测试低迭代次数-kdf-导致暴力破解安全漏洞)
  - [相关概念文件](#相关概念文件)
    - [补充定理链](#补充定理链)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Rust 的 `ring` crate 在密码学中提供什么功能？（理解层）](#测验-1rust-的-ring-crate-在密码学中提供什么功能理解层)
    - [测验 2：为什么密码学代码中绝对不应该使用 `unsafe` 或原始指针？（理解层）](#测验-2为什么密码学代码中绝对不应该使用-unsafe-或原始指针理解层)
    - [测验 3：Rust 的常量时间比较（Constant-Time Comparison）为什么对密码学重要？（理解层）](#测验-3rust-的常量时间比较constant-time-comparison为什么对密码学重要理解层)
    - [测验 4：`rustls` 与 OpenSSL 相比在安全性上有什么优势？（理解层）](#测验-4rustls-与-openssl-相比在安全性上有什么优势理解层)
    - [测验 5：在 Rust 中存储密码时，为什么必须使用 Argon2 / bcrypt / scrypt 而非 SHA-256？（理解层）](#测验-5在-rust-中存储密码时为什么必须使用-argon2--bcrypt--scrypt-而非-sha-256理解层)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)

> **Bloom 层级**: 应用 → 评价
**变更日志**:

- v1.0 (2026-05-25): 初始创建——密码学原语（对称/非对称/哈希/KDF）、Rust 生态（ring/rustls/dalek）、常量时间操作、后量子密码学预览

---

## 一、权威定义（Definition）
>

**可编译示例** — 标准库哈希与 HMAC 风格验证：

```rust
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// 计算数据的哈希值（用于完整性校验，非密码学安全）
fn compute_hash<T: Hash>(data: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    data.hash(&mut hasher);
    hasher.finish()
}

/// 常量时间比较（防止定时攻击）
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut result = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        result |= x ^ y;
    }
    result == 0
}

fn main() {
    let password = b"correct-horse-battery-staple";
    let stored_hash = compute_hash(&password.as_slice());

    let input = b"correct-horse-battery-staple";
    let input_hash = compute_hash(&input.as_slice());

    assert!(constant_time_eq(
        &stored_hash.to_le_bytes(),
        &input_hash.to_le_bytes()
    ));
}
```

> ⚠️ **注意**: `DefaultHasher` 仅适用于数据结构哈希，**不应用于密码学场景**。密码学哈希请使用 `sha2`/`blake3` crate。

### 1.1 Kerckhoffs 原则
>
> **Kerckhoffs's Principle (1883)** 密码系统的安全性不应依赖于算法的保密性，而应完全依赖于**密钥的保密性**。这一原则是现代密码学的基石：即使攻击者完全了解算法的实现细节，系统仍然应该是安全的。

```text
现代密码学的安全边界:
┌─────────────────────────────────────────────────────────────┐
│                      攻击者能力模型                           │
├─────────────────────────────────────────────────────────────┤
│ 已知明文攻击 (KPA)   : 攻击者知道部分明文-密文对              │
│ 选择明文攻击 (CPA)   : 攻击者可选择明文并获取密文            │
│ 选择密文攻击 (CCA)   : 攻击者可选择密文并获取解密结果        │
│ 侧信道攻击           : 攻击者观测时间、功耗、电磁泄漏          │
└─────────────────────────────────────────────────────────────┘
  ↑
  密码系统的安全性必须在上述所有攻击模型下保持
```

> **来源**: [Kerckhoffs 1883 — La Cryptographie Militaire](https://www.petitcolas.net/fabien/kerckhoffs/) · [Katz & Lindell — Introduction to Modern Cryptography](https://www.cs.umd.edu/~jkatz/imc.html)

### 1.2 密码学原语分类
>

| **原语类别** | **功能** | **典型算法** | **Rust Crate** |
|:---|:---|:---|:---|
| **对称加密** | 机密性（Confidentiality）| AES-GCM, ChaCha20-Poly1305 | `ring`, `aes-gcm`, `chacha20poly1305` |
| **非对称加密** | 密钥交换、数字签名 | RSA, ECDH, Ed25519, X25519 | `ring`, `ed25519-dalek`, `x25519-dalek` |
| **哈希函数** | 完整性（Integrity）| SHA-256, SHA-3, BLAKE3 | `sha2`, `sha3`, `blake3` |
| **消息认证码** | 认证 + 完整性 | HMAC-SHA256, KMAC | `ring`, `hmac` |
| **密钥派生** | 从密码生成密钥 | Argon2, PBKDF2, HKDF, scrypt | `argon2`, `pbkdf2`, `hkdf` |
| **随机数生成** | 不可预测性 | CSPRNG（OS / 硬件）| `ring::rand`, `rand::rngs::OsRng` |

> **来源**: [NIST Cryptographic Standards](https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines) · [IETF Crypto Forum](https://datatracker.ietf.org/rg/cfrg/about/)

### 1.3 威胁模型
>

```text
密码学威胁模型（STRIDE 的密码学视角）:
  Spoofing（伪造）    → 数字签名验证失败
  Tampering（篡改）   → MAC/哈希验证失败
  Repudiation（否认）  → 缺少数字签名
  Information Disclosure（信息泄露）→ 加密失败或侧信道泄露
  Denial of Service（拒绝服务）    → 资源耗尽攻击（如 Argon2 参数选择）
  Elevation of Privilege（权限提升）→ 密钥泄露导致 impersonation

Rust 的安全保证与密码学威胁的对应:
  内存安全（Ownership） → 防止密钥在内存中被意外读取/写入
  类型安全（Type System） → 防止明文和密文的类型混淆
  Send/Sync           → 确保密钥材料安全跨线程传递
  const fn            → 编译期密码学常量验证
```

> **来源**: [OWASP — Threat Modeling](https://owasp.org/www-community/Application_Threat_Modeling) · [NIST SP 800-57](https://csrc.nist.gov/publications/detail/sp/800-57-part-1/rev-5/final)

---

## 二、概念属性矩阵

| **维度** | **对称加密** | **非对称加密** | **哈希** | **KDF** |
|:---|:---|:---|:---|:---|
| **速度** | 快（~GB/s）| 慢（~MB/s）| 快（~GB/s）| 慢（可调）|
| **密钥管理** | 困难（n² 问题）| 简单（公钥分发）| 无密钥 | 输入为密码 |
| **主要用途** | 大量数据加密 | 密钥交换、签名 | 完整性校验 | 密码 → 密钥 |
| **量子威胁** | Grover（对折安全性）| Shor（完全破解）| Grover | 同左 |
| **Rust 安全** | `NonNull<u8>` 管理密钥 | `Scalar` 类型防止泄漏 | 常量时间比较 | 内存清零 |

> **来源**: [NIST SP 800-57](https://csrc.nist.gov/publications/detail/sp/800-57-part-1/rev-5/final) · [Post-Quantum Cryptography NIST](https://csrc.nist.gov/projects/post-quantum-cryptography)

---

## 三、对称加密

### 3.1 AES-GCM
>
> **[NIST FIPS 197](https://csrc.nist.gov/publications/detail/fips/197/final)** AES（Advanced Encryption Standard）是 NIST 于 2001 年标准化的分组密码，块大小 128 位，密钥长度支持 128/192/256 位。GCM（Galois/Counter Mode）提供**认证加密**（Authenticated Encryption），同时保证机密性和完整性。

```text
AES-GCM 参数:
  密钥长度: 128/192/256 位（推荐 256 位）
  Nonce (IV): 96 位（必须唯一，不可复用！）
  认证标签: 128 位

安全要求:
  ✅ Nonce 必须唯一：同一密钥下复用 Nonce 导致密钥恢复攻击
  ✅ 消息长度限制：单个密钥加密的总数据量 ≤ 2^39 - 256 位（~64GB）
  ✅ 推荐使用 96 位随机 Nonce（计数器或 CSPRNG）
```

```rust,ignore
use aes_gcm::{
    aead::{Aead, AeadCore, KeyInit, OsRng},
    Aes256Gcm, Nonce,
};

fn encrypt_aes_gcm(key: &[u8; 32], plaintext: &[u8]) -> Result<Vec<u8>, aes_gcm::Error> {
    let cipher = Aes256Gcm::new_from_slice(key)?;
    // ⚠️ Nonce 必须唯一！使用 CSPRNG 生成
    let nonce = Aes256Gcm::generate_nonce(&mut OsRng);
    let ciphertext = cipher.encrypt(&nonce, plaintext)?;

    // 输出: nonce (12 bytes) || ciphertext || tag (16 bytes)
    let mut result = nonce.to_vec();
    result.extend_from_slice(&ciphertext);
    Ok(result)
}

fn decrypt_aes_gcm(key: &[u8; 32], ciphertext_with_nonce: &[u8]) -> Result<Vec<u8>, aes_gcm::Error> {
    let cipher = Aes256Gcm::new_from_slice(key)?;
    let (nonce, ciphertext) = ciphertext_with_nonce.split_at(12);
    let nonce = Nonce::from_slice(nonce);
    cipher.decrypt(nonce, ciphertext)
}
```

> **来源**: [NIST FIPS 197](https://csrc.nist.gov/publications/detail/fips/197/final) · [NIST SP 800-38D](https://csrc.nist.gov/publications/detail/sp/800-38d/final) · [aes-gcm crate](https://docs.rs/aes-gcm/latest/aes_gcm/)

### 3.2 ChaCha20-Poly1305
>
> **[RFC 8439](https://tools.ietf.org/html/rfc8439)** ChaCha20-Poly1305 是 Daniel Bernstein 设计的流密码 + MAC 组合，被 TLS 1.3 采纳为必备算法。相比 AES-GCM，ChaCha20 在**没有硬件 AES 加速**的平台（如移动设备、低端 ARM）上性能更好，且实现更简单（抗侧信道攻击）。

```text
ChaCha20-Poly1305 参数:
  密钥长度: 256 位
  Nonce: 96 位（或 64 位 IETF 变体）
  计数器: 32 位

AES-GCM vs ChaCha20-Poly1305:
  ┌─────────────────┬─────────────────┬─────────────────────────────┐
  │     特性        │    AES-GCM      │   ChaCha20-Poly1305         │
  ├─────────────────┼─────────────────┼─────────────────────────────┤
  │ 硬件加速        │ AES-NI (~1cpb)  │ 无（纯软件）                 │
  │ 软件性能        │ 慢（无 AES-NI）  │ 快（~3-4 cpb）              │
  │ 侧信道抗性      │ 需注意          │ 天然恒定时间                 │
  │ 实现复杂度      │ 高（有限域运算） │ 低（仅位运算）               │
  │ TLS 1.3 要求    │ 必须支持         │ 必须支持                     │
  └─────────────────┴─────────────────┴─────────────────────────────┘
  cpb = cycles per byte
```

```rust,ignore
use chacha20poly1305::{
    aead::{Aead, AeadCore, KeyInit, OsRng},
    ChaCha20Poly1305, Nonce,
};

fn encrypt_chacha20(key: &[u8; 32], plaintext: &[u8]) -> Result<Vec<u8>, chacha20poly1305::Error> {
    let cipher = ChaCha20Poly1305::new_from_slice(key)?;
    let nonce = ChaCha20Poly1305::generate_nonce(&mut OsRng);
    let ciphertext = cipher.encrypt(&nonce, plaintext)?;

    let mut result = nonce.to_vec();
    result.extend_from_slice(&ciphertext);
    Ok(result)
}
```

> **来源**: [RFC 8439](https://tools.ietf.org/html/rfc8439) · [ChaCha20 Design](https://cr.yp.to/chacha.html) · [chacha20poly1305 crate](https://docs.rs/chacha20poly1305/latest/chacha20poly1305/)

---

## 四、非对称加密与数字签名

### 4.1 ECC 与 Ed25519
>
> **[NIST FIPS 186-5](https://csrc.nist.gov/publications/detail/fips/186/5/final)** 椭圆曲线密码学（ECC）相比 RSA 提供相同安全强度下更短的密钥和更快的运算。Ed25519 是 Daniel Bernstein 设计的基于 Curve25519 的 EdDSA 签名方案，被 IETF 标准化（[RFC 8032](https://www.rfc-editor.org/info/rfc8032)），特征：**恒定时间实现、确定性签名、紧凑的 64 字节签名**。

```text
Ed25519 参数:
  曲线: Edwards25519（birationally equivalent to Curve25519）
  私钥: 32 字节
  公钥: 32 字节
  签名: 64 字节
  安全级别: ~128 位

RSA vs Ed25519 对比:
  ┌─────────────────┬─────────────────┬─────────────────────────────┐
  │     特性        │  RSA-2048       │      Ed25519                │
  ├─────────────────┼─────────────────┼─────────────────────────────┤
  │ 公钥大小        │ 256 字节         │ 32 字节                      │
  │ 签名大小        │ 256 字节         │ 64 字节                      │
  │ 签名速度        │ 慢               │ 快                           │
  │ 验证速度        │ 快               │ 更快                         │
  │ 侧信道抗性      │ 需注意（padding） │ 天然恒定时间                 │
  │ 量子威胁        │ Shor 完全破解    │ Shor 完全破解                │
  └─────────────────┴─────────────────┴─────────────────────────────┘
```

```rust,ignore
use ed25519_dalek::{SigningKey, Signer, Verifier, VerifyingKey};
use rand::rngs::OsRng;

fn generate_keypair() -> (SigningKey, VerifyingKey) {
    let signing_key = SigningKey::generate(&mut OsRng);
    let verifying_key = signing_key.verifying_key();
    (signing_key, verifying_key)
}

fn sign_message(signing_key: &SigningKey, message: &[u8]) -> ed25519_dalek::Signature {
    signing_key.sign(message)
}

fn verify_signature(
    verifying_key: &VerifyingKey,
    message: &[u8],
    signature: &ed25519_dalek::Signature,
) -> Result<(), ed25519_dalek::SignatureError> {
    verifying_key.verify(message, signature)
}
```

> **来源**: [RFC 8032 — EdDSA](https://tools.ietf.org/html/rfc8032) · [ed25519-dalek crate](https://docs.rs/ed25519-dalek/latest/ed25519_dalek/) · [Curve25519 Paper](https://cr.yp.to/ecdh/curve25519-20060209.pdf)

### 4.2 X25519 密钥交换
>
> **[RFC 7748](https://tools.ietf.org/html/rfc7748)** X25519 是基于 Curve25519 的 ECDH 密钥交换协议，被 TLS 1.3 采用为必备算法。特征：**常量时间实现、无需要求验证点的合法性**（ twist-security 设计）。

```rust,ignore
use x25519_dalek::{EphemeralSecret, PublicKey};
use rand::rngs::OsRng;

// Alice
let alice_secret = EphemeralSecret::random_from_rng(&mut OsRng);
let alice_public = PublicKey::from(&alice_secret);

// Bob
let bob_secret = EphemeralSecret::random_from_rng(&mut OsRng);
let bob_public = PublicKey::from(&bob_secret);

// 共享密钥
let alice_shared = alice_secret.diffie_hellman(&bob_public);
let bob_shared = bob_secret.diffie_hellman(&alice_public);

assert_eq!(alice_shared.as_bytes(), bob_shared.as_bytes());
```

> **来源**: [RFC 7748](https://tools.ietf.org/html/rfc7748) · [x25519-dalek crate](https://docs.rs/x25519-dalek/latest/x25519_dalek/)

---

## 五、哈希与消息认证

### 5.1 哈希函数
>
> **[NIST FIPS 180-4](https://csrc.nist.gov/publications/detail/fips/180/4/final)** SHA-2 系列（SHA-256, SHA-384, SHA-512）是目前最广泛使用的密码学哈希函数。BLAKE3 是 BLAKE 系列的最新版本，提供并行哈希和密钥化哈希（MAC/ KDF），速度远超 SHA-256。

```text
哈希函数对比:
  ┌────────────┬─────────────┬─────────────┬────────────────────────────┐
  │   算法     │ 输出长度     │ 速度        │ 适用场景                    │
  ├────────────┼─────────────┼─────────────┼────────────────────────────┤
  │ SHA-256    │ 256 位       │ ~200 MB/s   │ 通用、兼容性优先            │
  │ SHA-3-256  │ 256 位       │ ~150 MB/s   │ 抗长度扩展攻击              │
  │ BLAKE3     │ 256 位       │ ~1+ GB/s    │ 高性能、并行、密钥化        │
  └────────────┴─────────────┴─────────────┴────────────────────────────┘

安全要求:
  ✅ 碰撞抗性：找到两个不同输入使 hash(x) = hash(y) 在计算上不可行
  ✅ 原像抗性：给定 hash(x)，找到 x 在计算上不可行
  ✅ 第二原像抗性：给定 x，找到 y ≠ x 使 hash(x) = hash(y) 不可行
```

```rust,ignore
use sha2::{Sha256, Digest};
use blake3;

// SHA-256
fn hash_sha256(data: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(data);
    hasher.finalize().into()
}

// BLAKE3
fn hash_blake3(data: &[u8]) -> [u8; 32] {
    blake3::hash(data).into()
}

// 密钥化哈希（MAC）
fn keyed_hash_blake3(key: &[u8; 32], data: &[u8]) -> [u8; 32] {
    blake3::keyed_hash(key, data).into()
}
```

> **来源**: [NIST FIPS 180-4](https://csrc.nist.gov/publications/detail/fips/180/4/final) · [BLAKE3 Paper](https://blake3.io/blake3.pdf) · [sha2 crate](https://docs.rs/sha2/latest/sha2/) · [blake3 crate](https://docs.rs/blake3/latest/blake3/)

### 5.2 HMAC
>
> **[RFC 2104](https://tools.ietf.org/html/rfc2104)** HMAC（Hash-based Message Authentication Code）是使用密钥的哈希函数，提供**消息认证**和**完整性**保证。HMAC 的安全性不依赖于底层哈希函数的强碰撞抗性（即使 MD5/SHA-1 被破解，HMAC-MD5/HMAC-SHA1 仍然是安全的）。

```rust,ignore
use hmac::{Hmac, Mac};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

fn hmac_sign(key: &[u8], message: &[u8]) -> Vec<u8> {
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC key length valid");
    mac.update(message);
    mac.finalize().into_bytes().to_vec()
}

fn hmac_verify(key: &[u8], message: &[u8], signature: &[u8]) -> bool {
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC key length valid");
    mac.update(message);
    mac.verify_slice(signature).is_ok()
}
```

> **来源**: [RFC 2104 — HMAC](https://tools.ietf.org/html/rfc2104) · [hmac crate](https://docs.rs/hmac/latest/hmac/)

### 5.3 密钥派生（KDF）
>
> **[RFC 9106](https://tools.ietf.org/html/rfc9106)** Argon2 是 2015 年 Password Hashing Competition 的获胜算法，专门设计用于**密码哈希**和**密钥派生**。相比 PBKDF2 和 bcrypt，Argon2 抵抗 GPU/ASIC 暴力破解的能力更强，且可调节内存、时间和并行度参数。

```text
KDF 对比:
  ┌────────────┬─────────────┬─────────────┬────────────────────────────┐
  │   算法     │ 内存需求     │ 时间可调    │ 推荐场景                    │
  ├────────────┼─────────────┼─────────────┼────────────────────────────┤
  │ PBKDF2     │ 低           │ 迭代次数    │ 兼容性要求高的场景          │
  │ bcrypt     │ 低           │ 成本因子    │ 传统系统                     │
  │ scrypt     │ 高           │ 成本因子    │ 加密货币（如 Litecoin）     │
  │ Argon2id   │ 高           │ 内存+时间   │ 新系统的首选（OWASP 推荐）  │
  └────────────┴─────────────┴─────────────┴────────────────────────────┘

Argon2id 推荐参数（OWASP 2023）:
  内存: 19 MiB (m=19456)
  迭代: 2 (t=2)
  并行度: 1 (p=1)
```

```rust,ignore
use argon2::{Argon2, PasswordHasher, PasswordVerifier, password_hash::{
    SaltString, PasswordHash, PasswordHasher as _, PasswordVerifier as _,
}};
use rand::rngs::OsRng;

fn hash_password(password: &str) -> Result<String, argon2::Error> {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default();
    let password_hash = argon2.hash_password(password.as_bytes(), &salt)?;
    Ok(password_hash.to_string())
}

fn verify_password(password: &str, password_hash: &str) -> Result<bool, argon2::Error> {
    let parsed_hash = PasswordHash::new(password_hash)?;
    let argon2 = Argon2::default();
    Ok(argon2.verify_password(password.as_bytes(), &parsed_hash).is_ok())
}

// HKDF: 从主密钥派生多个子密钥
use hkdf::Hkdf;
use sha2::Sha256;

fn derive_keys(master_key: &[u8], salt: &[u8]) -> ([u8; 32], [u8; 32]) {
    let hkdf = Hkdf::<Sha256>::new(Some(salt), master_key);
    let mut okm1 = [0u8; 32];
    let mut okm2 = [0u8; 32];
    hkdf.expand(b"encryption", &mut okm1).unwrap();
    hkdf.expand(b"authentication", &mut okm2).unwrap();
    (okm1, okm2)
}
```

> **来源**: [RFC 9106 — Argon2](https://tools.ietf.org/html/rfc9106) · [OWASP Password Storage](https://cheatsheetseries.owasp.org/cheatsheets/Password_Storage_Cheat_Sheet.html) · [RFC 5869 — HKDF](https://tools.ietf.org/html/rfc5869) · [argon2 crate](https://docs.rs/argon2/latest/argon2/) · [hkdf crate](https://docs.rs/hkdf/latest/hkdf/)

---

## 六、Rust 密码学生态

### 6.1 ring：安全原语聚合
>
> **[ring](https://briansmith.org/rustdoc/ring/)** 是 Brian Smith 开发的 Rust 密码学库，聚合了 BoringSSL（Google 的 OpenSSL 分支）的高性能、审计过的密码学原语。设计哲学：**最小 API 表面积、高安全性默认值、无 unsafe 暴露**。

```rust,ignore
use ring::aead::{Aes256Gcm, Nonce, UnboundKey, AES_256_GCM};
use ring::rand::SecureRandom;
use ring::signature::{Ed25519KeyPair, UnparsedPublicKey, ED25519};

// ring 的 API 设计：严格分离密钥和算法
fn ring_encrypt(key: &[u8; 32], plaintext: &[u8]) -> Result<Vec<u8>, ring::error::Unspecified> {
    let unbound_key = UnboundKey::new(&AES_256_GCM, key)?;
    let nonce_bytes = [0u8; 12];  // 实际应使用 CSPRNG
    let nonce = Nonce::assume_unique_for_key(nonce_bytes);
    // ... ring 的 API 较为底层，通常直接使用 aes-gcm crate
    todo!()
}

// ring 的 Ed25519 签名
fn ring_sign(key_pair: &Ed25519KeyPair, message: &[u8]) -> ring::signature::Signature {
    key_pair.sign(message)
}
```

> **设计特点**:
>
> - `ring` 的 API 刻意保持**小表面积**，只暴露最常用的操作（AES-GCM、ChaCha20-Poly1305、Ed25519、X25519、SHA-256/384/512）
> - 所有密钥材料通过**类型系统（Type System）**管理（`UnboundKey`、`SealingKey`、`OpeningKey`）
> - 不支持 AES-CBC、RSA-PKCS#1 v1.5 等被认为不安全的模式
>
> **来源**: [ring Documentation](https://briansmith.org/rustdoc/ring/) · [BoringSSL](https://boringssl.googlesource.com/boringssl/)

### 6.2 rustls：纯 Rust TLS
>
> **[rustls](https://docs.rs/rustls/latest/rustls/)** 是 Joseph Birr-Pixton 开发的纯 Rust TLS 库，目标是**替代 OpenSSL**。与 OpenSSL 相比：内存安全（Memory Safety）（无缓冲区溢出）、无 unsafe（核心代码）、API 设计更现代（基于 Rust 类型系统（Type System））。

```rust,ignore
use rustls::{ClientConfig, ServerConfig, RootCertStore};
use std::sync::Arc;

// rustls 客户端配置
fn create_tls_client() -> Arc<ClientConfig> {
    let mut root_store = RootCertStore::empty();
    root_store.extend(
        webpki_roots::TLS_SERVER_ROOTS.iter().cloned()
    );

    let config = ClientConfig::builder()
        .with_root_certificates(root_store)
        .with_no_client_auth();

    Arc::new(config)
}

// rustls 服务端配置
fn create_tls_server(cert_chain: Vec<CertificateDer<'static>>, key: PrivateKeyDer<'static>) -> Arc<ServerConfig> {
    let config = ServerConfig::builder()
        .with_no_client_auth()
        .with_single_cert(cert_chain, key)
        .expect("invalid certificate chain");

    Arc::new(config)
}
```

> **rustls 的安全设计**:
>
> - 默认禁用 TLS 1.0/1.1（只支持 TLS 1.2+）
> - 默认禁用 RSA 密钥交换（只支持 ECDHE）
> - 默认禁用压缩（CRIME/BREACH 攻击防护）
> - 证书验证使用 **webpki**（Rust 实现的 X.509 验证）
>
> **来源**: [rustls Documentation](https://docs.rs/rustls/latest/rustls/) · [rustls Book](https://docs.rs/rustls/latest/rustls/manual/index.html) · [Let's Encrypt — Rustls](https://letsencrypt.org/docs/client-options/)

### 6.3 dalek-cryptography：零知识友好
>
> **[dalek-cryptography](https://github.com/dalek-cryptography)** 是 isis agora lovecruft 主导开发的 Rust 密码学库集合，专注于**曲线密码学**和**零知识证明**。核心 crate：`curve25519-dalek`（曲线运算）、`ed25519-dalek`（签名）、`x25519-dalek`（密钥交换）、`bulletproofs`（范围证明）。

```text
 Dalek 生态定位:
  ├── curve25519-dalek: Curve25519/Ristretto 群运算
  ├── ed25519-dalek:    EdDSA 签名（确定性、常量时间）
  ├── x25519-dalek:     ECDH 密钥交换
  ├── bulletproofs:     零知识范围证明
  └── merlin:            Fiat-Shamir 变换的 STROBE 框架

设计特点:
  - 纯 Rust 实现（无外部 C 依赖）
  - 常量时间操作（通过 `subtle` crate 的条件选择）
  - 零知识证明友好（Ristretto 群编码消除 cofactor 问题）
```

> **来源**: [dalek-cryptography GitHub](https://github.com/dalek-cryptography) · [curve25519-dalek](https://docs.rs/curve25519-dalek/latest/curve25519_dalek/) · [Ristretto Group](https://ristretto.group/)

---

## 七、常量时间操作与侧信道防护

```text
定时攻击（Timing Attack）原理:
  若比较操作提前返回（如 `memcmp` 发现第一个不同字节即返回），
  攻击者可通过测量比较时间来推断密钥内容。

  正常比较: "password" vs "secret"
    p ≠ s → 立即返回（1 个字符时间）

  攻击者逐步猜测:
    guess "a..." → 1 字符时间（错误）
    guess "p..." → 2 字符时间（接近！）
    ...

常量时间比较: 无论输入如何，执行时间固定
```

```rust,ignore
use subtle::ConstantTimeEq;

// ❌ 错误：非常量时间比较（Rust 默认 ==）
fn insecure_compare(a: &[u8], b: &[u8]) -> bool {
    a == b  // 编译器可能优化为提前返回！
}

// ✅ 正确：常量时间比较
fn secure_compare(a: &[u8], b: &[u8]) -> bool {
    a.ct_eq(b).into()  // subtle::ConstantTimeEq
}

// 更底层的实现（教育用途）
fn ct_compare_impl(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut result: u8 = 0;
    for (x, y) in a.iter().zip(b.iter()) {
        result |= x ^ y;  // XOR: 相同字节 → 0，不同 → 非零
    }
    result == 0  // 编译器注意：这可能被优化！
    // 实际应使用 subtle::Choice 避免分支
}
```

> **Rust 的侧信道防护工具链**:
>
> - `subtle` crate: 常量时间条件选择（`Choice`、`CtOption`）
> - `constant_time_eq` crate: 专门的常量时间比较
> - Miri: 检测未定义行为（但不能检测所有侧信道）
> - dalek-cryptography: 所有运算默认常量时间
>
> **局限**: Rust 编译器可能将常量时间代码优化为分支代码。当前解决方案：
>
> 1. 使用 `core::hint::black_box` 阻止优化
> 2. 使用内联汇编（Inline Assembly）实现关键路径
> 3. 依赖 LLVM 的 `volatile` 语义
>
> **来源**: [subtle crate](https://docs.rs/subtle/latest/subtle/) · [Constant-Time Programming](https://bearssl.org/constanttime.html) · [Timing Attacks on Implementations](https://crypto.stanford.edu/~dabo/papers/ssl-timing.pdf)

---

## 八、后量子密码学预览

> **[NIST Post-Quantum Cryptography Standardization](https://csrc.nist.gov/projects/post-quantum-cryptography)** NIST 于 2024 年发布了首批后量子密码学标准：
>
> - **FIPS 203** — ML-KEM（Kyber）：密钥封装机制
> - **FIPS 204** — ML-DSA（Dilithium）：数字签名
> - **FIPS 205** — SLH-DSA（SPHINCS+）：基于哈希的签名

```text
后量子密码学在 Rust 中的状态（2025）:
  ┌─────────────────┬─────────────────┬─────────────────────────────┐
  │     标准        │    算法         │   Rust 生态支持             │
  ├─────────────────┼─────────────────┼─────────────────────────────┤
  │ FIPS 203        │ ML-KEM (Kyber)  │ pqc_kyber, ml-kem crate     │
  │ FIPS 204        │ ML-DSA (Dilith) │ pqc_dilithium               │
  │ FIPS 205        │ SLH-DSA         │ pqc_sphincsplus             │
  └─────────────────┴─────────────────┴─────────────────────────────┘

  迁移挑战:
    1. 密钥/签名大小：ML-DSA 签名 ~3KB（Ed25519 仅 64B）
    2. 性能：后量子算法比传统 ECC 慢 10-100x
    3. 混合方案：PQ + 传统并用（如 X25519 + ML-KEM）
    4. Rust 生态尚不成熟，主要依赖 C 封装（pqclean）
```

> **来源**: [NIST PQC](https://csrc.nist.gov/projects/post-quantum-cryptography) · [FIPS 203](https://csrc.nist.gov/pubs/fips/203/final) · [FIPS 204](https://csrc.nist.gov/pubs/fips/204/final) · [FIPS 205](https://csrc.nist.gov/pubs/fips/205/final)

---

## 九、反命题与边界

### 9.1 反命题树
>

```text
反命题 1: "Rust 的内存安全保证密码学实现天然安全"
├── 前提: Ownership + Borrow Checker 消除所有内存错误
├── 反驳:
│   ├── 侧信道攻击（定时、功耗、缓存）不受内存安全保护
│   ├── 密钥材料可能在 Drop 前被交换到磁盘（swap）
│   ├── 编译器优化可能破坏常量时间保证
│   └── 逻辑错误（如 Nonce 复用）与内存安全无关
└── 根结论: ❌ Rust 的内存安全是必要条件，不是充分条件。密码学安全需要专门的审计和测试。

反命题 2: "自己实现密码学算法比使用现有库更安全"
├── 前提: 隐藏算法细节增加安全性（违反 Kerckhoffs 原则）
├── 反驳:
│   ├── 密码学算法实现极易出错（Nonce 复用、边界条件、常量时间）
│   ├── 现有库（ring, rustls, dalek）经过广泛审计和密码学分析
│   ├── 自行实现缺少形式化验证和侧信道测试
│   └── "不要自己实现密码学"是行业共识（Schneier's Law）
└── 根结论: ❌ 密码学应使用经过审计的标准库，除非你是密码学家且有资源进行完整审计。

反命题 3: "AES-256 总是比 AES-128 更安全"
├── 前提: 密钥越长安全性越高
├── 反驳:
│   ├── AES-128 已足够抵抗所有已知攻击（包括量子计算的 Grover 算法：有效安全性从 128 降到 64，仍然安全）
│   ├── AES-256 在某些侧信道场景下反而更脆弱（相关密钥攻击的理论风险）
│   └── 实际系统的薄弱环节通常是密钥管理，而非算法强度
└── 根结论: ❌ AES-128 在大多数场景下已足够。选择 AES-256 应基于合规要求，而非纯粹的安全需求。
```

### 9.2 边界极限
>

| **边界** | **现状** | **理论极限** | **工程影响** |
|:---|:---|:---|:---|
| **常量时间保证** | `subtle` crate + 内联汇编（Inline Assembly） | 编译器优化可能破坏 | 需要密码学审计验证 |
| **密钥内存清零** | `zeroize` crate | 操作系统可能交换到磁盘 | 使用 `mlock` + `zeroize` |
| **量子威胁** | 混合方案（ECC + PQC）| Grover/Shor 算法 | 2030+ 预计需要完全迁移 |
| **侧信道防护** | 时间侧信道基本防护 | 功耗/电磁侧信道需硬件 | 高安全场景需要 HSM |
| **随机数质量** | OS CSPRNG (`/dev/urandom`) | 熵池耗尽风险 | 启动早期需要种子文件 |

> **来源**: [OWASP — Cryptographic Storage](https://cheatsheetseries.owasp.org/cheatsheets/Cryptographic_Storage_Cheat_Sheet.html) · [NIST SP 800-57](https://csrc.nist.gov/publications/detail/sp/800-57-part-1/rev-5/final)

---

## 十、边界测试

### 10.1 边界测试：非常量时间比较导致定时攻击（运行时信息泄露）

```rust,ignore
// ❌ 错误：非常量时间密码验证
fn insecure_password_verify(stored: &[u8], provided: &[u8]) -> bool {
    stored == provided  // Rust 的 slice == 可能提前返回！
}

// 攻击场景:
// 攻击者测量验证时间，逐步猜测密码
// guess "a..." → 1μs (第一个字节错误，立即返回)
// guess "p..." → 2μs (第一个字节正确，继续比较)
// ... 逐步缩小范围，最终恢复完整密码
```

> **修正**: 使用 `subtle::ConstantTimeEq` 或 `constant_time_eq`：
>
> ```rust
> use subtle::ConstantTimeEq;
> fn secure_password_verify(stored: &[u8], provided: &[u8]) -> bool {
>     stored.ct_eq(provided).into()
> }
> ```
>
> **来源**: [subtle crate](https://docs.rs/subtle/latest/subtle/) · [Timing Attacks](https://crypto.stanford.edu/~dabo/papers/ssl-timing.pdf)

### 10.2 边界测试：Nonce 复用破坏 AES-GCM 机密性（逻辑错误）

```rust,ignore
// ❌ 错误：固定 Nonce（ catastrophic failure！）
fn broken_encrypt(key: &[u8; 32], plaintext: &[u8]) -> Vec<u8> {
    let cipher = Aes256Gcm::new_from_slice(key).unwrap();
    let nonce = Nonce::from_slice(b"fixednonce!!");  // ❌ 固定 Nonce！
    let ciphertext = cipher.encrypt(nonce, plaintext).unwrap();
    ciphertext.to_vec()
}

// 攻击: 若同一密钥下加密两条消息 m1, m2
//   c1 = m1 ⊕ keystream
//   c2 = m2 ⊕ keystream
//   c1 ⊕ c2 = m1 ⊕ m2  → 已知明文攻击恢复密钥流！
// 更糟: 恢复密钥流后可伪造任意消息的认证标签
```

> **修正**: Nonce 必须**唯一且不可预测**。推荐方案：
>
> 1. **计数器**: 每次加密递增（需持久化计数器）
> 2. **CSPRNG**: 每次加密随机生成 96 位 Nonce（2^48 次加密后 birthday bound 风险）
> 3. **96 位随机 + 32 位计数器**: 组合方案（AES-GCM-SIV）
>
> **来源**: [NIST SP 800-38D](https://csrc.nist.gov/publications/detail/sp/800-38d/final) · [AES-GCM Security](https://csrc.nist.gov/publications/detail/sp/800-38d/final)

### 10.3 边界测试：低迭代次数 KDF 导致暴力破解（安全漏洞）

```rust,ignore
// ❌ 错误：Argon2 参数过低
fn weak_hash_password(password: &str) -> String {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::new(
        argon2::Algorithm::Argon2id,
        argon2::Version::V0x13,
        argon2::Params::new(4096, 1, 1, None).unwrap(),  // ❌ 仅 4KB 内存，1 次迭代！
    );
    let password_hash = argon2.hash_password(password.as_bytes(), &salt).unwrap();
    password_hash.to_string()
}

// 攻击: 使用 GPU/ASIC 集群，每秒可尝试数十亿次猜测
// 8 位密码（字母+数字）: ~2^47 种组合
// 在 modern GPU 上: 可在数小时/数天内破解
```

> **修正**: 遵循 **OWASP 2023 推荐参数**：
>
> ```rust
> let argon2 = Argon2::new(
>     argon2::Algorithm::Argon2id,
>     argon2::Version::V0x13,
>     argon2::Params::new(19456, 2, 1, None).unwrap(),  // ✅ 19MB, 2 次迭代
> );
> ```
>
> 或根据硬件能力和安全需求调整：内存越大、迭代越多，暴力破解成本越高。
>
> **来源**: [OWASP Password Storage](https://cheatsheetseries.owasp.org/cheatsheets/Password_Storage_Cheat_Sheet.html) · [RFC 9106](https://tools.ietf.org/html/rfc9106)

---

## 相关概念文件

- [安全实践](19_security_practices.md) — 防御性编程、安全模式
- [网络协议](38_network_protocols.md) — QUIC/HTTP-3、TLS 底层
- [区块链与智能合约安全](06_blockchain.md) — 链上密码学应用
- [Unsafe Rust](../03_advanced/03_unsafe.md) — 密码学实现中的 unsafe 边界
- [类型系统（Type System）](../01_foundation/02_type_system/04_type_system.md) — 类型安全与密码学抽象
- [内存管理](../02_intermediate/02_memory_management/03_memory_management.md) — 密钥材料的内存管理
- [并发编程](../03_advanced/01_concurrency.md) — 密码学操作的线程安全
- [形式化验证](../04_formal/05_verification_toolchain.md) — 密码学实现的形式化证明

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) · [Rust Standard Library](https://doc.rust-lang.org/std/)
> **对应 Rust 版本**: 1.96.1+ (Edition 2024)
> **过渡**: Security & Cryptography（安全与密码学） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Security & Cryptography（安全与密码学） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Security & Cryptography（安全与密码学） 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。

### 补充定理链

- **定理**: Security & Cryptography（安全与密码学） 定义 ⟹ 类型安全保证
- **定理**: Security & Cryptography（安全与密码学） 定义 ⟹ 类型安全保证
- **定理**: Security & Cryptography（安全与密码学） 定义 ⟹ 类型安全保证

## 嵌入式测验（Embedded Quiz）

### 测验 1：Rust 的 `ring` crate 在密码学中提供什么功能？（理解层）

**题目**: Rust 的 `ring` crate 在密码学中提供什么功能？

<details>
<summary>✅ 答案与解析</summary>

`ring` 是基于 BoringSSL 的安全密码学库，提供：AEAD（AES-GCM/ChaCha20-Poly1305）、ECDSA/Ed25519 签名、HKDF、PBKDF2、随机数生成等。优先选择 `ring` 而非自己实现。
</details>

---

### 测验 2：为什么密码学代码中绝对不应该使用 `unsafe` 或原始指针？（理解层）

**题目**: 为什么密码学代码中绝对不应该使用 `unsafe` 或原始指针（Raw Pointer）？

<details>
<summary>✅ 答案与解析</summary>

密码学实现 slightest 的内存错误（如时序攻击、密钥泄露到 swap）都可能导致安全崩溃。应使用经过审计的库（`ring`、`rustls`），它们已通过形式化验证和侧信道分析。
</details>

---

### 测验 3：Rust 的常量时间比较（Constant-Time Comparison）为什么对密码学重要？（理解层）

**题目**: Rust 的常量时间比较（Constant-Time Comparison）为什么对密码学重要？

<details>
<summary>✅ 答案与解析</summary>

标准 `==` 可能在第一个不同字节处短路返回，泄露密码长度信息。常量时间比较（如 `subtle::ConstantTimeEq`）遍历所有字节，时间只与长度相关，防止时序攻击。
</details>

---

### 测验 4：`rustls` 与 OpenSSL 相比在安全性上有什么优势？（理解层）

**题目**: `rustls` 与 OpenSSL 相比在安全性上有什么优势？

<details>
<summary>✅ 答案与解析</summary>

`rustls` 是纯 Rust 实现，无缓冲区溢出和内存泄漏风险。代码量更小（审计更容易），默认禁用不安全协议（SSLv3、TLS 1.0/1.1），证书验证严格。
</details>

---

### 测验 5：在 Rust 中存储密码时，为什么必须使用 Argon2 / bcrypt / scrypt 而非 SHA-256？（理解层）

**题目**: 在 Rust 中存储密码时，为什么必须使用 Argon2 / bcrypt / scrypt 而非 SHA-256？

<details>
<summary>✅ 答案与解析</summary>

SHA-256 设计为快速计算，易被 GPU/ASIC 暴力破解。Argon2 等是"密钥派生函数"（KDF），故意慢且内存硬，大幅增加暴力破解成本。
</details>

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Security & Cryptography（安全与密码学）** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Security & Cryptography（安全与密码学） 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Security & Cryptography（安全与密码学） 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Security & Cryptography（安全与密码学） 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Security & Cryptography（安全与密码学） 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 Security & Cryptography（安全与密码学） 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: Security & Cryptography（安全与密码学） 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Security & Cryptography（安全与密码学） 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。
