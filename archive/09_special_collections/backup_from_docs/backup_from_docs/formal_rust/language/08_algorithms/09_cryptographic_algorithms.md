# 密码学算法

## 📊 目录

- [密码学算法](#密码学算法)
  - [📊 目录](#-目录)
  - [1. 哈希算法](#1-哈希算法)
    - [1.1 SHA-256](#11-sha-256)
    - [1.2 HMAC](#12-hmac)
  - [2. 对称加密](#2-对称加密)
    - [2.1 AES-GCM](#21-aes-gcm)
  - [3. 非对称加密](#3-非对称加密)
    - [3.1 RSA加密/解密](#31-rsa加密解密)
  - [4. 数字签名](#4-数字签名)
  - [5. 批判性分析与未来值值值展望](#5-批判性分析与未来值值值展望)

## 1. 哈希算法

- SHA-256、SHA-3、BLAKE2等
- HMAC消息认证码

### 1.1 SHA-256

```rust
use sha2::{Sha256, Digest};
pub fn sha256_hash(data: &[u8]) -> [u8; 32] { /* ... */ }
```

### 1.2 HMAC

```rust
use hmac::{Hmac, Mac, NewMac};
use sha2::Sha256;
type HmacSha256 = Hmac<Sha256>;
pub fn hmac_sha256(key: &[u8], message: &[u8]) -> Vec<u8> { /* ... */ }
```

## 2. 对称加密

- AES、ChaCha20等

### 2.1 AES-GCM

```rust
use aes_gcm::{Aes256Gcm, aead::{Aead, KeyInit, OsRng}, Nonce};
pub fn aes_gcm_encrypt(key: &[u8; 32], plaintext: &[u8]) -> Result<(Vec<u8>, [u8; 12]), Box<dyn std::error::Error>> { /* ... */ }
```

## 3. 非对称加密

- RSA、ECDSA、Ed25519等

### 3.1 RSA加密/解密

```rust
use rsa::{PublicKey, RsaPrivateKey, RsaPublicKey, PaddingScheme};
pub fn rsa_encrypt(public_key: &RsaPublicKey, data: &[u8]) -> Result<Vec<u8>, Box<dyn std::error::Error>> { /* ... */ }
```

## 4. 数字签名

- ECDSA、Ed25519、RSA-PSS等

## 5. 批判性分析与未来值值值展望

- 密码学算法需关注安全、性能与实现正确性
- 未来值值值可探索量子安全密码、零知识证明与Rust密码库生态

"

---
