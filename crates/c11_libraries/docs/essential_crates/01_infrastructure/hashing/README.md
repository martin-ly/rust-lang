# 哈希与摘要

> **核心库**: sha2, blake3, md-5, xxhash-rust  
> **适用场景**: 密码学哈希、数据完整性、快速哈希、去重

---

## 📋 目录

- [哈希与摘要](#哈希与摘要)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [哈希算法分类](#哈希算法分类)
    - [算法对比](#算法对比)
  - [🔒 密码学哈希](#-密码学哈希)
    - [SHA-2 系列](#sha-2-系列)
    - [BLAKE3 - 现代高性能](#blake3---现代高性能)
  - [⚡ 非密码学哈希](#-非密码学哈希)
    - [xxHash - 极速哈希](#xxhash---极速哈希)
  - [💡 最佳实践](#-最佳实践)
    - [1. 选择合适的哈希算法](#1-选择合适的哈希算法)
    - [2. 密码存储](#2-密码存储)
    - [3. 文件完整性](#3-文件完整性)
  - [🔧 常见场景](#-常见场景)
    - [场景 1: 文件去重](#场景-1-文件去重)
    - [场景 2: 数据完整性校验](#场景-2-数据完整性校验)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

### 哈希算法分类

1. **密码学哈希**: SHA-2, SHA-3, BLAKE2/3
   - 用途: 密码、签名、证书
   - 特点: 抗碰撞、单向

2. **非密码学哈希**: xxHash, CityHash, MurmurHash
   - 用途: HashMap, 去重, 缓存
   - 特点: 极速、分布均匀

### 算法对比

| 算法 | 类型 | 速度 | 安全性 | 适用场景 |
|------|------|------|--------|----------|
| **SHA-256** | 密码学 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 证书、区块链 |
| **BLAKE3** | 密码学 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 现代通用 |
| **xxHash** | 非密码学 | ⭐⭐⭐⭐⭐ | ⭐⭐ | HashMap、去重 |
| **MD5** | 已破解 | ⭐⭐⭐⭐ | ❌ | 仅校验和 |

---

## 🔒 密码学哈希

### SHA-2 系列

```rust
use sha2::{Sha256, Sha512, Digest};

fn hash_sha256(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();
    format!("{:x}", result)
}

fn hash_sha512(data: &[u8]) -> String {
    let mut hasher = Sha512::new();
    hasher.update(data);
    let result = hasher.finalize();
    format!("{:x}", result)
}

fn main() {
    let data = b"Hello, World!";
    println!("SHA-256: {}", hash_sha256(data));
    println!("SHA-512: {}", hash_sha512(data));
}
```

### BLAKE3 - 现代高性能

```rust
use blake3::Hasher;

fn hash_blake3(data: &[u8]) -> String {
    let mut hasher = Hasher::new();
    hasher.update(data);
    let hash = hasher.finalize();
    hash.to_hex().to_string()
}

fn hash_file_blake3(path: &str) -> std::io::Result<String> {
    let mut hasher = Hasher::new();
    let mut file = std::fs::File::open(path)?;
    std::io::copy(&mut file, &mut hasher)?;
    Ok(hasher.finalize().to_hex().to_string())
}

fn main() {
    let data = b"Hello, World!";
    println!("BLAKE3: {}", hash_blake3(data));
}
```

---

## ⚡ 非密码学哈希

### xxHash - 极速哈希

```rust
use xxhash_rust::xxh3::xxh3_64;

fn hash_xxh3(data: &[u8]) -> u64 {
    xxh3_64(data)
}

fn main() {
    let data = b"Hello, World!";
    println!("xxHash3: {:x}", hash_xxh3(data));
}
```

---

## 💡 最佳实践

### 1. 选择合适的哈希算法

```rust
fn choose_hash_algorithm(purpose: &str) -> &'static str {
    match purpose {
        "password" => "argon2",        // 密码哈希使用专用算法
        "signature" => "sha256",       // 数字签名
        "file_integrity" => "blake3",  // 文件完整性
        "hashmap" => "xxhash",         // HashMap 键
        "checksum" => "crc32",         // 快速校验
        _ => "blake3"
    }
}
```

### 2. 密码存储

```rust
// ❌ 错误：直接使用通用哈希
use sha2::{Sha256, Digest};

fn bad_password_hash(password: &str) -> String {
    let mut hasher = Sha256::new();
    hasher.update(password.as_bytes());
    format!("{:x}", hasher.finalize())
}

// ✅ 正确：使用密码专用算法
use argon2::{Argon2, PasswordHasher, PasswordVerifier};
use argon2::password_hash::{rand_core::OsRng, SaltString};

fn hash_password(password: &str) -> Result<String, argon2::password_hash::Error> {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default();
    let hash = argon2.hash_password(password.as_bytes(), &salt)?;
    Ok(hash.to_string())
}
```

### 3. 文件完整性

```rust
use blake3::Hasher;
use std::fs::File;
use std::io::{self, Read};

fn compute_file_hash(path: &str) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut hasher = Hasher::new();
    
    let mut buffer = [0u8; 8192];
    loop {
        let bytes_read = file.read(&mut buffer)?;
        if bytes_read == 0 {
            break;
        }
        hasher.update(&buffer[..bytes_read]);
    }
    
    Ok(hasher.finalize().to_hex().to_string())
}

fn verify_file_integrity(path: &str, expected_hash: &str) -> io::Result<bool> {
    let actual_hash = compute_file_hash(path)?;
    Ok(actual_hash == expected_hash)
}
```

---

## 🔧 常见场景

### 场景 1: 文件去重

```rust
use blake3::Hasher;
use std::collections::HashMap;
use std::path::Path;

struct FileDeduplicator {
    hashes: HashMap<String, Vec<String>>,
}

impl FileDeduplicator {
    fn new() -> Self {
        Self {
            hashes: HashMap::new(),
        }
    }
    
    fn add_file(&mut self, path: &str) -> std::io::Result<()> {
        let hash = compute_file_hash(path)?;
        self.hashes
            .entry(hash)
            .or_insert_with(Vec::new)
            .push(path.to_string());
        Ok(())
    }
    
    fn find_duplicates(&self) -> Vec<&Vec<String>> {
        self.hashes
            .values()
            .filter(|files| files.len() > 1)
            .collect()
    }
}
```

### 场景 2: 数据完整性校验

```rust
use sha2::{Sha256, Digest};

#[derive(Debug)]
struct DataWithChecksum {
    data: Vec<u8>,
    checksum: String,
}

impl DataWithChecksum {
    fn new(data: Vec<u8>) -> Self {
        let checksum = Self::compute_checksum(&data);
        Self { data, checksum }
    }
    
    fn compute_checksum(data: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(data);
        format!("{:x}", hasher.finalize())
    }
    
    fn verify(&self) -> bool {
        Self::compute_checksum(&self.data) == self.checksum
    }
}
```

---

## 📚 延伸阅读

- [sha2 官方文档](https://docs.rs/sha2/)
- [blake3 官方文档](https://docs.rs/blake3/)
- [xxhash-rust 官方文档](https://docs.rs/xxhash-rust/)
- [密码学哈希最佳实践](https://cheatsheetseries.owasp.org/cheatsheets/Password_Storage_Cheat_Sheet.html)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
