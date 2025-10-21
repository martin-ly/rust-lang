# Encoding - 编码与解码

## 📋 目录

- [Encoding - 编码与解码](#encoding---编码与解码)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [Base64 编码](#base64-编码)
    - [基础用法](#基础用法)
    - [不同的 Base64 变体](#不同的-base64-变体)
    - [流式编码](#流式编码)
    - [实战：图片转 Data URL](#实战图片转-data-url)
  - [Hex 编码](#hex-编码)
    - [基础用法1](#基础用法1)
    - [大小写与格式](#大小写与格式)
    - [实战：哈希值显示](#实战哈希值显示)
    - [Hex 转字节数组](#hex-转字节数组)
  - [URL 编码](#url-编码)
    - [percent-encoding](#percent-encoding)
    - [urlencoding](#urlencoding)
    - [实战：构建查询字符串](#实战构建查询字符串)
  - [字符编码](#字符编码)
    - [encoding\_rs](#encoding_rs)
    - [检测与转换](#检测与转换)
    - [实战：读取 GBK 文件](#实战读取-gbk-文件)
  - [二进制编码](#二进制编码)
    - [整数编码（字节序）](#整数编码字节序)
    - [可变长度整数（VarInt）](#可变长度整数varint)
  - [使用场景](#使用场景)
    - [1. JWT Token 编码](#1-jwt-token-编码)
    - [2. 二进制数据传输](#2-二进制数据传输)
    - [3. 颜色值转换](#3-颜色值转换)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 性能优化](#2-性能优化)
    - [3. 安全考虑](#3-安全考虑)
    - [4. 编码选择指南](#4-编码选择指南)
  - [性能对比](#性能对比)
  - [技术选型](#技术选型)
  - [参考资源](#参考资源)

---

## 概述

编码（Encoding）是将数据从一种形式转换为另一种形式的过程，在数据传输、存储和展示中至关重要。

### 核心依赖

```toml
[dependencies]
# Base64 编码
base64 = "0.21"

# Hex 编码
hex = "0.4"

# URL 编码
urlencoding = "2.1"
percent-encoding = "2.3"

# 字符编码
encoding_rs = "0.8"

# Data URL
data-url = "0.3"
```

---

## Base64 编码

### 基础用法

```rust
use base64::{Engine as _, engine::general_purpose};

fn base64_basic() {
    let data = b"Hello, World!";
    
    // 编码
    let encoded = general_purpose::STANDARD.encode(data);
    println!("编码: {}", encoded);
    // 输出: SGVsbG8sIFdvcmxkIQ==
    
    // 解码
    let decoded = general_purpose::STANDARD.decode(&encoded).unwrap();
    println!("解码: {}", String::from_utf8(decoded).unwrap());
    // 输出: Hello, World!
}
```

### 不同的 Base64 变体

```rust
use base64::{Engine as _, engine::{self, general_purpose}};

fn base64_variants() {
    let data = b"Hello, World!";
    
    // 标准 Base64
    let standard = general_purpose::STANDARD.encode(data);
    println!("标准: {}", standard);
    
    // URL 安全（使用 - 和 _ 替代 + 和 /）
    let url_safe = general_purpose::URL_SAFE.encode(data);
    println!("URL安全: {}", url_safe);
    
    // 无填充
    let no_pad = general_purpose::STANDARD_NO_PAD.encode(data);
    println!("无填充: {}", no_pad);
}
```

### 流式编码

```rust
use base64::{Engine as _, engine::general_purpose};
use std::io::Write;

fn base64_streaming() {
    let data = b"Large data that needs streaming...";
    
    // 使用缓冲区
    let mut encoded = String::new();
    let engine = general_purpose::STANDARD;
    
    // 分块编码
    for chunk in data.chunks(1024) {
        encoded.push_str(&engine.encode(chunk));
    }
    
    println!("流式编码: {}", encoded);
}
```

### 实战：图片转 Data URL

```rust
use base64::{Engine as _, engine::general_purpose};
use std::fs;

fn image_to_data_url(path: &str) -> Result<String, std::io::Error> {
    // 读取图片
    let image_data = fs::read(path)?;
    
    // Base64 编码
    let encoded = general_purpose::STANDARD.encode(&image_data);
    
    // 构造 Data URL
    let mime_type = match path.rsplit('.').next() {
        Some("png") => "image/png",
        Some("jpg") | Some("jpeg") => "image/jpeg",
        Some("gif") => "image/gif",
        _ => "application/octet-stream",
    };
    
    Ok(format!("data:{};base64,{}", mime_type, encoded))
}

fn main() -> Result<(), std::io::Error> {
    let data_url = image_to_data_url("example.png")?;
    println!("Data URL: {}", &data_url[..100]); // 显示前100字符
    Ok(())
}
```

---

## Hex 编码

### 基础用法1

```rust
use hex;

fn hex_basic() {
    let data = b"Hello";
    
    // 编码为十六进制字符串
    let encoded = hex::encode(data);
    println!("Hex编码: {}", encoded);
    // 输出: 48656c6c6f
    
    // 解码
    let decoded = hex::decode(&encoded).unwrap();
    println!("解码: {}", String::from_utf8(decoded).unwrap());
    // 输出: Hello
}
```

### 大小写与格式

```rust
use hex;

fn hex_formats() {
    let data = b"Rust";
    
    // 小写（默认）
    let lowercase = hex::encode(data);
    println!("小写: {}", lowercase);
    // 输出: 52757374
    
    // 大写
    let uppercase = hex::encode_upper(data);
    println!("大写: {}", uppercase);
    // 输出: 52757374 (注：新版本需要手动转大写)
}
```

### 实战：哈希值显示

```rust
use hex;
use sha2::{Sha256, Digest};

fn hash_display(data: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(data);
    let result = hasher.finalize();
    
    // 将哈希值编码为十六进制
    hex::encode(result)
}

fn main() {
    let data = b"Hello, World!";
    let hash = hash_display(data);
    println!("SHA-256: {}", hash);
}
```

### Hex 转字节数组

```rust
use hex;

fn hex_to_bytes() {
    let hex_string = "48656c6c6f";
    
    // 方法1: Vec<u8>
    let bytes = hex::decode(hex_string).unwrap();
    println!("{:?}", bytes);
    
    // 方法2: 固定长度数组
    let mut array = [0u8; 5];
    hex::decode_to_slice(hex_string, &mut array).unwrap();
    println!("{:?}", array);
}
```

---

## URL 编码

### percent-encoding

```rust
use percent_encoding::{utf8_percent_encode, percent_decode_str, NON_ALPHANUMERIC};

fn url_encoding_percent() {
    let input = "Hello, 世界!";
    
    // 编码
    let encoded = utf8_percent_encode(input, NON_ALPHANUMERIC).to_string();
    println!("编码: {}", encoded);
    // 输出: Hello%2C%20%E4%B8%96%E7%95%8C%21
    
    // 解码
    let decoded = percent_decode_str(&encoded)
        .decode_utf8()
        .unwrap();
    println!("解码: {}", decoded);
    // 输出: Hello, 世界!
}
```

### urlencoding

```rust
use urlencoding::{encode, decode};

fn url_encoding_simple() {
    let input = "Hello, World! 你好";
    
    // 编码
    let encoded = encode(input);
    println!("编码: {}", encoded);
    // 输出: Hello%2C%20World%21%20%E4%BD%A0%E5%A5%BD
    
    // 解码
    let decoded = decode(&encoded).unwrap();
    println!("解码: {}", decoded);
    // 输出: Hello, World! 你好
}
```

### 实战：构建查询字符串

```rust
use percent_encoding::{utf8_percent_encode, NON_ALPHANUMERIC};
use std::collections::HashMap;

fn build_query_string(params: &HashMap<&str, &str>) -> String {
    params
        .iter()
        .map(|(k, v)| {
            format!(
                "{}={}",
                utf8_percent_encode(k, NON_ALPHANUMERIC),
                utf8_percent_encode(v, NON_ALPHANUMERIC)
            )
        })
        .collect::<Vec<_>>()
        .join("&")
}

fn main() {
    let mut params = HashMap::new();
    params.insert("name", "张三");
    params.insert("city", "北京");
    params.insert("email", "user@example.com");
    
    let query = build_query_string(&params);
    println!("查询字符串: {}", query);
    // 输出: name=%E5%BC%A0%E4%B8%89&city=%E5%8C%97%E4%BA%AC&email=user%40example.com
}
```

---

## 字符编码

### encoding_rs

```rust
use encoding_rs::{Encoding, UTF_8, GBK, SHIFT_JIS};

fn character_encoding() {
    let text = "你好，世界！";
    
    // UTF-8 编码（默认）
    let utf8_bytes = text.as_bytes();
    println!("UTF-8: {:?}", utf8_bytes);
    
    // 编码为 GBK
    let (encoded, _, _) = GBK.encode(text);
    println!("GBK: {:?}", encoded);
    
    // 从 GBK 解码
    let (decoded, _, _) = GBK.decode(&encoded);
    println!("解码: {}", decoded);
}
```

### 检测与转换

```rust
use encoding_rs::Encoding;

fn detect_and_convert(bytes: &[u8]) -> Result<String, Box<dyn std::error::Error>> {
    // 常见编码列表
    let encodings = [
        encoding_rs::UTF_8,
        encoding_rs::GBK,
        encoding_rs::GB18030,
        encoding_rs::SHIFT_JIS,
        encoding_rs::EUC_KR,
    ];
    
    // 尝试每种编码
    for encoding in &encodings {
        let (decoded, used_encoding, had_errors) = encoding.decode(bytes);
        if !had_errors {
            println!("检测到编码: {}", used_encoding.name());
            return Ok(decoded.into_owned());
        }
    }
    
    Err("无法检测编码".into())
}
```

### 实战：读取 GBK 文件

```rust
use encoding_rs::GBK;
use std::fs;

fn read_gbk_file(path: &str) -> Result<String, std::io::Error> {
    // 读取字节
    let bytes = fs::read(path)?;
    
    // GBK 解码
    let (decoded, _, had_errors) = GBK.decode(&bytes);
    
    if had_errors {
        eprintln!("警告：解码时遇到错误");
    }
    
    Ok(decoded.into_owned())
}

fn main() -> Result<(), std::io::Error> {
    let content = read_gbk_file("gbk_file.txt")?;
    println!("{}", content);
    Ok(())
}
```

---

## 二进制编码

### 整数编码（字节序）

```rust
fn endianness_example() {
    let number: u32 = 0x12345678;
    
    // 大端（Big-Endian）
    let be_bytes = number.to_be_bytes();
    println!("大端: {:?}", be_bytes);
    // [0x12, 0x34, 0x56, 0x78]
    
    // 小端（Little-Endian）
    let le_bytes = number.to_le_bytes();
    println!("小端: {:?}", le_bytes);
    // [0x78, 0x56, 0x34, 0x12]
    
    // 从字节恢复
    let be_number = u32::from_be_bytes(be_bytes);
    let le_number = u32::from_le_bytes(le_bytes);
    
    assert_eq!(be_number, number);
    assert_eq!(le_number, number);
}
```

### 可变长度整数（VarInt）

```rust
fn encode_varint(mut value: u64) -> Vec<u8> {
    let mut bytes = Vec::new();
    
    loop {
        let mut byte = (value & 0x7F) as u8;
        value >>= 7;
        
        if value != 0 {
            byte |= 0x80; // 设置继续位
        }
        
        bytes.push(byte);
        
        if value == 0 {
            break;
        }
    }
    
    bytes
}

fn decode_varint(bytes: &[u8]) -> Result<(u64, usize), &'static str> {
    let mut value = 0u64;
    let mut shift = 0;
    
    for (i, &byte) in bytes.iter().enumerate() {
        value |= ((byte & 0x7F) as u64) << shift;
        shift += 7;
        
        if byte & 0x80 == 0 {
            return Ok((value, i + 1));
        }
    }
    
    Err("VarInt 不完整")
}

fn main() {
    let numbers = [0, 127, 128, 16384, 2097151];
    
    for &n in &numbers {
        let encoded = encode_varint(n);
        let (decoded, len) = decode_varint(&encoded).unwrap();
        println!("原始: {}, 编码长度: {}, 解码: {}", n, len, decoded);
    }
}
```

---

## 使用场景

### 1. JWT Token 编码

```rust
use base64::{Engine as _, engine::general_purpose};
use serde_json::json;

fn create_jwt_token(payload: serde_json::Value) -> String {
    // 头部
    let header = json!({
        "alg": "HS256",
        "typ": "JWT"
    });
    
    // 编码头部和载荷
    let header_b64 = general_purpose::URL_SAFE_NO_PAD.encode(header.to_string());
    let payload_b64 = general_purpose::URL_SAFE_NO_PAD.encode(payload.to_string());
    
    // 生成签名（这里简化）
    let signature = "fake_signature";
    
    format!("{}.{}.{}", header_b64, payload_b64, signature)
}

fn main() {
    let payload = json!({
        "sub": "1234567890",
        "name": "John Doe",
        "iat": 1516239022
    });
    
    let token = create_jwt_token(payload);
    println!("JWT: {}", token);
}
```

### 2. 二进制数据传输

```rust
use base64::{Engine as _, engine::general_purpose};
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct BinaryData {
    #[serde(with = "base64_serde")]
    content: Vec<u8>,
}

mod base64_serde {
    use base64::{Engine as _, engine::general_purpose};
    use serde::{Serializer, Deserializer, Deserialize};
    
    pub fn serialize<S>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&general_purpose::STANDARD.encode(bytes))
    }
    
    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<u8>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        general_purpose::STANDARD
            .decode(s)
            .map_err(serde::de::Error::custom)
    }
}

fn main() {
    let data = BinaryData {
        content: vec![1, 2, 3, 4, 5],
    };
    
    let json = serde_json::to_string(&data).unwrap();
    println!("JSON: {}", json);
    // {"content":"AQIDBAU="}
    
    let decoded: BinaryData = serde_json::from_str(&json).unwrap();
    println!("解码: {:?}", decoded.content);
}
```

### 3. 颜色值转换

```rust
fn color_hex_to_rgb(hex: &str) -> Result<(u8, u8, u8), hex::FromHexError> {
    let hex = hex.trim_start_matches('#');
    let bytes = hex::decode(hex)?;
    
    if bytes.len() != 3 {
        return Err(hex::FromHexError::InvalidStringLength);
    }
    
    Ok((bytes[0], bytes[1], bytes[2]))
}

fn rgb_to_color_hex(r: u8, g: u8, b: u8) -> String {
    format!("#{}", hex::encode([r, g, b]))
}

fn main() {
    let hex_color = "#FF5733";
    let (r, g, b) = color_hex_to_rgb(hex_color).unwrap();
    println!("RGB: ({}, {}, {})", r, g, b);
    
    let hex = rgb_to_color_hex(255, 87, 51);
    println!("Hex: {}", hex);
}
```

---

## 最佳实践

### 1. 错误处理

```rust
use base64::{Engine as _, engine::general_purpose};
use thiserror::Error;

#[derive(Error, Debug)]
enum EncodingError {
    #[error("Base64 解码失败: {0}")]
    Base64Decode(#[from] base64::DecodeError),
    
    #[error("Hex 解码失败: {0}")]
    HexDecode(#[from] hex::FromHexError),
    
    #[error("UTF-8 解码失败: {0}")]
    Utf8Decode(#[from] std::string::FromUtf8Error),
}

fn safe_decode(encoded: &str) -> Result<String, EncodingError> {
    let bytes = general_purpose::STANDARD.decode(encoded)?;
    let text = String::from_utf8(bytes)?;
    Ok(text)
}
```

### 2. 性能优化

```rust
use base64::{Engine as _, engine::general_purpose};

// ✅ 复用缓冲区
fn encode_many_reuse_buffer(items: &[&[u8]]) -> Vec<String> {
    let mut results = Vec::with_capacity(items.len());
    let engine = general_purpose::STANDARD;
    
    for item in items {
        results.push(engine.encode(item));
    }
    
    results
}

// ✅ 预分配容量
fn decode_with_capacity(encoded: &str) -> Result<Vec<u8>, base64::DecodeError> {
    let engine = general_purpose::STANDARD;
    
    // 计算解码后大小
    let estimated_len = (encoded.len() * 3) / 4;
    let mut buffer = Vec::with_capacity(estimated_len);
    
    engine.decode_vec(encoded, &mut buffer)?;
    Ok(buffer)
}
```

### 3. 安全考虑

```rust
use base64::{Engine as _, engine::general_purpose};

// ✅ 验证输入长度
fn safe_encode(data: &[u8], max_len: usize) -> Result<String, &'static str> {
    if data.len() > max_len {
        return Err("数据过大");
    }
    
    Ok(general_purpose::STANDARD.encode(data))
}

// ✅ 常量时间比较（防止时序攻击）
fn constant_time_compare(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    
    let mut result = 0u8;
    for (&x, &y) in a.iter().zip(b.iter()) {
        result |= x ^ y;
    }
    
    result == 0
}
```

### 4. 编码选择指南

```rust
// 场景：存储二进制数据到文本
// 推荐：Base64

// 场景：URL 参数
// 推荐：URL-safe Base64 或 Percent Encoding

// 场景：调试输出
// 推荐：Hex

// 场景：哈希值显示
// 推荐：Hex

// 场景：跨语言文本
// 推荐：UTF-8

// 场景：网络协议
// 推荐：VarInt（可变长度整数）
```

---

## 性能对比

| 编码方式 | 编码速度 | 解码速度 | 空间效率 | 适用场景 |
|---------|---------|---------|---------|---------|
| **Base64** | 快 | 快 | 133% | 通用二进制编码 |
| **Hex** | 快 | 快 | 200% | 调试、哈希值 |
| **URL 编码** | 中 | 中 | 100-300% | URL 参数 |
| **VarInt** | 快 | 快 | 14-100% | 整数压缩 |

---

## 技术选型

| 场景 | 推荐方案 | 原因 |
|------|----------|------|
| **API Token** | `base64` (URL-safe) | 安全、紧凑 |
| **查询字符串** | `urlencoding` / `percent-encoding` | 标准兼容 |
| **调试输出** | `hex` | 可读性好 |
| **文件读取** | `encoding_rs` | 编码检测 |
| **二进制传输** | `base64` | 效率高 |
| **哈希显示** | `hex` | 惯例 |

---

## 参考资源

- [base64 文档](https://docs.rs/base64/)
- [hex 文档](https://docs.rs/hex/)
- [percent-encoding 文档](https://docs.rs/percent-encoding/)
- [encoding_rs 文档](https://docs.rs/encoding_rs/)
- [RFC 4648 - Base64](https://datatracker.ietf.org/doc/html/rfc4648)
- [RFC 3986 - URL 编码](https://datatracker.ietf.org/doc/html/rfc3986)
