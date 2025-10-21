# 压缩与编码

> **核心库**: flate2, bzip2, zstd, lz4, base64  
> **适用场景**: 数据压缩、文件压缩、网络传输、编码转换

---

## 📋 目录

- [压缩与编码](#压缩与编码)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [压缩算法对比](#压缩算法对比)
  - [🗜️ flate2 - GZIP/DEFLATE](#️-flate2---gzipdeflate)
    - [基础用法](#基础用法)
  - [📦 其他压缩算法](#-其他压缩算法)
    - [bzip2 - 高压缩率](#bzip2---高压缩率)
    - [zstd - 现代高效](#zstd---现代高效)
    - [lz4 - 极速压缩](#lz4---极速压缩)
  - [🔐 base64 - 编码转换](#-base64---编码转换)
  - [💡 最佳实践](#-最佳实践)
    - [1. 选择合适的压缩算法](#1-选择合适的压缩算法)
    - [2. 流式处理](#2-流式处理)
  - [🔧 常见场景](#-常见场景)
    - [场景 1: HTTP 响应压缩](#场景-1-http-响应压缩)
    - [场景 2: 日志文件归档](#场景-2-日志文件归档)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

### 压缩算法对比

| 算法 | 压缩率 | 速度 | 内存 | 适用场景 |
|------|--------|------|------|----------|
| **GZIP** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 通用、HTTP |
| **BZIP2** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | 归档 |
| **ZSTD** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 现代通用 |
| **LZ4** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 实时系统 |

---

## 🗜️ flate2 - GZIP/DEFLATE

### 基础用法

```rust
use flate2::Compression;
use flate2::write::{GzEncoder, GzDecoder};
use std::io::prelude::*;

fn compress_data(data: &[u8]) -> std::io::Result<Vec<u8>> {
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    encoder.write_all(data)?;
    encoder.finish()
}

fn decompress_data(data: &[u8]) -> std::io::Result<Vec<u8>> {
    let mut decoder = GzDecoder::new(Vec::new());
    decoder.write_all(data)?;
    decoder.finish()
}
```

---

## 📦 其他压缩算法

### bzip2 - 高压缩率

```rust
use bzip2::write::{BzEncoder, BzDecoder};
use bzip2::Compression;
use std::io::prelude::*;

fn compress_bz2(data: &[u8]) -> std::io::Result<Vec<u8>> {
    let mut encoder = BzEncoder::new(Vec::new(), Compression::best());
    encoder.write_all(data)?;
    encoder.finish()
}
```

### zstd - 现代高效

```rust
use zstd::stream::{encode_all, decode_all};

fn compress_zstd(data: &[u8]) -> std::io::Result<Vec<u8>> {
    encode_all(data, 3) // 压缩级别 3
}

fn decompress_zstd(data: &[u8]) -> std::io::Result<Vec<u8>> {
    decode_all(data)
}
```

### lz4 - 极速压缩

```rust
use lz4::{EncoderBuilder, Decoder};

fn compress_lz4(data: &[u8]) -> std::io::Result<Vec<u8>> {
    let mut encoder = EncoderBuilder::new()
        .level(4)
        .build(Vec::new())?;
    encoder.write_all(data)?;
    let (output, result) = encoder.finish();
    result?;
    Ok(output)
}
```

---

## 🔐 base64 - 编码转换

```rust
use base64::{Engine as _, engine::general_purpose};

fn encode_base64(data: &[u8]) -> String {
    general_purpose::STANDARD.encode(data)
}

fn decode_base64(encoded: &str) -> Result<Vec<u8>, base64::DecodeError> {
    general_purpose::STANDARD.decode(encoded)
}

fn main() {
    let data = b"Hello, World!";
    let encoded = encode_base64(data);
    println!("Encoded: {}", encoded);
    
    let decoded = decode_base64(&encoded).unwrap();
    println!("Decoded: {}", String::from_utf8_lossy(&decoded));
}
```

---

## 💡 最佳实践

### 1. 选择合适的压缩算法

```rust
fn choose_compression(scenario: &str) -> &'static str {
    match scenario {
        "http" => "gzip",         // 广泛支持
        "archive" => "zstd",      // 平衡性能和压缩率
        "realtime" => "lz4",      // 最快
        "maximum" => "bzip2",     // 最高压缩率
        _ => "gzip"
    }
}
```

### 2. 流式处理

```rust
use flate2::read::GzEncoder;
use std::fs::File;
use std::io::copy;

fn compress_file(input_path: &str, output_path: &str) -> std::io::Result<()> {
    let input = File::open(input_path)?;
    let output = File::create(output_path)?;
    let mut encoder = GzEncoder::new(input, Compression::default());
    let mut writer = std::io::BufWriter::new(output);
    copy(&mut encoder, &mut writer)?;
    Ok(())
}
```

---

## 🔧 常见场景

### 场景 1: HTTP 响应压缩

```rust
use flate2::write::GzEncoder;
use flate2::Compression;

fn compress_response(body: &str) -> Vec<u8> {
    let mut encoder = GzEncoder::new(Vec::new(), Compression::fast());
    encoder.write_all(body.as_bytes()).unwrap();
    encoder.finish().unwrap()
}
```

### 场景 2: 日志文件归档

```rust
use flate2::write::GzEncoder;
use std::fs::File;

fn archive_log(log_path: &str) -> std::io::Result<()> {
    let file = File::open(log_path)?;
    let output = File::create(format!("{}.gz", log_path))?;
    let mut encoder = GzEncoder::new(output, Compression::default());
    std::io::copy(&mut std::io::BufReader::new(file), &mut encoder)?;
    encoder.finish()?;
    Ok(())
}
```

---

## 📚 延伸阅读

- [flate2 官方文档](https://docs.rs/flate2/)
- [zstd 官方文档](https://docs.rs/zstd/)
- [压缩算法基准测试](https://github.com/lz4/lz4)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
