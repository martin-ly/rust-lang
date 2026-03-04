# Flate2 压缩形式化分析

> **主题**: DEFLATE/gzip/zlib流压缩
>
> **形式化框架**: 流式编码 + 内存安全
>
> **参考**: flate2 Documentation

---

## 目录

- [Flate2 压缩形式化分析](#flate2-压缩形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 编码器类型](#2-编码器类型)
    - [定理 2.1 (编码器装饰)](#定理-21-编码器装饰)
    - [定理 2.2 (压缩级别)](#定理-22-压缩级别)
  - [3. 流式压缩](#3-流式压缩)
    - [定理 3.1 (缓冲区管理)](#定理-31-缓冲区管理)
  - [4. 解压缩安全](#4-解压缩安全)
    - [定理 4.1 (畸形数据)](#定理-41-畸形数据)
    - [定理 4.2 (炸弹防护)](#定理-42-炸弹防护)
  - [5. 反例](#5-反例)
    - [反例 5.1 (忘记finish)](#反例-51-忘记finish)
    - [反例 5.2 (压缩炸弹)](#反例-52-压缩炸弹)

---

## 1. 引言

flate2提供:

- DEFLATE/gzip/zlib压缩
- 流式读写
- 多级压缩
- C库后端支持

---

## 2. 编码器类型

### 定理 2.1 (编码器装饰)

> 编码器包装Write实现压缩写入。

```rust
pub struct GzEncoder<W: Write> {
    inner: zio::Writer<GzHeader, Compress, W>,
}

impl<W: Write> Write for GzEncoder<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        // 压缩后写入底层
    }
}
```

∎

### 定理 2.2 (压缩级别)

> 级别范围0-9，默认6。

```rust
let encoder = GzEncoder::new(file, Compression::default());
let encoder = GzEncoder::new(file, Compression::best());    // 9
let encoder = GzEncoder::new(file, Compression::fast());    // 1
let encoder = GzEncoder::new(file, Compression::none());    // 0
```

∎

---

## 3. 流式压缩

### 定理 3.1 (缓冲区管理)

> 内部缓冲区自动刷新。

```rust
let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
encoder.write_all(data)?;  // 可能部分压缩
encoder.finish()?;         // 刷新所有数据
```

∎

---

## 4. 解压缩安全

### 定理 4.1 (畸形数据)

> 解压缩检测格式错误。

```rust
let mut decoder = GzDecoder::new(corrupt_data);
let mut output = Vec::new();
decoder.read_to_end(&mut output)?;  // 返回InvalidData错误
```

∎

### 定理 4.2 (炸弹防护)

> 应用层需限制输出大小。

```rust
// 防止zip bomb
let limit = 1024 * 1024 * 100;  // 100MB
let mut output = Vec::with_capacity(limit);
```

∎

---

## 5. 反例

### 反例 5.1 (忘记finish)

```rust
let mut encoder = GzEncoder::new(file, Compression::default());
encoder.write_all(data)?;
// 错误: 忘记finish，数据不完整
drop(encoder);  // 自动finish但可能忽略错误

// 正确
encoder.finish()?;
```

### 反例 5.2 (压缩炸弹)

```rust
// 解压不受信任的压缩数据需限制
let mut decoder = GzDecoder::new(untrusted);
let mut output = Vec::new();
decoder.read_to_end(&mut output)?;  // 可能OOM!
```

---

*文档版本: 1.0.0*
*定理数量: 5个*
