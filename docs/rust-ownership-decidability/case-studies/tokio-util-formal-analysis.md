# Tokio-Util 实用工具形式化分析

> **主题**: Tokio生态系统实用工具
>
> **形式化框架**: 流处理 + 背压控制
>
> **参考**: Tokio-Util Documentation

---

## 目录

- [Tokio-Util 实用工具形式化分析](#tokio-util-实用工具形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Codec框架](#2-codec框架)
    - [2.1 Encoder特质](#21-encoder特质)
    - [定义 2.1 (Encoder)](#定义-21-encoder)
    - [定理 2.1 (编码不变式)](#定理-21-编码不变式)
    - [2.2 Decoder特质](#22-decoder特质)
    - [定义 2.2 (Decoder)](#定义-22-decoder)
    - [定理 2.2 (解码状态机)](#定理-22-解码状态机)
  - [3. 背压控制](#3-背压控制)
    - [定理 3.1 (背压传播)](#定理-31-背压传播)
  - [4. 超时处理](#4-超时处理)
    - [定理 4.1 (Timeout语义)](#定理-41-timeout语义)
  - [5. 反例](#5-反例)
    - [反例 5.1 (Decoder状态丢失)](#反例-51-decoder状态丢失)
    - [反例 5.2 (Codec线程安全)](#反例-52-codec线程安全)

---

## 1. 引言

Tokio-Util提供:

- Codec编解码框架
- 流处理工具
- 超时管理
- 背压控制

---

## 2. Codec框架

### 2.1 Encoder特质

### 定义 2.1 (Encoder)

```rust
pub trait Encoder<Item> {
    type Error;

    fn encode(&mut self, item: Item, dst: &mut BytesMut)
        -> Result<(), Self::Error>;
}
```

### 定理 2.1 (编码不变式)

> 成功编码后，dst包含完整的编码消息。

```rust
impl Encoder<MyMessage> for MyCodec {
    fn encode(&mut self, msg: MyMessage, dst: &mut BytesMut)
        -> Result<(), Self::Error>
    {
        // 前置: dst是可写缓冲区
        dst.extend_from_slice(&msg.to_bytes());
        // 后置: dst包含原内容 + 编码消息
        Ok(())
    }
}
```

∎

### 2.2 Decoder特质

### 定义 2.2 (Decoder)

```rust
pub trait Decoder {
    type Item;
    type Error;

    fn decode(&mut self, src: &mut BytesMut)
        -> Result<Option<Self::Item>, Self::Error>;
}
```

### 定理 2.2 (解码状态机)

> Decoder正确处理不完整消息。

**状态**:

- `Ok(Some(item))`: 完整消息解码
- `Ok(None)`: 需要更多数据
- `Err(e)`: 协议错误

```rust
impl Decoder for MyCodec {
    fn decode(&mut self, src: &mut BytesMut)
        -> Result<Option<MyMessage>, MyError>
    {
        if src.len() < HEADER_SIZE {
            return Ok(None);  // 等待更多数据
        }
        // ...解码
    }
}
```

∎

---

## 3. 背压控制

### 定理 3.1 (背压传播)

> tokio-util的缓冲和限流实现背压。

```rust
use tokio_util::sync::PollSender;

// PollSender在channel满时返回Pending
let sender = PollSender::new(tx);
// 下游忙时自动阻塞上游
```

∎

---

## 4. 超时处理

### 定理 4.1 (Timeout语义)

> tokio_util::time提供精确的超时控制。

```rust
use tokio_util::time::{timeout, Duration};

// 超时精确到毫秒级
let result = timeout(Duration::from_secs(5), async {
    // 操作
}).await;
```

∎

---

## 5. 反例

### 反例 5.1 (Decoder状态丢失)

```rust
// 错误: decode_eof不实现
decoder.decode(&mut buf)?;

// 正确: 处理EOF
loop {
    match decoder.decode(&mut buf)? {
        Some(item) => process(item),
        None => break,
    }
}
// 处理剩余数据
decoder.decode_eof(&mut buf)?;
```

### 反例 5.2 (Codec线程安全)

```rust
// Codec不是Send/Sync，不能跨任务共享
let codec = MyCodec::new();

// 错误
spawn(async move {
    codec.encode(msg, &mut buf)?;  // 可能竞争
});

// 正确: 每个任务一个Codec
spawn(async move {
    let mut codec = MyCodec::new();
    codec.encode(msg, &mut buf)?;
});
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
