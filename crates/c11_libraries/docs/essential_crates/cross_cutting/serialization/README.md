# 序列化 (Serialization)

**类别**: 横切关注点  
**重要程度**: ⭐⭐⭐⭐⭐ (必备)  
**更新日期**: 2025-10-20

---

## 📋 概述

序列化是将数据结构转换为字节流的过程，反序列化则相反。Rust 的 **Serde** 生态是业界最优秀的序列化框架之一。

---

## 🔧 核心工具

### 1. serde (核心框架 ⭐⭐⭐⭐⭐)

**添加依赖**:

```toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"  # JSON
toml = "0.8"        # TOML
serde_yaml = "0.9"  # YAML
```

**用途**: 序列化和反序列化框架

#### 基础用法

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct User {
    id: u64,
    name: String,
    email: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    age: Option<u32>,
}

fn main() {
    let user = User {
        id: 1,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
        age: Some(30),
    };
    
    // 序列化到 JSON
    let json = serde_json::to_string(&user).unwrap();
    println!("{}", json);
    
    // 反序列化
    let user2: User = serde_json::from_str(&json).unwrap();
    println!("{:?}", user2);
}
```

#### 高级特性

**字段重命名**:

```rust
#[derive(Serialize, Deserialize)]
struct User {
    #[serde(rename = "userId")]
    user_id: u64,
    
    #[serde(rename = "fullName")]
    full_name: String,
}
```

**默认值**:

```rust
#[derive(Serialize, Deserialize)]
struct Config {
    #[serde(default = "default_port")]
    port: u16,
    
    #[serde(default)]  // 使用 Default trait
    workers: usize,
}

fn default_port() -> u16 {
    3000
}
```

**自定义序列化**:

```rust
use serde::{Serialize, Serializer};
use chrono::{DateTime, Utc};

#[derive(Serialize)]
struct Event {
    name: String,
    
    #[serde(serialize_with = "serialize_timestamp")]
    timestamp: DateTime<Utc>,
}

fn serialize_timestamp<S>(dt: &DateTime<Utc>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    serializer.serialize_i64(dt.timestamp())
}
```

---

### 2. serde_json (JSON ⭐⭐⭐⭐⭐)

**用途**: JSON 序列化

```rust
use serde_json::{json, Value};

// 创建 JSON 值
let value = json!({
    "name": "Alice",
    "age": 30,
    "emails": ["alice@example.com", "alice@work.com"]
});

// 美化输出
let pretty = serde_json::to_string_pretty(&value).unwrap();
println!("{}", pretty);

// 动态访问
if let Some(name) = value["name"].as_str() {
    println!("Name: {}", name);
}
```

---

### 3. bincode (二进制 ⭐⭐⭐⭐)

**添加依赖**: `cargo add bincode`  
**用途**: 高效二进制序列化

```rust
use bincode;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct Data {
    x: i32,
    y: String,
}

fn main() {
    let data = Data { x: 42, y: "hello".to_string() };
    
    // 序列化
    let bytes = bincode::serialize(&data).unwrap();
    println!("Bytes: {:?}", bytes);
    
    // 反序列化
    let data2: Data = bincode::deserialize(&bytes).unwrap();
    println!("x: {}, y: {}", data2.x, data2.y);
}
```

---

### 4. postcard (嵌入式 💡)

**添加依赖**: `cargo add postcard`  
**用途**: 无 std 环境的紧凑序列化

```rust
use postcard;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct Packet {
    id: u8,
    payload: [u8; 16],
}

fn main() {
    let packet = Packet {
        id: 1,
        payload: [0; 16],
    };
    
    let mut buf = [0u8; 32];
    let bytes = postcard::to_slice(&packet, &mut buf).unwrap();
    
    let packet2: Packet = postcard::from_bytes(bytes).unwrap();
}
```

---

### 5. rmp-serde (MessagePack 💡)

**添加依赖**: `cargo add rmp-serde`  
**用途**: MessagePack 格式

```rust
use rmp_serde;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct Data {
    x: i32,
    y: String,
}

fn main() {
    let data = Data { x: 42, y: "hello".to_string() };
    
    let bytes = rmp_serde::to_vec(&data).unwrap();
    let data2: Data = rmp_serde::from_slice(&bytes).unwrap();
}
```

---

### 6. ciborium (CBOR 💡)

**添加依赖**: `cargo add ciborium`  
**用途**: CBOR (Concise Binary Object Representation)

```rust
use ciborium;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct Data {
    x: i32,
    y: String,
}

fn main() {
    let data = Data { x: 42, y: "hello".to_string() };
    
    let mut bytes = Vec::new();
    ciborium::ser::into_writer(&data, &mut bytes).unwrap();
    
    let data2: Data = ciborium::de::from_reader(&bytes[..]).unwrap();
}
```

---

## 💡 最佳实践

### 1. 版本兼容性

```rust
use serde::{Serialize, Deserialize};

// v1
#[derive(Serialize, Deserialize)]
struct UserV1 {
    id: u64,
    name: String,
}

// v2 (向后兼容)
#[derive(Serialize, Deserialize)]
struct UserV2 {
    id: u64,
    name: String,
    #[serde(default)]  // 旧版本没有此字段
    email: Option<String>,
}
```

### 2. 枚举序列化

```rust
use serde::{Serialize, Deserialize};

// 外部标签 (默认)
#[derive(Serialize, Deserialize)]
enum Message {
    Request { id: u64, method: String },
    Response { id: u64, result: String },
}
// JSON: {"Request": {"id": 1, "method": "get"}}

// 内部标签
#[derive(Serialize, Deserialize)]
#[serde(tag = "type")]
enum Message2 {
    Request { id: u64, method: String },
    Response { id: u64, result: String },
}
// JSON: {"type": "Request", "id": 1, "method": "get"}

// 相邻标签
#[derive(Serialize, Deserialize)]
#[serde(tag = "type", content = "data")]
enum Message3 {
    Request { id: u64, method: String },
    Response { id: u64, result: String },
}
// JSON: {"type": "Request", "data": {"id": 1, "method": "get"}}

// 无标签
#[derive(Serialize, Deserialize)]
#[serde(untagged)]
enum Message4 {
    Request { id: u64, method: String },
    Response { id: u64, result: String },
}
// JSON: {"id": 1, "method": "get"}
```

### 3. 扁平化嵌套

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct Metadata {
    created_at: String,
    updated_at: String,
}

#[derive(Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
    
    #[serde(flatten)]
    metadata: Metadata,
}

// JSON: {"id": 1, "name": "Alice", "created_at": "...", "updated_at": "..."}
```

### 4. 性能优化

```rust
use serde::{Serialize, Deserialize};

// 使用 Cow 避免不必要的克隆
use std::borrow::Cow;

#[derive(Serialize, Deserialize)]
struct Message<'a> {
    #[serde(borrow)]
    text: Cow<'a, str>,
}

// 使用 &str 避免分配
#[derive(Deserialize)]
struct BorrowedData<'a> {
    #[serde(borrow)]
    name: &'a str,
}
```

---

## 📊 格式对比

| 格式 | 人类可读 | 大小 | 速度 | 推荐场景 |
|------|---------|------|------|---------|
| **JSON** | ✅ | 中 | ⭐⭐⭐⭐ | API, 配置 |
| **TOML** | ✅ | 大 | ⭐⭐⭐ | 配置文件 |
| **YAML** | ✅ | 中 | ⭐⭐ | 配置文件 |
| **Bincode** | ❌ | 小 | ⭐⭐⭐⭐⭐ | 内部通信 |
| **MessagePack** | ❌ | 小 | ⭐⭐⭐⭐ | RPC |
| **CBOR** | ❌ | 小 | ⭐⭐⭐⭐ | IoT, 嵌入式 |
| **Postcard** | ❌ | 极小 | ⭐⭐⭐⭐⭐ | 嵌入式 |

---

## 🎯 实战场景

### 场景1: API 响应

```rust
use axum::{Json, response::IntoResponse};
use serde::{Serialize, Deserialize};

#[derive(Serialize)]
struct ApiResponse<T> {
    success: bool,
    data: Option<T>,
    error: Option<String>,
}

impl<T: Serialize> ApiResponse<T> {
    fn success(data: T) -> Self {
        Self {
            success: true,
            data: Some(data),
            error: None,
        }
    }
    
    fn error(msg: String) -> Self {
        Self {
            success: false,
            data: None,
            error: Some(msg),
        }
    }
}

async fn get_user() -> impl IntoResponse {
    let user = User { id: 1, name: "Alice".to_string() };
    Json(ApiResponse::success(user))
}
```

### 场景2: 配置文件

```rust
use serde::{Serialize, Deserialize};
use std::fs;

#[derive(Serialize, Deserialize)]
struct Config {
    server: ServerConfig,
    database: DatabaseConfig,
}

#[derive(Serialize, Deserialize)]
struct ServerConfig {
    host: String,
    port: u16,
}

#[derive(Serialize, Deserialize)]
struct DatabaseConfig {
    url: String,
}

fn load_config() -> Config {
    let content = fs::read_to_string("config.toml").unwrap();
    toml::from_str(&content).unwrap()
}
```

---

## 🔗 相关资源

- [Serde Documentation](https://serde.rs/)
- [Serde Data Formats](https://serde.rs/#data-formats)
- [JSON Schema](https://json-schema.org/)

---

**导航**: [返回横切关注点](../README.md) | [返回主页](../../README.md)
