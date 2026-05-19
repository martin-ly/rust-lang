# Serde 最佳实践指南

> **定位**: Rust 序列化的事实标准深度指南
> **版本**: serde 1.x
> **适用场景**: API 开发、配置文件、数据持久化

---

## 📋 目录

- [Serde 最佳实践指南](#serde-最佳实践指南)
  - [📋 目录](#-目录)
  - [🎯 核心设计](#-核心设计)
  - [⚡ 基础用法](#-基础用法)
  - [🔧 高级特性](#-高级特性)
    - [自定义序列化](#自定义序列化)
    - [扁平化结构](#扁平化结构)
    - [多态反序列化](#多态反序列化)
  - [📊 性能优化](#-性能优化)
  - [🛡️ 安全注意事项](#️-安全注意事项)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 核心设计

Serde 采用 **序列化-反序列化分离** 架构：

```
┌─────────────┐      Serialize      ┌─────────────┐
│   Rust 类型  │  ───────────────→  │   数据格式   │
│   struct T  │                    │  JSON/YAML/  │
└─────────────┘                    │  Bincode/... │
                                   └─────────────┘
┌─────────────┐      Deserialize    ┌─────────────┐
│   Rust 类型  │  ←───────────────  │   数据格式   │
│   struct T  │                    │  JSON/YAML/  │
└─────────────┘                    │  Bincode/... │
                                   └─────────────┘
```

**核心 trait**:

- `Serialize`: Rust → 外部格式
- `Deserialize`: 外部格式 → Rust

---

## ⚡ 基础用法

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase")]  // 字段命名风格转换
pub struct User {
    pub id: u64,
    pub user_name: String,

    #[serde(skip_serializing_if = "Option::is_none")]  // 条件跳过
    pub email: Option<String>,

    #[serde(default)]  // 缺失时使用默认值
    pub is_active: bool,

    #[serde(skip)]  // 完全跳过序列化
    pub internal_token: String,
}
```

**JSON 序列化/反序列化**:

```rust
use serde_json;

let user = User {
    id: 1,
    user_name: "alice".into(),
    email: Some("alice@example.com".into()),
    is_active: true,
    internal_token: "secret".into(),
};

// 序列化
let json = serde_json::to_string_pretty(&user)?;

// 反序列化
let parsed: User = serde_json::from_str(&json)?;
```

---

## 🔧 高级特性

### 自定义序列化

```rust
use serde::{Serialize, Serializer, Deserialize, Deserializer};
use chrono::{DateTime, Utc};

mod iso8601 {
    use super::*;

    pub fn serialize<S>(date: &DateTime<Utc>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&date.to_rfc3339())
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<DateTime<Utc>, D::Error>
    where
        D: Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        DateTime::parse_from_rfc3339(&s)
            .map_err(serde::de::Error::custom)
            .map(|dt| dt.with_timezone(&Utc))
    }
}

#[derive(Serialize, Deserialize)]
pub struct Event {
    #[serde(with = "iso8601")]
    pub timestamp: DateTime<Utc>,
}
```

### 扁平化结构

```rust
#[derive(Serialize, Deserialize)]
pub struct ApiResponse {
    pub status: String,

    #[serde(flatten)]  // 将嵌套结构展开到当前层级
    pub data: ResponseData,
}

#[derive(Serialize, Deserialize)]
pub struct ResponseData {
    pub users: Vec<User>,
    pub total: usize,
}

// JSON: { "status": "ok", "users": [...], "total": 100 }
```

### 多态反序列化

```rust
#[derive(Serialize, Deserialize, Debug)]
#[serde(tag = "type", content = "payload")]  // 外部标签 + 内容
pub enum Message {
    Text { content: String },
    Image { url: String, width: u32, height: u32 },
    File { name: String, size: u64 },
}

// JSON:
// { "type": "Text", "payload": { "content": "hello" } }
// { "type": "Image", "payload": { "url": "...", "width": 100, "height": 100 } }
```

---

## 📊 性能优化

| 格式 | 序列化速度 | 反序列化速度 | 体积 | 可读性 |
|------|-----------|-------------|------|--------|
| JSON | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ |
| Bincode | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ❌ |
| MessagePack | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ❌ |
| YAML | ⭐⭐ | ⭐⭐ | ⭐⭐ | ⭐⭐⭐ |

**选择建议**:

- **API 通信**: JSON (可读性好)
- **内部服务**: MessagePack / Bincode (体积小)
- **配置文件**: YAML / TOML (人类可读)
- **持久化**: Bincode (性能最高)

---

## 🛡️ 安全注意事项

1. **拒绝服务**: 反序列化不受信任的数据时设置大小限制

   ```rust
   let config: Config = serde_json::from_str(input)?;
   // 确保输入大小已限制
   ```

2. **栈溢出**: 深度嵌套结构可能导致栈溢出

   ```rust
   // 使用 #[serde(deserialize_with)] 限制深度
   ```

3. **枚举反序列化**: 不受信任的 `tag` 值可能导致 panic

   ```rust
   // 使用 #[serde(other)] 处理未知变体
   #[serde(other)]
   Unknown,
   ```

---

## 🔗 参考资源

- [Serde 官方文档](https://serde.rs/)
- [serde_json 文档](https://docs.rs/serde_json)
- [项目 C10 网络模块](../../crates/c10_networks/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
**状态**: ✅ 已完善
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
