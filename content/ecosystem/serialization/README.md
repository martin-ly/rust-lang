# Serialization 目录

> **定位**: Rust 序列化生态的 crate 对比、最佳实践与性能考量。
> **Rust 版本**: 1.96.0+ (Edition 2024)

---

## 目录结构

```text
content/ecosystem/serialization/
├── README.md                  # 本文件
└── serde_best_practices.md    # Serde 最佳实践
```

---

## 核心 crate

| Crate | 格式/能力 | 特点 |
|---|---|---|
| **`serde`** | 框架 | Rust 序列化的事实标准，支持 derive |
| **`serde_json`** | JSON | 最常用，人类可读 |
| **`toml`** | TOML | 配置文件首选 |
| **`bincode`** | 二进制 | 紧凑、高效，适合 RPC/缓存 |
| **` postcard`** | 二进制 | 为 `no_std` 和嵌入式优化 |
| **`prost`** | Protocol Buffers | gRPC 服务 |
| **`rkyv`** | 零拷贝归档 | 高性能反序列化，适合游戏/数据分析 |

---

## 选型建议

- 配置文件 / 可读交换：TOML / JSON + serde
- 服务间通信：bincode / protobuf
- 极致性能/零拷贝：rkyv
- 嵌入式：`postcard`
