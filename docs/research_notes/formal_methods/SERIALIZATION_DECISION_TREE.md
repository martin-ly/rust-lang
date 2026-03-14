# 序列化格式选型决策树

> **创建日期**: 2026-02-24
> **状态**: ✅ 新建 (10/10决策树完成！)
> **任务ID**: P1-W8-T7

---

## 决策树

```text
需要序列化？
│
├── 人类可读？
│   ├── 是 → 文本格式
│   │   ├── 配置/调试 → JSON
│   │   ├── 结构化数据 → YAML/TOML
│   │   │   ├── 简单配置 → TOML (Cargo风格)
│   │   │   └── 复杂文档 → YAML
│   │   ├── 性能敏感 → CSV (表格)
│   │   └── Web/API → JSON
│   │
│   └── 否 → 二进制格式
│       ├── 性能优先 → bincode/flatbuffers
│       ├── 跨语言 → Protocol Buffers
│       ├── 模式演进 → Avro/Thrift
│       └── 嵌入式 → MessagePack/nanopb
│
├── 模式定义？
│   ├── 强类型 → serde + derive
│   ├── 动态类型 → serde_json::Value
│   └── 无模式 → flexbuffers
│
├── 向后兼容？
│   ├── 是 → Protocol Buffers/Avro
│   └── 否 → bincode/ron
│
└── 特定需求？
    ├── 零拷贝 → flatbuffers/capnp
    ├── 压缩 → MessagePack + zstd
    └── 加密 → 序列化后加密
```

---

## 格式对比

| 格式 | 可读 | 性能 | 模式 | 跨语言 | Rust crate | 适用场景 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| JSON | ✅ | 中 | 可选 | ✅ | serde_json | Web/API |
| TOML | ✅ | 低 | 可选 | ✅ | toml | 配置 |
| YAML | ✅ | 低 | 可选 | ✅ | serde_yaml | 复杂配置 |
| CSV | ✅ | 中 | 是 | ✅ | csv | 表格数据 |
| bincode | ❌ | 高 | 是 | ⚠️ | bincode | 内部通信 |
| MessagePack | ❌ | 高 | 可选 | ✅ | rmp-serde | 通用二进制 |
| Protobuf | ❌ | 高 | 必须 | ✅ | prost | 跨语言API |
| FlatBuffers | ❌ | 极高 | 必须 | ✅ | flatbuffers | 零拷贝 |
| Avro | ❌ | 高 | 必须 | ✅ | apache-avro | 大数据 |

---

## Serde生态

```rust
// 基本使用
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
struct Config {
    name: String,
    port: u16,
}

// JSON
let json = serde_json::to_string(&config)?;
let config: Config = serde_json::from_str(&json)?;

// 其他格式同理
let toml = toml::to_string(&config)?;
let bin = bincode::serialize(&config)?;
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 序列化格式选型决策树 (10/10决策树全部完成！)

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
