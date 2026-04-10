# Common: 共享库

> **工具集合** | **跨 crate 支持** | ⭐⭐⭐⭐⭐ 重要性

## 模块职责

本 crate 为所有学习 crate 提供共享功能：

- **错误处理**: 统一的错误类型和转换
- **序列化支持**: Serde 集成
- **日志追踪**: Tracing 集成
- **异步工具**: Tokio 和 Futures 支持
- **通用 Trait**: 共享接口定义
- **测试工具**: 测试辅助函数

## 目录结构

```
src/
├── lib.rs          # 模块入口
├── error.rs        # 错误处理
├── serialization.rs # 序列化
└── utils.rs        # 通用工具
```

## 主要类型和 Trait

### 错误处理

| 类型 | 描述 | 用途 |
|------|------|------|
| `CommonError` | 统一错误类型 | 跨 crate 错误 |
| `Result<T>` | 类型别名 | `std::result::Result<T, CommonError>` |
| `ErrorExt` | 错误扩展 | 便捷方法 |

### 序列化 Trait

| Trait | 描述 | 实现 |
|-------|------|------|
| `Serializable` | 可序列化 | Serde 集成 |
| `Deserializable` | 可反序列化 | Serde 集成 |

## 使用示例

### 错误处理

```rust
use common::{CommonError, Result};

fn may_fail() -> Result<i32> {
    if some_condition() {
        Ok(42)
    } else {
        Err(CommonError::new("操作失败"))
    }
}

fn main() -> Result<()> {
    let value = may_fail()?;
    println!("{}", value);
    Ok(())
}
```

### 序列化

```rust
use common::Serializable;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
struct User {
    name: String,
    age: u32,
}

fn main() -> common::Result<()> {
    let user = User {
        name: "Alice".to_string(),
        age: 30,
    };

    let json = user.to_json()?;
    println!("{}", json);

    let restored: User = User::from_json(&json)?;
    println!("{:?}", restored);

    Ok(())
}
```

## 特性标志

| 特性 | 描述 | 依赖 |
|------|------|------|
| `std` | 标准库支持 | 默认启用 |
| `serde` | 序列化支持 | `serde`, `serde_json` |
| `error-trait` | 错误处理 | `thiserror`, `anyhow` |
| `async` | 异步支持 | `tokio`, `futures` |
| `tracing` | 日志追踪 | `tracing`, `tracing-subscriber` |
| `full` | 全部启用 | 所有特性 |

## 依赖配置

```toml
[dependencies]
common = { path = "../common", features = ["serde", "async"] }
```

## 运行方式

```bash
# 运行测试
cargo test -p common
```

## 设计原则

1. **最小依赖**: 仅包含真正通用的功能
2. **可选特性**: 通过特性标志控制依赖
3. **零成本抽象**: 不引入运行时开销
4. **文档完善**: 所有公共 API 都有文档
