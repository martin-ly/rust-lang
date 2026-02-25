# 错误类型选择决策树

> **创建日期**: 2026-02-24
> **级别**: L1/L2
> **类型**: 决策树

---

## 决策流程

```
错误处理需求？
│
├── 快速原型/应用开发
│   ├── 需要简单传播
│   │   └── 使用anyhow
│   │       ├── Result<T, anyhow::Error>
│   │       └── 自动上下文
│   │
│   └── 需要特定错误
│       └── 使用thiserror
│           └── 派生Error trait
│
├── 库开发
│   ├── 公开API需要精确错误
│   │   └── 自定义枚举错误
│   │       ├── 实现std::error::Error
│   │       └── 提供详细错误信息
│   │
│   └── 内部错误
│       └── 使用std::io::Error等
│
└── 特定领域
    ├── IO错误
    │   └── std::io::Error
    │
    ├── 解析错误
    │   └── 自定义ParseError
    │
    └── 验证错误
        └── 自定义ValidationError
```

---

## 错误类型对比

| 类型 | 适用场景 | 性能 | 灵活性 |
| :--- | :--- | :--- | :--- |
| `anyhow::Error` | 应用开发 | 中 | 高 |
| `thiserror` | 库开发 | 高 | 中 |
| 自定义枚举 | 精确控制 | 高 | 低 |
| `Box<dyn Error>` | 动态分发 | 中 | 高 |

---

## anyhow示例

```rust
use anyhow::{Context, Result};

fn read_config() -> Result<Config> {
    let content = std::fs::read_to_string("config.toml")
        .context("读取配置文件失败")?;
    let config: Config = toml::from_str(&content)
        .context("解析配置失败")?;
    Ok(config)
}
```

## thiserror示例

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ConfigError {
    #[error("IO错误: {0}")]
    Io(#[from] std::io::Error),
    #[error("解析错误: {0}")]
    Parse(#[from] toml::de::Error),
    #[error("验证失败: {message}")]
    Validation { message: String },
}
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 决策树 10/10
