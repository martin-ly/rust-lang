# 软件工程

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至研究笔记，请参见：

| 主题 | 链接 |
| :--- | :--- |
| 设计模式 | [software_design_theory/01_design_patterns_formal/](../../research_notes/software_design_theory/01_design_patterns_formal/README.md) |
| 工作流模型 | [software_design_theory/02_workflow_safe_complete_models/](../../research_notes/software_design_theory/02_workflow_safe_complete_models/README.md) |
| 组合工程 | [software_design_theory/04_compositional_engineering/](../../research_notes/software_design_theory/04_compositional_engineering/README.md) |

---

## 目录结构

| 子目录 | 内容 |
| :--- | :--- |
| [07_testing/](07_testing/) | 测试方法论与实践 |

---

## 软件工程实践

### 代码组织

```rust
// 模块系统：清晰的代码边界
mod database {
    pub struct Connection;
    impl Connection {
        pub fn new() -> Self { Self }
    }
}

mod api {
    use super::database::Connection;

    pub struct Handler {
        db: Connection,
    }
}
```

### 错误处理

```rust
use std::result::Result;
use std::error::Error;

// 健壮的错误处理
fn robust_error_handling() -> Result<(), Box<dyn Error>> {
    let config = read_config()?;           // ? 传播错误
    let connection = establish_connection(&config)?;
    process_data(&connection)?;
    Ok(())
}

// 自定义错误类型
#[derive(Debug)]
enum AppError {
    ConfigError(String),
    ConnectionError(String),
    ProcessingError(String),
}

impl std::fmt::Display for AppError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            AppError::ConfigError(msg) => write!(f, "Config error: {}", msg),
            AppError::ConnectionError(msg) => write!(f, "Connection error: {}", msg),
            AppError::ProcessingError(msg) => write!(f, "Processing error: {}", msg),
        }
    }
}

impl Error for AppError {}
```

---

## 与核心文档的关联

| 本文档 | 核心文档 | 关系 |
| :--- | :--- | :--- |
| 本README | research_notes/software_design_theory/ | 索引/重定向 |

[返回主索引](../00_master_index.md)
