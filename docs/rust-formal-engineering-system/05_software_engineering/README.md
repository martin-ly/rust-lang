# 软件工程 {#软件工程}
>
> **EN**: Software Engineering Index
> **Summary**: 软件工程 Software Engineering Index. (stub/archive redirect)
> **分级**: [B]
> **Bloom 层级**: L5-L6
> **创建日期**: 2026-02-20
> **最后更新**: 2026-06-25（已按 Rust 1.97.0 复审）
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至研究笔记，请参见：

> **权威来源**: 本文件为 Rust 形式化工程体系专题入口；通用 Rust 概念解释请见对应 `concept/` 权威页：
>
> - [`concept/06_ecosystem/03_design_patterns/01_patterns.md`](../../../concept/06_ecosystem/03_design_patterns/01_patterns.md)
> - [`concept/01_foundation/07_modules_and_items/01_modules_and_paths.md`](../../../concept/01_foundation/07_modules_and_items/01_modules_and_paths.md)
> - [`concept/02_intermediate/03_error_handling/01_error_handling.md`](../../../concept/02_intermediate/03_error_handling/01_error_handling.md)
>
> 根据 AGENTS.md §3.4，`docs/` 仅保留专题工程视角内容；通用概念解释统一维护在 `concept/` 中。

| 主题 | 链接 |
| :--- | :--- |
| 设计模式 | [software_design_theory/01_design_patterns_formal/](../../research_notes/software_design_theory/01_design_patterns_formal/README.md) |
| 工作流模型 | [software_design_theory/02_workflow_safe_complete_models/](../../research_notes/software_design_theory/02_workflow_safe_complete_models/README.md) |
| 组合工程 | [software_design_theory/04_compositional_engineering/](../../research_notes/software_design_theory/04_compositional_engineering/README.md) |

---

## 目录结构 {#目录结构}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 子目录 | 内容 |
| :--- | :--- |
| [07_testing/](07_testing/README.md) | 测试方法论与实践 |

---

## 软件工程实践 {#软件工程实践}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 代码组织 {#代码组织}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
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

### 错误处理 {#错误处理}

```rust,ignore
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

## 与核心文档的关联 {#与核心文档的关联}

| 本文档 | 核心文档 | 关系 |
| :--- | :--- | :--- |
| 本README | research_notes/software_design_theory/ | 索引/重定向 |

[返回主索引](../00_master_index.md)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-25（已按 Rust 1.97.0 复审）
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**
