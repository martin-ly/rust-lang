# anyhow vs thiserror: Rust 错误处理生态指南

> **定位**: Rust 错误处理库的权威对比与选择指南
> **版本**: anyhow 1.x, thiserror 1.x, miette 7.x
> **适用场景**: 应用开发、库开发、CLI 工具

---

## 📋 目录

- [anyhow vs thiserror: Rust 错误处理生态指南](#anyhow-vs-thiserror-rust-错误处理生态指南)
  - [📋 目录](#-目录)
  - [🎯 核心对比](#-核心对比)
  - [📦 thiserror (库开发)](#-thiserror-库开发)
  - [📦 anyhow (应用开发)](#-anyhow-应用开发)
  - [📦 miette (诊断增强)](#-miette-诊断增强)
  - [🔄 使用模式](#-使用模式)
    - [库 + 应用协作](#库--应用协作)
    - [从 anyhow 转换到 thiserror](#从-anyhow-转换到-thiserror)
  - [📊 选择决策树](#-选择决策树)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 核心对比

| 维度 | `thiserror` | `anyhow` | `miette` |
|------|-------------|----------|----------|
| **定位** | 库的错误类型 | 应用的动态错误 | 诊断报告 |
| **目标用户** | 库作者 | 应用开发者 | CLI / 工具开发者 |
| **类型安全** | 高 (枚举) | 低 (dyn Error) | 中 (带诊断) |
| **调试输出** | 实现 `Display` | 自动链式回溯 | 丰富诊断 + 源码 |
| **API 稳定性** | 承诺稳定 | 承诺稳定 | 较新，发展中 |
| **编译开销** | 低 (derive 宏) | 低 | 中 |
| **典型依赖** | `std::error::Error` | `anyhow::Error` | `miette::Report` |

**一句话总结**:

- 写 **库 (library)** → `thiserror`
- 写 **应用 (application)** → `anyhow`
- 需要 **漂亮的错误报告** → `miette`

---

## 📦 thiserror (库开发)

`thiserror` 通过派生宏减少 `std::error::Error` 的手写样板：

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DataStoreError {
    #[error("data store disconnected")]
    Disconnect(#[from] std::io::Error),

    #[error("the data for key `{0}` is not available")]
    Redaction(String),

    #[error("invalid header (expected {expected:?}, found {found:?})")]
    InvalidHeader {
        expected: String,
        found: String,
    },

    #[error("unknown data store error")]
    Unknown,
}
```

**自动实现**: `Error`, `Display`, `From<std::io::Error>`

**库边界原则**:

```rust
// 库暴露具体错误 → 调用者可以 match
pub fn parse_config(path: &str) -> Result<Config, DataStoreError> {
    let content = std::fs::read_to_string(path)?; // From io::Error
    // ...
    Ok(config)
}
```

---

## 📦 anyhow (应用开发)

`anyhow` 提供动态错误类型，无需定义枚举：

```rust
use anyhow::{Context, Result};

fn get_cluster_info() -> Result<ClusterInfo> {
    let config = std::fs::read_to_string("/etc/app/config")
        .context("failed to read config")?;

    let cluster: ClusterInfo = serde_json::from_str(&config)
        .context("config is not valid JSON")?;

    Ok(cluster)
}
```

**特性**:

- `anyhow::Result<T>` = `Result<T, anyhow::Error>`
- `.context()` 添加上下文
- 自动回溯链 (backtrace on nightly / with `backtrace` feature)

---

## 📦 miette (诊断增强)

`miette` 专注于人类可读的错误报告，带源码标注：

```rust
use miette::{Diagnostic, Report};
use thiserror::Error;

#[derive(Error, Diagnostic, Debug)]
#[error("oops!")]
#[diagnostic(
    code(oops::my::bad),
    help("try doing it better next time?"),
)]
struct MyError {
    #[source_code]
    src: String,

    #[label("this bit here")]
    bad_bit: SourceSpan,
}
```

**输出示例**:

```
  × oops!
   ╰─▶ 1:12
   │
 1 │ let x = "hello"
   ·            ─┬─
   ·             ╰── this bit here
   ╰────
  help: try doing it better next time?
```

---

## 🔄 使用模式

### 库 + 应用协作

```rust
// === 库 (my-lib) ===
use thiserror::Error;

#[derive(Error, Debug)]
pub enum LibError {
    #[error("parse failed: {0}")]
    Parse(#[from] std::num::ParseIntError),
}

pub fn lib_api(s: &str) -> Result<i32, LibError> {
    Ok(s.parse()?)
}

// === 应用 (my-app) ===
use anyhow::{Context, Result};
use my_lib::lib_api;

fn main() -> Result<()> {
    let value = lib_api("abc")
        .context("library call failed")?;
    println!("{}", value);
    Ok(())
}
```

### 从 anyhow 转换到 thiserror

```rust
// 早期原型 (anyhow)
fn fetch_data() -> anyhow::Result<Data> { /* ... */ }

// 稳定后提取为库 → 定义具体错误类型
#[derive(thiserror::Error, Debug)]
pub enum FetchError { /* ... */ }

fn fetch_data() -> Result<Data, FetchError> { /* ... */ }
```

---

## 📊 选择决策树

```
你是开发库 (library) 还是应用 (application)?
├── 库 ──→ 需要调用者区分错误类型?
│           ├── 是 ──→ thiserror
│           └── 否 ──→ std::io::Error 或自定义类型
└── 应用 ──→ 需要漂亮的诊断报告?
            ├── 是 ──→ miette
            └── 否 ──→ anyhow
```

**组合使用**: `thiserror` 定义库错误 + `anyhow` 在应用层聚合

---

## 🔗 参考资源

- [thiserror docs](https://docs.rs/thiserror)
- [anyhow docs](https://docs.rs/anyhow)
- [miette docs](https://docs.rs/miette)
- [项目 Common 模块](../../crates/common/src/error/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
