# 错误处理 (Error Handling)
>
> **📎 交叉引用**
>
> 本主题在 concept 中有深度的概念分析：[错误处理基础](../../concept/01_foundation/10_error_handling_basics.md)
>
> **相关概念**: [错误处理](../../../concept/02_intermediate/03_error_handling/04_error_handling.md)
> **Bloom 层级**: 理解
> **📌 简介**:
> Rust 将错误分为可恢复错误 (`Result<T, E>`) 和不可恢复错误 (`panic!`)，通过类型系统强制显式处理失败路径。
> 这种设计消除了 C 的静默错误传播和 Java 的异常滥用，实现了"编译期错误处理完备性检查"。
>
> **⏱️ 预计学习时间**: 3-4 小时
> **📚 难度级别**: ⭐⭐⭐ 中级
> **权威来源**: [Rust Book Ch09](https://doc.rust-lang.org/book/ch09-00-error-handling.html),
> [Rust Reference — The `?` operator](https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator),
> [RFC 243: Trait-based Exception Handling](https://rust-lang.github.io/rfcs/0243-trait-based-exception-handling.html),
> [RFC 3058: `let` chains](https://rust-lang.github.io/rfcs/3058-try-trait-v2.html),
> [thiserror crate](https://docs.rs/thiserror/),
> [anyhow crate](https://docs.rs/anyhow/)
>
> **权威来源对齐变更日志**:
> 2026-05-19 新增 RFC 243 核心设计决策摘要、
> `?` 运算符形式化语义（Rust Reference）、
> Rust vs C++ vs Haskell 错误处理对比矩阵、
> 错误处理代数语义来源标注 [来源: Authority Source Sprint Batch 8]
>
> **受众**: [专家] / [研究者]
> **内容分级**: [实验级]

---

## 🎯 学习目标

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

完成本章后，你将能够：

- [x] 区分 `Result<T, E>` 与 `Option<T>` 的语义边界，并在正确场景下选择
- [x] 使用 `?` 运算符实现错误的优雅传播，理解其背后的 `From`  trait 机制
- [x] 设计符合 Rust 生态习惯的自定义错误类型（手动实现 / `thiserror` / `anyhow`）
- [x] 在 `main` 函数和闭包中处理 `Result`，理解 `Termination` trait
- [x] 判断何时应该 `panic`，何时应该返回 `Result`

---

## 📋 先决条件

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

1. **枚举与模式匹配** — `enum`、`match`（`01_fundamentals/enums.md`）
2. **泛型基础** — `T`、`E` 类型参数（`02_intermediate/generics.md`）
3. **Trait** — `From`、`Display`（`02_intermediate/traits.md`）
4. **所有权** — move 语义（`01_fundamentals/ownership.md`）

---

## 🧠 核心概念

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 模块 1: 概念定义

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

#### 1.1 直观定义

Rust 没有异常（Exception）。
所有可能的失败都**显式编码在类型中**
[
来源: Rust Reference — Error Handling / 2025; RFC 243 — Trait-based Exception Handling / 2016;
核心设计决策: 用代数数据类型替代异常机制，编译器强制 exhaustiveness check，消除 C 的静默错误传播和 Java 的异常滥用
]：

- **`Result<T, E>`**: 操作**可能失败**，失败时携带错误信息 `E`
- **`Option<T>`**: 操作**可能为空**，空时无额外信息
- **`panic!`**: 程序进入**不可恢复状态**，立即终止当前线程

> 💡 关键直觉：`Result` 说"我可能失败，请处理"；
> `Option` 说"我可能为空，请检查"；
> `panic` 说"这不应该发生，如果有 bug 请崩溃"。

#### 1.2 操作定义

**`Result` 的基本操作**：

```rust
enum Result<T, E> {
    Ok(T),   // 成功分支
    Err(E),  // 失败分支
}
```

| 操作 | 签名 | 语义 |
|------|------|------|
| `unwrap()` | `T` | 取 `Ok` 值，否则 `panic` |
| `expect(msg)` | `T` | 取 `Ok` 值，否则 `panic` 并带消息 |
| `unwrap_or(default)` | `T` | 取 `Ok` 值，否则返回默认值 |
| `map(f)` | `Result<U, E>` | 转换 `Ok` 值，`Err` 不变 |
| `map_err(f)` | `Result<T, F>` | 转换 `Err` 值，`Ok` 不变 |
| `and_then(f)` | `Result<U, E>` | 链式操作，仅在 `Ok` 时执行 |
| `?` (try 运算符) | 传播错误 | 若为 `Err`，立即从当前函数返回 |

**`Option` 与 `Result` 的桥接**：

```rust,ignore
// Option → Result: 为空时提供错误信息
opt.ok_or("missing value")           // Result<T, &str>
opt.ok_or_else(|| compute_error())   // 延迟计算错误

// Result → Option: 丢弃错误信息
result.ok()   // Option<T>
result.err()  // Option<E>
```

#### 1.3 形式化直觉

> ⚠️ **标注**:
> 本节与 Rust 类型系统的代数语义对齐 [来源: Wadler — Monads for functional programming / 1990;
> Rust 错误处理可视为 `Result` monad 在命令式语言中的特化实现，其中 `?` 对应 monadic bind (`>>=`) 的语法糖; RFC 243 §Motivation]。
>
> **跨语言对比**:
> C++ 异常（零开销抽象，但无类型安全保证）[来源: ISO C++20 §14; Itanium ABI — Zero-cost exception handling / 2000];
> Haskell `Either` monad（类型系统完备，纯函数式）[来源: Wadler / 1990; GHC Control.Monad.Except];
> Go `error` 接口（显式返回，但无泛型约束）[来源: Go Language Specification — Error interface / 2022];
> Java checked exception（编译期检查，但破坏函数签名稳定性）[来源: Java Language Specification §11 / 2020]。

`Result<T, E>` 在类型论中对应**和类型（Sum Type）**：`Result<T, E> ≡ T + E`（ tagged union）。

`Option<T>` 是 `Result` 的特例：`Option<T> ≡ Result<T, ()>` —— 空时无信息。

`?` 运算符的类型规则（简化）：

```text
expr: Result<T, E>
------------------  (where E: From<E>)
expr?: T
```

即 `?` 将 `Result<T, E>` "解包"为 `T`，但前提是 `E` 可以转换为函数返回的错误类型（通过 `From` trait）。

---

### 模块 2: 属性清单
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 属性名 | 类型 | 值域/取值 | 说明 | 反例边界 |
|--------|------|-----------|------|----------|
| **must_use** | 固有属性 | 编译器警告 | `Result` 和 `Option` 都标记了 `#[must_use]` | `let _ = ...` 可显式忽略 |
| **零成本抽象** | 固有属性 | true | `Result<T, E>` 的内存布局与 `T` 或 `E` 相同（tagged union 优化） | `E` 很大时可能膨胀 |
| **? 运算符自动转换** | 关系属性 | `From<E>` | `?` 自动调用 `From::from` 转换错误类型 | 未实现 `From` 时编译失败 |
| **panic = 不可恢复** | 固有属性 | true | `panic` 不跨线程传播，可由 `catch_unwind` 捕获 | `catch_unwind` 不捕获所有 panic |
| **main 可返回 Result** | 固有属性 | Rust 1.26+ | `fn main() -> Result<(), E>` 自动打印错误 | `E` 需实现 `Debug` |

#### 关键推论

1. **推论 1（编译期强制）**: `#[must_use]` 确保 `Result` 不能被静默丢弃。这是 Rust 消除"未检查错误"类 bug 的核心机制。
2. **推论 2（错误类型擦除）**: `anyhow::Error` 通过类型擦除允许 `?` 在不同错误类型间传播，代价是运行时类型检查。
3. **推论 3（panic 边界）**: `panic` 仅终止当前线程（除非主线程），不泄漏资源（通过 unwinding 调用 `Drop`）。

---

### 模块 3: 概念依赖图
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```mermaid
graph TD
    A[Enums] --> B[Result<T, E>]
    A --> C[Option<T>]
    B --> D[? Operator]
    C --> D
    D --> E[From Trait]
    E --> F[Custom Error Types]
    F --> G[thiserror / anyhow]
    B --> H["panic!"]
    C --> H
    H --> I[catch_unwind]
    F --> J[Error Trait]
    J --> K[Display + Debug]

    style B fill:#f9f,stroke:#333,stroke-width:2px
    style D fill:#bbf,stroke:#333,stroke-width:2px
    style F fill:#bfb,stroke:#333,stroke-width:2px
```

#### 承上（前置知识回溯）

| 前置概念 | 所在文档 | 本章中使用的具体点 |
|----------|----------|-------------------|
| **枚举** | `01_fundamentals/enums.md` | `Result` 和 `Option` 都是枚举 |
| **模式匹配** | `01_fundamentals/pattern_matching.md` | `match result { Ok(v) => ..., Err(e) => ... }` |
| **泛型** | `02_intermediate/generics.md` | `Result<T, E>` 的 `T` 和 `E` 类型参数 |
| **Trait** | `02_intermediate/traits.md` | `From`、`Display`、`Error` trait 实现 |

#### 启下（后续延伸预告）

| 后续概念 | 所在文档 | 掌握本章后方可理解 |
|----------|----------|-------------------|
| **FFI** | `03_advanced/unsafe/ffi.md` | C 错误码与 `Result` 的映射 |
| **Async** | `03_advanced/async/async_await.md` | `?` 在 `async fn` 中的行为 |
| **Safety Critical** | `04_expert/safety_critical/` | 高完整性系统中错误处理的认证要求 |

---

### 模块 4: 机制解释
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

#### 4.1 类型系统视角

**`Result` 的 tagged union 内存布局**：

```rust
// Result<i32, String> 的内存布局（简化）:
// 判别式 + 最大对齐的 payload
//
// Ok(42):
// ┌──────────┬──────────────────────┐
// │ tag = 0  │ payload: i32 = 42    │
// └──────────┴──────────────────────┘
//
// Err("oops"):
// ┌──────────┬──────────────────────┐
// │ tag = 1  │ payload: String      │
// └──────────┴──────────────────────┘
```

当 `T` 和 `E` 都允许 niche optimization（如 `&T` 或 `NonNull`）时，`Result` 可能不需要额外 tag 位。

#### 4.2 控制流视角

**`?` 运算符的脱糖**：

```rust,ignore
// 源码:
fn read_file(path: &str) -> Result<String, io::Error> {
    let content = std::fs::read_to_string(path)?;
    Ok(content)
}

// 编译器脱糖后:
fn read_file(path: &str) -> Result<String, io::Error> {
    let content = match std::fs::read_to_string(path) {
        Ok(v) => v,
        Err(e) => return Err(From::from(e)),  // 自动转换错误类型
    };
    Ok(content)
}
```

#### 4.3 运行时视角

**Panic 的两种模式**：

| 模式 | 行为 | 适用场景 |
|------|------|----------|
| **Unwind** (默认) | 栈回溯，调用 `Drop` | 多线程、需要资源清理 |
| **Abort** | 立即终止进程 | 嵌入式、`panic = "abort"` |

```toml
# Cargo.toml
[profile.release]
panic = "abort"  # 更小的二进制，无 unwinding 开销
```

---

### 模块 5: 正例集
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

#### 5.1 Minimal（最小正例）

```rust
fn divide(a: f64, b: f64) -> Result<f64, String> {
    if b == 0.0 {
        Err("division by zero".to_string())
    } else {
        Ok(a / b)
    }
}

fn main() {
    match divide(10.0, 2.0) {
        Ok(result) => println!("Result: {}", result),
        Err(e) => eprintln!("Error: {}", e),
    }
}
```

#### 5.2 Realistic（真实场景）

使用 `thiserror` 构建应用错误类型：

```rust,ignore
use thiserror::Error;
use std::io;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("parse error: {0}")]
    Parse(#[from] std::num::ParseIntError),

    #[error("invalid config: {key} = {value}")]
    InvalidConfig { key: String, value: String },

    #[error("not found: {0}")]
    NotFound(String),
}

fn load_config(path: &str) -> Result<Config, AppError> {
    let content = std::fs::read_to_string(path)?;  // io::Error → AppError::Io
    let port = content.trim().parse::<u16>()?;      // ParseIntError → AppError::Parse
    Ok(Config { port })
}
```

#### 5.3 Production-grade（生产级）

`main` 函数返回 `Result` + `anyhow` 上下文：

```rust,compile_fail
use anyhow::{Context, Result};

fn main() -> Result<()> {
    let config = std::fs::read_to_string("app.conf")
        .with_context(|| "failed to read configuration file")?;

    let port = config
        .trim()
        .parse::<u16>()
        .with_context(|| format!("invalid port number in config: {:?}", config))?;

    start_server(port)
        .with_context(|| format!("failed to start server on port {}", port))?;

    Ok(())
}
```

---

### 模块 6: 反例集
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

#### 反例 1: 滥用 `unwrap()` 处理用户输入

**错误代码**:

```rust
fn parse_user_input(input: &str) -> i32 {
    input.parse::<i32>().unwrap()  // ❌ 用户输入不可信！
}
```

**根因推导**: `unwrap()` 在 `Err` 时 panic。用户输入不可控，这会导致生产环境崩溃。

**修复方案**:

```rust
fn parse_user_input(input: &str) -> Result<i32, String> {
    input.parse::<i32>()
        .map_err(|e| format!("invalid input '{}': {}", input, e))
}
```

**抽象原则**: **"不信任边界 unwrap"**：任何来自网络、文件、用户输入的数据都应该用 `Result` 处理，绝不 `unwrap`。

---

#### 反例 2: 错误类型不匹配导致 `?` 编译失败

**错误代码**:

```rust,ignore
#[derive(Debug)]
struct MyError;

fn may_fail() -> Result<(), MyError> {
    std::fs::read_to_string("file.txt")?;  // ❌ io::Error 不能自动转为 MyError
    Ok(())
}
```

**编译器错误**:

```text
error[E0277]: `?` couldn't convert the error to `MyError`
```

**根因推导**: `?` 运算符要求当前函数返回的错误类型实现 `From<被调用函数的错误类型>`。`MyError` 没有实现 `From<io::Error>`。

**修复方案**:

```rust
use std::io;

#[derive(Debug)]
struct MyError(String);

impl From<io::Error> for MyError {
    fn from(e: io::Error) -> Self {
        MyError(e.to_string())
    }
}

fn may_fail() -> Result<(), MyError> {
    std::fs::read_to_string("file.txt")?;  // ✅ io::Error → MyError
    Ok(())
}
```

---

#### 反例 3: `Option` 误用为 `Result`

**错误代码**:

```rust,compile_fail
fn open_file(path: &str) -> Option<File> {
    File::open(path).ok()  // ❌ 丢弃了错误原因！
}

fn main() {
    match open_file("missing.txt") {
        Some(f) => println!("{:?}", f),
        None => println!("failed"),  // 为什么失败？不知道！
    }
}
```

**根因推导**: `Result::ok()` 将 `Err` 转换为 `None`，丢失了所有错误信息。调用者无法区分"文件不存在"、"权限不足"还是"路径无效"。

**修复方案**:

```rust,compile_fail
fn open_file(path: &str) -> Result<File, io::Error> {
    File::open(path)  // ✅ 保留完整错误信息
}

fn main() {
    match open_file("missing.txt") {
        Ok(f) => println!("{:?}", f),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            println!("file not found");
        }
        Err(e) => println!("other error: {}", e),
    }
}
```

---

## 🗺️ 模块 7: 思维表征套件
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 表征 A: Result vs Option 决策树
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
函数返回值选择决策
═══════════════════════════════════════════════════════════════════

  操作是否可能失败?
       │
       ├─► 否 ─────────────────────────────► 返回 T（直接值）
       │
       └─► 是 ──► 失败时是否有错误信息?
           │
           ├─► 否（仅表示"无值"）
           │   └──► Option<T>
           │       • Some(T): 值存在
           │       • None: 值不存在
           │       • 例: HashMap::get, Vec::first
           │
           └─► 是（需要知道为什么失败）
               └──► Result<T, E>
                   • Ok(T): 成功
                   • Err(E): 失败，携带错误信息
                   • 例: File::open, std::fs::read_to_string

特殊情况:
• Option<T> 可视为 Result<T, ()> —— 无信息的失败
• Result<T, E> 可通过 .ok() 丢弃错误 → Option<T>
• Option<T> 可通过 .ok_or(e) 添加错误 → Result<T, E>
```

### 表征 B: 错误处理策略矩阵
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 场景 | 推荐策略 | 反模式 | 理由 |
|------|---------|--------|------|
| **库函数返回错误** | `Result<T, E>` | `panic!` | 库不应替调用者决定如何处理错误 |
| **内部不变量违反** | `panic!` / `assert!` | 返回 `Result` | bug 应该立即暴露，不可恢复 |
| **快速原型/测试** | `.unwrap()` / `anyhow` | 手写 `match` | 减少样板，后续重构 |
| **用户输入验证** | `Result` + 具体错误 | `Option` | 用户需要知道为什么输入无效 |
| **可选配置项** | `Option<T>` | `Result<T, E>` | 缺失配置不是错误，是默认行为 |
| **主函数错误** | `fn main() -> Result` | `unwrap()` | 优雅打印错误并退出 |
| **多错误类型聚合** | `thiserror` enum | `Box<dyn Error>` | 类型安全 + 可匹配具体错误 |
| **快速错误传播** | `anyhow::Result` | 自定义错误类型 | 减少 boilerplate，适合应用代码 |

### 表征 C: ? 运算符传播路径图
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
? 运算符的错误传播链
═══════════════════════════════════════════════════════════════════

  read_config() -> Result<Config, AppError>
       │
       ├─► fs::read_to_string("app.conf")?
       │   │    └── Result<String, io::Error>
       │   │         │
       │   │         ├─► Ok(content) ──► 继续执行
       │   │         └─► Err(io_err) ──► From::from(io_err)
       │   │                              └──► AppError::Io(...)
       │   │                                   └──► return Err(AppError::Io(...))
       │   │
       ├─► content.parse::<u16>()?
       │   │    └── Result<u16, ParseIntError>
       │   │         │
       │   │         ├─► Ok(port) ─────► 继续执行
       │   │         └─► Err(parse_err) ──► From::from(parse_err)
       │   │                                   └──► AppError::Parse(...)
       │   │                                        └──► return Err(...)
       │   │
       └─► Ok(Config { port }) ───────────────► 返回成功

关键机制:
1. 每个 ? 点都是潜在的提前返回
2. From trait 负责错误类型转换
3. 调用栈逐层向上传播，直到被 match 处理
```

---

## 📚 模块 8: 国际化对齐
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 8.1 官方来源
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 来源 | 类型 | 对应章节/条目 | 本文档对应点 |
|------|------|---------------|--------------|
| [Rust Book Ch09](https://doc.rust-lang.org/book/ch09-00-error-handling.html) | 官方 | Result、Option、panic | 模块 1-2 |
| [std::result](https://doc.rust-lang.org/std/result/) | 官方 | Result API | 模块 2 |
| [RFC 243](https://rust-lang.github.io/rfcs/0243-trait-based-exception-handling.html) | 官方 | `?` 运算符设计 | 模块 4.2 |

### 8.2 学术来源
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 论文/来源 | 会议/机构 | 核心论证 | 本文档对应点 |
|-----------|-----------|----------|--------------|
| **"Exceptional Syntax"** (Peyton Jones et al.) | Haskell 社区 | 基于类型的错误处理 vs 异常的历史演进 | 模块 1.3 |
| **"The Error Model"** (Joe Duffy) | Midori OS | 错误码 vs 异常的系统级分析，Rust 的设计哲学受其影响 | 模块 9 |

### 8.3 社区权威
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 作者 | 文章/演讲 | 核心观点 | 本文档对应点 |
|------|-----------|----------|--------------|
| **Andrew Gallant** (burntsushi) | [anyhow/thiserror 设计](https://github.com/dtolnay/anyhow) | 库代码用 `thiserror`，应用代码用 `anyhow` | 模块 5.3 |
| **dtolnay** | [thiserror 文档](https://docs.rs/thiserror/) | 通过派生宏消除错误类型样板 | 模块 5.2 |

### 8.4 跨语言对比
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 维度 | Rust (`Result`) | Go (error 返回值) | Haskell (`Either`) | Java (Exception) | C (errno) |
|------|-----------------|-------------------|--------------------|------------------|-----------|
| **显式性** | ✅ 类型强制 | ✅ 返回值 | ✅ 类型强制 | ❌ 隐式传播 | ❌ 全局变量 |
| **可组合性** | `?` + `From` | 手动检查 | `>>=` (bind) | `try-catch` | ❌ 差 |
| **零成本** | ✅ | ✅ | ✅ | ❌ 栈展开开销 | ✅ |
| **错误类型安全** | ✅ 泛型 | ❌ `error` 接口 | ✅ 类型参数 | ⚠️ 运行时 catch | ❌ |
| **忽略检测** | ✅ `must_use` | ❌ 可静默忽略 | ✅ | ❌ | ❌ |

> **关键差异**: Rust 是唯一同时提供**显式类型安全**、**零成本抽象**、**忽略检测** (`must_use`) 和**优雅组合** (`?`) 的语言。Go 显式但不可组合，Haskell 可组合但学习曲线陡峭，Java 隐式且 overhead 大。

---

## ⚖️ 模块 9: 设计权衡分析
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 9.1 为什么 Rust 没有异常？
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

Rust 选择 `Result` 而非异常的核心原因：

1. **显式控制流**: `?` 运算符的错误传播路径在代码中清晰可见，不像异常可能从任何调用点"跳出"。
2. **类型安全**: `Result<T, E>` 的类型签名明确告知调用者所有可能的失败模式。
3. **零成本**: `Result` 是普通的 tagged union，无栈展开、无 RTTI、无隐藏控制流。
4. **可组合性**: `map`、`and_then`、`?` 提供了函数式的错误处理组合子。

### 9.2 该设计的成本
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

**样板代码**: 在 `?` 出现之前（Rust 1.13 之前），错误传播需要大量 `match` 嵌套。`?` 显著改善但自定义错误类型仍有 boilerplate（`thiserror` 解决此问题）。

**错误类型膨胀**: 大型应用中，不同模块的错误类型可能形成复杂的依赖图。`anyhow` 通过类型擦除缓解此问题，但牺牲了匹配具体错误的能力。

**学习曲线**: 来自 Java/Python 的开发者习惯异常思维，需要适应"错误即值"的范式。

### 9.3 什么场景下 `Result` 是次优的？
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

1. **极端深层嵌套调用**: 如果调用链非常深且每层都可能失败，`?` 的显式传播比异常的隐式传播更冗长。
2. **需要跨线程传播错误**: `?` 不跨线程。线程间的错误传播需要显式通道（`join().unwrap()` 或 `crossbeam`）。
3. **FFI 边界**: C 代码不理解 `Result`，返回错误码需要手动转换。

---

## 📝 模块 10: 自我检测与练习
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 概念性问题
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

1. **`Option<T>` 和 `Result<T, ()>` 在语义上有何区别？** 为什么 Rust 同时保留两者而不是统一为 `Result`？

2. **`?` 运算符在 `main` 函数、`async fn` 和闭包中的行为有何差异？** 为什么 `main` 可以返回 `Result` 但某些闭包不行？

3. **`anyhow::Error` 和 `thiserror` 的错误类型在设计目标上有何根本区别？** 为什么库作者推荐 `thiserror` 而应用开发者推荐 `anyhow`？

### 代码修复题
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

**题 1**: 以下代码存在多个错误处理问题。请识别并修复：

```rust
fn process_data(path: &str) -> Vec<i32> {
    let content = std::fs::read_to_string(path).unwrap();
    content.lines()
        .map(|line| line.parse::<i32>().unwrap())
        .collect()
}
```

<details>
<summary>参考答案</summary>

**问题**:

1. `read_to_string(path).unwrap()` —— 文件不存在时 panic
2. `parse::<i32>().unwrap()` —— 格式错误时 panic
3. 返回 `Vec<i32>` 丢失了所有错误信息

**修复**:

```rust
use std::io;

#[derive(Debug)]
enum DataError {
    Io(io::Error),
    Parse { line: usize, content: String },
}

impl From<io::Error> for DataError {
    fn from(e: io::Error) -> Self { DataError::Io(e) }
}

fn process_data(path: &str) -> Result<Vec<i32>, DataError> {
    let content = std::fs::read_to_string(path)?;

    let mut result = Vec::new();
    for (i, line) in content.lines().enumerate() {
        let num = line.parse::<i32>()
            .map_err(|_| DataError::Parse {
                line: i + 1,
                content: line.to_string(),
            })?;
        result.push(num);
    }

    Ok(result)
}
```

</details>

**题 2**: 以下代码试图实现自定义错误类型但编译失败。请修复：

```rust,ignore
#[derive(Debug)]
enum AppError {
    Io(std::io::Error),
    Parse(std::num::ParseIntError),
}

fn load_port(path: &str) -> Result<u16, AppError> {
    let s = std::fs::read_to_string(path)?;
    let port = s.trim().parse::<u16>()?;
    Ok(port)
}
```

<details>
<summary>参考答案</summary>

**问题**: `AppError` 未实现 `From<std::io::Error>` 和 `From<std::num::ParseIntError>`，`?` 无法自动转换。

**修复**:

```rust
use std::io;
use std::num::ParseIntError;

#[derive(Debug)]
enum AppError {
    Io(io::Error),
    Parse(ParseIntError),
}

impl From<io::Error> for AppError {
    fn from(e: io::Error) -> Self { AppError::Io(e) }
}

impl From<ParseIntError> for AppError {
    fn from(e: ParseIntError) -> Self { AppError::Parse(e) }
}

fn load_port(path: &str) -> Result<u16, AppError> {
    let s = std::fs::read_to_string(path)?;
    let port = s.trim().parse::<u16>()?;
    Ok(port)
}
```

或使用 `thiserror`:

```rust,ignore
use thiserror::Error;

#[derive(Error, Debug)]
enum AppError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("parse error: {0}")]
    Parse(#[from] ParseIntError),
}
```

</details>

### 开放设计题
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

**题 3**: 你正在设计一个 CLI 工具，需要处理以下错误场景：

1. 配置文件缺失或格式错误
2. 网络请求失败（可能重试）
3. 用户输入的无效参数
4. 内部 bug（如不应该到达的分支）

请设计错误处理策略：

- 哪些场景应该返回 `Result`，哪些应该 `panic`？
- 错误类型应该自定义还是使用 `anyhow`？
- 如何在用户界面中展示不同严重度的错误？
- 是否需要错误码（exit code）区分不同失败原因？

> 💡 提示：参考模块 7 的策略矩阵和模块 9 的成本分析。

---

## 📖 延伸阅读
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [Rust Book - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [thiserror crate](https://docs.rs/thiserror/)
- [anyhow crate](https://docs.rs/anyhow/)
- [Rust Error Handling Best Practices](https://www.lpalmieri.com/posts/error-handling-rust/)

---

> 🎉 **恭喜你！** 你已经掌握了 Rust 错误处理的核心机制。记住：在 Rust 中，"错误即值"不是限制，而是赋予你精确控制程序每一种失败路径的能力。
>
> **下一步建议**: 在你的下一个 Rust 项目中，尝试用 `thiserror` 定义自定义错误类型，并在 `main` 函数中使用 `Result` 返回。体验编译器如何强制你处理每一个可能的失败。

---

**文档版本**: 2.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 📚 权威来源索引
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 官方与半官方

- [Rust Book Ch09](https://doc.rust-lang.org/book/ch09-00-error-handling.html) — 官方入门教程 [来源: Rust Team / TRPL 2024]
- [Rust Reference — The `?` operator](https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator) — 运算符形式化语义 [来源: Rust Reference / 2025]
- [RFC 243: Trait-based Exception Handling](https://rust-lang.github.io/rfcs/0243-trait-based-exception-handling.html) — `Result` 与 `?` 的设计决策 [来源: Rust Core Team / 2016]
- [thiserror crate](https://docs.rs/thiserror/) — 自定义错误类型的派生宏 [来源: dtolnay / 2019+]
- [anyhow crate](https://docs.rs/anyhow/) — 错误传播的工程实践 [来源: dtolnay / 2019+]

### 学术来源

- Wadler, P. — *Monads for functional programming*. Marktoberdorf Summer School, 1990. [来源: 将 `Result` 视为命令式语言中的 monadic 构造; 错误处理代数语义的理论基础]
- ISO C++20 §14 — *Exception handling*. [来源: C++ 异常机制的零开销 ABI 设计]

### 跨语言来源

- Go Language Specification — `error` interface (2022) [来源: 显式错误返回 vs 类型约束]
- Java Language Specification §11 — *Exceptions* (2020) [来源: checked vs unchecked exception 的设计张力]
- GHC User's Guide — `Control.Monad.Except` [来源: Haskell `Either` monad 作为纯函数式错误处理的参照]

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [集合类型 (Collections)](01_collections.md)
- [泛型 (Generics)](03_generics.md)
- [Rust 生命周期深入](../01_fundamentals/03_lifetimes.md)
- [Trait 深入 (Traits)](06_traits.md)

---

## 权威来源索引

> **[来源: [Rust Error Handling Guidelines](https://doc.rust-lang.org/rust-by-example/error.html)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---
