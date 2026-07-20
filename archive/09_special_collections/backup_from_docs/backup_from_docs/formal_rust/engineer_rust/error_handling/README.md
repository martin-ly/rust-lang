# 错误处理（Error Handling）

## 1. 定义与软件工程对标

**错误处理**是指系统在运行时对异常或不可预期情况的检测、报告与恢复。软件工程wiki强调，健壮的错误处理机制是高可靠性系统的基础。
**Error handling** refers to detecting, reporting, and recovering from exceptional or unexpected conditions at runtime. Robust error handling is fundamental for reliable systems in software engineering.

## 2. Rust 1.88 最新特性

- **`try_blocks`**：块级错误传播，简化复杂流程。
- **`#[expect]`属性**：可控lint，提升开发体验。
- **`anyhow`/`thiserror`**：主流错误链与自定义错误类型。

## 3. 典型惯用法（Idioms）

- 使用 `Result`/`Option` 明确错误边界
- `?` 运算符简化错误传播
- `anyhow`/`thiserror` 统一错误链
- `panic::catch_unwind` 捕获不可恢复错误

## 4. 代码示例（含1.88新特性）

```rust
// try_blocks 新特性
fn parse_and_double(s: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let res = try {
        let n: i32 = s.parse()?;
        n * 2
    };
    res
}

// #[expect] 属性
#[expect(unused_variables)]
fn foo() {
    let x = 1;
}
```

## 5. 软件工程概念对照

- **异常安全（Exception Safety）**：Rust 强制显式错误处理，防止遗漏。
- **错误分层（Error Layering）**：业务/系统/依赖错误分层，便于定位。
- **可恢复与不可恢复错误**：Result/Option vs panic!。

## 6. FAQ

- Q: Rust 如何实现统一的错误链？
  A: 推荐使用 `thiserror`/`anyhow`，支持自动转换和链式追踪。

---

## 理论基础

- 错误类型与分层（可恢复/不可恢复）
- 显式错误与隐式错误传播
- 错误边界与异常安全
- 错误语义与错误码设计

## 工程实践

- Rust 错误处理机制（Result、Option、panic! 等）
- 自定义错误类型与错误链
- anyhow、thiserror 等主流库实践
- 错误日志与追踪
- 错误与 API 设计、用户体验

## 形式化要点

- 错误传播路径的形式化建模
- 错误边界与恢复策略的可验证性
- 错误类型系统的正确性证明

## 推进计划

1. 理论基础与错误模型梳理
2. Rust 错误处理机制与工程实践
3. 形式化建模与恢复策略验证
4. 错误链与日志追踪集成
5. 推进快照与断点恢复

## 断点快照

- [x] 目录结构与 README 初稿
- [ ] 理论基础与错误模型补全
- [ ] 工程案例与代码片段
- [ ] 形式化建模与验证
- [ ] 交叉引用与持续完善

---

## 深度扩展：理论阐释

### 错误类型与分层

- 可恢复错误（Result）、不可恢复错误（panic!）。
- 错误分层：业务错误、系统错误、外部依赖错误。
- Rust 强制显式错误处理，提升健壮性。

### 显式错误与隐式错误传播

- ? 运算符简化错误传播链。
- anyhow/thiserror 支持自定义错误类型与错误链。

### 错误边界与异常安全

- 错误边界用于隔离错误影响范围，防止异常蔓延。
- panic::catch_unwind 可捕获 panic，防止线程崩溃。

### 错误语义与错误码设计

- 错误类型应表达语义，便于定位与处理。
- 错误码设计需兼顾可扩展性与可维护性。

---

## 深度扩展：工程代码片段

### 1. 基本错误处理

```rust
fn parse_num(s: &str) -> Result<i32, std::num::ParseIntError> {
    s.parse()
}
```

### 2. ? 运算符与错误传播

```rust
fn double_num(s: &str) -> Result<i32, std::num::ParseIntError> {
    let n = s.parse()?;
    Ok(n * 2)
}
```

### 3. 自定义错误类型与错误链

```rust
use thiserror::Error;
#[derive(Error, Debug)]
pub enum MyError {
    #[error("Parse error: {0}")]
    Parse(#[from] std::num::ParseIntError),
    #[error("Other error: {0}")]
    Other(String),
}
```

### 4. panic 捕获与边界

```rust
use std::panic;
let result = panic::catch_unwind(|| {
    panic!("崩溃");
});
assert!(result.is_err());
```

---

## 深度扩展：典型场景案例

### 配置文件解析与错误链

- 多层错误通过 thiserror/anyhow 自动转换与链式追踪。

### API 服务错误分层

- 业务错误、系统错误、外部依赖错误分层处理，提升可维护性。

### 并发与异步下的错误处理

- 异步任务错误通过 JoinHandle::join/await 统一收集。

---

## 深度扩展：形式化证明与自动化测试

### 形式化证明思路

- Rust 类型系统强制显式错误处理，防止遗漏。
- 错误链与边界可用自动化测试覆盖。

### 自动化测试用例

```rust
#[test]
fn test_double_num() {
    assert_eq!(double_num("2"), Ok(4));
    assert!(double_num("abc").is_err());
}
```
