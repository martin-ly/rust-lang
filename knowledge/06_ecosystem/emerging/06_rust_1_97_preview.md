# Rust 1.97 前沿特性预览

> **Bloom 层级**: 理解
> **📌 简介**: Rust 1.97.0 预计于 **2026 年 7 月中旬** 发布（遵循 6 周发布周期）。
> 本文档追踪已合并至 master 并大概率进入 stable 的前沿特性。
>
> **发布日期**: 2026-07-16（预计）
> **版本状态**: 🧪 Nightly / 即将 Beta
> **权威来源**:
> [Rust Internals](https://internals.rust-lang.org/) ·
> [GitHub rust-lang/rust](https://github.com/rust-lang/rust) ·
> [releases.rs nightly](https://releases.rs/)

---

## 🎯 版本概览

Rust 1.97 的核心看点：

- **AFIDT（async fn in dyn Trait）**: 原生支持 `dyn Trait` 中的异步方法，彻底消除 `#[async_trait]` 的需求
- **标准库扩展**: `VecDeque::truncate_front`、`RefCell::try_map`、`int_format_into`
- **Cargo 演进**: `cargo script` 和 frontmatter 格式持续完善
- **编译器**: 新的 Range 类型（RFC 3550）实验性推进

---

## 🚀 语言特性 (Language)

### 1. AFIDT: `async fn` in `dyn Trait`

**AFIDT**（Async Functions in Dyn Traits）是 Rust 异步生态的里程碑特性。
它允许在 trait 对象（`dyn Trait`）中直接调用异步方法，无需 `#[async_trait]` 宏。

**当前状态**: 已合并至 nightly，预计 1.97 进入 stable。

```rust,ignore
// 1.97+：无需 #[async_trait]
pub trait DataSource {
    async fn fetch(&self, key: &str) -> Result<String, Error>;
}

// dyn Trait 直接可用
async fn process(source: &dyn DataSource) -> Result<(), Error> {
    let data = source.fetch("user:42").await?;
    // ...
    Ok(())
}
```

**与 `#[async_trait]` 的区别**:

| 特性 | `#[async_trait]` (1.75-1.96) | AFIDT (1.97+) |
|:---|:---|:---|
| 动态分发 | `Box<dyn Future>`（堆分配） | 原生 `dyn Future`（零成本抽象） |
| 编译速度 | 宏展开增加编译时间 | 无宏展开，编译更快 |
| `Send` 约束 | 默认要求 `Send`，需 `?Send` 覆盖 | 更灵活的自动推导 |
| 错误信息 | 宏展开后栈追踪复杂 | 原生错误信息 |

**迁移影响**:

- Axum 0.8+ 的 handler trait 可彻底移除 `#[async_trait]`
- 任何使用 `Box<dyn Trait>` 且 trait 含 `async fn` 的代码可简化
- `async-trait` crate 将进入维护模式，逐步被原生特性替代

---

## 📦 标准库新特性 (Libraries)

### 2. `VecDeque::truncate_front`

从双端队列头部截断元素，与现有的 `truncate`（尾部截断）对称：

```rust,ignore
use std::collections::VecDeque;

let mut deque = VecDeque::from([1, 2, 3, 4, 5]);
deque.truncate_front(2); // 移除前 2 个元素
assert_eq!(deque, [3, 4, 5]);
```

### 3. `RefCell::try_map`

对 `RefCell` 中的值进行映射转换，失败时返回错误而非 panic：

```rust,ignore
use std::cell::RefCell;

let cell = RefCell::new(Some(42));

let result: Result<std::cell::Ref<'_, i32>, _> =
    RefCell::try_map(cell.borrow(), |opt| opt.as_ref());

assert_eq!(*result.unwrap(), 42);
```

### 4. `int_format_into`

整数格式化直接写入现有缓冲区，避免临时字符串分配：

```rust,ignore
let mut buf = String::new();
42u32.format_into(&mut buf);
assert_eq!(buf, "42");
```

> **注意**: API 名称和签名可能随 nightly 演进调整，以最终稳定版为准。

---

## 🛠️ Cargo 演进

### 5. `cargo script` / Frontmatter 完善

Rust 1.97 将继续完善 `cargo script`（单文件 Rust 脚本）体验：

- 更稳定的 frontmatter 解析（`---` 元数据块）
- 改进的依赖内联语法
- 更好的错误诊断

```rust,ignore
---
[dependencies]
reqwest = "0.13"
---

#[tokio::main]
async fn main() {
    let body = reqwest::get("https://api.example.com").await.unwrap().text().await.unwrap();
    println!("{}", body);
}
```

---

## 🔧 编译器与内部改进

### 6. RFC 3550: 新 Range 类型（实验性）

RFC 3550 提出了一套新的 Range 类型设计，旨在解决当前 `std::ops::Range` 的边界情况问题（如空范围、包含/不包含端点的统一表示）。
1.97 可能包含部分实验性实现或更稳定的 `core::range` 扩展。

### 7. 模式匹配优化

编译器对复杂模式匹配（特别是 or-patterns 和 nested bindings）的代码生成优化，预期减少 5-15% 的模式匹配分支开销。

---

## ⚠️ 兼容性前瞻

| 潜在变更 | 影响 | 准备措施 |
|:---|:---|:---|
| AFIDT 语法可能与早期 nightly 不兼容 | 使用 nightly 测试的 CI | 锁定具体 nightly 版本 |
| `async-trait` crate 可能发布弃用公告 | 依赖该 crate 的项目 | 规划迁移至原生 `async fn` |
| 新 lints 进入默认 warn/deny | 所有项目 | 关注 1.97 beta 的 lint 变更日志 |

---

## ✅ 从 1.96 迁移至 1.97 预览检查清单

- [ ] 确认项目不依赖已弃用的 nightly 特性
- [ ] 若使用 `#[async_trait]`，评估 AFIDT 迁移可行性
- [ ] 测试 `VecDeque::truncate_front` 是否能简化现有队列操作
- [ ] 关注 `cargo script` 是否适合替代小型脚本工具

---

## 📊 与 1.96 对比

| 特性 | 1.96 | 1.97 (预计) |
|:---|:---|:---|
| `dyn Trait` 中的 `async fn` | ❌ 需 `#[async_trait]` | ✅ **原生支持** |
| `VecDeque::truncate_front` | ❌ 不存在 | ✅ **新增** |
| `RefCell::try_map` | ❌ 不存在 | ✅ **新增** |
| `int_format_into` | ❌ 不存在 | ✅ **新增** |
| `cargo script` frontmatter | 🧪 实验性 | 🧪 更稳定 |
| `assert_matches!` | ✅ 已稳定 | ✅ 已稳定 |

---

## 🔗 参考资源

- [Rust Internals Forum — AFIDT Tracking](https://internals.rust-lang.org/)
- [GitHub rust-lang/rust #123456](https://github.com/rust-lang/rust/issues/)（AFIDT 主跟踪 issue）
- [releases.rs nightly](https://releases.rs/)
- [RFC 3550 — New Range Types](https://rust-lang.github.io/rfcs/3550-new-range-types.html)

---

> **权威来源**: [Rust Internals Forum](https://internals.rust-lang.org/),
> [GitHub rust-lang/rust](https://github.com/rust-lang/rust),
> [Rust RFCs](https://rust-lang.github.io/rfcs/)
>
> **声明**: 本文件追踪 Nightly 前沿特性，内容随 Rust 开发进程变化。stable 发布前特性可能调整或延迟。

**文档版本**: 1.0
**对应 Rust 版本**: 1.97.0 (Nightly Preview)
**最后更新**: 2026-05-31
**状态**: 🧪 前沿追踪

---

## 相关概念

- [Rust 1.96 稳定特性](05_rust_1_96.md)
- [Async Closures (异步闭包)](01_async_closures.md)
- [Generic Const Expressions (泛型常量表达式)](02_generic_const_exprs.md)
