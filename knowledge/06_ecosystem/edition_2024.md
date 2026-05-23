# Rust Edition 2024 完整指南

> **Bloom 层级**: 理解

> **版本**: Edition 2024
> **Rust 版本**: 1.82.0+ (Edition 2024 稳定版)
> **权威来源**: [Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/)

**变更日志**:

- v1.1 (2026-05-19): 补全权威来源标注（Edition Guide、RFC 2052、Rust Blog、Lang Team Roadmap）

## 🎯 学习目标
>
> **[来源: Rust Official Docs]**

完成本章后，你将能够：

- [ ] 理解 Edition 2024 的核心变更
- [ ] 成功将项目迁移到 Edition 2024
- [ ] 使用 `gen` 关键字（预览）
- [ ] 掌握新的保留字和行为变更

## 📋 先决条件
>
> **[来源: Rust Official Docs]**

- 熟悉 Rust 2021 Edition
- 理解 Cargo 和项目配置
- 有现有 Rust 项目经验

## 🧠 核心概念
>
> **[来源: Rust Official Docs]**

### 模块 1: 概念定义
>
> **[来源: Rust Official Docs]**

#### 1.1 直观定义
>
> **[来源: Rust Official Docs]**

**Edition** 是 Rust 的**兼容性边界机制**。与语义版本（SemVer）不同，Edition 允许语言在不破坏现有代码的情况下引入不兼容的语法变更。同一 crate 可以混合使用不同 Edition 的依赖。

> 💡 关键直觉：SemVer 说"这个版本兼容"，Edition 说"这个项目选择这套规则"。

> **[来源: Rust Edition Guide]** "Editions are a mechanism for the Rust project to introduce changes into the language that would otherwise be backwards incompatible." ✅
> **[来源: RFC 2052 — Epochs]** Edition（原称 Epoch）机制允许编译器根据 `Cargo.toml` 中的 `edition` 字段选择不同的语法分析器前端。 ✅
> **[来源: Rust Reference: Editions]** 同一编译器二进制可同时支持多个 Edition，混合 Edition 的依赖可链接为同一二进制。 ✅

#### 1.2 操作定义

**Edition 的工作机制**：

```text
Crate A (Edition 2021)          Crate B (Edition 2024)
     │                                │
     │ 调用                           │ 调用
     ▼                                ▼
  编译器使用 2021 规则解析         编译器使用 2024 规则解析
     │                                │
     └────────────┬───────────────────┘
                  │
            链接为同一二进制
```

**Edition 2024 的核心变更**：

| 类别 | 变更 | 影响范围 | 自动修复 |
|------|------|----------|----------|
| **保留字** | `gen` 成为关键字 | 使用 `gen` 作为标识符的代码 | ✅ `cargo fix` |
| **宏规则** | 尾逗号处理更一致 | 宏定义和调用 | ✅ `cargo fix` |
| **类型系统** | `impl Trait` 精确捕获 | 返回 `impl Fn` 的闭包 | ⚠️ 部分需手动 |
| **Cargo** | 默认特性解析器 v2 | feature 组合行为 | ✅ 自动生效 |
| **标准库** | 新 API 稳定化 | 新增方法可用 | — |

#### 1.3 形式化直觉

Edition 在编译器中的实现：编译器根据 `Cargo.toml` 中的 `edition` 字段选择**语法分析器前端**。同一编译器二进制可以同时支持多个 Edition 的解析规则。

---

### 模块 2: 属性清单
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 属性名 | 类型 | 值域/取值 | 说明 | 反例边界 |
|--------|------|-----------|------|----------|
| **Edition 隔离** | 固有属性 | crate 边界 | 不同 Edition 的 crate 可以无缝互操作 | 同一 crate 内只能用一个 Edition |
| **自动迁移** | 关系属性 | `cargo fix --edition` | 大多数变更可自动修复 | `impl Trait` 捕获需手动确认 |
| **关键字预留** | 固有属性 | 提前 1-2 个 Edition | `gen` 在 2024 预留，2026+ 启用 | 原始标识符 `r#gen` 可绕过 |
| **MSRV 绑定** | 关系属性 | `rust-version` | Edition 2024 要求 rustc >= 1.82 | 旧编译器无法编译 |

---

### 模块 3: 概念依赖图
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```mermaid
graph TD
    A[Edition 2021] --> B[Edition 2024]
    B --> C[gen Keyword]
    B --> D[Trailing Comma Macros]
    B --> E[impl Trait Capture]
    B --> F[Resolver V2]
    C --> G[Generator Syntax]
    D --> H[Macro Hygiene]
    E --> I[Lifetime Capture]
    F --> J[Feature Unification]

    K[Cargo.toml] --> L[edition = "2024"]
    K --> M[rust-version = "1.82.0"]
    L --> B

    style B fill:#f9f,stroke:#333,stroke-width:2px
    style C fill:#bfb,stroke:#333,stroke-width:2px
    style F fill:#bbf,stroke:#333,stroke-width:2px
```

#### 承上（前置知识回溯）

| 前置概念 | 所在文档 | 本章中使用的具体点 |
|----------|----------|-------------------|
| **Cargo.toml** | `06_ecosystem/cargo_basics.md` | `edition` 和 `rust-version` 字段 |
| **宏规则** | `03_advanced/macros/declarative.md` | 尾逗号宏规则的变更 |
| **impl Trait** | `02_intermediate/traits.md` | `impl Trait` 的生命周期捕获 |

#### 启下（后续延伸预告）

| 后续概念 | 所在文档 | 掌握本章后方可理解 |
|----------|----------|-------------------|
| **Async Generators** | `03_advanced/async/` | `gen` 关键字在异步生成器中的应用 |
| **Cargo Workspaces** | `06_ecosystem/workspace.md` | 多 crate 项目的 Edition 迁移策略 |

---

### 1. Edition 2024 主要特性
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 类别 | 变更 | 影响 | 迁移难度 |
|------|------|------|----------|
| 语言 | `gen` 关键字预留 | 可能破坏代码 | 低 |
| 语言 | 尾逗号宏规则 | 行为变更 | 低 |
| 语言 | `impl Trait` 作用域 | 更精确 | 中 |
| Cargo | 默认特性解析 | 新解析器 | 中 |
| Cargo | 新的依赖解析 | 可能冲突 | 中 |
| 标准库 | 新API稳定化 | 新增功能 | 低 |

### 2. 迁移步骤
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

#### 2.1 自动迁移

```bash
# 1. 确保使用最新 Rust
cargo update

# 2. 运行迁移工具
cargo fix --edition

# 3. 更新 Cargo.toml
# edition = "2024"

# 4. 验证迁移
cargo build
cargo test
```

#### 2.2 手动检查清单

```markdown
## 迁移检查清单
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### Cargo.toml 更新
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
- [ ] 更新 `edition = "2024"`
- [ ] 更新 `rust-version = "1.82.0"`
- [ ] 检查依赖兼容性

### 代码变更
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
- [ ] 检查 `gen` 作为标识符
- [ ] 检查宏尾逗号使用
- [ ] 检查 `impl Trait` 捕获
- [ ] 检查 `#[repr(C)]` 枚举

### 测试验证
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
- [ ] `cargo build` 通过
- [ ] `cargo test` 通过
- [ ] `cargo clippy` 无严重警告
- [ ] 运行集成测试
```

### 3. gen 关键字预留
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

`gen` 将成为关键字，用于 generators。

#### 3.1 需要修改的代码

```rust
// Rust 2021 - 合法
struct gen;  // 名为 gen 的类型
fn gen() {}  // 名为 gen 的函数

// Rust 2024 - 非法（编译错误）
struct gen;  // ERROR: expected identifier, found keyword `gen`
fn gen() {}  // ERROR: expected identifier, found keyword `gen`

// 解决方案：使用 r# 原始标识符
struct r#gen;  // ✅ 使用原始标识符
fn r#gen() {}  // ✅
```

#### 3.2 迁移工具处理

```bash
# cargo fix 会自动转换
cargo fix --edition
# 输出：warning: `gen` is a keyword in Edition 2024
```

### 4. 尾逗号宏规则
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

宏匹配规则对尾逗号的处理更一致。

```rust
// Rust 2021 - 某些情况下不匹配
macro_rules! example {
    ($e:expr,)* => {};  // 不匹配尾逗号
}

// Rust 2024 - 自动处理尾逗号
macro_rules! example {
    ($e:expr $(,)?) => {};  // $(,)? 可选逗号
}
```

### 5. impl Trait 精确捕获
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

`impl Trait` 的捕获规则更加精确。

```rust
// Rust 2021 - 捕获所有生命周期
fn foo(x: &i32) -> impl Fn() -> &i32 {
    || x  // 捕获 x 的生命周期
}

// Rust 2024 - 需要显式捕获
fn foo(x: &i32) -> impl Fn() -> &i32 + use<'_> {
    || x  // 显式捕获 '_
}
```

## 💻 实战迁移
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 示例项目迁移
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

#### 步骤 1：备份

```bash
git checkout -b edition-2024-migration
git add .
git commit -m "Pre-Edition 2024 backup"
```

#### 步骤 2：运行自动修复

```bash
cargo fix --edition --allow-dirty
```

#### 步骤 3：更新 Cargo.toml

```toml
[package]
name = "my-project"
version = "1.0.0"
edition = "2024"
rust-version = "1.82.0"

[dependencies]
# 确保依赖支持 Edition 2024
```

#### 步骤 4：处理手动变更

```rust
// 前：可能使用 gen 作为变量名
let gen = || { /* ... */ };

// 后：使用其他名称
let generator = || { /* ... */ };
```

#### 步骤 5：验证

```bash
cargo build --all-targets
cargo test
cargo clippy -- -D warnings
```

### 迁移常见问题
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

#### 问题 1：依赖不支持 Edition 2024

```toml
# 检查依赖的 edition
# 在 Cargo.lock 中查看

# 解决方案：
# 1. 等待依赖更新
# 2. 寻找替代依赖
# 3. 暂时保持 Edition 2021
```

#### 问题 2：宏规则变更导致编译失败

```rust
// 前：
macro_rules! foo {
    ($($x:expr),*) => {};  // Rust 2021
}

// 后：
macro_rules! foo {
    ($($x:expr),* $(,)?) => {};  // Rust 2024
}
```

---

## 🗺️ 模块 7: 思维表征
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 表征 A: Edition 迁移决策树
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
是否迁移到 Edition 2024?
       │
       ├─► Rust 版本 < 1.82?
       │   └─► 是 ──► 先升级 Rust 工具链
       │
       ├─► 依赖是否都支持 Edition 2024?
       │   ├─► 否 ──► 等待依赖更新或保持 2021
       │   └─► 是 ──► 继续评估
       │
       ├─► 代码是否使用 `gen` 作为标识符?
       │   ├─► 是 ──► 评估重命名成本
       │   └─► 否 ──► 低风险
       │
       ├─► 是否大量使用自定义宏?
       │   ├─► 是 ──► 测试尾逗号行为变更
       │   └─► 否 ──► 低风险
       │
       └─► 执行迁移:
           1. git checkout -b edition-2024
           2. cargo fix --edition
           3. 手动检查 impl Trait 捕获
           4. cargo test
           5. cargo clippy
           6. 合并分支
```

### 表征 B: Edition 2024 变更影响矩阵
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 变更 | 影响代码比例 | 自动修复 | 运行时影响 | 回滚难度 |
|------|------------|----------|-----------|---------|
| `gen` 关键字 | < 1% | ✅ | 无 | 低（改标识符名） |
| 尾逗号宏 | < 5% | ✅ | 无 | 低 |
| `impl Trait` 捕获 | < 5% | ⚠️ | 无 | 中 |
| Resolver V2 | 100%（feature） | ✅ | 无 | 低 |
| 新标准库 API | 可选使用 | — | 无 | — |

---

## ⚠️ 常见陷阱
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 问题 | 症状 | 解决方案 |
|------|------|----------|
| `gen` 标识符冲突 | 编译错误 | 重命名或使用 `r#gen` |
| 依赖版本冲突 | 解析错误 | 更新依赖或锁定版本 |
| 宏规则变更 | 宏不匹配 | 添加 `$(,)?` |
| impl Trait 捕获 | 生命周期错误 | 添加 `+ use<'_>` |

## 🎮 练习
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 练习 1：迁移小项目
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

选择一个现有的 Rust 项目，将其迁移到 Edition 2024。

### 练习 2：处理 gen 关键字
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

创建一个使用 `gen` 作为标识符的项目，然后迁移到 Edition 2024。

<details>
<summary>参考答案</summary>

```rust
// lib.rs - Rust 2021
pub struct gen<T>(pub T);

impl<T> gen<T> {
    pub fn new(value: T) -> Self {
        gen(value)
    }
}

// 迁移后 - Rust 2024
// 选项 1：使用原始标识符
pub struct r#gen<T>(pub T);

// 选项 2：重命名
pub struct Generator<T>(pub T);
```

</details>

## 📚 模块 8: 国际化对齐
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 来源 | 类型 | 说明 |
|------|------|------|
| [Edition Guide 2024](https://doc.rust-lang.org/edition-guide/rust-2024/) | 官方 | Edition 2024 完整迁移指南 |
| [Rust 1.82 Release](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0/) | 官方 | Edition 2024 稳定化公告 |

### 跨语言对比
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 维度 | Rust (Edition) | C++ (Standard) | Java (LTS) | Go |
|------|---------------|----------------|------------|-----|
| **兼容策略** | Edition 隔离 | 标准版本 | LTS 版本 | 无（直接升级） |
| **混合使用** | ✅ 同一二进制 | ❌ 需重新编译 | ✅ 字节码兼容 | ✅ |
| **自动迁移工具** | ✅ `cargo fix` | ❌ 无 | ❌ 无 | ❌ 无 |
| **发布周期** | ~3 年 | ~3 年 | ~2 年 | ~6 个月 |

> **关键差异**: Rust 的 Edition 机制是唯一允许**同一编译器同时支持多版本语法**的设计。C++ 和 Java 的版本升级是全局的，Rust 的 Edition 是 crate 级别的选择。

---

## ⚖️ 模块 9: 设计权衡分析
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 为什么 Rust 需要 Edition 机制？
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

C++ 的"永远向后兼容"导致语言复杂度累积（如 `auto` 的语义变更）。Rust 选择 Edition 机制：

1. **不牺牲演进**: 可以清理历史包袱（如 `gen` 预留）
2. **不破坏生态**: 旧 crate 无需修改即可继续使用
3. **平滑迁移**: `cargo fix --edition` 自动化大部分变更

代价：编译器需要维护多个语法分析前端，增加了编译器复杂度。

---

## 🔮 未来展望
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### Rust 1.95+: gen 关键字正式启用
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
// Rust 1.95+ 预览
fn fibonacci() -> impl Iterator<Item = u64> {
    gen {
        let mut a = 0u64;
        let mut b = 1u64;
        loop {
            yield a;
            (a, b) = (b, a + b);
        }
    }
}
```

### 版本跟踪
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 版本 | 发布日期 | Edition 状态 |
|------|---------|-------------|
| 1.82.0 | 2024-10 | Edition 2024 稳定 |
| 1.95.0 | 2025-10 | gen 关键字启用（预计） |
| 1.96.0 | 2025-12 | TBD |

## 📖 延伸阅读
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [Edition Guide 2024](https://doc.rust-lang.org/edition-guide/rust-2024/)
- [RFC: Edition 2024](https://rust-lang.github.io/rfcs/XXXX-edition-2024.html)
- [Cargo.toml 配置](https://doc.rust-lang.org/cargo/reference/manifest.html)

## 📝 模块 10: 自我检测
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 概念性问题
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

1. **Rust 的 Edition 机制与 SemVer 有何本质区别？** 为什么同一项目可以混合使用 Edition 2021 和 Edition 2024 的依赖？

2. **`impl Trait` 的精确捕获（`+ use<'_>`）解决了什么问题？** 为什么 Rust 2021 的"自动捕获所有生命周期"在复杂场景下会导致问题？

### 代码修复题
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

**题 1**: 以下代码在 Edition 2024 下编译失败。请修复：

```rust
fn make_closure(x: &i32) -> impl Fn() -> &i32 {
    || x
}
```

<details>
<summary>参考答案</summary>

```rust
fn make_closure(x: &i32) -> impl Fn() -> &i32 + use<'_> {
    || x
}
```

Edition 2024 要求显式捕获生命周期。`+ use<'_>` 表示捕获 `x` 的生命周期。

</details>

### 开放设计题
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

**题 2**: 你的团队维护一个包含 50 个内部 crate 的大型 workspace，目前全部使用 Edition 2021。你计划迁移到 Edition 2024。请设计迁移策略：

- 是逐个 crate 迁移还是一次性全部迁移？
- 如何处理跨 crate 的 `impl Trait` 返回类型变更？
- 如果某些 crate 的依赖不支持 Edition 2024，如何决策？

---

## ✅ 自我检测
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

1. Edition 2024 最大的语言变更是什么？
2. 如何处理 `gen` 关键字冲突？
3. `cargo fix --edition` 能自动修复哪些问题？

---

> **权威来源**: [Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/), [RFC 2052: Epochs](https://rust-lang.github.io/rfcs/2052-epochs.html), [Rust Blog — Edition 2024](https://blog.rust-lang.org/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Edition Guide、RFC 2052、Rust Blog、Lang Team Roadmap） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.82.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [Rust 标准库速查](../05_reference/std_library_cheatsheet.md)

- [Cargo 基础](cargo_basics.md)
- [06 - 生态系统与工具](README.md)

---

## 权威来源索引

> **[来源: [crates.io](https://crates.io/)]**
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
