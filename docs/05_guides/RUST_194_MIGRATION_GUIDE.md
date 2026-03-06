# Rust 1.94 迁移指南

> **文档类型**: 迁移指南
> **Rust 版本**: 1.94.0 (从 1.93.x 升级)
> **发布日期**: 2026-03-05
> **创建日期**: 2026-03-06
> **最后更新**: 2026-03-06
> **难度**: ⭐ (简单)
> **预计迁移时间**: 15-30 分钟

---

## 📋 目录

- [Rust 1.94 迁移指南](#rust-194-迁移指南)
  - [📋 目录](#-目录)
  - [🎯 快速开始](#-快速开始)
  - [📊 版本变更概览](#-版本变更概览)
    - [从 1.93 到 1.94 的主要变更](#从-193-到-194-的主要变更)
  - [🚀 升级步骤](#-升级步骤)
    - [步骤 1: 更新 Rust 工具链](#步骤-1-更新-rust-工具链)
    - [步骤 2: 验证当前代码](#步骤-2-验证当前代码)
    - [步骤 3: 运行测试](#步骤-3-运行测试)
    - [步骤 4: 采用新特性（可选）](#步骤-4-采用新特性可选)
      - [采用 ControlFlow 模式](#采用-controlflow-模式)
  - [⚠️ 破坏性变更](#️-破坏性变更)
    - [已确认的破坏性变更](#已确认的破坏性变更)
  - [📜 已弃用特性](#-已弃用特性)
  - [✨ 新特性采用指南](#-新特性采用指南)
    - [1. ControlFlow 模式](#1-controlflow-模式)
    - [2. Edition 2024（可选）](#2-edition-2024可选)
  - [🔄 Edition 2024 迁移](#-edition-2024-迁移)
    - [检查 Edition 兼容性](#检查-edition-兼容性)
    - [迁移清单](#迁移清单)
      - [Edition 2024 主要变更](#edition-2024-主要变更)
      - [自动迁移](#自动迁移)
  - [✅ 升级检查清单](#-升级检查清单)
  - [🔧 故障排除](#-故障排除)
    - [问题 1: 编译警告](#问题-1-编译警告)
    - [问题 2: 测试失败](#问题-2-测试失败)
    - [问题 3: 依赖问题](#问题-3-依赖问题)
  - [📚 示例代码](#-示例代码)
    - [迁移前后的代码对比](#迁移前后的代码对比)
      - [示例 1: 提前返回模式](#示例-1-提前返回模式)
      - [示例 2: Edition 2024 项目](#示例-2-edition-2024-项目)
  - [🔗 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [代码示例](#代码示例)

---

## 🎯 快速开始

如果你急于升级，只需执行以下命令：

```bash
# 更新 Rust 工具链
rustup update stable

# 验证版本
rustc --version  # 应显示 rustc 1.94.0

# 检查项目
cd your_project
cargo check

# 运行测试
cargo test
```

**Rust 1.94 是向后兼容的**，大多数项目无需修改即可升级。

---

## 📊 版本变更概览

### 从 1.93 到 1.94 的主要变更

```markdown
╔══════════════════════════════════════════════════════════════════╗
║  Rust 1.94 迁移概览                                              ║
╠══════════════════════════════════════════════════════════════════╣
║  ⚠️  破坏性变更:  无                                             ║
║  📜 已弃用特性:    少量                                          ║
║  ✨ 新特性:        Edition 2024 完善、ControlFlow API            ║
║  ⚡ 性能改进:      编译器优化                                    ║
╚══════════════════════════════════════════════════════════════════╝
```

**变更详情**:

| 类别 | 变更数量 | 影响程度 |
| :--- | :--- | :--- |
| 破坏性变更 | 0 | 无 |
| 已弃用 | 少量 | 低 |
| Edition 2024 | 完善支持 | 可选采用 |
| 性能优化 | 多项 | 自动受益 |
| 工具更新 | 多项 | 自动受益 |

---

## 🚀 升级步骤

### 步骤 1: 更新 Rust 工具链

```bash
# 更新 stable 工具链
rustup update stable

# 验证版本
rustc --version
# 期望输出: rustc 1.94.0 (4a4ef493e 2026-03-02)

cargo --version
# 期望输出: cargo 1.94.0
```

### 步骤 2: 验证当前代码

```bash
# 进入项目目录
cd your_project

# 检查代码（不编译）
cargo check

# 详细检查（包括所有目标）
cargo check --all-targets

# 检查所有特性组合
cargo check --all-features
```

### 步骤 3: 运行测试

```bash
# 运行所有测试
cargo test

# 运行 Clippy 检查
cargo clippy -- -D warnings

# 检查格式化
cargo fmt -- --check
```

### 步骤 4: 采用新特性（可选）

#### 采用 ControlFlow 模式

```rust
// 之前：手动实现提前返回
fn find_negative_manual(numbers: &[i32]) -> Option<i32> {
    for &n in numbers {
        if n < 0 {
            return Some(n);
        }
    }
    None
}

// 之后：使用 ControlFlow
use std::ops::ControlFlow;

fn find_negative_controlflow(numbers: &[i32]) -> Option<i32> {
    numbers.iter().try_for_each(|&n| {
        if n < 0 { ControlFlow::Break(n) }
        else { ControlFlow::Continue(()) }
    }).break_value()
}
```

---

## ⚠️ 破坏性变更

### 已确认的破坏性变更

**Rust 1.94 没有破坏性变更**，与 1.93 完全向后兼容。

---

## 📜 已弃用特性

少量内部 API 被标记为已弃用，但不会影响大多数用户代码。

---

## ✨ 新特性采用指南

### 1. ControlFlow 模式

`ControlFlow` 类型用于在迭代操作中实现提前返回：

```rust
use std::ops::ControlFlow;

// 查找第一个满足条件的元素
fn find_first<T>(items: &[T], predicate: impl Fn(&T) -> bool) -> Option<&T> {
    items.iter().try_for_each(|item| {
        if predicate(item) {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    }).break_value()
}

// 验证所有元素
fn all_satisfy<T>(items: &[T], predicate: impl Fn(&T) -> bool) -> bool {
    matches!(
        items.iter().try_for_each(|item| {
            if predicate(item) {
                ControlFlow::Continue(())
            } else {
                ControlFlow::Break(())
            }
        }),
        ControlFlow::Continue(())
    )
}

fn main() {
    let numbers = vec![1, 2, -3, 4, 5];

    if let Some(neg) = find_first(&numbers, |&n| n < 0) {
        println!("Found negative: {}", neg);
    }

    assert!(all_satisfy(&[2, 4, 6], |&n| n % 2 == 0));
}
```

**可用方法**:

- `is_continue()` / `is_break()` - 检查状态
- `break_value()` - 获取 Break 值
- `continue_value()` - 获取 Continue 值

### 2. Edition 2024（可选）

升级到 Edition 2024 可以解锁新语言特性：

```bash
# 自动迁移
cargo fix --edition
```

**Edition 2024 主要特性**:

- `gen` 关键字支持
- `use<..>` 精确捕获语法
- 改进的闭包类型推断
- `unsafe_op_in_unsafe_fn` 默认启用

---

## 🔄 Edition 2024 迁移

### 检查 Edition 兼容性

```bash
# 预览 Edition 2024 迁移
cargo fix --edition --broken-code --dry-run
```

### 迁移清单

#### Edition 2024 主要变更

| 特性 | 2021 | 2024 | 说明 |
|------|------|------|------|
| `gen` 关键字 | 保留 | 关键字 | 用于生成器 |
| `use<..>` | 不可用 | 可用 | 精确捕获 |
| Tail expr drop | 旧顺序 | 新顺序 | 尾表达式 drop 顺序 |
| `unsafe_op` | 允许 | 警告 | unsafe 块内的 unsafe 操作 |

#### 自动迁移

```bash
# 自动修复大多数问题
cargo fix --edition

# 修复 Edition idioms
cargo fix --edition-idioms

# 构建验证
cargo build
```

---

## ✅ 升级检查清单

- [ ] Rust 工具链更新到 1.94.0
- [ ] `cargo check` 无警告
- [ ] `cargo test` 通过
- [ ] `cargo clippy` 无警告
- [ ] CI/CD 流程验证通过
- [ ] （可选）Edition 2024 迁移

---

## 🔧 故障排除

### 问题 1: 编译警告

**现象**:

```text
warning: ...
```

**解决**:

```bash
# 运行 clippy 检查
cargo clippy

# 自动修复
cargo fix
```

### 问题 2: 测试失败

**现象**:

```text
test result: FAILED
```

**解决**:

```bash
# 详细测试输出
cargo test -- --nocapture

# 检查特定测试
cargo test test_name
```

### 问题 3: 依赖问题

**现象**:

```text
error: failed to select a version for `xxx`
```

**解决**:

```bash
# 更新依赖
cargo update

# 清理并重新构建
cargo clean
cargo build
```

---

## 📚 示例代码

### 迁移前后的代码对比

#### 示例 1: 提前返回模式

**之前** (Rust 1.93):

```rust
fn find_first_negative(numbers: &[i32]) -> Option<i32> {
    for &n in numbers {
        if n < 0 {
            return Some(n);
        }
    }
    None
}
```

**之后** (Rust 1.94，使用 ControlFlow):

```rust
use std::ops::ControlFlow;

fn find_first_negative(numbers: &[i32]) -> Option<i32> {
    numbers.iter().try_for_each(|&n| {
        if n < 0 { ControlFlow::Break(n) }
        else { ControlFlow::Continue(()) }
    }).break_value()
}
```

#### 示例 2: Edition 2024 项目

**之前** (Cargo.toml):

```toml
[package]
name = "my_project"
version = "0.1.0"
edition = "2021"
```

**之后** (Cargo.toml):

```toml
[package]
name = "my_project"
version = "0.1.0"
edition = "2024"
rust-version = "1.94"
```

---

## 🔗 相关资源

### 官方文档

- [Rust 1.94 Release Notes](https://releases.rs/)
- [Edition 2024 Guide](https://doc.rust-lang.org/edition-guide/rust-2024/)
- [Standard Library API](https://doc.rust-lang.org/std/)
- [Cargo Guide](https://doc.rust-lang.org/cargo/)

### 项目内部文档

- [Rust 1.94 发布说明](../06_toolchain/16_rust_1.94_release_notes.md)
- [Rust 1.94 采用指南](../06_toolchain/18_rust_1.94_adoption_guide.md)
- [Rust 1.94 速查卡](../02_reference/quick_reference/rust_194_features_cheatsheet.md)

### 代码示例

- [Rust 1.94 特性示例](../crates/c01_ownership_borrow_scope/src/rust_194_features.rs)

---

**最后更新**: 2026-03-06
**维护者**: 文档团队
**状态**: ✅ 与 Rust 1.94.0 同步

> **注意**: 本文档基于实际的 Rust 1.94.0 版本特性编写。
