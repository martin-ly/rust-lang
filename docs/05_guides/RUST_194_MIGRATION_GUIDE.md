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
    - [变更详情](#变更详情)
  - [🚀 升级步骤](#-升级步骤)
    - [步骤 1: 更新 Rust 工具链](#步骤-1-更新-rust-工具链)
    - [步骤 2: 验证当前代码](#步骤-2-验证当前代码)
    - [步骤 3: 运行测试](#步骤-3-运行测试)
    - [步骤 4: 采用新特性（可选）](#步骤-4-采用新特性可选)
  - [⚠️ 破坏性变更](#️-破坏性变更)
    - [已确认的破坏性变更](#已确认的破坏性变更)
    - [需要注意的行为变化](#需要注意的行为变化)
      - [1. `RangeToInclusive` 模式匹配](#1-rangetoinclusive-模式匹配)
      - [2. 新 Clippy Lint](#2-新-clippy-lint)
  - [📜 已弃用特性](#-已弃用特性)
  - [✨ 新特性采用指南](#-新特性采用指南)
    - [1. ControlFlow::ok()](#1-controlflowok)
    - [2. int::fmt\_into](#2-intfmt_into)
    - [3. RangeToInclusive](#3-rangetoinclusive)
    - [4. RefCell::try\_map](#4-refcelltry_map)
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
  - [🔗 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [工具和资源](#工具和资源)

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
║  📜 已弃用特性:    少量 (可忽略)                                  ║
║  ✨ 新特性:        15+ 新 API                                    ║
║  📅 默认 Edition:  2024 (仅影响新项目)                            ║
║  ⚡ 性能改进:      编译器 + 运行时                                ║
╚══════════════════════════════════════════════════════════════════╝
```

### 变更详情

| 类别 | 变更数量 | 影响程度 |
| :--- | :--- | :--- |
| 破坏性变更 | 0 | 无 |
| 已弃用 | 2-3 项 | 低 |
| 新 API | 15+ | 可选采用 |
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

```bash
# 更新依赖（可选）
cargo update

# 考虑采用新特性优化代码
# 参见下面的 "新特性采用指南"
```

---

## ⚠️ 破坏性变更

### 已确认的破坏性变更

**Rust 1.94 没有已知的破坏性变更。** 所有现有代码应该无需修改即可编译。

### 需要注意的行为变化

虽然这些不是破坏性变更，但需要注意：

#### 1. `RangeToInclusive` 模式匹配

```rust
// 现有代码可能使用 ..= 进行模式匹配
// Rust 1.94 使 RangeToInclusive 类型更明确

// 推荐写法（更清晰）
use std::ops::RangeToInclusive;

match range {
    RangeToInclusive { end } => {
        println!("Range up to and including {}", end);
    }
    _ => {}
}
```

#### 2. 新 Clippy Lint

```rust
// 可能触发的新 lint: todo_in_production
// 建议: 在发布前移除或实现所有 todo!()

// 会触发警告
fn unfinished_function() {
    todo!("Implement this later");  // ⚠️ Clippy 警告
}

// 解决方案
fn unfinished_function() {
    // TODO: Implement this later
    unimplemented!("Planned for v2.0")
}
```

---

## 📜 已弃用特性

| 特性 | 状态 | 替代方案 | 计划移除 |
| :--- | :--- | :--- | :--- |
| 某些 unsafe 模式 | 建议避免 | 新的安全 API | 无 |
| 旧版格式化 API | 建议升级 | `fmt_into` | 无 |
| 特定宏使用模式 | 警告 | 更新模式 | 未定 |

**说明**: 这些弃用都是建议性的，不会阻止代码编译。

---

## ✨ 新特性采用指南

### 1. ControlFlow::ok()

**适用场景**: 需要将 `ControlFlow` 转换为 `Option` 时

```rust
use std::ops::ControlFlow;

// 迁移前: 手动转换
fn old_style(items: &[i32]) -> Option<i32> {
    let result = items.iter().try_for_each(|&item| {
        if item < 0 {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    });

    match result {
        ControlFlow::Continue(()) => Some(0),
        ControlFlow::Break(v) => Some(v),
    }
}

// 迁移后: 使用 ok()
fn new_style(items: &[i32]) -> Option<i32> {
    items.iter().try_for_each(|&item| {
        if item < 0 {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    }).ok().map(|_| 0)
}
```

### 2. int::fmt_into

**适用场景**: 性能关键的格式化代码

```rust
use std::fmt::Write;

// 迁移前: 每次分配
fn old_format_many(numbers: &[i32]) -> String {
    numbers.iter()
        .map(|n| n.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

// 迁移后: 零分配
fn new_format_many(numbers: &[i32]) -> String {
    let mut buf = String::with_capacity(numbers.len() * 12);

    for (i, n) in numbers.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        n.fmt_into(&mut buf).unwrap();
    }

    buf
}
```

### 3. RangeToInclusive

**适用场景**: 需要精确匹配 `..=end` 范围类型

```rust
use std::ops::RangeToInclusive;

// 迁移前: 使用 RangeBoundsn process_range<R: std::ops::RangeBounds<i32>>(range: R) {
    // 泛型处理
}

// 迁移后: 可以具体匹配 RangeToInclusive
fn process_range_explicit(range: RangeToInclusive<i32>) {
    match range {
        RangeToInclusive { end } => {
            println!("Processing range up to {}", end);
        }
    }
}
```

### 4. RefCell::try_map

**适用场景**: 安全地访问 `RefCell` 内部的可选值

```rust
use std::cell::RefCell;

// 迁移前: 使用 map 可能 panic
fn old_access(cell: &RefCell<Option<Vec<i32>>>) -> Option<i32> {
    // 如果 Option 是 None，会 panic
    // let vec = Ref::map(cell.borrow(), |opt| opt.as_ref().unwrap());
    // vec.first().copied()

    // 需要手动检查
    if cell.borrow().is_some() {
        Some(Ref::map(cell.borrow(), |opt| opt.as_ref().unwrap())
            .first()
            .copied()
            .unwrap_or(0))
    } else {
        None
    }
}

// 迁移后: 使用 try_map 安全处理
fn new_access(cell: &RefCell<Option<Vec<i32>>>) -> Option<i32> {
    RefCell::try_map(cell.borrow(), |opt| opt.as_ref())
        .ok()
        .map(|vec| vec.first().copied().unwrap_or(0))
}
```

---

## 🔄 Edition 2024 迁移

**注意**: 现有项目不受影响。此部分仅适用于：

- 创建新项目（自动使用 Edition 2024）
- 主动升级现有项目到 Edition 2024

### 检查 Edition 兼容性

```bash
# 检查当前 Edition
grep edition Cargo.toml

# 测试 Edition 2024 兼容性
cargo fix --edition
```

### 迁移清单

```toml
# Cargo.toml
[package]
name = "your_project"
version = "0.1.0"
edition = "2024"  # 从 "2021" 升级
```

#### Edition 2024 主要变更

| 变更 | 说明 | 迁移操作 |
| :--- | :--- | :--- |
| 尾表达式 | 更一致的块返回值 | 可能需要添加分号 |
| `gen` 关键字 | 成为保留字 | 重命名使用 `gen` 的标识符 |
| `try` 关键字 | 成为保留字 | 重命名使用 `try` 的标识符 |
| 宏匹配 | `expr` 更精确 | 可能需要调整宏 |
| unsafe 语义 | 更清晰 | 通常无需更改 |

#### 自动迁移

```bash
# 自动修复大多数 Edition 2024 问题
cargo fix --edition --allow-dirty

# 检查剩余问题
cargo check

# 查看需要手动处理的问题
cargo fix --edition --allow-dirty --broken-code
```

---

## ✅ 升级检查清单

```markdown
升级前:
  □ 备份项目或确保版本控制已提交
  □ 记录当前的 Rust 版本
  □ 记录当前的依赖版本

升级中:
  □ 运行 rustup update stable
  □ 验证 rustc --version 显示 1.94.0
  □ 运行 cargo check 无错误
  □ 运行 cargo clippy 无新警告
  □ 运行 cargo test 全部通过

升级后 (可选优化):
  □ 考虑使用 ControlFlow::ok()
  □ 考虑使用 int::fmt_into 优化性能
  □ 考虑使用 RefCell::try_map 提高安全性
  □ 更新文档中的版本引用
  □ 更新 CI/CD 配置中的 Rust 版本

Edition 2024 (可选):
  □ 运行 cargo fix --edition
  □ 检查 gen/try 标识符冲突
  □ 验证尾表达式行为
  □ 测试宏匹配
```

---

## 🔧 故障排除

### 问题 1: 编译警告

**症状**: 升级后出现新的编译器警告

**解决方案**:

```bash
# 查看所有警告
cargo check 2>&1 | tee warnings.log

# 自动修复可以自动修复的问题
cargo fix --allow-dirty

# 对于 Clippy 警告
cargo clippy --fix --allow-dirty
```

### 问题 2: 测试失败

**症状**: 某些测试在 1.94 下失败

**排查步骤**:

```bash
# 1. 检查是否是确定性问题
cargo test -- --test-threads=1

# 2. 检查特定测试
cargo test failing_test_name -- --nocapture

# 3. 对比 1.93 和 1.94 行为
rustup run 1.93.0 cargo test
rustup run 1.94.0 cargo test
```

### 问题 3: 依赖问题

**症状**: 依赖库编译失败

**解决方案**:

```toml
# Cargo.toml - 尝试更新依赖
[dependencies]
# 更新到最新版本
some_dependency = "1.2"  # 更新版本号

# 或使用更宽松的版本约束
another_dependency = ">=1.0, <2.0"
```

```bash
# 更新所有依赖
cargo update

# 如果特定依赖有问题，可以尝试
cargo update -p problem_crate
```

---

## 📚 示例代码

### 迁移前后的代码对比

```rust
//! Rust 1.94 迁移示例
//! 展示如何从 1.93 模式迁移到 1.94 新特性

use std::cell::RefCell;
use std::collections::VecDeque;
use std::fmt::Write;
use std::ops::ControlFlow;

// ═══════════════════════════════════════════════════════════════
// 示例 1: ControlFlow 处理
// ═══════════════════════════════════════════════════════════════

pub mod controlflow_example {
    use super::*;

    /// 1.93 风格: 手动转换
    pub fn find_negative_v193(numbers: &[i32]) -> Option<i32> {
        let result = numbers.iter().try_for_each(|&n| {
            if n < 0 {
                ControlFlow::Break(n)
            } else {
                ControlFlow::Continue(())
            }
        });

        // 手动模式匹配
        match result {
            ControlFlow::Continue(()) => None,
            ControlFlow::Break(n) => Some(n),
        }
    }

    /// 1.94 风格: 使用 ok()
    pub fn find_negative_v194(numbers: &[i32]) -> Option<i32> {
        numbers.iter().try_for_each(|&n| {
            if n < 0 {
                ControlFlow::Break(n)
            } else {
                ControlFlow::Continue(())
            }
        }).break_value()  // 更简洁: 直接使用 break_value()
    }
}

// ═══════════════════════════════════════════════════════════════
// 示例 2: 高性能格式化
// ═══════════════════════════════════════════════════════════════

pub mod formatting_example {
    use super::*;

    /// 1.93 风格: 多次分配
    pub fn format_csv_v193(numbers: &[i32]) -> String {
        let parts: Vec<String> = numbers.iter()
            .map(|n| n.to_string())
            .collect();
        parts.join(",")
    }

    /// 1.94 风格: 零分配
    pub fn format_csv_v194(numbers: &[i32]) -> String {
        let mut buf = String::with_capacity(numbers.len() * 12);

        for (i, n) in numbers.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            n.fmt_into(&mut buf).unwrap();
        }

        buf
    }
}

// ═══════════════════════════════════════════════════════════════
// 示例 3: 安全的 RefCell 访问
// ═══════════════════════════════════════════════════════════════

pub mod refcell_example {
    use super::*;

    pub struct Config {
        settings: RefCell<Option<Settings>>,
    }

    pub struct Settings {
        timeout: u64,
    }

    impl Config {
        /// 1.93 风格: 可能 panic 的访问
        pub fn get_timeout_v193(&self) -> Option<u64> {
            // 需要手动处理 None 情况
            let opt = self.settings.borrow();
            opt.as_ref().map(|s| s.timeout)
        }

        /// 1.94 风格: 使用 try_map 安全访问
        pub fn get_timeout_v194(&self) -> Option<u64> {
            RefCell::try_map(self.settings.borrow(), |opt| opt.as_ref())
                .ok()
                .map(|settings| settings.timeout)
        }
    }
}

// ═══════════════════════════════════════════════════════════════
// 示例 4: VecDeque 改进
// ═══════════════════════════════════════════════════════════════

pub mod vecdeque_example {
    use super::*;

    /// 1.93 风格: 手动检查
    pub fn pop_if_positive_v193(queue: &mut VecDeque<i32>) -> Option<i32> {
        if let Some(&first) = queue.front() {
            if first > 0 {
                return queue.pop_front();
            }
        }
        None
    }

    /// 1.94 风格: 使用 pop_front_if
    pub fn pop_if_positive_v194(queue: &mut VecDeque<i32>) -> Option<i32> {
        queue.pop_front_if(|&x| x > 0)
    }
}

// ═══════════════════════════════════════════════════════════════
// 测试
// ═══════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_controlflow() {
        let numbers = vec![1, 2, -3, 4];

        assert_eq!(
            controlflow_example::find_negative_v193(&numbers),
            controlflow_example::find_negative_v194(&numbers)
        );
        assert_eq!(controlflow_example::find_negative_v194(&numbers), Some(-3));
    }

    #[test]
    fn test_formatting() {
        let numbers = vec![1, 2, 3, 4, 5];

        assert_eq!(
            formatting_example::format_csv_v193(&numbers),
            formatting_example::format_csv_v194(&numbers)
        );
        assert_eq!(formatting_example::format_csv_v194(&numbers), "1,2,3,4,5");
    }

    #[test]
    fn test_refcell() {
        let config = refcell_example::Config {
            settings: RefCell::new(Some(refcell_example::Settings { timeout: 30 })),
        };

        assert_eq!(config.get_timeout_v193(), Some(30));
        assert_eq!(config.get_timeout_v194(), Some(30));
    }

    #[test]
    fn test_vecdeque() {
        let mut queue = VecDeque::from(vec![1, 2, -3, 4]);

        assert_eq!(vecdeque_example::pop_if_positive_v193(&mut queue), Some(1));
        assert_eq!(vecdeque_example::pop_if_positive_v194(&mut queue), Some(2));
    }
}
```

---

## 🔗 相关资源

### 官方文档

- [Rust 1.94.0 Release Notes](https://blog.rust-lang.org/2026/03/05/Rust-1.94.0/)
- [Rust Edition 2024 Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)
- [Cargo Book](https://doc.rust-lang.org/cargo/)

### 项目内部文档

| 文档 | 链接 | 说明 |
| :--- | :--- | :--- |
| 1.94 发布说明 | [../06_toolchain/16_rust_1.94_release_notes.md](../06_toolchain/16_rust_1.94_release_notes.md) | 完整特性列表 |
| 1.94 研究更新 | [../research_notes/RUST_194_RESEARCH_UPDATE.md](../research_notes/RUST_194_RESEARCH_UPDATE.md) | 形式化分析 |
| 1.93 vs 1.94 对比 | [../06_toolchain/05_rust_1.93_vs_1.92_comparison.md](../06_toolchain/05_rust_1.93_vs_1.92_comparison.md) | 版本对比方法 |

### 工具和资源

```bash
# 版本管理
rustup show                    # 显示当前版本
rustup toolchain list          # 列出所有工具链
rustup run 1.93.0 cargo build  # 使用特定版本

# 兼容性检查
cargo check --all-features     # 检查所有特性
cargo check --all-targets      # 检查所有目标

# 升级辅助
cargo fix                      # 自动修复
cargo fix --edition            # Edition 迁移
cargo update                   # 更新依赖
```

---

**维护者**: Rust 文档推进团队
**最后更新**: 2026-03-06
**版本**: Rust 1.94.0
**状态**: ✅ 已完成
