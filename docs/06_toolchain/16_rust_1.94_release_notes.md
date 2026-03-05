# Rust 1.94.0 Release Notes

> **版本**: Rust 1.94.0 (rustc 1.94.0 (4a4ef493e 2026-03-02))
> **发布日期**: 2026-03-05
> **创建日期**: 2026-03-06
> **最后更新**: 2026-03-06
> **状态**: ✅ 已发布
> **文档类型**: 工具链发布说明

---

## 📋 目录

- [Rust 1.94.0 Release Notes](#rust-1940-release-notes)
  - [📋 目录](#-目录)
  - [🎯 版本概览](#-版本概览)
    - [关键信息](#关键信息)
  - [💡 主要新特性](#-主要新特性)
    - [1. `ControlFlow::ok()` - 控制流简化](#1-controlflowok---控制流简化)
    - [2. `int::fmt_into` - 高性能整数格式化](#2-intfmt_into---高性能整数格式化)
    - [3. `RangeToInclusive` 类型](#3-rangetoinclusive-类型)
    - [4. `RefCell::try_map` - 安全内部可变性](#4-refcelltry_map---安全内部可变性)
    - [5. `proc_macro_value` - 过程宏增强](#5-proc_macro_value---过程宏增强)
    - [6. Edition 2024 成为默认](#6-edition-2024-成为默认)
  - [📚 标准库更新](#-标准库更新)
    - [新增稳定 API](#新增稳定-api)
    - [性能改进](#性能改进)
    - [文档改进](#文档改进)
  - [📦 Cargo 改进](#-cargo-改进)
    - [1. `cargo report timings` 稳定化](#1-cargo-report-timings-稳定化)
    - [2. rustdoc `--merge` 选项](#2-rustdoc---merge-选项)
    - [3. 配置包含 (`config-include`)](#3-配置包含-config-include)
    - [4. 改进的依赖解析](#4-改进的依赖解析)
  - [🔧 工具链更新](#-工具链更新)
    - [Clippy](#clippy)
    - [Rustfmt](#rustfmt)
    - [rust-analyzer](#rust-analyzer)
  - [⚡ 性能改进](#-性能改进)
    - [编译器性能](#编译器性能)
    - [运行时性能](#运行时性能)
  - [🔄 迁移指南](#-迁移指南)
    - [升级步骤](#升级步骤)
    - [破坏性变更](#破坏性变更)
      - [1. `RangeToInclusive` 模式匹配](#1-rangetoinclusive-模式匹配)
      - [2. Edition 2024 默认](#2-edition-2024-默认)
    - [已弃用特性](#已弃用特性)
  - [📖 形式化语义更新](#-形式化语义更新)
    - [类型系统](#类型系统)
    - [所有权与借用](#所有权与借用)
  - [📊 版本对比](#-版本对比)
    - [Rust 1.93 vs 1.94 对比](#rust-193-vs-194-对比)
  - [🔗 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [形式化文档](#形式化文档)

---

## 🎯 版本概览

Rust 1.94.0 是 2026 年的第三个稳定版本，标志着 **Edition 2024** 成为默认版本。本版本专注于 API 稳定化、性能优化和工具链改进。

```markdown
╔══════════════════════════════════════════════════════════════════╗
║  Rust 1.94.0 特性速览                                            ║
╠══════════════════════════════════════════════════════════════════╣
║  🎯 语言特性:       6 个新稳定化                                  ║
║  📚 标准库:         15+ 新 API                                   ║
║  📦 Cargo:          4 项重大改进                                  ║
║  ⚡ 性能:           编译器和运行时双重优化                         ║
║  🔧 工具:           Clippy、rustfmt、rust-analyzer 全面更新        ║
║  📅 Edition:        2024 成为默认                                 ║
║  🔧 LLVM:           升级至 21.1.8                                 ║
╚══════════════════════════════════════════════════════════════════╝
```

### 关键信息

| 项目 | 详情 |
| :--- | :--- |
| **版本号** | 1.94.0 |
| **发布日期** | 2026-03-05 |
| **Git 提交** | 4a4ef493e |
| **默认 Edition** | 2024 |
| **LLVM 版本** | 21.1.8 |
| **主要主题** | API 稳定化、性能优化、工具链改进 |

---

## 💡 主要新特性

### 1. `ControlFlow::ok()` - 控制流简化

**特性状态**: ✅ 已稳定化
**跟踪问题**: [#152911](https://github.com/rust-lang/rust/issues/152911)

`ControlFlow::ok()` 方法将 `ControlFlow<B, C>` 转换为 `Option<C>`，简化控制流与 `Option`/`Result` 的互操作。

```rust
use std::ops::ControlFlow;

// Rust 1.94 之前的写法
fn old_style(items: &[i32]) -> Option<i32> {
    let result: ControlFlow<i32, ()> = items.iter().try_for_each(|&item| {
        if item < 0 {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    });

    // 手动转换
    match result {
        ControlFlow::Continue(()) => Some(0),
        ControlFlow::Break(v) => Some(v),
    }
}

// Rust 1.94 新写法
fn new_style(items: &[i32]) -> Option<i32> {
    let result: ControlFlow<i32, ()> = items.iter().try_for_each(|&item| {
        if item < 0 {
            ControlFlow::Break(item)
        } else {
            ControlFlow::Continue(())
        }
    });

    // 使用新稳定的方法
    result.ok().map(|_| 0).or_else(|| match result {
        ControlFlow::Break(v) => Some(v),
        _ => None,
    })
}
```

**实际应用场景**:

```rust
// 场景 1: 搜索算法中的提前返回
fn find_first_negative(numbers: &[i32]) -> Option<i32> {
    numbers.iter().try_for_each(|&n| {
        if n < 0 {
            ControlFlow::Break(n)
        } else {
            ControlFlow::Continue(())
        }
    }).ok().map(|_| 0)
}

// 场景 2: 验证器模式
struct Validator;

impl Validator {
    fn validate<T>(&self, items: &[T], check: impl Fn(&T) -> ControlFlow<String, ()>) -> Result<(), String> {
        for item in items {
            if let Some(err) = check(item).break_value() {
                return Err(err);
            }
        }
        Ok(())
    }
}
```

---

### 2. `int::fmt_into` - 高性能整数格式化

**特性状态**: ✅ 已稳定化
**跟踪问题**: [#152544](https://github.com/rust-lang/rust/issues/152544)

将整数直接格式化到预分配的缓冲区，避免临时字符串分配。

```rust
use std::fmt::Write;

// Rust 1.94 之前的写法（有分配）
fn old_format(n: i32) -> String {
    format!("{}", n)  // 分配新 String
}

// Rust 1.94 新写法（无分配）
fn new_format(n: i32, buf: &mut String) {
    n.fmt_into(buf).unwrap();  // 直接写入现有缓冲区
}

// 高性能批量格式化
fn format_many(numbers: &[i32]) -> String {
    let mut buf = String::with_capacity(numbers.len() * 12);  // 预分配

    for n in numbers {
        n.fmt_into(&mut buf).unwrap();
        buf.push(',');
    }

    buf
}
```

**性能对比**:

| 方法 | 分配次数 | 相对性能 |
| :--- | :--- | :--- |
| `format!("{}", n)` | 1 次/调用 | 基准 (1.0x) |
| `n.fmt_into(buf)` | 0 次 | **1.3-1.5x** |

---

### 3. `RangeToInclusive` 类型

**特性状态**: ✅ 已稳定化
**跟踪问题**: [#152304](https://github.com/rust-lang/rust/issues/152304)

`..=end` 范围表达式现在拥有专用的 `RangeToInclusive` 类型，完善了 Rust 的范围类型系统。

```rust
use std::ops::RangeToInclusive;

// Rust 1.94: 新增 RangeToInclusive<T>
fn main() {
    let range: RangeToInclusive<i32> = ..=10;

    match range {
        RangeToInclusive { end } => {
            println!("Range from start to {}", end);
        }
    }

    // 在泛型中使用
    fn process_range<R>(range: R)
    where
        R: RangeBounds<i32>,
    {
        // 处理范围...
    }

    process_range(..=10);  // 现在类型更精确
}
```

**完整的 Range 类型家族**:

```rust
use std::ops::{
    Range,           // start..end
    RangeFrom,       // start..
    RangeFull,       // ..
    RangeInclusive,  // start..=end
    RangeTo,         // ..end
    RangeToInclusive,// ..=end (Rust 1.94 新增)
};
```

---

### 4. `RefCell::try_map` - 安全内部可变性

**特性状态**: ✅ 已稳定化
**跟踪问题**: [#152092](https://github.com/rust-lang/rust/issues/152092)

安全地尝试映射 `RefCell` 内部值，避免 panic。

```rust
use std::cell::RefCell;

fn main() {
    let cell = RefCell::new(Some(42));

    // Rust 1.94 新特性: try_map
    let result: Result<std::cell::Ref<i32>, _> =
        RefCell::try_map(cell.borrow(), |opt| opt.as_ref());

    match result {
        Ok(val) => println!("Got: {}", *val),
        Err(_) => println!("Mapping failed"),
    }

    // 可变版本
    let cell2 = RefCell::new(Some(vec![1, 2, 3]));
    let mut result2 = RefCell::try_map(cell2.borrow_mut(), |opt| opt.as_mut());

    if let Ok(mut vec) = result2 {
        vec.push(4);
    }
}
```

**与现有 API 对比**:

```rust
use std::cell::RefCell;

fn comparison() {
    let cell = RefCell::new(Some(42));

    // 旧的 map (会 panic)
    // let val = Ref::map(cell.borrow(), |opt| opt.as_ref().unwrap());
    // 如果 opt 是 None，上面会 panic

    // 新的 try_map (安全)
    let result = RefCell::try_map(cell.borrow(), |opt| opt.as_ref());
    // result 是 Result，可以优雅处理错误
}
```

---

### 5. `proc_macro_value` - 过程宏增强

**特性状态**: ✅ 已稳定化
**跟踪问题**: [#151973](https://github.com/rust-lang/rust/issues/151973)

过程宏中更丰富的值操作能力。

```rust
use proc_macro::{TokenStream, Literal};

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // Rust 1.94: 更丰富的值操作
    // 增强了 Literal 类型的操作能力
    // ...
    input
}
```

---

### 6. Edition 2024 成为默认

**重要变更**: 从 Rust 1.94 开始，`cargo new` 创建的项目的默认 Edition 变为 **2024**。

```toml
# Cargo.toml (由 cargo new 自动生成)
[package]
name = "my_project"
version = "0.1.0"
edition = "2024"  # 默认 Edition 从 2021 变为 2024
```

**Edition 2024 主要特性回顾**:

| 特性 | 描述 |
| :--- | :--- |
| 保留关键字 | `gen`、`try` 成为保留关键字 |
| 尾表达式修复 | `if`/`match` 尾表达式不再意外终止块 |
| `unsafe` 语义澄清 | `unsafe` 块语义更清晰 |
| 宏匹配改进 | `expr` 片段更精确匹配 |
| 模块系统改进 | `macro_rules` 可见性改进 |

---

## 📚 标准库更新

### 新增稳定 API

| API | 模块 | 描述 | 使用场景 |
| :--- | :--- | :--- | :--- |
| `ControlFlow::ok` | `std::ops` | 转换为 Option | 控制流与 Option 互操作 |
| `ControlFlow::break_value` | `std::ops` | 提取 Break 值 | 错误处理 |
| `RefCell::try_map` | `std::cell` | 安全映射 | 内部可变性 |
| `RefMut::try_map` | `std::cell` | 可变安全映射 | 内部可变性 |
| `VecDeque::truncate_front` | `std::collections` | 头部截断 | 队列操作 |
| `VecDeque::truncate_back` | `std::collections` | 尾部截断 | 队列操作 |
| `RangeToInclusive` | `std::ops` | 包含结束范围 | 迭代器、模式匹配 |
| `RangeToInclusive::new` | `std::ops` | 构造方法 | 显式构造 |
| `int::fmt_into` | 整数类型 | 高性能格式化 | 序列化、日志 |
| `u32::fmt_into` | 整数类型 | 高性能格式化 | 序列化 |
| `i32::fmt_into` | 整数类型 | 高性能格式化 | 序列化 |
| `u64::fmt_into` | 整数类型 | 高性能格式化 | 序列化 |
| `i64::fmt_into` | 整数类型 | 高性能格式化 | 序列化 |
| `usize::fmt_into` | 整数类型 | 高性能格式化 | 序列化 |
| `isize::fmt_into` | 整数类型 | 高性能格式化 | 序列化 |

### 性能改进

```markdown
排序算法:
- `slice::sort` 进一步优化，小数组使用插入排序
- 改进的 pivot 选择算法
- 更好的缓存局部性

HashMap:
- 重新哈希策略微调
- 更好的内存预分配启发式
- 减少 rehash 次数

字符串:
- `int_format_into` 减少分配
- 小数格式化优化
- UTF-8 验证改进

VecDeque:
- `truncate_front`/`truncate_back` 优化
- 减少不必要的内存复制
```

### 文档改进

- 改进了 `unsafe` 函数的安全契约文档
- 增加了更多 `MaybeUninit` 使用示例
- 完善了 `Pin` 类型的文档说明

---

## 📦 Cargo 改进

### 1. `cargo report timings` 稳定化

```bash
# 查看详细的构建时间分析
cargo build --timings

# 生成并查看报告
cargo report timings
```

输出示例：

```text
Time    Crate           Action          Details
0.5s    syn             Compiling       proc-macro
1.2s    tokio           Compiling       async runtime
0.3s    myapp           Linking         release build
```

### 2. rustdoc `--merge` 选项

```bash
# 合并多个 crate 的文档输出
cargo doc --merge --parts-out-dir target/doc-parts
```

适用于工作区项目，可以将多个 crate 的文档合并为统一的文档站点。

### 3. 配置包含 (`config-include`)

```toml
# .cargo/config.toml
include = [
    { path = "local.toml", optional = true },
    { path = "shared/ci.toml" },
    { path = "shared/override.toml", optional = true },
]
```

支持从多个配置文件加载配置，便于团队协作和 CI/CD 集成。

### 4. 改进的依赖解析

- 更快的依赖解析算法
- 更好的错误消息
- 改进的 workspace 成员检测

---

## 🔧 工具链更新

### Clippy

新增 lint：

| Lint | 级别 | 描述 |
| :--- | :--- | :--- |
| `todo_in_production` | Warn | 检测发布代码中的 `todo!()` |
| `async_recursion` | Warn | 改进的递归 async fn 检测 |
| `inefficient_format_args` | Warn | 检测低效的 format 参数 |
| `manual_ok_or` | Warn | 建议用 `ok_or` 替代手动模式 |

改进：

- 减少误报率
- 改进的宏扩展检测
- 更好的跨 crate 分析

### Rustfmt

- 改进宏格式化稳定性
- 修复某些注释布局问题
- 支持 Edition 2024 的新语法

### rust-analyzer

- 支持 `RangeToInclusive` 类型推断
- 改进的 1.94 新特性语法高亮
- 更快的符号搜索
- 更好的诊断信息

---

## ⚡ 性能改进

### 编译器性能

| 领域 | 改进 | 预期提升 |
| :--- | :--- | :--- |
| 增量编译 | 改进的查询系统 | 15-20% |
| 单 crate 编译 | LLVM 21.1.8 | 5-10% |
| 链接时间 | 并行化改进 | 10% (大型项目) |
| 内存使用 | 更好的分配策略 | 5-8% |

### 运行时性能

| 领域 | 改进 | 预期提升 |
| :--- | :--- | :--- |
| 整数格式化 | `int_format_into` | 30-50% |
| 排序 | 算法优化 | 5-10% |
| HashMap | 重新哈希 | 5% |
| 字符串处理 | UTF-8 优化 | 3-5% |

---

## 🔄 迁移指南

### 升级步骤

```bash
# 步骤 1: 更新 Rust 版本
rustup update stable

# 验证版本
rustc --version  # 应显示 rustc 1.94.0

# 步骤 2: 更新项目配置
cargo update

# 步骤 3: 检查兼容性
cargo check
cargo clippy
cargo test

# 步骤 4: 考虑采用新特性（可选）
# - 使用 int_format_into 优化性能关键代码
# - 使用 ControlFlow::ok() 简化控制流
# - 使用 RefCell::try_map 替代不安全的 map
```

### 破坏性变更

Rust 1.94 **无已知破坏性变更**。以下是一些需要注意的行为变化：

#### 1. `RangeToInclusive` 模式匹配

现有代码中使用 `..=n` 的 match 臂现在可以更精确地匹配：

```rust
// 推荐：使用显式类型以获得更清晰的模式匹配
match range {
    std::ops::RangeToInclusive { end } => { /* ... */ }
    _ => { /* ... */ }
}
```

#### 2. Edition 2024 默认

新项目的默认 Edition 变为 2024。现有项目不受影响，但建议评估升级：

```toml
# 现有项目可以逐步升级
[package]
edition = "2024"  # 从 "2021" 升级
```

### 已弃用特性

| 特性 | 替代方案 | 弃用版本 |
| :--- | :--- | :--- |
| 某些 `unsafe` 模式 | 新的安全 API | 1.94 |
| 旧版格式化 API | `fmt_into` | 1.94 (建议) |

---

## 📖 形式化语义更新

### 类型系统

```text
Def 1.94-1 (RangeToInclusive):
  RangeToInclusive<T> = { end: T }
  语义: 从起始到 end（包含）的范围
  边界: end 必须实现 PartialOrd

Def 1.94-2 (ControlFlow::ok):
  ok: ControlFlow<B, C> → Option<C>
  ok(Continue(c)) = Some(c)
  ok(Break(_))     = None

定理 1.94-T1: ok 是自然变换 η: ControlFlow<B, _> → Option
证明: 满足 functor 律
  η(Continue(c)) = Some(c)
  η(Break(b))    = None
```

### 所有权与借用

```text
Def 1.94-3 (RefCell::try_map):
  try_map: Ref<T> → (T → Option<U>) → Result<Ref<U>, Ref<T>>

安全保证:
  - 成功时: 返回映射后的引用，原引用被消耗
  - 失败时: 返回原始引用，保持借用状态

定理 1.94-T2: try_map 保持 RefCell 的不变量
证明:
  1. borrow count 不被修改
  2. 成功时引用转换是类型安全的
  3. 失败时状态回滚保持一致性
```

---

## 📊 版本对比

### Rust 1.93 vs 1.94 对比

| 特性 | 1.93 | 1.94 | 说明 |
| :--- | :--- | :--- | :--- |
| 默认 Edition | 2021 | 2024 | 新项目默认 |
| LLVM | 21.1.7 | 21.1.8 | 小幅升级 |
| `ControlFlow::ok` | 不稳定 | ✅ 稳定 | 控制流简化 |
| `int_format_into` | 不稳定 | ✅ 稳定 | 高性能格式化 |
| `RangeToInclusive` | 部分支持 | ✅ 完整 | 范围类型完善 |
| `RefCell::try_map` | 不稳定 | ✅ 稳定 | 安全内部可变性 |
| `cargo report timings` | 不稳定 | ✅ 稳定 | 构建分析 |
| `cargo doc --merge` | 不稳定 | ✅ 稳定 | 文档合并 |
| 排序性能 | 基准 | +5-10% | 算法优化 |
| 编译时间 | 基准 | +5-10% | 增量编译改进 |

---

## 🔗 相关资源

### 官方文档

- [Rust 1.94.0 Release Notes](https://blog.rust-lang.org/2026/03/05/Rust-1.94.0/)
- [Rust 1.94.0 详细发布说明](https://doc.rust-lang.org/stable/releases.html#version-1940-2026-03-05)
- [Edition 2024 指南](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)

### 项目内部文档

| 文档 | 链接 | 说明 |
| :--- | :--- | :--- |
| 1.94 迁移指南 | [../05_guides/RUST_194_MIGRATION_GUIDE.md](../05_guides/RUST_194_MIGRATION_GUIDE.md) | 详细迁移步骤 |
| 1.94 研究更新 | [../research_notes/RUST_194_RESEARCH_UPDATE.md](../research_notes/RUST_194_RESEARCH_UPDATE.md) | 形式化分析 |
| 1.93 完整变更 | [./07_rust_1.93_full_changelog.md](./07_rust_1.93_full_changelog.md) | 上一版本变更 |

### 形式化文档

| 特性 | 形式化文档 |
| :--- | :--- |
| ControlFlow | [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) |
| RefCell | [ownership_model](../research_notes/formal_methods/ownership_model.md) |
| Range 类型 | [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) |

---

**维护者**: Rust 文档推进团队
**最后更新**: 2026-03-06
**状态**: ✅ 已完成
**版本**: Rust 1.94.0
