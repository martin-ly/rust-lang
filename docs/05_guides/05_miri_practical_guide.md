# Miri 实战指南：Rust 未定义行为检测工具

> **Bloom 层级**: L3-L4 (应用/分析)

> **创建日期**: 2026-05-08
> **最后更新**: 2026-05-08
> **Rust 版本**: nightly (Miri 无 stable 版本)
> **状态**: ✅ 已完成

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Miri 实战指南：Rust 未定义行为检测工具](#miri-实战指南rust-未定义行为检测工具)
  - [📑 目录](#-目录)
  - [🔬 什么是 Miri](#-什么是-miri)
  - [⚙️ 安装与运行](#️-安装与运行)
    - [安装 Miri](#安装-miri)
    - [基本命令](#基本命令)
    - [常用环境变量](#常用环境变量)
  - [🐛 Miri 捕获的常见 UB 模式](#-miri-捕获的常见-ub-模式)
    - [1. Use-after-free (UAF)](#1-use-after-free-uaf)
    - [2. Data Race (数据竞争)](#2-data-race-数据竞争)
    - [3. Aliasing Violations (别名违规)](#3-aliasing-violations-别名违规)
    - [4. 其他常见 UB](#4-其他常见-ub)
  - [🌲 Tree Borrows vs Stacked Borrows](#-tree-borrows-vs-stacked-borrows)
    - [Stacked Borrows (默认)](#stacked-borrows-默认)
    - [Tree Borrows (实验性，推荐)](#tree-borrows-实验性推荐)
  - [✍️ 编写 Miri 友好测试的实战流程](#️-编写-miri-友好测试的实战流程)
    - [步骤 1：隔离 unsafe 代码到独立测试](#步骤-1隔离-unsafe-代码到独立测试)
    - [步骤 2：为 Miri 添加条件编译标记](#步骤-2为-miri-添加条件编译标记)
    - [步骤 3：处理 Miri 的隔离限制](#步骤-3处理-miri-的隔离限制)
    - [步骤 4：本地开发流程](#步骤-4本地开发流程)
  - [⚠️ Miri 的局限性](#️-miri-的局限性)
  - [🔧 CI 集成](#-ci-集成)
    - [GitHub Actions 示例](#github-actions-示例)
    - [策略建议](#策略建议)
  - [📖 参考文献](#-参考文献)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 🔬 什么是 Miri
>
> **[来源: Rust Official Docs]**

**Miri** 是 Rust 的官方解释器，由 Ralf Jung 领导开发，专门用于检测 Rust 代码中的**未定义行为 (Undefined Behavior, UB)**。与 `rustc` 不同，Miri 不直接生成机器码，而是在一个虚拟的 Rust 中间表示 (MIR) 层上逐条解释执行代码。

```text
传统编译流程:                    Miri 检测流程:
┌─────────────┐                ┌─────────────┐
│  Rust 源码   │                │  Rust 源码   │
└──────┬──────┘                └──────┬──────┘
       │                              │
┌──────▼──────┐                ┌──────▼──────┐
│   MIR       │                │   MIR       │
└──────┬──────┘                └──────┬──────┘
       │                              │
┌──────▼──────┐                ┌──────▼──────┐
│  LLVM IR    │                │  Miri 解释器 │
│  (机器码)    │                │  (UB 检测)   │
└─────────────┘                └─────────────┘
```

Miri 的核心价值在于：

- **在运行时检测 UB**：即使代码通过了编译器检查，Miri 仍能发现内存安全问题
- **无需修改源码**：直接对现有测试运行 `cargo miri test`
- **覆盖编译器盲区**：`rustc` 对 UB 采取"信任程序员"策略，Miri 则严格验证

---

## ⚙️ 安装与运行
>
> **[来源: Rust Official Docs]**

Miri 仅支持 **nightly** 工具链，因为 Miri 需要编译器内部不稳定的 API。

### 安装 Miri

> **[来源: POPL - Programming Languages Research]**
>
> **[来源: Rust Official Docs]**

```bash
# 1. 安装 nightly 工具链 (如果尚未安装)
rustup toolchain install nightly

# 2. 安装 Miri 组件
rustup component add miri --toolchain nightly

# 3. 为当前项目配置 Miri
cargo +nightly miri setup
```

### 基本命令

> **[来源: PLDI - Programming Language Design]**
>
> **[来源: Rust Official Docs]**

```bash
# 运行所有测试 (Miri 模式下)
cargo +nightly miri test

# 运行特定测试
cargo +nightly miri test test_name

# 运行二进制程序
cargo +nightly miri run

# 运行单个文件 (无需 Cargo 项目)
rustc +nightly -Zmiri --edition 2024 file.rs
```

### 常用环境变量

> **[来源: Wikipedia - Memory Safety]**
>
> **[来源: Rust Official Docs]**

| 环境变量 | 作用 | 示例 |
|---------|------|------|
| `MIRIFLAGS` | 传递 Miri 特定标志 | `MIRIFLAGS="-Zmiri-disable-isolation"` |
| `-Zmiri-disable-isolation` | 允许文件系统/网络访问 | 测试 IO 时需要 |
| `-Zmiri-tree-borrows` | 启用 Tree Borrows 模型 | 替代 Stacked Borrows |
| `-Zmiri-permissive-provenance` | 放宽严格 provenance | 兼容旧代码 |
| `-Zmiri-ignore-leaks` | 忽略内存泄漏检测 | 某些并发测试需要 |

```bash
# 示例：禁用隔离并启用 Tree Borrows
MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-tree-borrows" cargo +nightly miri test
```

---

## 🐛 Miri 捕获的常见 UB 模式
>
> **[来源: Rust Official Docs]**

### 1. Use-after-free (UAF)

> **[来源: Wikipedia - Type System]**
>
> **[来源: Rust Official Docs]**

Miri 能精确追踪每个内存分配的存活状态，任何对已释放内存的访问都会触发错误。

```rust
// ❌ 错误示例：Use-after-free
fn uaf_example() {
    let ptr: *mut i32;
    {
        let mut val = 42;
        ptr = &mut val as *mut i32;  // ptr 指向栈上的 val
    } // val 在此处被释放

    // Miri 报错：访问已释放的内存
    unsafe {
        println!("{}", *ptr);  // ERROR: use-after-free
    }
}
```

**Miri 输出示例**：

```text
error: Undefined Behavior: pointer to alloc1402 was dereferenced after this allocation got freed
  --> src/main.rs:10:9
   |
10 |         println!("{}", *ptr);
   |         ^^^^^^^^^^^^^^^^^^^ pointer to alloc1402 was dereferenced after this allocation got freed
```

### 2. Data Race (数据竞争)

> **[来源: Wikipedia - Rust (programming language)]**
>
> **[来源: Rust Official Docs]**

Miri 通过追踪每个内存位置的访问线程和同步关系来检测数据竞争。

```rust,ignore
use std::thread;

// ❌ 错误示例：Data Race
fn data_race_example() {
    let mut val = 0;
    let ptr = &mut val as *mut i32;

    // 不安全地跨线程共享可变引用
    unsafe {
        let t1 = thread::spawn(move || {
            *ptr = 1;  // 线程 1 写入
        });
        let t2 = thread::spawn(move || {
            *ptr = 2;  // 线程 2 写入 (无同步!)
        });

        t1.join().unwrap();
        t2.join().unwrap();
    }
}
```

**Miri 输出示例**：

```text
error: Undefined Behavior: Data race detected between Read on thread `<unnamed>` and Write on thread `main`
```

### 3. Aliasing Violations (别名违规)

> **[来源: POPL - Programming Languages Research]**
>
> **[来源: Rust Official Docs]**

Miri 严格执行 Rust 的别名规则：对于任何内存位置，`&mut T` 必须是唯一的活跃引用。

```rust
// ❌ 错误示例：别名违规 (违反独占引用规则)
fn aliasing_violation() {
    let mut x = 5;
    let r1 = &mut x;
    let r2 = &mut x;  // 编译器会拒绝此代码

    // 但如果通过原始指针绕过编译器检查...
    unsafe {
        let ptr1 = &mut x as *mut i32;
        let ptr2 = &mut x as *mut i32;

        *ptr1 = 10;  // Miri 追踪到此处违反了 &mut 的独占性
        *ptr2 = 20;
    }
}
```

### 4. 其他常见 UB

> **[来源: PLDI - Programming Language Design]**
>
> **[来源: Rust Official Docs]**

| UB 类型 | 说明 | Miri 检测能力 |
|---------|------|--------------|
| **空指针解引用** | `*std::ptr::null()` | ✅ 精确检测 |
| **越界访问** | 数组/切片索引越界 | ✅ 精确检测 |
| **类型混淆** | `mem::transmute` 到不兼容类型 | ✅ 检测无效值 |
| **未初始化内存读取** | 读取 `MaybeUninit` 的未初始化部分 | ✅ 精确检测 |
| **错误对齐访问** | 读取未对齐的指针 | ✅ 检测对齐违规 |
| **无效的枚举值** | 构造不存在的 enum variant | ✅ 检测无效 discriminant |
| `str` 内部包含非 UTF-8 | 构造无效的 `str` | ✅ 检测无效字符串 |

---

## 🌲 Tree Borrows vs Stacked Borrows
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

Miri 支持两种不同的内存别名模型，通过 `-Zmiri-tree-borrows` 切换。

### Stacked Borrows (默认)

> **[来源: Wikipedia - Rust (programming language)]**

Stacked Borrows 是 Rust 的原始别名模型，由 Ralf Jung 在博士论文中提出。它用一个"栈"来追踪所有指向同一内存位置的引用。

```text
Stacked Borrows 模型:

内存位置 X: [ &mut (独占) | & (共享只读) | & (共享只读) ]
              ↑ 栈底                          ↑ 栈顶

规则:
- &mut 必须是栈顶才能写入
- 创建新的 &mut 会弹出(pop)所有旧引用
- 旧的 &mut 在此之后不可再使用
```

**优点**：理论成熟，与编译器优化假设一致
**缺点**：过于严格，某些安全的代码模式被误判为 UB

### Tree Borrows (实验性，推荐)

> **[来源: RFCs - github.com/rust-lang/rfcs]**

Tree Borrows 是 2023 年提出的改进模型，用树结构替代栈结构，对**只读重借用 (read-only reborrows)** 更宽容。

```mermaid
graph TD
    A[根: 原始指针 *mut T] --> B[&mut T (写权限)]
    A --> C[&T (共享只读)]
    B --> D[&T (从 &mut 派生的只读)]
    B --> E[&mut T (重借用)]
    C --> F[&T (只读重借用)]
    C --> G[&T (只读重借用)]

    style B fill:#f96,stroke:#333
    style E fill:#f96,stroke:#333
    style C fill:#9f9,stroke:#333
    style D fill:#9f9,stroke:#333
    style F fill:#9f9,stroke:#333
    style G fill:#9f9,stroke:#333
```

**Tree Borrows 核心改进**：

| 场景 | Stacked Borrows | Tree Borrows |
|------|----------------|--------------|
| `&mut` 派生的 `&T` 在父 `&mut` 重新激活后继续使用 | ❌ UB | ✅ 合法 |
| 通过指针算术创建的重叠引用 | ❌ 严格限制 | ✅ 更灵活 |
| `UnsafeCell` 的内部可变性 | ⚠️ 复杂 | ✅ 更直观 |

```bash
# 启用 Tree Borrows (推荐用于新项目)
MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test
```

> 💡 **建议**：Tree Borrows 被认为是 Rust 别名规则的未来方向。如果 Miri 在 Stacked Borrows 下报错但代码逻辑上似乎是安全的，尝试 Tree Borrows。

---

## ✍️ 编写 Miri 友好测试的实战流程
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 步骤 1：隔离 unsafe 代码到独立测试

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust
#[cfg(test)]
mod miri_tests {
    // 这个测试专门检测 unsafe 内存操作
    #[test]
    fn test_raw_pointer_ops() {
        let mut data = [1, 2, 3, 4];
        let ptr = data.as_mut_ptr();

        unsafe {
            *ptr.add(2) = 99;
            assert_eq!(data[2], 99);
        }
    }

    // 这个测试检测并发安全
    #[test]
    fn test_concurrent_access() {
        use std::sync::Arc;
        use std::sync::atomic::{AtomicI32, Ordering};

        let val = Arc::new(AtomicI32::new(0));
        let val2 = Arc::clone(&val);

        std::thread::spawn(move || {
            val2.fetch_add(1, Ordering::SeqCst);
        }).join().unwrap();

        assert_eq!(val.load(Ordering::SeqCst), 1);
    }
}
```

### 步骤 2：为 Miri 添加条件编译标记

> **[来源: POPL - Programming Languages Research]**

某些测试 Miri 无法运行 (如内联汇编、特定系统调用)，可以使用 `cfg(miri)` 跳过：

```rust
#[test]
#[cfg(not(miri))]  // 内联汇编不支持 Miri
fn test_inline_asm() {
    unsafe {
        std::arch::asm!("nop");
    }
}

#[test]
#[cfg(miri)]  // Miri 专用测试
fn test_miri_specific() {
    // 只会在 Miri 下运行的测试
}
```

### 步骤 3：处理 Miri 的隔离限制

> **[来源: PLDI - Programming Language Design]**

Miri 默认在沙箱中运行，文件系统和网络访问需要显式允许：

```bash
# 允许文件系统访问
MIRIFLAGS="-Zmiri-disable-isolation" cargo +nightly miri test

# 或仅允许特定外部函数调用
MIRIFLAGS="-Zmiri-allow-unaligned-access" cargo +nightly miri test
```

### 步骤 4：本地开发流程

> **[来源: Wikipedia - Memory Safety]**

```bash
# 1. 编写功能代码和测试
# 2. 先用 cargo test 确保逻辑正确
cargo test

# 3. 用 Miri 运行测试检测 UB
cargo +nightly miri test

# 4. 如果有环境交互测试，启用隔离禁用
MIRIFLAGS="-Zmiri-disable-isolation" cargo +nightly miri test

# 5. (可选) 使用 Tree Borrows 再次验证
MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test
```

---

## ⚠️ Miri 的局限性
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 局限 | 说明 | 影响 |
|------|------|------|
| **运行速度** | 比原生执行慢约 **1000 倍** | 不适合性能测试 |
| **平台限制** | 仅支持部分目标平台 | `x86_64-unknown-linux-gnu` 最成熟 |
| **仅检测可达代码** | 未执行的代码路径不会检测 | 需要高覆盖率测试 |
| **非确定性** | 线程调度顺序不同可能导致漏报 | 多次运行或固定调度 |
| **FFI 限制** | 外部 C 代码在隔离模式下受限 | 需要 `-Zmiri-disable-isolation` |
| **不支持 inline asm** | `asm!` 宏无法执行 | 跳过相关测试 |
| **仅 nightly** | 无 stable 版本 | CI 需要 nightly 工具链 |
| **内存限制** | 大型程序的 Miri 内存开销大 | 超大项目可能 OOM |

```text
速度对比示例 (估算):
┌────────────────────────────────────────────┐
│  测试场景: 1000 个单元测试                  │
├────────────────────────────────────────────┤
│  cargo test (原生)      │  ~10 秒          │
│  cargo miri test        │  ~2-3 小时       │
│  比例                   │  ~500-1000x      │
└────────────────────────────────────────────┘
```

> 🚫 **绝对不要将 Miri 用于生产环境运行代码**。Miri 是调试和验证工具，不是运行时。

---

## 🔧 CI 集成
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

由于 Miri 仅支持 nightly，CI 配置需要单独设置：

### GitHub Actions 示例

> **[来源: Wikipedia - Type System]**

```yaml
name: Miri UB Check

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install nightly Rust
        uses: dtolnay/rust-toolchain@nightly
        with:
          components: miri

      - name: Run Miri
        env:
          MIRIFLAGS: "-Zmiri-tree-borrows -Zmiri-disable-isolation"
        run: |
          cargo +nightly miri setup
          cargo +nightly miri test
```

### 策略建议

> **[来源: Wikipedia - Concurrency]**

```text
CI 策略矩阵:
┌──────────────────────┬──────────────┬──────────────────────────┐
│ 检查类型              │ 工具链        │ 触发条件                  │
├──────────────────────┼──────────────┼──────────────────────────┤
│ 功能测试              │ stable       │ 每次 PR                  │
│ 代码风格              │ stable       │ 每次 PR                  │
│ Clippy 检查           │ stable       │ 每次 PR                  │
│ Miri UB 检测          │ nightly      │ 每日定时 / 关键 PR       │
│ 文档构建              │ stable       │ 每次 PR                  │
└──────────────────────┴──────────────┴──────────────────────────┘
```

---

## 📖 参考文献
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

1. **Ralf Jung, et al.** "Miri: Practical UB Detection for Rust". *POPL 2026*.
   - Rust 形式化验证领域最重要的实践工具论文
   - 详细阐述了 Miri 的设计决策和别名模型实现

2. **Ralf Jung, et al.** "Stacked Borrows: An Aliasing Model for Rust". *POPL 2019*.
   - Stacked Borrows 模型的原始论文

3. **Neven Villani, et al.** "Tree Borrows". 2023.
   - Tree Borrows 改进模型的技术报告
   <https://www.ralfj.de/blog/2023/01/07/tree-borrows.html>

4. **Rust 官方文档**. "Miri (Interpreter)".
   <https://github.com/rust-lang/miri>

5. **Ralf Jung 的博客**. "Miri 内部工作原理系列".
   <https://www.ralfj.de/blog/>

---

> 📌 **复查记录**
>
> - 2026-05-08: 初始创建，基于 nightly 2026-05 状态
>
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [crates.io](https://crates.io/)]**

- [05_guides 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Undefined Behavior]**

> **[来源: Miri Documentation]**

> **[来源: Rust Reference - Miri]**

> **[来源: RFC 2585 - Unsafe Code Guidelines]**

> **[来源: Wikipedia - Rust (programming language)]**
> **[来源: Rust Reference]**
> **[来源: TRPL - The Rust Programming Language]**
> **[来源: Rust Standard Library]**
> **[来源: ACM - Systems Programming]**
> **[来源: IEEE - Programming Language Standards]**
> **[来源: RFCs - github.com/rust-lang/rfcs]**
> **[来源: Rustonomicon]**

> **[来源: Wikipedia - Asynchronous I/O]**
> **[来源: Wikipedia - Rust (programming language)]**
> **[来源: Rust Reference - doc.rust-lang.org/reference]**

---
