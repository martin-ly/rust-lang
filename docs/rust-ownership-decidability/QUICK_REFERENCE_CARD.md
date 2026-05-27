# Rust 所有权系统 - 快速参考卡片

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> 一页纸速查，核心概念快速回顾

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 所有权系统 - 快速参考卡片](#rust-所有权系统---快速参考卡片)
  - [📑 目录](#-目录)
  - [🎯 所有权三原则](#-所有权三原则)
  - [🔄 借用规则](#-借用规则)
  - [⏱️ 生命周期规则](#️-生命周期规则)
  - [🧠 智能指针速查](#-智能指针速查)
  - [🎨 常见模式](#-常见模式)
    - [RAII 模式](#raii-模式)
    - [类型状态模式](#类型状态模式)
    - [内部可变性](#内部可变性)
  - [⚡ 并发 Send/Sync](#-并发-sendsync)
  - [🔧 错误快速修复](#-错误快速修复)
  - [📊 验证工具](#-验证工具)
  - [📚 快速导航](#-快速导航)
  - [🎓 学习路径](#-学习路径)
  - [🔗 关键链接](#-关键链接)
  - [🆕 Rust 1.94 所有权系统更新](#-rust-194-所有权系统更新)
    - [新特性对所有权系统的影响](#新特性对所有权系统的影响)
    - [形式化更新](#形式化更新)
  - [**最后更新**: 2026-03-14](#最后更新-2026-03-14)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 🎯 所有权三原则
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust,ignore
1. 唯一性     // 每个值有且仅有一个所有者
2. 作用域绑定 // 所有者离开作用域时释放值
3. 可转移性   // 所有权可以转移 (Move)
```

---

## 🔄 借用规则
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust,ignore
// 不可变借用: 多个 &T 同时存在
let r1 = &data;
let r2 = &data;  // OK

// 可变借用: 仅一个 &mut T
let r = &mut data;  // OK
// let r2 = &mut data;  // 错误!
// let r3 = &data;      // 错误!

// XOR 规则: 不能同时存在可变和不可变借用
```

---

## ⏱️ 生命周期规则
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```rust,ignore
// 编译器自动推断 (省略规则)
fn first(x: &str) -> &str { &x[0..1] }

// 显式注解 (多输入)
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str

// 'static: 整个程序生命周期
let s: &'static str = "编译期字符串";
```

---

## 🧠 智能指针速查
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 指针 | 用途 | Send | Sync |
|:-----|:-----|:----:|:----:|
| `Box<T>` | 堆分配 | T: Send | T: Sync |
| `Rc<T>` | 共享所有权(单线程) | ❌ | ❌ |
| `Arc<T>` | 共享所有权(多线程) | ✅ | ✅ |
| `RefCell<T>` | 内部可变性(单线程) | ❌ | ❌ |
| `Mutex<T>` | 内部可变性(多线程) | ✅ | ✅ |

---

## 🎨 常见模式
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### RAII 模式
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust,ignore
pub struct LockGuard<'a> {
    lock: &'a Lock,
}

impl<'a> Drop for LockGuard<'a> {
    fn drop(&mut self) {
        self.lock.release();
    }
}
```

### 类型状态模式
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust,ignore
pub struct Ready;
pub struct Running;

impl Connection<Ready> {
    pub fn start(self) -> Connection<Running>;
}
```

### 内部可变性
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust
use std::cell::RefCell;
let data = RefCell::new(5);
*data.borrow_mut() += 1;
```

---

## ⚡ 并发 Send/Sync
>
> **[来源: [crates.io](https://crates.io/)]**

```rust,ignore
// Send: 可跨线程转移所有权
// Sync: 可跨线程共享引用 (&T: Send)

// 自动实现规则:
impl Send for T where T: Send { }
impl Sync for T where &T: Send { }

// 常见类型:
// i32: Send + Sync
// Rc<T>: !Send, !Sync
// Arc<T>: Send + Sync (if T: Send + Sync)
// RefCell<T>: Send (if T: Send), !Sync
// Mutex<T>: Send + Sync (if T: Send)
```

---

## 🔧 错误快速修复
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 错误 | 修复方法 |
|:-----|:---------|
| E0382 (use of moved) | `.clone()` 或改用 `&T` |
| E0499 (multi mut) | 使用作用域或 `RefCell` |
| E0502 (mut + immut) | 顺序化借用 |
| E0597 (lifetime) | 延长作用域或 `Rc/Arc` |

---

## 📊 验证工具
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 工具 | 用途 | 命令 |
|:-----|:-----|:-----|
| Miri | UB 检测 | `cargo miri run` |
| Kani | 模型检测 | `cargo kani` |
| Clippy | Lint | `cargo clippy` |

---

## 📚 快速导航
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
📖 理论
├── UNIFIED_THEORETICAL_FRAMEWORK.md  // 统一框架
├── THEOREM_DEPENDENCY_GRAPH.md       // 定理依赖
└── coq-formalization/                // Coq证明

💻 实践
├── INTERACTIVE_LEARNING_GUIDE.md     // 交互学习
├── exercises/                        // 练习题
└── case-studies/                     // 案例分析

❓ 参考
├── COMPREHENSIVE_FAQ.md              // FAQ
├── ERROR_DIAGNOSTICS_GUIDE.md        // 错误诊断
└── QUICK_REFERENCE_CARD.md           // 本卡片
```

---

## 🎓 学习路径
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
初学者: 概念卡片 → 交互指南 → 基础练习
进阶:   详细概念 → 设计模式 → 案例研究
专家:   理论框架 → Coq证明 → 研究前沿
```

---

## 🔗 关键链接
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [完整认证](./FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md)
- [知识梳理](./COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md)
- [案例索引](case-studies/COMPLETE_DOMAIN_COVERAGE_INDEX.md)

---

*打印此页，随时查阅* 🖨️

---

## 🆕 Rust 1.94 所有权系统更新
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **适用版本**: Rust 1.94.0+

### 新特性对所有权系统的影响
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 特性 | 所有权影响 | 可判定性 |
|------|-----------|---------|
| rray_windows | 安全的切片访问 | ✅ 编译期检查 |
| ControlFlow | 控制流语义 | ✅ 类型安全 |
| LazyCell/LazyLock | 延迟初始化 | ✅ Send/Sync 检查 |

### 形式化更新

- rray_windows 的边界安全证明
- ControlFlow 的代数性质
- 延迟初始化的生命周期分析

**最后更新**: 2026-03-14
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [rust-ownership-decidability 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
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

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
