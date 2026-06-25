# 所有权概念卡片 - 全面深度解析

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **概念**: Ownership (所有权)
> **领域**: Rust编程语言核心机制
> **理论基础**: 仿射类型系统 (Affine Type System)、线性逻辑 (Linear Logic)
> **权威来源**: Rust官方文档, RustBelt (Jung et al., 2018), TAPL (Pierce, 2002)

---

## 目录
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

- [所有权概念卡片 - 全面深度解析](#所有权概念卡片---全面深度解析)
  - [目录](#目录)
  - [1. 概念定义 (Concept Definition)](#1-概念定义-concept-definition)
    - [1.1 形式化定义](#11-形式化定义)
    - [1.2 核心属性](#12-核心属性)
  - [2. 关系图谱](#2-关系图谱)
  - [3. 示例与反例](#3-示例与反例)
    - [正确示例](#正确示例)
    - [反例](#反例)
  - [4. 场景决策树](#4-场景决策树)
  - [5. 参考文献](#5-参考文献)
  - [权威来源索引](#权威来源索引)

## 1. 概念定义 (Concept Definition)
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 1.1 形式化定义
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```text
定义 1.1 (所有权 Ownership)
────────────────────────────────────────────────────────────
在Rust中，所有权是一个编译时概念，用于管理内存资源的唯一访问权。

形式化表示:
  Own(v, T) ≡ 值v具有类型T，且当前执行上下文持有v的唯一访问权

语义:
  Own(v, T) = true  ⟹  上下文可以读取、修改、转移或释放v
────────────────────────────────────────────────────────────
```

### 1.2 核心属性

| 属性 | 描述 | 数学基础 |
|------|------|---------|
| **唯一性** | 最多一个所有者 | 线性逻辑 |
| **可转移性** | 所有权可Move | 线性蕴含 |
| **作用域绑定** | 自动释放 | RAII |

---

## 2. 关系图谱

```text
                    所有权(Ownership)
                         │
        ┌────────────────┼────────────────┐
        │                │                │
        ▼                ▼                ▼
   ┌─────────┐     ┌──────────┐    ┌──────────┐
   │   Move  │     │  Borrow  │    │   Copy   │
   │ (转移)  │     │  (借用)  │    │  (复制)  │
   └────┬────┘     └────┬─────┘    └────┬─────┘
        │               │               │
        ▼               ▼               ▼
   ┌─────────┐     ┌──────────┐    ┌──────────┐
   │   Drop  │     │ &T/&mut T│    │  Clone   │
   │ (释放)  │     │(引用类型)│    │ (深拷贝) │
   └─────────┘     └──────────┘    └──────────┘
```

---

## 3. 示例与反例

### 正确示例

```rust
let s1 = String::from("hello");  // s1获得所有权
let s2 = s1;                      // 所有权转移到s2
println!("{}", s2);               // OK
```

### 反例

```rust,ignore
let s1 = String::from("hello");
let s2 = s1;
println!("{}", s1);  // 错误: 使用了已移动的值
```

---

## 4. 场景决策树

```text
开始
  │
  ├─ 需要多个所有者? ─┬─ 是 ─→ Rc<T> / Arc<T>
  │                   └─ 否
  │
  ├─ 需要修改? ─┬─ 是 ─→ &mut T / RefCell<T>
  │             └─ 否 ─→ &T
  │
  └─ 默认 ─→ Move语义
```

---

## 5. 参考文献

1. Rust官方文档: The Rust Programming Language
2. Jung et al. (2018). RustBelt. POPL.
3. Pierce, B.C. (2002). TAPL. MIT Press.

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- Parent README

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**

> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**
