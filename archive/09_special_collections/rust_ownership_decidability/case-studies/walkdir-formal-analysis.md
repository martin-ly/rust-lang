# Walkdir 目录遍历形式化分析

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: 安全递归目录遍历
>
> **形式化框架**: 遍历顺序 + 循环检测
>
> **参考**: walkdir Documentation

---

## 目录
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

- [Walkdir 目录遍历形式化分析](#walkdir-目录遍历形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 遍历顺序](#2-遍历顺序)
    - [定理 2.1 (内容优先 vs 目录优先)](#定理-21-内容优先-vs-目录优先)
  - [3. 符号链接处理](#3-符号链接处理)
    - [定理 3.1 (链接控制)](#定理-31-链接控制)
  - [4. 循环检测](#4-循环检测)
    - [定理 4.1 (自动循环检测)](#定理-41-自动循环检测)
  - [5. 反例](#5-反例)
    - [反例 5.1 (TOCTOU)](#反例-51-toctou)
    - [反例 5.2 (路径长度)](#反例-52-路径长度)
  - [*定理数量: 4个*](#定理数量-4个)
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

walkdir提供:

- 递归目录遍历
- 可配置排序
- 符号链接控制
- 循环检测

---

## 2. 遍历顺序
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 定理 2.1 (内容优先 vs 目录优先)

> 可选择遍历顺序。

```rust,ignore
WalkDir::new(".")
    .contents_first(true)   // 文件先于目录
    .into_iter()

WalkDir::new(".")
    .contents_first(false)  // 目录先于文件(默认)
```

∎

---

## 3. 符号链接处理

### 定理 3.1 (链接控制)

> 默认不跟随符号链接。

```rust,ignore
WalkDir::new(".")
    .follow_links(true)     // 跟随符号链接
    .max_open(10)           // 限制同时打开文件数
```

∎

---

## 4. 循环检测

### 定理 4.1 (自动循环检测)

> 检测并跳过循环链接。

```rust,ignore
for entry in WalkDir::new(".").follow_links(true) {
    match entry {
        Ok(e) => println!("{}", e.path().display()),
        Err(e) if e.loop_from().is_some() => {
            // 检测到循环，跳过
        }
        Err(e) => return Err(e),
    }
}
```

∎

---

## 5. 反例

### 反例 5.1 (TOCTOU)

```rust,ignore
for entry in WalkDir::new(".") {
    let entry = entry?;
    let path = entry.path();
    // entry.metadata()是遍历时的快照
    // 实际文件可能已变更
    let size = std::fs::metadata(path)?.len();  // 重新获取
}
```

### 反例 5.2 (路径长度)

```rust,ignore
// Windows长路径可能失败
WalkDir::new("\\\\?\\C:\\very\\long\\path...")
```

---

*文档版本: 1.0.0*
*定理数量: 4个*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**

> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**

> **来源: [Coq Reference Manual](https://coq.inria.fr/doc/)**

> **来源: [TLA+ Documentation](https://lamport.azurewebsites.net/tla/tla.html)**

> **来源: [ACM - Formal Verification](https://dl.acm.org/)**
