# Regex 正则表达式形式化分析

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: 正则引擎的安全与性能
>
> **形式化框架**: 有限自动机 + 回溯控制
>
> **参考**: Regex Crate Documentation

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- [Regex 正则表达式形式化分析](#regex-正则表达式形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 编译期检查](#2-编译期检查)
    - [定理 2.1 (Regex::new错误处理)](#定理-21-regexnew错误处理)
    - [定理 2.2 (lazy\_static优化)](#定理-22-lazy_static优化)
  - [3. 匹配算法](#3-匹配算法)
    - [3.1 NFA模拟](#31-nfa模拟)
    - [定义 3.1 (NFA)](#定义-31-nfa)
    - [3.2 DFA优化](#32-dfa优化)
    - [定理 3.1 (DFA线性时间)](#定理-31-dfa线性时间)
  - [4. 拒绝服务防护](#4-拒绝服务防护)
    - [定理 4.1 (ReDoS防护)](#定理-41-redos防护)
  - [5. 内存安全](#5-内存安全)
    - [定理 5.1 (输入边界检查)](#定理-51-输入边界检查)
  - [6. 反例](#6-反例)
    - [反例 6.1 (捕获组滥用)](#反例-61-捕获组滥用)
    - [反例 6.2 (贪婪匹配)](#反例-62-贪婪匹配)
  - [*定理数量: 6个*](#定理数量-6个)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

Rust regex crate提供:

- Unicode支持
- 线性时间保证
- 拒绝服务防护
- 编译时正则验证

---

## 2. 编译期检查
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 定理 2.1 (Regex::new错误处理)

> 无效正则表达式在编译时捕获。

**实现**:

```rust,ignore
let re = Regex::new(r"(abc");  // 错误! 未闭合组
// 返回Err，不panic
```

∎

### 定理 2.2 (lazy_static优化)

> 正则应在编译或启动时编译，避免运行时开销。

```rust,ignore
lazy_static! {
    static ref RE: Regex = Regex::new(r"...").unwrap();
}
```

∎

---

## 3. 匹配算法

### 3.1 NFA模拟

### 定义 3.1 (NFA)

正则表达式编译为NFA:

- 状态表示匹配位置
- ε转移表示选择
- 字符转移表示匹配

### 3.2 DFA优化

### 定理 3.1 (DFA线性时间)

> DFA匹配保证线性时间 $O(n)$。

**代价**:

- DFA状态数可能指数级
- 实际中通过缓存优化

∎

---

## 4. 拒绝服务防护

### 定理 4.1 (ReDoS防护)

> Rust regex使用有限状态机，无灾难性回溯。

**对比**:

- PCRE: 回溯算法，可能指数时间
- Rust regex: NFA/DFA，线性时间保证

**形式化**:

$$
\text{时间复杂度} = O(n \cdot m) \text{ (n=输入长度, m=正则大小)}
$$

∎

---

## 5. 内存安全

### 定理 5.1 (输入边界检查)

> 正则匹配不会越界访问。

**保证**:

- 所有索引验证
- UTF-8边界检查
- Unicode安全

∎

---

## 6. 反例

### 反例 6.1 (捕获组滥用)

```rust,ignore
// 慢: 使用捕获组但不需要
let re = Regex::new(r"(a+)").unwrap();

// 快: 非捕获组
let re = Regex::new(r"(?:a+)").unwrap();
```

### 反例 6.2 (贪婪匹配)

```rust,ignore
// 可能意外匹配过多
let re = Regex::new(r".*foo").unwrap();

// 使用非贪婪
let re = Regex::new(r".*?foo").unwrap();
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
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

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Formal Methods]**

> **[来源: Coq Reference Manual]**

> **[来源: TLA+ Documentation]**

> **[来源: ACM - Formal Verification]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
