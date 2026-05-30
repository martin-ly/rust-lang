# 形式化验证前沿

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **难度**: 🔴 高级
> **主题**: 定理证明、模型检测、Rust 验证工具链

---

## 📑 目录
>
- [形式化验证前沿](#形式化验证前沿)
  - [📑 目录](#目录)
  - [当前研究热点](#当前研究热点)
    - [1. RustBelt 项目](#1-rustbelt-项目)
    - [2. Aeneas 项目](#2-aeneas-项目)
    - [3. Kani / CBMC](#3-kani--cbmc)
  - [开放问题](#开放问题)
  - [相关工具](#相关工具)
  - *文档版本: 1.0.0*
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 当前研究热点
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 1. RustBelt 项目
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

RustBelt 是首个完整的 Rust 形式化安全证明。

```
核心成果:
- 在 Iris (分离逻辑框架) 中形式化 Rust 核心
- 证明标准库原语的安全性
- 处理 unsafe 代码的模块化验证
```

### 2. Aeneas 项目
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

将 Rust 翻译到纯函数式语言进行验证。

```rust,ignore
// Rust 代码
type List = Option<Box<Node>>;

// 翻译为 (类似):
// type List = ListCons u32 List | ListNil
// 然后使用 Lean/Coq 证明
```

### 3. Kani / CBMC

模型检测 Rust 代码的状态空间。

```bash
# 验证所有可能输入
cargo kani --function my_function
```

---

## 开放问题

1. **Unsafe 代码验证**: 如何模块化验证 unsafe 块?
2. **异步/并发**: 形式化验证 async/await 的正确性
3. **性能模型**: 形式化推理与运行时性能的关系
4. **类型系统扩展**: GAT、泛型关联类型的元理论

---

## 相关工具

| 工具 | 方法 | 状态 |
|-----|------|------|
| Creusot | 前置/后置条件 | 活跃开发 |
| Kani | 模型检测 | 生产可用 |
| Aeneas | 程序翻译 | 研究阶段 |
| RustBelt | 分离逻辑 | 研究完成 |

---

*文档版本: 1.0.0*
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

- [10-research-frontiers 目录](./README.md)
- [上级目录](../README.md)

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
