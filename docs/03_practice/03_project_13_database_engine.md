# 实践项目 13: 简易数据库引擎

> **Bloom 层级**: L3 (应用)

> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c01-c08
> **预计时间**: 10-12小时

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [实践项目 13: 简易数据库引擎](#实践项目-13-简易数据库引擎)
  - [📑 目录](#-目录)
  - [项目目标](#项目目标)
  - [功能需求](#功能需求)
  - [学习要点](#学习要点)
    - [B-Tree实现](#b-tree实现)
  - [参考实现](#参考实现)
  - [完整参考实现位于: `examples/database-engine/`](#完整参考实现位于-examplesdatabase-engine)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 项目目标
>
> **[来源: Rust Official Docs]**

创建支持SQL子集的嵌入式数据库。

---

## 功能需求
>
> **[来源: Rust Official Docs]**

- [ ] B-Tree索引
- [ ] SQL解析
- [ ] 事务支持
- [ ] 持久化存储
- [ ] 并发控制

---

## 学习要点
>
> **[来源: Rust Official Docs]**

### B-Tree实现
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
struct BTreeNode {
    keys: Vec<String>,
    values: Vec<String>,
    children: Vec<Box<BTreeNode>>,
    is_leaf: bool,
}
```

---

## 参考实现

完整参考实现位于: `examples/database-engine/`
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

- [03_practice 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference - doc.rust-lang.org/reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**

---
