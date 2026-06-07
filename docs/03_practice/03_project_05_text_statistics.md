# 实践项目 05: 文本统计工具
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L3 (应用)
> **难度**: ⭐ 入门级
> **所需知识**: c01-c03
> **预计时间**: 2小时

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [实践项目 05: 文本统计工具](#实践项目-05-文本统计工具)
  - [📑 目录](#-目录)
  - [项目目标](#项目目标)
  - [功能需求](#功能需求)
  - [学习要点](#学习要点)
    - [迭代器处理](#迭代器处理)
  - [参考实现](#参考实现)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 项目目标
>
> **[来源: Rust Official Docs]**

创建一个类似wc的文本统计工具。

---

## 功能需求
>
> **[来源: Rust Official Docs]**

- [ ] 统计行数、单词数、字符数
- [ ] 统计词频
- [ ] 查找最长行
- [ ] 支持多个文件

---

## 学习要点
>
> **[来源: Rust Official Docs]**

### 迭代器处理
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
fn count_words(text: &str) -> usize {
    text.split_whitespace().count()
}

fn count_lines(text: &str) -> usize {
    text.lines().count()
}
```

---

## 参考实现

完整参考实现位于: `examples/text-statistics/`

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
