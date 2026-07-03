# 实践项目 04: 密码生成器 {#实践项目-04-密码生成器}

> **EN**: Project 04 Password Generator
> **Summary**: 实践项目 04 Project 04 Password Generator.
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L3 (应用)
> **难度**: ⭐ 入门级
> **所需知识**: c01-c03
> **预计时间**: 1-2小时

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [实践项目 04: 密码生成器 {#实践项目-04-密码生成器}](#实践项目-04-密码生成器-实践项目-04-密码生成器)
  - [📑 目录 {#目录}](#-目录-目录)
  - [项目目标 {#项目目标}](#项目目标-项目目标)
  - [功能需求 {#功能需求}](#功能需求-功能需求)
  - [学习要点 {#学习要点}](#学习要点-学习要点)
    - [随机数生成 {#随机数生成}](#随机数生成-随机数生成)
  - [参考实现 {#参考实现}](#参考实现-参考实现)
  - [完整参考实现位于: `examples/password-generator/`](#完整参考实现位于-examplespassword-generator)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 项目目标 {#项目目标}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

创建一个安全的随机密码生成器。

---

## 功能需求 {#功能需求}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [ ] 生成随机密码: `passgen -l 16`
- [ ] 支持选项: 大小写、数字、特殊字符
- [ ] 密码强度评估
- [ ] 批量生成

---

## 学习要点 {#学习要点}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 随机数生成 {#随机数生成}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
use rand::{thread_rng, Rng};

fn generate_password(length: usize) -> String {
    const CHARSET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ\
                            abcdefghijklmnopqrstuvwxyz\
                            0123456789";
    let mut rng = thread_rng();

    (0..length)
        .map(|_| CHARSET[rng.gen_range(0..CHARSET.len())] as char)
        .collect()
}
```

---

## 参考实现 {#参考实现}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

完整参考实现位于: `examples/password-generator/`
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](README.md)

---

## 相关概念 {#相关概念}

- [03_practice 目录](README.md)
- [docs 索引](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

---
