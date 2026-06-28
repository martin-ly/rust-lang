# 实践项目 03: 表达式计算器
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L3 (应用)
> **难度**: ⭐ 入门级
> **所需知识**: c01-c04
> **预计时间**: 3-4小时

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [实践项目 03: 表达式计算器](.#实践项目-03-表达式计算器)
  - [📑 目录](.#-目录)
  - [项目目标](.#项目目标)
  - [功能需求](.#功能需求)
  - [学习要点](.#学习要点)
    - [递归下降解析](.#递归下降解析)
  - [参考实现](.#参考实现)
  - [相关概念](.#相关概念)
  - [权威来源索引](.#权威来源索引)

## 项目目标
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

创建一个支持四则运算和括号的表达式计算器。

---

## 功能需求
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [ ] 解析数学表达式: `calc "2 + 3 * 4"`
- [ ] 支持 +, -, *, / 运算符
- [ ] 支持括号: `(2 + 3) * 4`
- [ ] 错误处理: 除零、非法表达式

---

## 学习要点
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 递归下降解析
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust
enum Expr {
    Number(f64),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

fn eval(expr: &Expr) -> f64 {
    match expr {
        Expr::Number(n) => *n,
        Expr::Add(a, b) => eval(a) + eval(b),
        Expr::Mul(a, b) => eval(a) * eval(b),
    }
}
```

---

## 参考实现
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

完整参考实现位于: `examples/calculator/`

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

## 相关概念

- [03_practice 目录](README.md)
- [docs 索引](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

---
