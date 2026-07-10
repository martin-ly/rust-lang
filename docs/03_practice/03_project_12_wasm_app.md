# 实践项目 12: WebAssembly应用 {#实践项目-12-webassembly应用}

> **EN**: Project 12 Wasm App
> **Summary**: 实践项目 12 Project 12 Wasm App.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L3
> **难度**: ⭐⭐⭐ 专家级
> **所需知识**: c12 (WASM)
> **预计时间**: 6-8小时

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [实践项目 12: WebAssembly应用 {#实践项目-12-webassembly应用}](#实践项目-12-webassembly应用-实践项目-12-webassembly应用)
  - [📑 目录 {#目录}](#-目录-目录)
  - [项目目标 {#项目目标}](#项目目标-项目目标)
  - [功能需求 {#功能需求}](#功能需求-功能需求)
  - [学习要点 {#学习要点}](#学习要点-学习要点)
    - [WASM绑定 {#wasm绑定}](#wasm绑定-wasm绑定)
  - [参考实现 {#参考实现}](#参考实现-参考实现)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 项目目标 {#项目目标}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

创建编译到WebAssembly的浏览器应用。

---

## 功能需求 {#功能需求}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [ ] Rust编译到WASM
- [ ] JavaScript互操作
- [ ] DOM操作
- [ ] Canvas绘图
- [ ] 游戏或可视化

---

## 学习要点 {#学习要点}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### WASM绑定 {#wasm绑定}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[wasm_bindgen]
extern "C" {
    fn alert(s: &str);
}
```

---

## 参考实现 {#参考实现}

完整参考实现位于: `examples/wasm-app/`

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
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
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
