# 参考文献与外部资源

## 目录

- [参考文献与外部资源](#参考文献与外部资源)
  - [目录](#目录)
  - [学术论文](#学术论文)
    - [RustBelt 系列](#rustbelt-系列)
    - [Oxide](#oxide)
    - [Aeneas](#aeneas)
    - [别名模型](#别名模型)
    - [形式化方法](#形式化方法)
  - [官方文档](#官方文档)
    - [Rust 核心文档](#rust-核心文档)
    - [异步编程](#异步编程)
    - [标准库](#标准库)
  - [工具与项目](#工具与项目)
    - [Miri](#miri)
    - [Prusti](#prusti)
    - [Aeneas\*](#aeneas-1)
    - [Creusot](#creusot)
    - [Kani](#kani)
    - [Flux](#flux)
  - [博客与文章](#博客与文章)
    - [Ralf Jung 的博客](#ralf-jung-的博客)
    - [Faster Than Lime](#faster-than-lime)
    - [Cliffle](#cliffle)
    - [Without Boats](#without-boats)
  - [视频资源](#视频资源)
    - [Rust语言团队](#rust语言团队)
    - [会议演讲](#会议演讲)
    - [推荐演讲](#推荐演讲)
  - [书籍](#书籍)
    - [核心书籍](#核心书籍)
    - [专业书籍](#专业书籍)
  - [在线课程](#在线课程)
  - [社区资源](#社区资源)
    - [论坛与讨论](#论坛与讨论)
    - [Discord服务器](#discord服务器)
    - [中文社区](#中文社区)
  - [相关研究项目](#相关研究项目)
    - [内存安全](#内存安全)
    - [类型系统](#类型系统)
    - [并发验证](#并发验证)
  - [标准与规范](#标准与规范)
  - [工具链](#工具链)
  - [持续更新](#持续更新)

## 学术论文

### RustBelt 系列

- **RustBelt: Securing the Foundations of the Rust Programming Language**
  Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer
  POPL 2018
  <https://plv.mpi-sws.org/rustbelt/>

- **Safe Systems Programming in Rust: The Promise and the Challenge**
  Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer
  CACM 2021

### Oxide

- **Oxide: The Essence of Rust**
  Aaron Weiss, Daniel Patterson, Amal Ahmed
  arXiv:1903.00982
  <https://arxiv.org/abs/1903.00982>

### Aeneas

- **Aeneas: Rust Verification by Functional Translation**
  Son Ho, Jonathan Protzenko
  ICFP 2022
  <https://arxiv.org/abs/2206.07185>

### 别名模型

- **Stacked Borrows: An Aliasing Model for Rust**
  Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer
  POPL 2021
  <https://plv.mpi-sws.org/rustbis/stacked-borrows/>

- **Tree Borrows**
  Neven Villani
  <https://www.ralfj.de/blog/2023/06/02/tree-borrows.html>

### 形式化方法

- **Viper: A Verification Infrastructure for Permission-Based Reasoning**
  Peter Müller, Malte Schwerhoff, Alexander J. Summers
  VSTTE 2016

- **Creusot: A Foundry for the Deductive Verification of Rust Programs**
  Xavier Denis, Jacques-Henri Jourdan, Claude Marché
  ICFP 2022

---

## 官方文档

### Rust 核心文档

- [The Rust Programming Language (TRPL)](https://doc.rust-lang.org/book/)
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/) - Unsafe Rust指南
- [The Rust Reference](https://doc.rust-lang.org/reference/)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)

### 异步编程

- [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/)
- [Tokio Documentation](https://tokio.rs/)

### 标准库

- [std::pin](https://doc.rust-lang.org/std/pin/index.html)
- [std::marker::PhantomData](https://doc.rust-lang.org/std/marker/struct.PhantomData.html)

---

## 工具与项目

### Miri

- [Miri GitHub](https://github.com/rust-lang/miri)
- [Tree Borrows in Miri](https://github.com/rust-lang/miri#tree-borrows)

### Prusti

- [Prusti Website](https://www.prusti.org/)
- [Prusti GitHub](https://github.com/viperproject/prusti-dev)
- [Prusti Tutorial](https://viperproject.github.io/prusti-dev/user-guide/)

### Aeneas*

- [Aeneas GitHub](https://github.com/AeneasVerif/aeneas)
- [Aeneas Tutorial](https://github.com/AeneasVerif/aeneas-tutorial)

### Creusot

- [Creusot GitHub](https://github.com/creusot-rs/creusot)

### Kani

- [Kani GitHub](https://github.com/model-checking/kani)
- [Kani Documentation](https://model-checking.github.io/kani/)

### Flux

- [Flux GitHub](https://github.com/flux-rs/flux)
- Refinement types for Rust

---

## 博客与文章

### Ralf Jung 的博客

- [Understanding Rust through the lens of type theory](https://www.ralfj.de/blog/)
- [Tree Borrows](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)
- [The Scope of Unsafe](https://www.ralfj.de/blog/2016/01/09/the-scope-of-unsafe.html)

### Faster Than Lime

- [Pin and Suffering](https://fasterthanli.me/articles/pin-and-suffering)
- [Understanding Rust Through Arrays](https://fasterthanli.me/articles/thoughts-on-rust-in-2023)

### Cliffle

- [The Rusty Scabbard](https://cliffle.com/blog/)
- [Zero-cost Async](https://cliffle.com/blog/on-rust/)s-future/

### Without Boats

- [The Soul of Rust](https://without.boats/blog/)
- [Async/Await Design](https://without.boats/blog/the-soul-of-rust/)

---

## 视频资源

### Rust语言团队

- [Rust Lang Team Meetings](https://www.youtube.com/@RustLangTV)

### 会议演讲

- **RustConf** (<https://rustconf.com/>)
- **Rust Nation** (<https://rustnationuk.com/>)
- **EuroRust** (<https://eurorust.eu/>)

### 推荐演讲

- "The Talk" - Aaron Turon on Ownership
- "Rust: A Type System for the Next 40 Years" - Felix Klock
- "The Story of Rust" - Steve Klabnik

---

## 书籍

### 核心书籍

- **The Rust Programming Language** (Steve Klabnik, Carol Nichols)
- **Programming Rust** (Jim Blandy, Jason Orendorff, Leonora Tindall)
- **Rust for Rustaceans** (Jon Gjengset)
- **Zero To Production In Rust** (Luca Palmieri)

### 专业书籍

- **The Rustonomicon** - Unsafe Rust
- **Rust Design Patterns** (Rust Community)
- **Command Line Applications in Rust**
- **WebAssembly with Rust**

---

## 在线课程

- **Rustlings** (<https://github.com/rust-lang/rustlings>)
- **Rust by Example** (<https://doc.rust-lang.org/rust-by-example/>)
- **Exercism Rust Track** (<https://exercism.org/tracks/rust>)
- **Rust on Educative**
- **Coursera Rust Courses**

---

## 社区资源

### 论坛与讨论

- [Rust Users Forum](https://users.rust-lang.org/)
- [Rust Internals Forum](https://internals.rust-lang.org/)
- [Rust on Stack Overflow](https://stackoverflow.com/questions/tagged/rust)
- [Reddit r/rust](https://www.reddit.com/r/rust/)

### Discord服务器

- [Rust Programming Language Community](https://discord.gg/rust-lang)
- [Rust Community Server](https://discord.gg/rust-lang-community)

### 中文社区

- [Rust语言中文社区](https://rustcc.cn/)
- [Rust中文 Wiki](https://rustwiki.org/)

---

## 相关研究项目

### 内存安全

- **CompCert** - 验证的C编译器
- **Bedrock** - Coq中的底层编程
- **VST** - Verified Software Toolchain

### 类型系统

- **Idris** - 依赖类型语言
- **Agda** - 依赖类型证明助手
- **Lean** - 定理证明和编程

### 并发验证

- **Iris** - 高阶并发分离逻辑
- **Cosmo** - 模块化并发验证

---

## 标准与规范

- [Rust RFCs](https://rust-lang.github.io/rfcs/)
- [Rust Reference](https://doc.rust-lang.org/reference/)
- [Rust Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)
- [Rust Platform Support](https://doc.rust-lang.org/nightly/rustc/platform-support.html)

---

## 工具链

- [rustup](https://rustup.rs/) - Rust安装管理器
- [Cargo](https://doc.rust-lang.org/cargo/) - 包管理器
- [Clippy](https://github.com/rust-lang/rust-clippy) - Linter
- [rustfmt](https://github.com/rust-lang/rustfmt) - 格式化工具
- [rust-analyzer](https://rust-analyzer.github.io/) - IDE支持

---

## 持续更新

本参考文献列表将持续更新。欢迎通过Issue或PR提交新的资源。

最后更新：2026年3月
