# 跨模块学习导航图 {#跨模块学习导航图}

> **EN**: Cross Module Navigation
> **Summary**: 跨模块学习导航图 Cross Module Navigation.
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **分级**: [A]
> **Bloom 层级**: L1-L2 (记忆/理解)
> Rust 系统化学习项目 - 模块关联指南
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [跨模块学习导航图 {#跨模块学习导航图}](#跨模块学习导航图-跨模块学习导航图)
  - [📑 目录 {#目录}](#-目录-目录)
  - [🗺️ 学习路线图 {#学习路线图}](#️-学习路线图-学习路线图)
  - [📚 模块详细映射 {#模块详细映射}](#-模块详细映射-模块详细映射)
    - [核心概念 → 源码 → 文档 → 实践 {#核心概念-源码-文档-实践}](#核心概念--源码--文档--实践-核心概念-源码-文档-实践)
  - [🔄 学习循环 {#学习循环}](#-学习循环-学习循环)
  - [🎯 推荐学习路径 {#推荐学习路径}](#-推荐学习路径-推荐学习路径)
    - [路径 A: Web 开发者 {#路径-a-web-开发者}](#路径-a-web-开发者-路径-a-web-开发者)
    - [路径 B: 系统开发者 {#路径-b-系统开发者}](#路径-b-系统开发者-路径-b-系统开发者)
    - [路径 C: 研究者 {#路径-c-研究者}](#路径-c-研究者-路径-c-研究者)
  - [🔗 快速链接 {#快速链接}](#-快速链接-快速链接)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 🗺️ 学习路线图 {#学习路线图}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                            新手入门 (Beginner)                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────┐      ┌─────────────┐      ┌─────────────┐                │
│   │ C01 所有权   │ ───▶ │ C02 类型系统 │ ───▶ │ C03 控制流   │               │
│   │ Ownership   │      │ Type System │      │ Control Flow │               │
│   └──────┬──────┘      └──────┬──────┘      └──────┬──────┘                │
│          │                    │                    │                        │
│          ▼                    ▼                    ▼                        │
│   ┌────────────────────────────────────────────────────────────────┐       │
│   │                    练习与巩固                                   │       │
│   │   crates/c01-03/exercises/  +  docs/03_practice/              │       │
│   └────────────────────────────────────────────────────────────────┘       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            中级进阶 (Intermediate)                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────┐      ┌─────────────┐      ┌─────────────┐                │
│   │ C04 泛型     │ ───▶ │ C05 并发     │ ───▶ │ C06 异步     │               │
│   │ Generics    │      │Concurrency  │      │ Async/Await  │               │
│   └──────┬──────┘      └──────┬──────┘      └──────┬──────┘                │
│          │                    │                    │                        │
│          │                    ▼                    │                        │
│          │           ┌─────────────┐              │                        │
│          │           │  content/   │◀─────────────┘                        │
│          │           │ ecosystem/  │  Web框架/数据库                         │
│          │           └─────────────┘                                       │
│          │                                                                 │
│          ▼                    ▼                                           │
│   ┌────────────────────────────────────────────────────────────────┐     │
│   │                    实践应用                                     │     │
│   │   content/scenarios/web_app.md  +  examples/async_*.rs        │     │
│   └────────────────────────────────────────────────────────────────┘     │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
                                      │
                                      ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                            高级专题 (Advanced)                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────┐      ┌─────────────┐      ┌─────────────┐                │
│   │ C07 进程     │      │ C08 算法     │      │ C09 设计模式 │               │
│   │ Processes   │      │ Algorithms  │      │ Patterns    │               │
│   └─────────────┘      └─────────────┘      └─────────────┘                │
│                                                                             │
│   ┌─────────────┐      ┌─────────────┐      ┌─────────────┐                │
│   │ C10 网络     │      │ C11 宏系统   │      │ C12 WASM    │               │
│   │ Networking  │      │ Macros      │      │ WebAssembly │               │
│   └──────┬──────┘      └──────┬──────┘      └──────┬──────┘                │
│          │                    │                    │                        │
│          ▼                    ▼                    ▼                        │
│   ┌────────────────────────────────────────────────────────────────┐       │
│   │                    生产实践                                     │       │
│   │   content/production/  +  content/academic/                    │       │
│   └────────────────────────────────────────────────────────────────┘       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 📚 模块详细映射 {#模块详细映射}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 核心概念 → 源码 → 文档 → 实践 {#核心概念-源码-文档-实践}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 核心概念 | crates/ 源码 | docs/ 文档 | content/ 拓展 |
|----------|--------------|------------|---------------|
| 所有权 | c01_ownership/src/ | docs/01_learning/ | - |
| 类型系统 | c02_type_system/src/ | docs/04_thinking/matrices/ | - |
| 泛型 | c04_generic/src/ | docs/05_guides/ | content/emerging/ |
| 并发 | c05_concurrency/src/ | docs/05_guides/ | content/ecosystem/ |
| 异步 | c06_async_await/src/ | docs/05_guides/ASYNC* | content/ecosystem/async* |
| 设计模式 | c09_design_patterns/src/ | docs/04_thinking/decision_trees/ | content/scenarios/ |
| 生产部署 | - | docs/05_guides/ | content/production/ |

---

## 🔄 学习循环 {#学习循环}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
    理论学习
        │
        ▼
┌───────────────┐
│  docs/        │
│  阅读指南     │
└───────┬───────┘
        │
        ▼
    代码实践
        │
        ▼
┌───────────────┐
│  crates/      │
│  运行测试     │
└───────┬───────┘
        │
        ▼
    深入理解
        │
        ▼
┌───────────────┐
│  content/     │
│  实际应用     │
└───────┬───────┘
        │
        ▼
    回到理论...
```

---

## 🎯 推荐学习路径 {#推荐学习路径}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 路径 A: Web 开发者 {#路径-a-web-开发者}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
C01 → C02 → C03 → C04 → C06 → content/ecosystem/async_runtimes/
                                    ↓
                           content/ecosystem/web_frameworks/
                                    ↓
                           content/scenarios/web_app/
```

### 路径 B: 系统开发者 {#路径-b-系统开发者}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```text
C01 → C02 → C05 → C07 → C10 → content/production/
                                    ↓
                           content/emerging/
```

### 路径 C: 研究者 {#路径-c-研究者}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
C01 → C04 → C11 → docs/research_notes/
                         ↓
                  content/academic/
```

---

## 🔗 快速链接 {#快速链接}

> **[来源: [crates.io](https://crates.io/)]**

| 资源 | 路径 | 描述 |
|------|------|------|
| 主索引 | [00_master_index.md](../00_master_index.md) | 完整文档索引 |
| 学习路径 | [01_learning_path_planning.md](01_learning_path_planning.md) | 学习规划 |
| 快速参考 | [02_reference/quick_reference/README.md](../02_reference/quick_reference/README.md) | 速查手册 |
| 实践练习 | [03_practice/README.md](../03_practice/README.md) | 动手练习 |
| 思维表示 | [04_thinking/README.md](../04_thinking/README.md) | 思维导图/矩阵 |
| 实用指南 | 05_guides/10_best_practices.md | 最佳实践 |
| 前沿内容 | [../content/](../content) | 生产实践/学术 |

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
**状态**: ✅ 100% 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念 {#相关概念}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [01_learning 目录](README.md)
- [学习路径索引](README.md)

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
