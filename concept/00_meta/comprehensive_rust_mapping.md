> **内容分级**: [元层]
>
# Comprehensive Rust 课程映射
>
> **EN**: Comprehensive Rust Mapping
> **Summary**: Comprehensive Rust Mapping. Core Rust concept.
> **受众**: [初学者 → 进阶]
> **Bloom 层级**: 知道 → 应用
> **A/S/P 标记**: **A** — Application
> **双维定位**: C×Kno — 将 Google 的 Comprehensive Rust 课程映射到本知识体系
> **定位**: 本文件建立 **Comprehensive Rust**（Google 开发的免费 Rust 课程）与本知识体系中 `concept/` 文件的双向映射，帮助学习者将课程章节定位到深层概念文档。
> **前置概念**: [Learning Guide](./learning_guide.md) · [Bloom Taxonomy](./03_bloom_taxonomy.md)
> **后置概念**: [Application Domains](../06_ecosystem/04_application_domains.md)

---

> **来源**: [Comprehensive Rust — Google](https://google.github.io/comprehensive-rust/) ·
> [Comprehensive Rust GitHub](https://github.com/google/comprehensive-rust) ·
> [Google Rust Course Blog](https://blog.google/technology/developers/comprehensive-rust/)

---

## 📑 目录

- [Comprehensive Rust 课程映射](#comprehensive-rust-课程映射)
  - [📑 目录](#-目录)
  - [一、课程概览](#一课程概览)
    - [1.1 Comprehensive Rust 是什么](#11-comprehensive-rust-是什么)
    - [1.2 课程结构](#12-课程结构)
  - [二、章节映射表](#二章节映射表)
    - [2.1 Day 1 — Rust 基础](#21-day-1--rust-基础)
    - [2.2 Day 2 — 所有权与类型系统](#22-day-2--所有权与类型系统)
    - [2.3 Day 3 — 泛型与 Trait](#23-day-3--泛型与-trait)
    - [2.4 Day 4 — Android \& 高级主题](#24-day-4--android--高级主题)
  - [三、互补性分析](#三互补性分析)
  - [四、来源与延伸阅读](#四来源与延伸阅读)
  - [相关概念文件](#相关概念文件)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：本文档《Comprehensive Rust 课程映射》在 Rust 知识体系中属于哪一层级的元数据？（理解层）](#测验-1本文档comprehensive-rust-课程映射在-rust-知识体系中属于哪一层级的元数据理解层)
    - [测验 2：《Comprehensive Rust 课程映射》的主要用途是什么？（理解层）](#测验-2comprehensive-rust-课程映射的主要用途是什么理解层)
    - [测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）](#测验-3元数据层文档能否替代-l1-l7-的核心概念学习理解层)

---

## 一、课程概览

### 1.1 Comprehensive Rust 是什么

> **[Comprehensive Rust](https://google.github.io/comprehensive-rust/)** 是 Google Android 团队于 2022 年发布、持续维护的免费 Rust 课程，目标是在 **4 天**内将有经验的程序员（C++/Java/Go 背景）培训到能阅读、修改和编写 Rust 代码的水平。课程特点：
> [来源: [Google Blog — Comprehensive Rust](https://blog.google/technology/developers/comprehensive-rust/)]

- **实践导向**: 每 30–45 分钟讲解后紧跟练习题
- **多语言对比**: 明确标注与 C++、Java、Go 的差异
- **Android 集成**: Day 4 专门讲解 Rust 在 Android 开发中的应用
- **持续更新**: 跟随 Rust 稳定版更新（当前覆盖 Edition 2021/2024）

### 1.2 课程结构

```text
Comprehensive Rust 课程结构 (2026 版):

Day 1: Rust 基础 (6 小时)
├── 欢迎与工具链
├── 变量与可变性
├── 标量与复合类型
├── 函数与控制流
└── 用户定义类型 (struct/enum)

Day 2: 所有权与类型系统 (6 小时)
├── 所有权与移动语义
├── 借用与引用
├── 字符串与切片
├── 模式匹配
├── 方法、Trait 与泛型
└── 标准库类型 (Vec, HashMap, Box, Rc, Arc)

Day 3: 深入 Rust (6 小时)
├── 结构体内存布局
├── 生命周期
├── 错误处理 (Result/Option)
├── unsafe Rust
└── 并发基础 (线程、通道、Send/Sync)

Day 4: Android 与高级主题 (4 小时)
├── Android 构建系统
├── AIDL 与 FFI
├── Async Rust
└── 宏与测试
```

---

## 二、章节映射表

### 2.1 Day 1 — Rust 基础

| Comprehensive Rust 章节 | 本知识体系对应文件 | 对应章节 | 补充深度 |
|:---|:---|:---|:---|
| **Welcome** | [`00_meta/learning_guide.md`](./learning_guide.md) | 〇、学习路径选择全景 | 本体系提供更细粒度的背景适配 |
| **Hello, World** | [`06_ecosystem/01_toolchain.md`](../06_ecosystem/01_toolchain.md) | §1.1 安装与配置 | 补充 `rustup` 原理和交叉编译 |
| **Variables** | [`01_foundation/01_ownership.md`](../01_foundation/01_ownership.md) | §2.1 变量绑定 | 补充移动语义的前置形式化 |
| **Scalar Types** | [`01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) | §2.1 标量类型 | 补充类型推导与类型别名 |
| **Compound Types** | [`01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) | §2.2 复合类型 | 补充元组 fanout 模式 (Rust 1.85+) |
| **Control Flow** | [`01_foundation/07_control_flow.md`](../01_foundation/07_control_flow.md) | §1 核心概念 | 补充 `if let` temporary scope (Ed 2024) |
| **User-Defined Types** | [`01_foundation/04_type_system.md`](../01_foundation/04_type_system.md) | §3 结构体与枚举 | 补充 `#[repr(C)]` 内存布局 |

### 2.2 Day 2 — 所有权与类型系统

| Comprehensive Rust 章节 | 本知识体系对应文件 | 对应章节 | 补充深度 |
|:---|:---|:---|:---|
| **Ownership** | [`01_foundation/01_ownership.md`](../01_foundation/01_ownership.md) | §3 Move 语义 | 补充线性逻辑形式化映射 |
| **Borrowing** | [`01_foundation/02_borrowing.md`](../01_foundation/02_borrowing.md) | §2 借用规则 | 补充借用冲突矩阵 |
| **Strings & Slices** | [`01_foundation/02_borrowing.md`](../01_foundation/02_borrowing.md) | §3.2 切片 | 补充 `str` 的 UTF-8 不变式 |
| **Pattern Matching** | [`01_foundation/07_control_flow.md`](../01_foundation/07_control_flow.md) | §3.2 模式匹配 | 补充穷尽性检查原理 |
| **Methods & Traits** | [`02_intermediate/01_traits.md`](../02_intermediate/01_traits.md) | §1–3 全部 | 补充 coherence 与 orphan rules |
| **Generics** | [`02_intermediate/02_generics.md`](../02_intermediate/02_generics.md) | §1–3 全部 | 补充单态化与编译膨胀 |
| **Standard Library Types** | [`01_foundation/08_collections.md`](../01_foundation/08_collections.md) | §1–3 全部 | 补充 `FromIterator` for tuples |

### 2.3 Day 3 — 泛型与 Trait

| Comprehensive Rust 章节 | 本知识体系对应文件 | 对应章节 | 补充深度 |
|:---|:---|:---|:---|
| **Struct Memory Layout** | [`03_advanced/03_unsafe.md`](../03_advanced/03_unsafe.md) | §2.1 内存布局 | 补充对齐与填充 |
| **Lifetimes** | [`01_foundation/03_lifetimes.md`](../01_foundation/03_lifetimes.md) | §2 全部 | 补充 NLL、Polonius |
| **Error Handling** | [`02_intermediate/04_error_handling.md`](../02_intermediate/04_error_handling.md) | §1–3 全部 | 补充 `?` 运算符与 `Try` trait |
| **Unsafe Rust** | [`03_advanced/03_unsafe.md`](../03_advanced/03_unsafe.md) | §3 全部 | 补充 Miri、Stacked/Tree Borrows |
| **Concurrency** | [`03_advanced/01_concurrency.md`](../03_advanced/01_concurrency.md) | §1–3 全部 | 补充 `Send`/`Sync` 自动推导 |

### 2.4 Day 4 — Android & 高级主题

| Comprehensive Rust 章节 | 本知识体系对应文件 | 对应章节 | 补充深度 |
|:---|:---|:---|:---|
| **Android Build System** | [`06_ecosystem/17_cross_compilation.md`](../06_ecosystem/17_cross_compilation.md) | §3 Android NDK | 补充 AOSP 集成 |
| **AIDL & FFI** | [`03_advanced/05_rust_ffi.md`](../03_advanced/05_rust_ffi.md) | §2 C 互操作 | 补充 JNI/NDK 绑定 |
| **Async Rust** | [`03_advanced/02_async.md`](../03_advanced/02_async.md) | §1–3 全部 | 补充 `async fn` 状态机 |
| **Macros & Testing** | [`02_intermediate/17_macro_patterns.md`](../02_intermediate/17_macro_patterns.md) | §1–2 全部 | 补充声明宏 hygiene |

---

## 三、互补性分析

```text
Comprehensive Rust 与本知识体系的互补关系:

  Comprehensive Rust 优势:
  ├── 结构化课程节奏（4 天密集培训）
  ├── 大量练习题与即时反馈
  ├── Google 内部实践验证
  └── Android 特定内容（AIDL/NDK）

  本知识体系优势:
  ├── 概念深度（形式化映射、定理链）
  ├── 反例与边界分析（编译错误教学）
  ├── 跨层关联（L1-L7 完整链路）
  └── 认知科学框架（Bloom 层级、认知路径）

  联合学习路径建议:
  ├── 第 1 周: Comprehensive Rust Day 1-2 + 本体系 L1 文件
  ├── 第 2 周: Comprehensive Rust Day 3 + 本体系 L2 文件
  ├── 第 3 周: Comprehensive Rust Day 4 + 本体系 L3 文件
  └── 第 4 周: 本体系 L4-L7 选择性深入
```

> **映射洞察**: Comprehensive Rust 是**「宽而浅」**的入门路径，本知识体系是**「窄而深」**的概念网络。两者结合可实现「先建立全局地图，再深入每个 territory」的学习效果。

---

## 四、来源与延伸阅读

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Comprehensive Rust 官网](https://google.github.io/comprehensive-rust/) | ✅ 一级 | Google 官方课程 |
| [Comprehensive Rust GitHub](https://github.com/google/comprehensive-rust) | ✅ 一级 | 源码与练习题 |
| [Google Blog — 课程发布](https://blog.google/technology/developers/comprehensive-rust/) | ✅ 一级 | 官方发布说明 |
| [Rust by Example](https://doc.rust-lang.org/rust-by-example/) | ✅ 一级 | 互补的示例驱动学习 |

---

## 相关概念文件

- [Learning Guide](./learning_guide.md) — 本知识体系学习指南
- [Bloom Taxonomy](./03_bloom_taxonomy.md) — 认知层级框架
- [Application Domains](../06_ecosystem/04_application_domains.md) — Rust 应用领域分析

---

> **权威来源**: [Comprehensive Rust](https://google.github.io/comprehensive-rust/), [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)
> **权威来源对齐变更日志**: 2026-06-02 创建，映射 Comprehensive Rust 2026 版

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-02
**状态**: ✅ 概念文件创建完成

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文档《Comprehensive Rust 课程映射》在 Rust 知识体系中属于哪一层级的元数据？（理解层）

**题目**: 本文档《Comprehensive Rust 课程映射》在 Rust 知识体系中属于哪一层级的元数据？

<details>
<summary>✅ 答案与解析</summary>

属于 00_meta 元数据层，为整个知识体系提供导航、评估、审计和结构化的支持框架，辅助学习者定位和理解核心概念。
</details>

---

### 测验 2：《Comprehensive Rust 课程映射》的主要用途是什么？（理解层）

**题目**: 《Comprehensive Rust 课程映射》的主要用途是什么？

<details>
<summary>✅ 答案与解析</summary>

作为知识体系的支撑文档，提供学习路径导航、概念关系映射、质量评估标准或审计检查清单，帮助学习者和维护者高效使用知识库。
</details>

---

### 测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）

**题目**: 元数据层文档能否替代 L1-L7 的核心概念学习？

<details>
<summary>✅ 答案与解析</summary>

不能。元数据层提供导航和评估框架，但不能替代对核心概念（所有权、类型系统、并发等）的深入理解与实践。
</details>
