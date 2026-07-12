# 项目文档体系分工协议 {#项目文档体系分工协议}

> **EN**: Documentation Division Of Labor
> **Summary**: 项目文档体系分工协议 Documentation Division Of Labor. (stub/archive redirect)
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **分级**: [B]
> **Bloom 层级**: L2
> **创建日期**: 2026-05-12
> **版本**: 1.0
> **状态**: ✅ 已生效
> **适用范围**: `docs/`、`knowledge/`、`guides/`、`content/` 全部文档

---

## 📑 目录 {#目录}

- [项目文档体系分工协议 {#项目文档体系分工协议}](#项目文档体系分工协议-项目文档体系分工协议)
  - [📑 目录 {#目录}](#-目录-目录)
  - [1. 背景与目的 {#1-背景与目的}](#1-背景与目的-1-背景与目的)
  - [2. 四大文档体系定位 {#2-四大文档体系定位}](#2-四大文档体系定位-2-四大文档体系定位)
    - [2.1 `knowledge/` — 面向学习者的分层教程 {#21-knowledge-面向学习者的分层教程}](#21-knowledge--面向学习者的分层教程-21-knowledge-面向学习者的分层教程)
    - [2.2 `docs/05_guides/` — 面向开发者的专题查阅指南 {#22-docs05\_guides-面向开发者的专题查阅指南}](#22-docs05_guides--面向开发者的专题查阅指南-22-docs05_guides-面向开发者的专题查阅指南)
    - [2.3 `docs/02_reference/` — 速查卡与边界特例 {#23-docs02\_reference-速查卡与边界特例}](#23-docs02_reference--速查卡与边界特例-23-docs02_reference-速查卡与边界特例)
    - [2.4 `docs/research_notes/` — 学术与形式化内容 {#24-docsresearch\_notes-学术与形式化内容}](#24-docsresearch_notes--学术与形式化内容-24-docsresearch_notes-学术与形式化内容)
    - [2.5 `docs/content/` — 学术与场景化内容 {#25-docscontent-学术与场景化内容}](#25-docscontent--学术与场景化内容-25-docscontent-学术与场景化内容)
  - [3. 重复消除规则 {#3-重复消除规则}](#3-重复消除规则-3-重复消除规则)
    - [3.1 禁止重复清单 {#31-禁止重复清单}](#31-禁止重复清单-31-禁止重复清单)
    - [3.2 交叉引用规范 {#32-交叉引用规范}](#32-交叉引用规范-32-交叉引用规范)
  - [4. 版本标注统一规范 {#4-版本标注统一规范}](#4-版本标注统一规范-4-版本标注统一规范)
    - [4.1 必须标注的位置 {#41-必须标注的位置}](#41-必须标注的位置-41-必须标注的位置)
    - [4.2 必须包含版本声明的文件 {#42-必须包含版本声明的文件}](#42-必须包含版本声明的文件-42-必须包含版本声明的文件)
  - [5. 评审与更新机制 {#5-评审与更新机制}](#5-评审与更新机制-5-评审与更新机制)
  - [6. 相关文档 {#6-相关文档}](#6-相关文档-6-相关文档)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 1. 背景与目的 {#1-背景与目的}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本项目存在四个并行的文档体系，导致同一主题在多处重复出现，维护成本高昂。本协议明确各体系的定位、边界和协作规则，从根本上消除重复和混乱。

---

## 2. 四大文档体系定位 {#2-四大文档体系定位}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 2.1 `knowledge/` — 面向学习者的分层教程 {#21-knowledge-面向学习者的分层教程}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**核心定位**: 按学习难度分层（00_start → 04_expert），面向渐进式学习。

| 层级 | 目标读者 | 内容特征 |
|------|----------|----------|
| `00_start/` | 零基础 | 安装、Hello World、设计哲学 |
| `01_fundamentals/` | 初学者 | 所有权（Ownership）、借用（Borrowing）、生命周期、迭代器 |
| `02_intermediate/` | 进阶者 | 泛型（Generics）、Trait、错误处理（Error Handling）、智能指针（Smart Pointer） |
| `03_advanced/` | 高级开发者 | async/await、Unsafe、FFI、宏系统 |
| `04_expert/` | 专家/研究者 | 编译器内部、形式化验证、安全关键系统 |
| `05_reference/` | 全阶段 | 关键字参考、标准库速查 |
| `06_ecosystem/` | 工程实践 | Cargo、Tokio、Axum、部署 |

**写作规范**:

- 必须有明确的**学习路径**和**前置知识**说明
- 必须有**代码示例**和**练习题**
- 语言风格：教学式、循序渐进
- 版本标注：顶部必须标注 `Rust X.Y.Z+ (Edition 2024)`

---

### 2.2 `docs/05_guides/` — 面向开发者的专题查阅指南 {#22-docs05_guides-面向开发者的专题查阅指南}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

**核心定位**: 按技术专题组织，面向已有基础的开发者的快速查阅和实践参考。

**写作规范**:

- 必须有**目录导航**和**快速开始**章节
- 必须有**完整代码示例**（可直接编译运行）
- 必须有**常见问题 (FAQ)** 和**性能优化建议**
- 语言风格：手册式、问题导向
- 与 `knowledge/` 的关系：`05_guides/` 不重复基础知识，直接切入专题深度

**当前专题清单**:

- `05_async_programming_usage_guide.md` (C06)
- `05_threads_concurrency_usage_guide.md` (C05)
- `05_design_patterns_usage_guide.md` (C09)
- `05_macro_system_usage_guide.md` (C11)
- `05_wasm_usage_guide.md` (C12)
- `05_embedded_rust_guide.md` (C13)
- `05_unsafe_rust_guide.md` (C01/C07)
- `05_performance_tuning_guide.md` (C08)
- `05_type_system_usage_guide.md` (C02) ⬅️ **待创建**
- `05_control_flow_functions_usage_guide.md` (C03) ⬅️ **待创建**
- `05_algorithms_usage_guide.md` (C08) ⬅️ **待创建**

---

### 2.3 `docs/02_reference/` — 速查卡与边界特例 {#23-docs02_reference-速查卡与边界特例}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

**核心定位**: 纯速查格式，极简、结构化、可打印。

**写作规范**:

- 单文件聚焦一个主题
- 表格 > 段落，代码 > 解释
- 必须包含**边界特例**和**反模式警告**
- 不展开理论，只给结论和示例

---

### 2.4 `docs/research_notes/` — 学术与形式化内容 {#24-docsresearch_notes-学术与形式化内容}

**核心定位**: 形式化方法、类型理论、软件设计理论、证明索引。

**写作规范**:

- 必须有**定理-证明**结构或**形式化规约**
- 必须有**引用来源**（论文、RFC、官方规范）
- 语言风格：学术式、精确
- 与工程实践的链接：每个理论主题必须指向 `crates/` 中的对应代码示例

---

### 2.5 `docs/content/` — 学术与场景化内容 {#25-docscontent-学术与场景化内容}

**核心定位**: 学术研究（Tree Borrows、Coq 形式化）、知识表征矩阵、应用场景案例。

**写作规范**:

- 聚焦**学术研究**和**跨领域应用**而非生态工具教程
- 生态工具深度解析已迁移至 `knowledge/06_ecosystem/`
- 必须有**引用来源**（论文、RFC、官方规范）

---

## 3. 重复消除规则 {#3-重复消除规则}

### 3.1 禁止重复清单 {#31-禁止重复清单}

以下主题在 `docs/` 和 `knowledge/` 中**不得同时存在详细教程**。选择保留一个，另一个改为精简概述或重定向：

| 主题 | 保留位置 | `docs/` 处理方式 | `knowledge/` 处理方式 |
|------|----------|------------------|----------------------|
| 异步编程 | `knowledge/03_advanced/async/` | `05_guides/` 保留专题指南 | 保留教程 |
| 线程并发 | `knowledge/03_advanced/concurrency/` | `05_guides/` 保留专题指南 | 保留教程 |
| Unsafe Rust | `knowledge/03_advanced/unsafe/` | `05_guides/` 保留专题指南 | 保留教程 |
| 宏系统 | `knowledge/03_advanced/macros/` | `05_guides/` 保留专题指南 | 保留教程 |
| 性能优化 | `knowledge/03_advanced/performance_optimization.md` | `05_guides/` 保留专题指南 | 保留教程 |
| 设计模式 | `knowledge/04_expert/` | `05_guides/` 保留专题指南 | 保留教程 |

### 3.2 交叉引用规范 {#32-交叉引用规范}

- `knowledge/` 中提及专题深度内容时，必须链接到 `docs/05_guides/` 或 `docs/02_reference/`
- `docs/05_guides/` 中提及基础知识时，必须链接到 `knowledge/` 对应层级
- `docs/research_notes/` 中提及代码实现时，必须链接到 `crates/` 对应模块

---

## 4. 版本标注统一规范 {#4-版本标注统一规范}

### 4.1 必须标注的位置 {#41-必须标注的位置}

以下文件顶部必须包含版本声明：

```markdown
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **创建日期**: YYYY-MM-DD
> **最后更新**: YYYY-MM-DD
> **状态**: 🟡 进行中 / ✅ 已完成 / 🔴 待更新
```

### 4.2 必须包含版本声明的文件 {#42-必须包含版本声明的文件}

- `docs/00_master_index.md`
- `docs/10_terminology_standard.md`
- `docs/10_authoritative_sources_and_citations.md`
- `knowledge/INDEX.md`
- `knowledge/README.md`
- 所有 `docs/05_guides/*_GUIDE.md`
- 所有 `docs/02_reference/quick_reference/*.md`
- 所有 `docs/06_toolchain/rust_1.*_*.md`

---

## 5. 评审与更新机制 {#5-评审与更新机制}

| 检查项 | 频率 | 负责人 |
|--------|------|--------|
| 版本号一致性检查 | 每次 Rust 新版本发布后 | 自动化脚本 |
| 文档重复扫描 | 每季度 | 维护者 |
| 断链检查 | 每月 | `scripts/check_links.py` |
| 归档文档清理 | 每半年 | 维护者 |
| 本协议本身评审 | 每年 | 项目维护团队 |

---

## 6. 相关文档 {#6-相关文档}

- `00_documentation_lifecycle.md` — 文档生命周期管理制度
- `DOCS_STRUCTURE_OVERVIEW.md` — 完整结构总览
- `07_documentation_cross_reference_guide.md` — 跨文档映射网络

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念 {#相关概念}

- [上级目录](../README.md)

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
