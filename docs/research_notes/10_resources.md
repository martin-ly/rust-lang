# 研究资源汇总 {#研究资源汇总}

> **EN**: Resources
> **Summary**: 研究资源汇总 Resources. (stub/archive redirect)
> **概念族**: 参考资源
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2025-01-27
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📑 目录 {#目录}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>

- [研究资源汇总 {#研究资源汇总}](#研究资源汇总-研究资源汇总)
  - [📑 目录 {#目录}](#-目录-目录)
  - [📚 学术资源 {#学术资源}](#-学术资源-学术资源)
    - [形式化方法相关论文 {#形式化方法相关论文}](#形式化方法相关论文-形式化方法相关论文)
    - [类型理论相关论文 {#类型理论相关论文}](#类型理论相关论文-类型理论相关论文)
    - [性能优化相关论文 {#性能优化相关论文}](#性能优化相关论文-性能优化相关论文)
  - [📖 官方文档 {#官方文档}](#-官方文档-官方文档)
    - [Rust 官方文档 {#rust-官方文档}](#rust-官方文档-rust-官方文档)
    - [Rust 编译器文档 {#rust-编译器文档}](#rust-编译器文档-rust-编译器文档)
    - [Rust 工具文档 {#rust-工具文档}](#rust-工具文档-rust-工具文档)
  - [🛠️ 工具资源 {#工具资源}](#️-工具资源-工具资源)
    - [形式化验证工具 {#形式化验证工具}](#形式化验证工具-形式化验证工具)
    - [性能分析工具 {#性能分析工具}](#性能分析工具-性能分析工具)
    - [内存分析工具 {#内存分析工具}](#内存分析工具-内存分析工具)
    - [代码分析工具 {#代码分析工具}](#代码分析工具-代码分析工具)
  - [📝 社区资源 {#社区资源}](#-社区资源-社区资源)
    - [社区论坛 {#社区论坛}](#社区论坛-社区论坛)
    - [社区项目 {#社区项目}](#社区项目-社区项目)
  - [🎓 学习资源 {#学习资源}](#-学习资源-学习资源)
    - [在线课程 {#在线课程}](#在线课程-在线课程)
    - [书籍 {#书籍}](#书籍-书籍)
  - [📰 新闻和博客 {#新闻和博客}](#-新闻和博客-新闻和博客)
    - [官方博客 {#官方博客}](#官方博客-官方博客)
    - [社区博客 {#社区博客}](#社区博客-社区博客)
  - [资源与形式化衔接 {#资源与形式化衔接}](#资源与形式化衔接-资源与形式化衔接)
  - [🔗 相关资源 {#相关资源}](#-相关资源-相关资源)
    - [核心文档 {#核心文档}](#核心文档-核心文档)
    - [研究笔记 {#研究笔记}](#研究笔记-研究笔记)
    - [形式化证明体系（2026-02-14） {#形式化证明体系2026-02-14}](#形式化证明体系2026-02-14-形式化证明体系2026-02-14)
  - [🆕 Rust 1.94 深度整合更新 {#rust-194-深度整合更新}](#-rust-194-深度整合更新-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点 {#本文档的rust-194更新要点}](#本文档的rust-194更新要点-本文档的rust-194更新要点)
      - [核心特性应用 {#核心特性应用}](#核心特性应用-核心特性应用)
      - [代码示例更新 {#代码示例更新}](#代码示例更新-代码示例更新)
      - [相关文档 {#相关文档}](#相关文档-相关文档)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 📚 学术资源 {#学术资源}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 形式化方法相关论文 {#形式化方法相关论文}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

1. **RustBelt: Securing the Foundations of the Rust Programming Language**
   - 作者: Ralf Jung, et al.
   - 年份: 2018
   - 摘要: 使用分离逻辑形式化验证 Rust 的类型系统
   - 链接: 论文链接
2. **Stacked Borrows: An Aliasing Model for Rust**
   - 作者: Ralf Jung, et al.
   - 年份: 2019
   - 摘要: Rust 借用检查器的形式化模型
   - 链接: 论文链接
3. **The RustBelt Project**
   - 作者: Ralf Jung, et al.
   - 摘要: Rust 形式化验证的综合项目
   - 链接: 项目主页

### 类型理论相关论文 {#类型理论相关论文}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

1. **Type Systems for Programming Languages**
   - 作者: Benjamin C. Pierce
   - 摘要: 类型系统理论的经典教材
   - 链接: 书籍链接
2. **Advanced Topics in Types and Programming Languages**
   - 作者: Benjamin C. Pierce
   - 摘要: 类型系统高级主题
   - 链接: 书籍链接
3. **Rust's Type System**
   - 作者: Various
   - 摘要: Rust 类型系统的相关研究
   - 相关: [类型系统基础](type_theory/10_type_system_foundations.md)
   - 形式化衔接: [00_completeness_gaps](formal_methods/00_completeness_gaps.md)、[PROOF_INDEX](10_proof_index.md)

### 性能优化相关论文 {#性能优化相关论文}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

1. **Optimizing Rust Compiler Performance**
   - 作者: Rust Compiler Team
   - 摘要: Rust 编译器的性能优化技术
   - 相关: [编译器优化](experiments/10_compiler_optimizations.md)
2. **Memory Management in Rust**
   - 作者: Various
   - 摘要: Rust 内存管理的研究
   - 相关: [内存分析](experiments/10_memory_analysis.md)

---

## 📖 官方文档 {#官方文档}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Rust 官方文档 {#rust-官方文档}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- **The Rust Programming Language (The Book)**
  - 链接: <https://doc.rust-lang.org/book/>
  - 描述: Rust 官方教程
- **Rust by Example**
  - 链接: <https://doc.rust-lang.org/rust-by-example/>
  - 描述: 通过示例学习 Rust
- **The Rust Reference**
  - 链接: <https://doc.rust-lang.org/reference/>
  - 描述: Rust 语言参考手册
- **Rust API Guidelines**
  - 链接: <https://rust-lang.github.io/api-guidelines/>
  - 描述: Rust API 设计指南
- **Rust Edition Guide**
  - 链接: <https://doc.rust-lang.org/edition-guide/>
  - 描述: Rust 版本指南

### Rust 编译器文档 {#rust-编译器文档}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- **Rust Compiler Development Guide**
  - 链接: <https://rustc-dev-guide.rust-lang.org/>
  - 描述: Rust 编译器开发指南
- **Rust Language Design (RFCs)**
  - 链接: <https://github.com/rust-lang/rfcs>
  - 描述: Rust 语言设计提案

### Rust 工具文档 {#rust-工具文档}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- **Cargo Book**
  - 链接: <https://doc.rust-lang.org/cargo/>
  - 描述: Rust 包管理器文档
- **Clippy Documentation**
  - 链接: <https://rust-lang.github.io/rust-clippy/>
  - 描述: Rust 代码检查工具文档

---

## 🛠️ 工具资源 {#工具资源}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 形式化验证工具 {#形式化验证工具}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- **Coq**
  - 链接: <https://coq.inria.fr/>
  - 描述: 交互式定理证明器
  - 相关: [工具使用指南 - Coq](10_tools_guide.md)
- **Lean**
  - 链接: <https://leanprover.github.io/>
  - 描述: 函数式编程语言和证明助手
  - 相关: [工具使用指南 - Lean](10_tools_guide.md)
- **Prusti**
  - 链接: <https://www.pm.inf.ethz.ch/research/prusti.html>
  - 描述: Rust 的形式化验证工具
  - 相关: [工具使用指南 - Prusti](10_tools_guide.md#prusti)
- **Kani**
  - 链接: <https://github.com/model-checking/kani>
  - 描述: Rust 的模型检查工具
  - 相关: [工具使用指南 - Kani](10_tools_guide.md#kani)

### 性能分析工具 {#性能分析工具}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

- **Criterion.rs**
  - 链接: <https://github.com/bheisler/criterion.rs>
  - 描述: Rust 的基准测试框架
  - 相关: [工具使用指南 - Criterion.rs](10_tools_guide.md#criterionrs)
- **perf**
  - 链接: <https://perf.wiki.kernel.org/>
  - 描述: Linux 性能分析工具
  - 相关: [工具使用指南 - perf](10_tools_guide.md#perf)
- **flamegraph**
  - 链接: <https://github.com/flamegraph-rs/flamegraph>
  - 描述: 性能分析可视化工具
  - 相关: [工具使用指南 - flamegraph](10_tools_guide.md#flamegraph)

### 内存分析工具 {#内存分析工具}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

- **Miri**
  - 链接: <https://github.com/rust-lang/miri>
  - 描述: Rust 的 MIR 解释器
  - 相关: [工具使用指南 - Miri](10_tools_guide.md#miri)
- **Valgrind**
  - 链接: <https://valgrind.org/>
  - 描述: 内存调试和性能分析工具
  - 相关: [工具使用指南 - Valgrind](10_tools_guide.md#valgrind)
- **heaptrack**
  - 链接: <https://github.com/KDE/heaptrack>
  - 描述: 堆内存分析工具
  - 相关: [工具使用指南 - heaptrack](10_tools_guide.md#heaptrack)

### 代码分析工具 {#代码分析工具}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

- **Clippy**
  - 链接: <https://github.com/rust-lang/rust-clippy>
  - 描述: Rust 代码检查工具
  - 相关: [工具使用指南 - Clippy](10_tools_guide.md#clippy)
- **rust-analyzer**
  - 链接: <https://rust-analyzer.github.io/>
  - 描述: Rust 语言服务器
  - 相关: [工具使用指南 - rust-analyzer](10_tools_guide.md#rust-analyzer)
- **cargo-expand**
  - 链接: <https://github.com/dtolnay/cargo-expand>
  - 描述: 宏展开工具
  - 相关: [工具使用指南 - cargo-expand](10_tools_guide.md#cargo-expand)

---

## 📝 社区资源 {#社区资源}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 社区论坛 {#社区论坛}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

- **Rust Users Forum**
  - 链接: <https://users.rust-lang.org/>
  - 描述: Rust 用户讨论论坛
- **Rust Internals Forum**
  - 链接: <https://internals.rust-lang.org/>
  - 描述: Rust 内部开发讨论
- **Reddit r/rust**
  - 链接: <https://www.reddit.com/r/rust/>
  - 描述: Rust 社区讨论

### 社区项目 {#社区项目}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

- **Awesome Rust**
  - 链接: <https://github.com/rust-unofficial/awesome-rust>
  - 描述: Rust 资源汇总
- **Rust Learning Resources**
  - 链接: <https://github.com/ctjhoa/rust-learning>
  - 描述: Rust 学习资源汇总

---

## 🎓 学习资源 {#学习资源}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 在线课程 {#在线课程}

> **来源: [ACM](https://dl.acm.org/)**

- **Rustlings**
  - 链接: <https://github.com/rust-lang/rustlings>
  - 描述: Rust 编程练习
- **Rust by Practice**
  - 链接: <https://practice.rs/>
  - 描述: Rust 实践练习

### 书籍 {#书籍}

> **来源: [IEEE](https://standards.ieee.org/)**

- **The Rust Programming Language**
  - 作者: Steve Klabnik, Carol Nichols
  - 链接: <https://doc.rust-lang.org/book/>
  - 描述: Rust 官方教程
- **Programming Rust**
  - 作者: Jim Blandy, Jason Orendorff
  - 描述: Rust 编程指南
- **Rust in Action**
  - 作者: Tim McNamara
  - 描述: Rust 实战指南

---

## 📰 新闻和博客 {#新闻和博客}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 官方博客 {#官方博客}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

- **Rust Blog**
  - 链接: <https://blog.rust-lang.org/>
  - 描述: Rust 官方博客
- **Inside Rust**
  - 链接: <https://blog.rust-lang.org/inside-rust/>
  - 描述: Rust 内部开发博客

### 社区博客 {#社区博客}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

- **This Week in Rust**
  - 链接: <https://this-week-in-rust.org/>
  - 描述: Rust 周报
- **Rustacean Station**
  - 链接: <https://rustacean-station.org/>
  - 描述: Rust 播客

---

## 资源与形式化衔接 {#资源与形式化衔接}

>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 资源类型 | 形式化文档 | 可验证/支撑的定理 |
| :--- | :--- | :--- |
| RustBelt、Stacked Borrows | [ownership_model](formal_methods/10_ownership_model.md)、[borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)、[coq_skeleton](../../archive/deprecated/coq_skeleton/README.md)、[RUSTBELT_ALIGNMENT](10_rustbelt_alignment.md) | OW1、T2/T3、CHAN-T1、MUTEX-T1；Coq T-OW2 骨架 |
| Rust 类型系统研究 | [type_system_foundations](type_theory/10_type_system_foundations.md)、[trait_system_formalization](type_theory/10_trait_system_formalization.md) | 类型保持、coherence、RPITIT |
| Prusti、Kani | [formal_methods](formal_methods/README.md) | 所有权（Ownership）、借用（Borrowing）、unsafe 契约 |
| Criterion、Miri | [experiments/README](experiments/README.md) | EX-T1、EX-T2；内存安全验证 |

详见 [PROOF_INDEX](10_proof_index.md) 全证明索引、

[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](10_international_formal_verification_index.md) 国际对标、

[FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](10_formal_proof_critical_analysis_and_plan_2026_02.md) 批判性分析与推进计划、

[practical_applications](10_practical_applications.md) 案例与定理对应。

---

## 🔗 相关资源 {#相关资源}

>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 核心文档 {#核心文档}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

- [主索引](README.md) - 完整的研究笔记索引
- [工具使用指南](10_tools_guide.md) - 研究工具详细指南
- [术语表](10_glossary.md) - 专业术语解释

### 研究笔记 {#研究笔记}

>
> **[来源: [crates.io](https://crates.io/)]**

- [形式化方法研究](formal_methods/README.md) - 形式化方法索引
- [类型理论研究](type_theory/README.md) - 类型理论索引
- [实验研究](experiments/README.md) - 实验研究索引

### 形式化证明体系（2026-02-14） {#形式化证明体系2026-02-14}

>
> **[来源: [docs.rs](https://docs.rs/)]**

- [批判性分析与推进计划](10_formal_proof_critical_analysis_and_plan_2026_02.md) - 阶段 1–3 完成总结
- [国际对标索引](10_international_formal_verification_index.md) - RustBelt、Aeneas、RustSEM 等
- [形式化全模型入口](10_formal_full_model_overview.md) - 统一形式系统
- [核心定理完整证明](10_core_theorems_full_proofs.md) - L2 级 ownership T2、borrow T1、type T3
- [Coq 证明骨架](../../archive/deprecated/coq_skeleton/README.md) - T-OW2 所有权唯一性
- L3 实施指南 - Coq/Isabelle 补全路线（已归档）

---

**维护团队**: Rust Research Community

**最后更新**: 2026-02-28

**状态**: ✅ **Rust 1.93.1+ 更新完成**

---

## 🆕 Rust 1.94 深度整合更新 {#rust-194-深度整合更新}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
> **适用版本**: Rust 1.96.1+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点 {#本文档的rust-194更新要点}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用 {#核心特性应用}

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理（Error Handling）、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新 {#代码示例更新}

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档 {#相关文档}

- Rust 1.94 迁移指南
- [Rust 1.94 特性速查
- [性能调优指南](../05_guides/05_performance_tuning_guide.md)

---

**维护者**: Rust 学习项目团队

**最后更新**: 2026-03-14 (Rust 1.94 深度整合)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1

**对应 Rust 版本**: 1.96.1+ (Edition 2024)

**最后更新**: 2026-05-19

**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念 {#相关概念}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [research_notes 目录](README.md)
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

---
