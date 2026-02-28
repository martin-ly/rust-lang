# 研究资源汇总

> **创建日期**: 2025-01-27
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📊 目录 {#-目录}

- [研究资源汇总](#研究资源汇总)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [📚 学术资源 {#-学术资源}](#-学术资源--学术资源)
    - [形式化方法相关论文](#形式化方法相关论文)
    - [类型理论相关论文](#类型理论相关论文)
    - [性能优化相关论文](#性能优化相关论文)
  - [📖 官方文档 {#-官方文档}](#-官方文档--官方文档)
    - [Rust 官方文档](#rust-官方文档)
    - [Rust 编译器文档](#rust-编译器文档)
    - [Rust 工具文档](#rust-工具文档)
  - [🛠️ 工具资源 {#️-工具资源}](#️-工具资源-️-工具资源)
    - [形式化验证工具](#形式化验证工具)
    - [性能分析工具](#性能分析工具)
    - [内存分析工具](#内存分析工具)
    - [代码分析工具](#代码分析工具)
  - [📝 社区资源 {#-社区资源}](#-社区资源--社区资源)
    - [社区论坛](#社区论坛)
    - [社区项目](#社区项目)
  - [🎓 学习资源 {#-学习资源}](#-学习资源--学习资源)
    - [在线课程](#在线课程)
    - [书籍](#书籍)
  - [📰 新闻和博客 {#-新闻和博客}](#-新闻和博客--新闻和博客)
    - [官方博客](#官方博客)
    - [社区博客](#社区博客)
  - [资源与形式化衔接](#资源与形式化衔接)
  - [🔗 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [核心文档](#核心文档)
    - [研究笔记](#研究笔记)
    - [形式化证明体系（2026-02-14）](#形式化证明体系2026-02-14)

---

## 📚 学术资源 {#-学术资源}

### 形式化方法相关论文

1. **RustBelt: Securing the Foundations of the Rust Programming Language**
   - 作者: Ralf Jung, et al.
   - 年份: 2018
   - 摘要: 使用分离逻辑形式化验证 Rust 的类型系统
   - 链接: [论文链接](https://plv.mpi-sws.org/rustbelt/)

2. **Stacked Borrows: An Aliasing Model for Rust**
   - 作者: Ralf Jung, et al.
   - 年份: 2019
   - 摘要: Rust 借用检查器的形式化模型
   - 链接: [论文链接](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)

3. **The RustBelt Project**
   - 作者: Ralf Jung, et al.
   - 摘要: Rust 形式化验证的综合项目
   - 链接: [项目主页](https://plv.mpi-sws.org/rustbelt/)

### 类型理论相关论文

1. **Type Systems for Programming Languages**
   - 作者: Benjamin C. Pierce
   - 摘要: 类型系统理论的经典教材
   - 链接: [书籍链接](https://www.cis.upenn.edu/~bcpierce/tapl/)

2. **Advanced Topics in Types and Programming Languages**
   - 作者: Benjamin C. Pierce
   - 摘要: 类型系统高级主题
   - 链接: [书籍链接](https://www.cis.upenn.edu/~bcpierce/attapl/)

3. **Rust's Type System**
   - 作者: Various
   - 摘要: Rust 类型系统的相关研究
   - 相关: [类型系统基础](./type_theory/type_system_foundations.md)
   - 形式化衔接: [00_completeness_gaps](type_theory/00_completeness_gaps.md)、[PROOF_INDEX](PROOF_INDEX.md)

### 性能优化相关论文

1. **Optimizing Rust Compiler Performance**
   - 作者: Rust Compiler Team
   - 摘要: Rust 编译器的性能优化技术
   - 相关: [编译器优化](./experiments/compiler_optimizations.md)

2. **Memory Management in Rust**
   - 作者: Various
   - 摘要: Rust 内存管理的研究
   - 相关: [内存分析](./experiments/memory_analysis.md)

---

## 📖 官方文档 {#-官方文档}

### Rust 官方文档

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

### Rust 编译器文档

- **Rust Compiler Development Guide**
  - 链接: <https://rustc-dev-guide.rust-lang.org/>
  - 描述: Rust 编译器开发指南

- **Rust Language Design (RFCs)**
  - 链接: <https://github.com/rust-lang/rfcs>
  - 描述: Rust 语言设计提案

### Rust 工具文档

- **Cargo Book**
  - 链接: <https://doc.rust-lang.org/cargo/>
  - 描述: Rust 包管理器文档

- **Clippy Documentation**
  - 链接: <https://rust-lang.github.io/rust-clippy/>
  - 描述: Rust 代码检查工具文档

---

## 🛠️ 工具资源 {#️-工具资源}

### 形式化验证工具

- **Coq**
  - 链接: <https://coq.inria.fr/>
  - 描述: 交互式定理证明器
  - 相关: [工具使用指南 - Coq](./TOOLS_GUIDE.md#coq)

- **Lean**
  - 链接: <https://leanprover.github.io/>
  - 描述: 函数式编程语言和证明助手
  - 相关: [工具使用指南 - Lean](./TOOLS_GUIDE.md#lean)

- **Prusti**
  - 链接: <https://www.pm.inf.ethz.ch/research/prusti.html>
  - 描述: Rust 的形式化验证工具
  - 相关: [工具使用指南 - Prusti](./TOOLS_GUIDE.md#prusti)

- **Kani**
  - 链接: <https://github.com/model-checking/kani>
  - 描述: Rust 的模型检查工具
  - 相关: [工具使用指南 - Kani](./TOOLS_GUIDE.md#kani)

### 性能分析工具

- **Criterion.rs**
  - 链接: <https://github.com/bheisler/criterion.rs>
  - 描述: Rust 的基准测试框架
  - 相关: [工具使用指南 - Criterion.rs](./TOOLS_GUIDE.md#criterionrs)

- **perf**
  - 链接: <https://perf.wiki.kernel.org/>
  - 描述: Linux 性能分析工具
  - 相关: [工具使用指南 - perf](./TOOLS_GUIDE.md#perf)

- **flamegraph**
  - 链接: <https://github.com/flamegraph-rs/flamegraph>
  - 描述: 性能分析可视化工具
  - 相关: [工具使用指南 - flamegraph](./TOOLS_GUIDE.md#flamegraph)

### 内存分析工具

- **Miri**
  - 链接: <https://github.com/rust-lang/miri>
  - 描述: Rust 的 MIR 解释器
  - 相关: [工具使用指南 - Miri](./TOOLS_GUIDE.md#miri)

- **Valgrind**
  - 链接: <https://valgrind.org/>
  - 描述: 内存调试和性能分析工具
  - 相关: [工具使用指南 - Valgrind](./TOOLS_GUIDE.md#valgrind)

- **heaptrack**
  - 链接: <https://github.com/KDE/heaptrack>
  - 描述: 堆内存分析工具
  - 相关: [工具使用指南 - heaptrack](./TOOLS_GUIDE.md#heaptrack)

### 代码分析工具

- **Clippy**
  - 链接: <https://github.com/rust-lang/rust-clippy>
  - 描述: Rust 代码检查工具
  - 相关: [工具使用指南 - Clippy](./TOOLS_GUIDE.md#clippy)

- **rust-analyzer**
  - 链接: <https://rust-analyzer.github.io/>
  - 描述: Rust 语言服务器
  - 相关: [工具使用指南 - rust-analyzer](./TOOLS_GUIDE.md#rust-analyzer)

- **cargo-expand**
  - 链接: <https://github.com/dtolnay/cargo-expand>
  - 描述: 宏展开工具
  - 相关: [工具使用指南 - cargo-expand](./TOOLS_GUIDE.md#cargo-expand)

---

## 📝 社区资源 {#-社区资源}

### 社区论坛

- **Rust Users Forum**
  - 链接: <https://users.rust-lang.org/>
  - 描述: Rust 用户讨论论坛

- **Rust Internals Forum**
  - 链接: <https://internals.rust-lang.org/>
  - 描述: Rust 内部开发讨论

- **Reddit r/rust**
  - 链接: <https://www.reddit.com/r/rust/>
  - 描述: Rust 社区讨论

### 社区项目

- **Awesome Rust**
  - 链接: <https://github.com/rust-unofficial/awesome-rust>
  - 描述: Rust 资源汇总

- **Rust Learning Resources**
  - 链接: <https://github.com/ctjhoa/rust-learning>
  - 描述: Rust 学习资源汇总

---

## 🎓 学习资源 {#-学习资源}

### 在线课程

- **Rustlings**
  - 链接: <https://github.com/rust-lang/rustlings>
  - 描述: Rust 编程练习

- **Rust by Practice**
  - 链接: <https://practice.rs/>
  - 描述: Rust 实践练习

### 书籍

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

## 📰 新闻和博客 {#-新闻和博客}

### 官方博客

- **Rust Blog**
  - 链接: <https://blog.rust-lang.org/>
  - 描述: Rust 官方博客

- **Inside Rust**
  - 链接: <https://blog.rust-lang.org/inside-rust/>
  - 描述: Rust 内部开发博客

### 社区博客

- **This Week in Rust**
  - 链接: <https://this-week-in-rust.org/>
  - 描述: Rust 周报

- **Rustacean Station**
  - 链接: <https://rustacean-station.org/>
  - 描述: Rust 播客

---

## 资源与形式化衔接

| 资源类型 | 形式化文档 | 可验证/支撑的定理 |
| :--- | :--- | :--- |
| RustBelt、Stacked Borrows | [ownership_model](formal_methods/ownership_model.md)、[borrow_checker_proof](formal_methods/borrow_checker_proof.md)、[coq_skeleton](coq_skeleton/)、[RUSTBELT_ALIGNMENT](RUSTBELT_ALIGNMENT.md) | OW1、T2/T3、CHAN-T1、MUTEX-T1；Coq T-OW2 骨架 |
| Rust 类型系统研究 | [type_system_foundations](type_theory/type_system_foundations.md)、[trait_system_formalization](type_theory/trait_system_formalization.md) | 类型保持、coherence、RPITIT |
| Prusti、Kani | [formal_methods](formal_methods/README.md) | 所有权、借用、unsafe 契约 |
| Criterion、Miri | [experiments/README](experiments/README.md) | EX-T1、EX-T2；内存安全验证 |

详见 [PROOF_INDEX](PROOF_INDEX.md) 全证明索引、
[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) 国际对标、
[FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md) 批判性分析与推进计划、
[practical_applications](practical_applications.md) 案例与定理对应。

---

## 🔗 相关资源 {#-相关资源}

### 核心文档

- [主索引](./README.md) - 完整的研究笔记索引
- [工具使用指南](./TOOLS_GUIDE.md) - 研究工具详细指南
- [术语表](./GLOSSARY.md) - 专业术语解释

### 研究笔记

- [形式化方法研究](./formal_methods/README.md) - 形式化方法索引
- [类型理论研究](./type_theory/README.md) - 类型理论索引
- [实验研究](./experiments/README.md) - 实验研究索引

### 形式化证明体系（2026-02-14）

- [批判性分析与推进计划](./FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md) - 阶段 1–3 完成总结
- [国际对标索引](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) - RustBelt、Aeneas、RustSEM 等
- [形式化全模型入口](./FORMAL_FULL_MODEL_OVERVIEW.md) - 统一形式系统
- [核心定理完整证明](./CORE_THEOREMS_FULL_PROOFS.md) - L2 级 ownership T2、borrow T1、type T3
- [Coq 证明骨架](./coq_skeleton/) - T-OW2 所有权唯一性
- [L3 实施指南](../archive/deprecated/COQ_ISABELLE_PROOF_SCAFFOLDING.md) - Coq/Isabelle 补全路线（已归档）

---

**维护团队**: Rust Research Community
**最后更新**: 2026-02-28
**状态**: ✅ **Rust 1.93.1+ 更新完成**
