# 学术论文与形式化工具对齐索引 {#学术论文与形式化工具对齐索引}

> **概念族**: 权威来源对齐 / 学术资源
> **内容分级**: [核心级]
> **层级**: L0-L6
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [学术论文与形式化工具对齐索引](#学术论文与形式化工具对齐索引)
  - [目录](#目录)
  - [一、对齐说明](#一对齐说明)
  - [二、形式化语义与内存模型](#二形式化语义与内存模型)
  - [三、所有权与借用形式化](#三所有权与借用形式化)
  - [四、类型系统形式化](#四类型系统形式化)
  - [五、并发与异步形式化](#五并发与异步形式化)
  - [六、验证工具](#六验证工具)
  - [七、顶级会议/期刊资源](#七顶级会议期刊资源)
    - [7.1 顶级会议](#71-顶级会议)
    - [7.2 顶级期刊](#72-顶级期刊)
  - [八、按出版商分类](#八按出版商分类)
    - [8.1 ACM Digital Library (ACM DL)](#81-acm-digital-library-acm-dl)
    - [8.2 IEEE Xplore](#82-ieee-xplore)
    - [8.3 Springer](#83-springer)
    - [8.4 arXiv](#84-arxiv)
  - [九、未覆盖缺口](#九未覆盖缺口)
  - [相关概念](#相关概念)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的形式化内容与相关学术论文、验证工具建立映射，覆盖 Rust 语义、内存模型、所有权、借用、类型系统、并发、异步等核心主题的学术来源。新增“顶级会议/期刊资源”与“按出版商分类”两章，以支撑权威来源对齐网络的国际化（IEEE/ACM/arXiv/Springer）建设。

---

## 二、形式化语义与内存模型 {#二形式化语义与内存模型}

| 论文/工具 | 机构/作者 | 主题 | 项目文档 | 状态 |
|-----------|-----------|------|----------|------|
| [RustBelt (POPL 2018)](https://dl.acm.org/doi/10.1145/3158154) | MPI-SWS (Jung et al.) | 所有权、借用、unsafe 语义 | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) | ✅ |
| [RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/) | MPI-SWS | Iris 逻辑中的 Rust 形式化 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ |
| [Stacked Borrows (POPL 2020)](https://dl.acm.org/doi/10.1145/3371109) | MPI-SWS (Jung et al.) | 别名模型 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| [Tree Borrows (PLDI 2025)](https://dl.acm.org/doi/10.1145/3735592) | ETH Zürich / MPI-SWS (Villani et al.) | 改进别名模型 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| [RustSEM (FMSD 2024)](https://link.springer.com/article/10.1007/s10703-024-00460-3) | 多机构 (K-Framework) | 可执行操作语义 | [10_rustsem_semantics.md](10_rustsem_semantics.md) | ✅ |

---

## 三、所有权与借用形式化 {#三所有权与借用形式化}

| 论文/工具 | 机构/作者 | 主题 | 项目文档 | 状态 |
|-----------|-----------|------|----------|------|
| [RustBelt](https://dl.acm.org/doi/10.1145/3158154) | MPI-SWS (Jung et al.) | 所有权公理 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ |
| [Aeneas (ICFP 2022)](https://dl.acm.org/doi/10.1145/3547647) | EPFL / INRIA (Ho & Protzenko) | 可验证 Rust 子集 | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) / [10_aeneas_integration_plan.md](10_aeneas_integration_plan.md) | ✅ |
| [Oxide (arXiv 2019)](https://arxiv.org/abs/1903.00982) | 宾夕法尼亚大学 (Weiss et al.) | 类型化操作语义 | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 🔄 |

---

## 四、类型系统形式化 {#四类型系统形式化}

| 论文/工具 | 机构/作者 | 主题 | 项目文档 | 状态 |
|-----------|-----------|------|----------|------|
| [Rust RFCs – Associated Items](https://rust-lang.github.io/rfcs/0195-associated-items.html) | Rust 社区 | 关联类型 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ |
| [Ferrocene FLS](https://spec.ferrocene.dev/) | Ferrous Systems | 安全关键类型系统规范 | [10_ferrocene_fls_alignment.md](10_ferrocene_fls_alignment.md) | ✅ |
| [coq-of-rust](https://github.com/formal-land/coq-of-rust) | Formal Land | Coq/Rocq 中的 Rust 翻译 | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | ✅ |
| [Oxide](https://arxiv.org/abs/1903.00982) | 宾夕法尼亚大学 (Weiss et al.) | 线性/所有权类型语义 | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 🔄 |

---

## 五、并发与异步形式化 {#五并发与异步形式化}

| 论文/工具 | 机构/作者 | 主题 | 项目文档 | 状态 |
|-----------|-----------|------|----------|------|
| [RustBelt – Send/Sync](https://dl.acm.org/doi/10.1145/3158154) | MPI-SWS (Jung et al.) | 并发安全形式化 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | ✅ |
| [Aeneas – async support](https://dl.acm.org/doi/10.1145/3547647) | EPFL / INRIA (Ho & Protzenko) | 异步状态机验证 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ |
| [Async Rust: 从 Semantics to Safety](https://arxiv.org/abs/2201.12334) | 多机构 | 异步语义 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | 🔄 |

---

## 六、验证工具 {#六验证工具}

| 工具 | 类型 | 主要论文/来源 | 项目文档 | 状态 |
|------|------|---------------|----------|------|
| [Aeneas](https://aeneas-verification.github.io/) | 基于借用的验证 | [ICFP 2022, DOI 10.1145/3547647](https://dl.acm.org/doi/10.1145/3547647) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | ✅ |
| [coq-of-rust](https://github.com/formal-land/coq-of-rust) | Coq/Rocq 翻译 | [GitHub / Formal Land](https://github.com/formal-land/coq-of-rust) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | ✅ |
| [RustHorn](https://github.com/sosnek/rusthorn) | CHC 验证 | [PLDI 2020 / arXiv](https://arxiv.org/abs/2002.09002) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 🔄 |
| [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html) | 合约验证 | [OOPSLA 2019, DOI 10.1145/3360573](https://dl.acm.org/doi/10.1145/3360573) / [NFM 2022, DOI 10.1007/978-3-031-06773-0_5](https://link.springer.com/chapter/10.1007/978-3-031-06773-0_5) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) / [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | 🔄 |
| [Creusot](https://github.com/creusot-rs/creusot) | WhyML/Why3 验证 | [ICFEM 2022, DOI 10.1007/978-3-031-17244-1_6](https://link.springer.com/chapter/10.1007/978-3-031-17244-1_6) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) / [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | 🔄 |
| [Kani](https://github.com/model-checking/kani) | 模型检查 | [ICSE-SEIP 2022, DOI 10.1145/3510457.3513031](https://dl.acm.org/doi/10.1145/3510457.3513031) | [10_verification_tools_matrix.md](10_verification_tools_matrix.md) / [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | ✅ |

---

## 七、顶级会议/期刊资源 {#七顶级会议期刊资源}

本节按顶级会议/期刊汇总与 Rust 直接相关的代表性论文与工具，覆盖 POPL、PLDI、OOPSLA、ICFP、CC、ECOOP 及 TOPLAS、JFP、FMSD 等权威出版渠道。

### 7.1 顶级会议 {#71-顶级会议}

| 会议 | 论文/工具 | 作者/机构 | 出版来源 | DOI / 链接 | 项目文档映射 | 状态 |
|------|-----------|-----------|----------|------------|--------------|------|
| **POPL** | RustBelt: Securing the Foundations of the Rust Programming Language | Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer (MPI-SWS) | PACMPL 2, POPL, Article 66 (2018) | [10.1145/3158154](https://dl.acm.org/doi/10.1145/3158154) | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) / [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ |
| **POPL** | Stacked Borrows: An Aliasing Model for Rust | Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer (MPI-SWS) | PACMPL 4, POPL, Article 41 (2020) | [10.1145/3371109](https://dl.acm.org/doi/10.1145/3371109) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| **POPL** | RustBelt Meets Relaxed Memory | Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer, et al. (MPI-SWS) | PACMPL 4, POPL (2020) | [10.1145/3371073](https://dl.acm.org/doi/10.1145/3371073) | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | ✅ |
| **PLDI** | Tree Borrows: A New Aliasing Model for Rust (Distinguished Paper) | Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung | PACMPL 9, PLDI, Article 188 (2025) | [10.1145/3735592](https://dl.acm.org/doi/10.1145/3735592) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| **PLDI** | RefinedRust: A Type System for High-Assurance Verification of Rust Programs | Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, Derek Dreyer | PACMPL 8, PLDI (2024) | [10.1145/3656422](https://dl.acm.org/doi/10.1145/3656422) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 🔄 |
| **OOPSLA** | Leveraging Rust Types for Modular Specification and Verification | Vytautas Astrauskas, Peter Müller, Federico Poli, Alexander J. Summers (ETH Zürich) | PACMPL 3, OOPSLA, Article 147 (2019) | [10.1145/3360573](https://dl.acm.org/doi/10.1145/3360573) | [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | 🔄 |
| **ICFP** | Aeneas: Rust Verification by Functional Translation | Son Ho, Jonathan Protzenko (EPFL / INRIA) | PACMPL 6, ICFP (2022) | [10.1145/3547647](https://dl.acm.org/doi/10.1145/3547647) | [10_aeneas_integration_plan.md](10_aeneas_integration_plan.md) / [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | ✅ |
| **ICFP** | GhostCell: Separating Permissions from Data in Rust | Joshua Yanovski, Hoang-Hai Dang, Ralf Jung, Derek Dreyer | PACMPL 5, ICFP, Article 92 (2021) | [10.1145/3473597](https://dl.acm.org/doi/10.1145/3473597) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | 🔄 |
| **CC** | — | — | — | — | — | ⏳ |
| **ECOOP** | — | — | — | — | — | ⏳ |

### 7.2 顶级期刊 {#72-顶级期刊}

| 期刊 | 论文/工具 | 作者/机构 | 出版来源 | DOI / 链接 | 项目文档映射 | 状态 |
|------|-----------|-----------|----------|------------|--------------|------|
| **TOPLAS** | — | — | — | — | — | ⏳ |
| **JFP** | Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent Separation Logic | Ralf Jung, Robbert Krebbers, Jacques-Henri Jourdan, Aleš Bizjak, Lars Birkedal, Derek Dreyer | JFP 28 (2018), e20 | [10.1017/S0956796818000151](https://doi.org/10.1017/S0956796818000151) | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) | ✅ |
| **FMSD** | RustSEM: An Executable Operational Semantics for Rust | 多机构 (K-Framework) | Formal Methods in System Design (2024) | [10.1007/s10703-024-00460-3](https://link.springer.com/article/10.1007/s10703-024-00460-3) | [10_rustsem_semantics.md](10_rustsem_semantics.md) | ✅ |

---

## 八、按出版商分类 {#八按出版商分类}

### 8.1 ACM Digital Library (ACM DL) {#81-acm-digital-library-acm-dl}

| 论文/工具 | 会议/期刊 | DOI / 链接 | 项目文档映射 | 状态 |
|-----------|-----------|------------|--------------|------|
| RustBelt | POPL 2018 | [10.1145/3158154](https://dl.acm.org/doi/10.1145/3158154) | [10_rustbelt_alignment.md](10_rustbelt_alignment.md) | ✅ |
| Stacked Borrows | POPL 2020 | [10.1145/3371109](https://dl.acm.org/doi/10.1145/3371109) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| RustBelt Meets Relaxed Memory | POPL 2020 | [10.1145/3371073](https://dl.acm.org/doi/10.1145/3371073) | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | ✅ |
| Tree Borrows | PLDI 2025 | [10.1145/3735592](https://dl.acm.org/doi/10.1145/3735592) | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ |
| Aeneas | ICFP 2022 | [10.1145/3547647](https://dl.acm.org/doi/10.1145/3547647) | [10_aeneas_integration_plan.md](10_aeneas_integration_plan.md) | ✅ |
| Prusti (核心论文) | OOPSLA 2019 | [10.1145/3360573](https://dl.acm.org/doi/10.1145/3360573) | [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | 🔄 |
| Kani | ICSE-SEIP 2022 | [10.1145/3510457.3513031](https://dl.acm.org/doi/10.1145/3510457.3513031) | [10_verification_tools_matrix.md](10_verification_tools_matrix.md) | ✅ |
| RefinedRust | PLDI 2024 | [10.1145/3656422](https://dl.acm.org/doi/10.1145/3656422) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 🔄 |

### 8.2 IEEE Xplore {#82-ieee-xplore}

| 论文/工具 | 会议/期刊 | DOI / 链接 | 项目文档映射 | 状态 |
|-----------|-----------|------------|--------------|------|
| — | — | — | — | ⏳ |

> **说明**：Rust 形式化领域在 IEEE 渠道的直接论文相对较少；IEEE 上多见 Rust 系统/安全/嵌入式应用研究（如 QRS、ISSRE、ICSE 等）。本索引当前聚焦 PL 形式化主线，IEEE 形式化条目待后续补充。

### 8.3 Springer {#83-springer}

| 论文/工具 | 会议/期刊 | DOI / 链接 | 项目文档映射 | 状态 |
|-----------|-----------|------------|--------------|------|
| RustSEM | FMSD 2024 | [10.1007/s10703-024-00460-3](https://link.springer.com/article/10.1007/s10703-024-00460-3) | [10_rustsem_semantics.md](10_rustsem_semantics.md) | ✅ |
| Creusot | ICFEM 2022 | [10.1007/978-3-031-17244-1_6](https://link.springer.com/chapter/10.1007/978-3-031-17244-1_6) | [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | 🔄 |
| Prusti 项目综述 | NFM 2022 | [10.1007/978-3-031-06773-0_5](https://link.springer.com/chapter/10.1007/978-3-031-06773-0_5) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 🔄 |

### 8.4 arXiv {#84-arxiv}

| 论文/工具 | 版本/年份 | 链接 | 项目文档映射 | 状态 |
|-----------|-----------|------|--------------|------|
| Oxide: The Essence of Rust | arXiv:1903.00982 (2019) | [arxiv.org/abs/1903.00982](https://arxiv.org/abs/1903.00982) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | 🔄 |
| Async Rust: from Semantics to Safety | arXiv:2201.12334 (2022) | [arxiv.org/abs/2201.12334](https://arxiv.org/abs/2201.12334) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | 🔄 |
| RustHorn | arXiv:2002.09002 (2020) | [arxiv.org/abs/2002.09002](https://arxiv.org/abs/2002.09002) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | 🔄 |
| coq-of-rust / Rocq-of-Rust | GitHub 持续更新 | [github.com/formal-land/coq-of-rust](https://github.com/formal-land/coq-of-rust) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) | ✅ |

---

## 九、未覆盖缺口 {#九未覆盖缺口}

1. **CC / ECOOP 中的 Rust 论文**：目前未做系统梳理，需后续补充编译器构造、面向对象程序设计等方向的工作。
2. **IEEE Xplore 形式化条目**：IEEE 渠道 Rust 形式化论文较少，但系统/安全/验证应用研究可进一步挖掘并映射。
3. **TOPLAS / JFP 期刊**：除 Iris 与 RustSEM 外，TOPLAS 中 Rust 形式化工作、JFP 中 Rust 类型理论论文待补充。
4. **RustHorn、Prusti、Creusot 的具体论文与项目论证链**可进一步关联到 [10_international_formal_verification_index.md](10_international_formal_verification_index.md)。
5. **异步 Rust 的学术论文**（如 async/await 语义、Future/poll 形式化）可专门整理。
6. **形式化验证工具的最新进展**（RefinedRust、Verus、Miri 论文）需持续跟踪。

> **权威来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/) | [Aeneas](https://aeneas-verification.github.io/) | [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) | [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3) | [ACM DL](https://dl.acm.org/) | [IEEE Xplore](https://ieeexplore.ieee.org/) | [Springer](https://link.springer.com/) | [arXiv](https://arxiv.org/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [国际形式化验证索引](10_international_formal_verification_index.md)
- [RustBelt 对齐](10_rustbelt_alignment.md)
- [Ferrocene FLS 对齐](10_ferrocene_fls_alignment.md)
- [验证工具实战对齐](10_verification_tools_practical_alignment.md)
- [验证工具矩阵](10_verification_tools_matrix.md)
- [Aeneas 整合计划](10_aeneas_integration_plan.md)
- [知识图谱索引](10_knowledge_graph_index.md)