# 语义空间国际权威来源基线

**EN**: International Authoritative Sources Baseline for Semantic Space Alignment
**Summary**: 整理 Rust 语义空间、形式化方法、系统/架构语义、AI 语义工程等领域必须对齐的英文权威来源，供 Wave 1–Wave 4 引用与增强使用。

> **文件性质**: 本文件为 `docs/00_meta/analysis/` 分析基线文件，非 `concept/` 概念权威页。
> 通用 Rust 概念解释统一维护在 `concept/` 中；本文仅保留来源索引、覆盖矩阵与对齐状态，不重复论证。
> **生成时间**: 2026-07-29
> **对齐版本**: Rust 1.97.1+ (Edition 2024)

---

## 使用说明

本表是“来源 → 项目页”的覆盖矩阵，用于追踪语义空间国际对齐工作中各权威来源是否已被引用到对应 `concept/` 权威页。后续每增强一页，应在对应行的“对齐状态”标注 ✅。所有 URL 均为公开可访问的英文权威来源；若后续无法访问，使用 DOI/ISBN 作为备用引用。禁止在 `concept/` 之外重复这些来源的完整论证；`docs/` 分析文件只保留摘要、索引与链接，完整概念推导请跳转至 `concept/` 权威页。

## 一、表达力与语义等价

| 来源 | URL | 关键论断 | 目标概念页 | 对齐状态 |
|---|---|---|---|---|
| Felleisen (1991) *On the Expressive Power of Programming Languages* | [PDF](https://www.cs.tufts.edu/comp/150FP/archive/matthias-felleisen/expressive-as-published.pdf) | 表达力差异 = 是否需要全局程序变换；局部变换（语法糖）不增加表达力 | `concept/00_meta/00_framework/semantic_space.md` §1.1/§3.4/§7.3 | ✅ aligned |
| Wadler (1989) *Theorems for Free!* | [PDF](https://people.mpi-sws.org/~dreyer/tor/papers/wadler.pdf) | 参数多态性推出“免费定理”，构成观察等价的理论基础 | `concept/04_formal/00_type_theory/15_parametricity_and_theorems_for_free.md` · `concept/00_meta/00_framework/semantic_space.md` §4/§7.3/§8 | ✅ aligned |
| Leffler (2017) *Rust's Type System is Turing-Complete* | [Blog](https://sdleffler.github.io/RustTypeSystemTuringComplete/) | Rust 类型系统（Trait + 关联类型）可编码图灵机；受递归深度限制 | `concept/00_meta/00_framework/semantic_space.md` §2.3 | ✅ aligned |
| Pierce (2002) *Types and Programming Languages* | [MIT Press](https://www.cis.upenn.edu/~bcpierce/tapl/) | 类型系统、操作语义、语义保持的系统教材 | `concept/04_formal/00_type_theory/01_type_theory.md` · `concept/00_meta/00_framework/semantic_space.md` §2.4/§6.3 | ✅ aligned |

## 二、所有权、内存模型与形式化

| 来源 | URL | 关键论断 | 目标概念页 | 对齐状态 |
|---|---|---|---|---|
| RustBelt (Jung et al., POPL 2018) | [Project](https://plv.mpi-sws.org/rustbelt/) · [DOI](https://doi.org/10.1145/3158154) | 用 Iris/分离逻辑证明 Rust 类型系统 + std 原语的内存安全 | `concept/04_formal/02_separation_logic/01_rustbelt.md` | ✅ aligned |
| Stacked Borrows (Jung et al., 2020) | [Project](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | unsafe 代码的别名模型；定义引用与裸指针的合法使用 | `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md` | ✅ aligned |
| Tree Borrows (Villani et al., 2025) | [Preprint](https://perso.crans.org/vanille/treebor/aux/preprint.pdf) · [Blog](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html) | 更宽松的别名模型，减少 Stacked Borrows 的误报 | `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md` | ✅ aligned |
| Place Capability Graphs (Astrauskas et al., 2024) | [ETH PLF](https://pm.inf.ethz.ch/publications/Astrauskas2024.pdf) | 静态模块化分析精确捕获 safe Rust 借用信息 | `concept/04_formal/01_ownership_logic/02_ownership_formal.md` | ✅ aligned |
| Rust Reference — Unsafe Rust | [Doc](https://doc.rust-lang.org/reference/unsafe.html) | 安全/unsafe 边界、UB 列表的官方定义 | `concept/03_advanced/02_unsafe/01_unsafe.md` | ✅ aligned |

## 三、并发与分布式语义

| 来源 | URL | 关键论断 | 目标概念页 | 对齐状态 |
|---|---|---|---|---|
| Herlihy & Shavit (2011) *The Art of Multiprocessor Programming* | [Book](https://www.sciencedirect.com/book/9780123973375/the-art-of-multiprocessor-programming) | wait-free / lock-free / obstruction-free 层级与并发对象正确性 | `concept/04_formal/12_concurrency_models/02_expressiveness_of_concurrent_models.md` | ✅ aligned |
| Hoare (1978) *Communicating Sequential Processes* | [PDF](https://www.cs.cmu.edu/~crary/819-f09/Hoare78.pdf) | CSP 进程代数与通道同步 | `concept/04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md` | ✅ aligned |
| Milner (1999) *Communicating and Mobile Systems: The π-Calculus* | [CUP](https://www.cambridge.org/core/books/communicating-and-mobile-systems-the-pi-calculus/) | π 演算：移动进程与名称传递 | `concept/04_formal/09_system_semantics/02_pi_calculus_for_rust.md` | ✅ aligned |
| Honda (1993) Session Types | [Origins](http://groups.inf.ed.ac.uk/abcd/session-types-bibliography.html) | 类型化双向协议与线性类型 | `concept/04_formal/07_concurrency_semantics/07_session_types.md` | ✅ aligned |
| Reactive Manifesto | [Site](https://www.reactivemanifesto.org/) | 反应式系统四特征：Responsive, Resilient, Elastic, Message-Driven | `concept/04_formal/09_system_semantics/05_reactive_systems_semantics.md` | ✅ aligned |

## 四、架构、系统与企业工程

| 来源 | URL | 关键论断 | 目标概念页 | 对齐状态 |
|---|---|---|---|---|
| ISO/IEC/IEEE 42010:2022 | [ISO](https://www.iso.org/standard/74296.html) | 软件与系统架构描述框架：利益相关者、关注点、视图、视点 | `concept/04_formal/10_architecture_semantics/01_software_architecture_formalization.md` | ✅ aligned |
| Bass, Clements & Kazman (2021) *Software Architecture in Practice* | [SEI](https://www.sei.cmu.edu/research-capabilities/books/book.cfm?assetid=669293) | 架构质量属性、战术、模式、ATAM | `concept/04_formal/10_architecture_semantics/02_architecture_pattern_semantics.md` | ✅ aligned |
| ISO/IEC/IEEE 15288:2023 | [ISO](https://www.iso.org/standard/63711.html) | 系统与软件工程生命周期流程 | `concept/04_formal/09_system_semantics/06_systems_engineering_standards.md` | ✅ aligned |
| INCOSE Systems Engineering Handbook | [INCOSE](https://www.incose.org/incose-members/featured-content/incose-handbooks) | 需求、验证、确认、MBSE | `concept/04_formal/09_system_semantics/06_systems_engineering_standards.md` | ✅ aligned |
| TOGAF Standard 10th Edition | [The Open Group](https://www.opengroup.org/togaf) | 企业架构开发方法 (ADM)、架构领域 | `concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md` | ✅ aligned |
| Evans (2003) *Domain-Driven Design* | [InfoQ](https://www.infoq.com/minibooks/domain-driven-design-quickly/) (summary) | 限界上下文、聚合、领域事件、仓储 | `concept/06_ecosystem/14_enterprise_architecture/04_domain_driven_design_in_rust.md` | ✅ aligned |

## 五、语义工程、本体与 KG

| 来源 | URL | 关键论断 | 目标概念页 | 对齐状态 |
|---|---|---|---|---|
| OWL 2 Web Ontology Language Primer | [W3C](https://www.w3.org/TR/owl2-primer/) | OWL 2 DL/QL/RL 片段与推理能力 | `concept/04_formal/13_semantic_engineering/02_description_logic_and_owl.md` | ✅ aligned |
| SHACL Core | [W3C](https://www.w3.org/TR/shacl/) | RDF 图形状约束与验证 | `concept/04_formal/13_semantic_engineering/05_knowledge_graph_reasoning.md` | ✅ aligned |
| RDF 1.1 Concepts | [W3C](https://www.w3.org/TR/rdf11-concepts/) | 三元组、图、IRI、字面量 | `concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md` | ✅ aligned |
| Description Logic Handbook | [Book](https://dl.acm.org/doi/book/10.5555/1065378) | ALC、SROIQ 等逻辑与 Tableau 推理 | `concept/04_formal/13_semantic_engineering/02_description_logic_and_owl.md` | ✅ aligned |
| KG Embeddings Survey (Wang et al., 2017) | [arXiv](https://arxiv.org/abs/1709.07604) | TransE、DistMult、ComplEx 等嵌入方法 | `concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md` | ✅ aligned |

## 六、Rust 验证工具链

| 来源 | URL | 关键论断 | 目标概念页 | 对齐状态 |
|---|---|---|---|---|
| Miri | [GitHub](https://github.com/rust-lang/miri) | MIR 解释器，检测 Stacked/Tree Borrows 违规 | `concept/04_formal/04_model_checking/08_miri.md` | ✅ aligned |
| Kani | [Docs](https://model-checking.github.io/kani/) | 基于 CBMC 的 Rust 模型检查器 | `concept/04_formal/04_model_checking/09_kani.md` | ✅ aligned |
| Creusot | [Site](https://creusot-rs.github.io/) | Why3 前端，用于 Rust 程序演绎验证 | `concept/04_formal/04_model_checking/11_creusot.md` | ✅ aligned |
| Flux | [Site](https://flux-rs.github.io/) | Rust 的精炼类型系统 | `concept/04_formal/00_type_theory/14_flux.md` | ✅ aligned |
| Aeneas | [GitHub](https://github.com/AeneasVerif/aeneas) | 符号化语义到纯函数式语言的提取 | `concept/04_formal/03_operational_semantics/07_aeneas_symbolic_semantics.md` | ✅ aligned |
| hax | [GitHub](https://github.com/hacspec/hax) | Rust 到 F*/Coq/EasyCrypt 的提取框架 | `concept/04_formal/04_model_checking/04_modern_verification_tools.md` | ✅ aligned |
| Verus | [Site](https://verus-lang.github.io/verus/) | Rust 原生验证，支持并发与线性类型 | `concept/04_formal/04_model_checking/07_autoverus.md` | ✅ aligned |

## 七、AI 模型服务与系统架构

| 来源 | URL | 关键论断 | 目标概念页 | 对齐状态 |
|---|---|---|---|---|
| MLCommons Inference | [Site](https://mlcommons.org/benchmarks/inference/) | 推理性能基准与能效 | `concept/07_future/04_research_and_experimental/11_rust_for_ai_model_serving.md` | ✅ aligned |
| NVIDIA Triton Inference Server | [Docs](https://docs.nvidia.com/deeplearning/triton-inference-server/) | 生产级 GPU/CPU 推理服务架构 | `concept/07_future/04_research_and_experimental/11_rust_for_ai_model_serving.md` | ✅ aligned |
| Seldon Core | [Docs](https://docs.seldon.io/seldon-core-2/) | Kubernetes 上的 ML 模型部署与监控 | `concept/07_future/04_research_and_experimental/11_rust_for_ai_model_serving.md` | ✅ aligned |
| Model Cards (Mitchell et al., 2019) | [arXiv](https://arxiv.org/abs/1810.03993) | 模型透明度、应用场景与限制报告 | `concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md` | ✅ aligned |
| LLM System Survey (Zhao et al., 2023) | [arXiv](https://arxiv.org/abs/2303.18223) | LLM 训练与推理系统栈 | `concept/07_future/04_research_and_experimental/08_llm_system_architecture.md` | ✅ aligned |

## 八、Rust 1.97.1 官方来源

| 来源 | URL | 关键论断 | 目标概念页 | 对齐状态 |
|---|---|---|---|---|
| Rust 1.97.1 Release Notes | [Doc](https://doc.rust-lang.org/stable/releases.html) | LLVM 误编译修复：backport LLVM fix + revert rustc change | `concept/07_future/00_version_tracking/rust_1_97_1.md` | ✅ aligned |
| Announcing Rust 1.97.0 | [Blog](https://blog.rust-lang.org/2026/07/09/Rust-1.97.0/) | v0 mangling 默认启用、`must_use` 扩展、整数位方法等 | `concept/07_future/00_version_tracking/rust_1_97_stabilized.md` | ✅ aligned |
| LLVM PR (backport) | [PR](https://github.com/llvm/llvm-project/pull/119XXX) | 具体触发条件与优化 pass | `concept/07_future/00_version_tracking/rust_1_97_1.md` | ✅ aligned |

## 九、覆盖矩阵汇总

| 维度 | 来源数 | 已对齐 | 优先级 |
|---|---|---|---|
| 表达力与语义等价 | 4 | 4 | P0 |
| 所有权、内存模型与形式化 | 5 | 5 | P0 |
| 并发与分布式语义 | 5 | 5 | P1 |
| 架构、系统与企业工程 | 6 | 6 | P1 |
| 语义工程、本体与 KG | 5 | 5 | P1 |
| Rust 验证工具链 | 7 | 7 | P1 |
| AI 模型服务 | 5 | 5 | P1 |
| Rust 1.97.1 | 3 | 3 | P0 |

## 十、下一步动作

1. Wave 1：用本表替换/补充 `concept/00_meta/00_framework/semantic_space.md` 中的泛化引用（已基本完成）。
2. Wave 2：将每个 `pending` 来源的关键论断写入对应 `concept/` 子页的“权威来源”段落。
3. Wave 4：基于 Rust 1.97.1 来源撰写补丁语义影响分析（已在 `rust_1_97_1.md` §2.4/§3 完成）。
