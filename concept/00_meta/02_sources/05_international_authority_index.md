> **内容分级**: [综述级]

# International Authority Index（国际化权威来源索引）
>
> **EN**: International Authority Index
> **Summary**: A curated, categorized index of authoritative international sources for Rust: official docs, academic formalization, industrial ecosystems, standards bodies, enterprise/software/system architecture, semantic engineering, AI systems, and cross-language references.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者 / 进阶]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 为每个 Rust 概念提供可验证的国际权威来源映射
> **定位**: 集中维护 Rust 知识体系所需的国际权威来源 URL，便于 concept/、knowledge/、docs/ 各层统一引用，避免重复搜索与链接失效。
> **前置概念**: [Authority Source Map](01_authority_source_map.md) · [Sources](03_sources.md) · [Topic-Authority Alignment Map](04_topic_authority_alignment_map.md)
> **后置概念**: [Concept Index](../04_navigation/03_concept_index.md) · [Knowledge Mindmap](../00_framework/knowledge_mindmap.md)
>
> **来源**:
> [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) ·
> [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) ·
> [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) ·
> [Rust By Example](https://doc.rust-lang.org/rust-by-example/index.html)

---

> **对应 Crate**: N/A
> **对应练习**: N/A

## 📑 目录

- [International Authority Index（国际化权威来源索引）](#international-authority-index国际化权威来源索引)
  - [📑 目录](#-目录)
  - [一、Rust 官方文档](#一rust-官方文档)
  - [二、形式化与验证生态](#二形式化与验证生态)
  - [三、工业与生态库](#三工业与生态库)
    - [异步与网络](#异步与网络)
    - [数据库与 ORM](#数据库与-orm)
    - [并发与并行](#并发与并行)
    - [GUI 与跨平台](#gui-与跨平台)
    - [游戏与图形](#游戏与图形)
    - [FFI 与互操作](#ffi-与互操作)
    - [嵌入式](#嵌入式)
    - [安全与密码学](#安全与密码学)
    - [序列化、CLI、错误处理、可观测性](#序列化cli错误处理可观测性)
  - [四、跨语言权威入口](#四跨语言权威入口)
    - [C++](#c)
    - [Haskell](#haskell)
    - [Go](#go)
    - [学术通用](#学术通用)
  - [五、标准与行业规范](#五标准与行业规范)
  - [六、社区权威博客与演讲](#六社区权威博客与演讲)
  - [七、企业架构与软件工程标准](#七企业架构与软件工程标准)
  - [八、系统工程与模型驱动工程](#八系统工程与模型驱动工程)
  - [九、语义工程、本体论与知识图谱](#九语义工程本体论与知识图谱)
  - [十、AI 系统架构、MLOps/LLMOps 与安全对齐](#十ai-系统架构mlopsllmops-与安全对齐)
  - [十一、国际课程与书籍](#十一国际课程与书籍)
    - [国际课程](#国际课程)
    - [权威书籍](#权威书籍)
  - [十二、使用建议](#十二使用建议)

---

## 一、Rust 官方文档

| 来源 | URL | 适用主题 |
|:---|:---|:---|
| The Rust Programming Language (TRPL) | <https://doc.rust-lang.org/book/> | 入门、所有权、类型系统、并发、Async |
| The Rust Reference | <https://doc.rust-lang.org/reference/> | 语法、语义、Items、类型、Unsafe |
| The Rustonomicon | <https://doc.rust-lang.org/nomicon/> | Unsafe Rust、FFI、内存模型 |
| Rust By Example | <https://doc.rust-lang.org/rust-by-example/> | 示例驱动的语法与标准库用法 |
| The Cargo Book | <https://doc.rust-lang.org/cargo/> | Cargo、Workspace、Features、Publishing |
| The Edition Guide | <https://doc.rust-lang.org/edition-guide/> | Edition 差异、迁移指南 |
| The rustc Book | <https://doc.rust-lang.org/rustc/> | 编译器选项、目标平台 |
| The Rustdoc Book | <https://doc.rust-lang.org/rustdoc/> | 文档生成、Scraped Examples |
| Asynchronous Programming in Rust | <https://rust-lang.github.io/async-book/> | Future、Pin、Waker、Executors |
| Rust and WebAssembly | <https://rustwasm.github.io/docs/book/> | WASM、wasm-bindgen、web-sys |
| The Embedded Rust Book | <https://doc.rust-lang.org/embedded-book/> | embedded-hal、no_std、Bare Metal |
| Rust RFCs | <https://rust-lang.github.io/rfcs/> | 语言特性设计、Roadmap |
| Rust Project Goals | <https://rust-lang.github.io/rust-project-goals/> | 项目目标与年度路线图 |
| Rust Blog / Inside Rust | <https://blog.rust-lang.org/> · <https://blog.rust-lang.org/inside-rust/> | 发布说明、内部实现更新 |
| Rust API Guidelines | <https://rust-lang.github.io/api-guidelines/> | API 设计、命名、互操作、可预测性 |
| Rustfmt Style Guide | <https://rust-lang.github.io/style-guide/> | 代码格式与 style edition |

---

## 二、形式化与验证生态

| 来源 | URL | 说明 |
|:---|:---|:---|
| RustBelt (POPL 2018) | <https://plv.mpi-sws.org/rustbelt/> | Rust 形式化基础：所有权、类型系统 |
| Stacked Borrows | <https://plv.mpi-sws.org/rustbelt/stacked-borrows/> | 别名模型（已被 Tree Borrows 演进） |
| Tree Borrows | <https://plv.mpi-sws.org/rustbelt/> | 新的别名模型（PLDI 2025 Distinguished Paper） |
| Iris Project | <https://iris-project.org/> | 高阶并发分离逻辑框架 |
| Aeneas | <https://github.com/AeneasVerif/aeneas> | Rust 符号语义与验证 |
| Prusti | <https://www.pm.inf.ethz.ch/research/prusti.html> | 演绎验证（ETH Zürich） |
| Kani | <https://model-checking.github.io/kani/> | Rust 模型检查器（AWS） |
| Verus | <https://verus-lang.github.io/verus/guide/> | 低级系统验证 Rust |
| Miri | <https://github.com/rust-lang/miri> | UB 检测解释器 |
| Ferrocene | <https://ferrocene.dev/> | 安全关键领域 Rust |
| Safety Tags RFC | 待正式 RFC 编号 | 类型安全标签（预览） |
| Borrow Sanitizer MCP | <https://github.com/rust-lang/compiler-team/issues/958> | 运行时借用检查 sanitizer |
| a-mir-formality | <https://github.com/rust-lang/a-mir-formality> | Rust 核心类型系统形式化 |

---

## 三、工业与生态库

本节聚焦「工业与生态库」，覆盖异步与网络、数据库与 ORM、并发与并行、GUI 与跨平台等方面。
论述顺序由定义到边界：先明确「工业与生态库」在「International Authority Index（国际化权威来源索引）」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。
读完后应能用一句话复述「工业与生态库」的判定标准，并指出它在全页论证链中的位置。

### 异步与网络

| 来源 | URL |
|:---|:---|
| Tokio | <https://tokio.rs/> |
| Tokio Scheduler Internals（Carl Lerche, 2019） | <https://tokio.rs/blog/2019-10-scheduler> |
| futures-rs 官方文档 | <https://docs.rs/futures/latest/futures/> |
| Async WG 路线图（async-fundamentals-initiative） | <https://rust-lang.github.io/async-fundamentals-initiative/roadmap.html> |
| Writing an OS in Rust — Async/Await 章（phil-opp，深度实现源：手写 executor/Waker） | <https://os.phil-opp.com/async-await/> |
| async-std | <https://async.rs/> |
| Axum | <https://docs.rs/axum/latest/axum/> |
| Actix-web | <https://actix.rs/> |
| reqwest | <https://docs.rs/reqwest/latest/reqwest/> |
| tonic | <https://github.com/hyperium/tonic> |
| Quinn (QUIC) | <https://github.com/quinn-rs/quinn> |

### 数据库与 ORM

| 来源 | URL |
|:---|:---|
| Sea-ORM | <https://www.sea-ql.org/SeaORM/> |
| sqlx | <https://github.com/launchbadge/sqlx> |
| diesel | <https://diesel.rs/> |

### 并发与并行

| 来源 | URL |
|:---|:---|
| crossbeam | <https://docs.rs/crossbeam/latest/crossbeam/> |
| rayon | <https://docs.rs/rayon/latest/rayon/> |
| parking_lot | <https://docs.rs/parking_lot/latest/parking_lot/> |

### GUI 与跨平台

| 来源 | URL |
|:---|:---|
| Tauri | <https://tauri.app/> |
| Dioxus | <https://dioxuslabs.com/> |
| Leptos | <https://leptos.dev/> |
| egui | <https://www.egui.rs/> |
| Iced | <https://iced.rs/> |

### 游戏与图形

| 来源 | URL |
|:---|:---|
| Bevy | <https://bevyengine.org/> |
| wgpu | <https://wgpu.rs/> |

### FFI 与互操作

| 来源 | URL |
|:---|:---|
| bindgen | <https://rust-lang.github.io/rust-bindgen/> |
| cbindgen | <https://github.com/mozilla/cbindgen> |
| PyO3 | <https://pyo3.rs/> |
| wasm-bindgen | <https://rustwasm.github.io/wasm-bindgen/> |

### 嵌入式

| 来源 | URL |
|:---|:---|
| embedded-hal | <https://docs.rs/embedded-hal/latest/embedded_hal/> |
| cortex-m | <https://docs.rs/cortex-m/latest/cortex_m/> |
| riscv-rt | <https://docs.rs/riscv-rt/latest/riscv_rt/> |

### 安全与密码学

| 来源 | URL |
|:---|:---|
| ring | <https://github.com/briansmith/ring> |
| rustls | <https://github.com/rustls/rustls> |

### 序列化、CLI、错误处理、可观测性

| 来源 | URL |
|:---|:---|
| serde | <https://serde.rs/> |
| clap | <https://docs.rs/clap/latest/clap/> |
| anyhow | <https://docs.rs/anyhow/latest/anyhow/> |
| thiserror | <https://docs.rs/thiserror/latest/thiserror/> |
| tracing | <https://docs.rs/tracing/latest/tracing/> |

---

## 四、跨语言权威入口

本节聚焦「跨语言权威入口」，覆盖C++、Haskell、Go与学术通用。
论述顺序由定义到边界：先明确「跨语言权威入口」在「International Authority Index（国际化权威来源索引）」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。
读完后应能用一句话复述「跨语言权威入口」的判定标准，并指出它在全页论证链中的位置。

### C++

- **cppreference**: <https://en.cppreference.com/>
- **C++ Core Guidelines**: <https://isocpp.github.io/CppCoreGuidelines/CppCoreGuidelines.html>
- **Itanium C++ ABI**: <https://itanium-cxx-abi.github.io/cxx-abi/abi.html>

### Haskell

- **GHC User Guide**: <https://downloads.haskell.org/ghc/latest/docs/users_guide/>
- **Typeclassopedia**: <https://wiki.haskell.org/Typeclassopedia>
- **Haskell Wiki**: <https://wiki.haskell.org/Haskell>

### Go

- **Go Spec**: <https://go.dev/ref/spec>
- **Effective Go**: <https://go.dev/doc/effective_go>
- **Go Memory Model**: <https://go.dev/ref/mem>

### 学术通用

- **TAPL (Pierce 2002)**: <https://www.cis.upenn.edu/~bcpierce/tapl/>
- **Software Foundations**: <https://softwarefoundations.cis.upenn.edu/>

---

## 五、标准与行业规范

| 来源 | URL | 说明 |
|:---|:---|:---|
| ISO/IEC 9899 (C Standard) | <https://www.iso.org/standard/74528.html> | C 语言标准 |
| ISO/IEC 14882 (C++ Standard) | <https://www.iso.org/standard/83626.html> | C++ 语言标准 |
| ISO/IEC/IEEE 42010:2022 | <https://www.iso.org/standard/74296.html> | 系统与软件工程——架构描述 |
| MISRA C:2012 | <https://misra.org.uk/> | 嵌入式 C 安全规范 |
| ISO 26262 | <https://www.iso.org/standard/68383.html> | 汽车功能安全 |
| IEC 61508 | <https://webstore.iec.ch/publication/66912> | 工业功能安全 |
| DO-178C / ED-12C | <https://www.rtca.org/product/do-178c/> | 航空机载软件审定 |
| EN 50128 | <https://www.cenelec.eu/dyn/www/f?p=104:110:14827060398951::::FSP_ORG_ID:2128753> | 铁路控制与保护软件 |
| ISO/SAE 21434 | <https://www.iso.org/standard/70918.html> | 道路车辆网络安全工程 |
| IEC 62443 | <https://webstore.iec.ch/publication/66912> | 工业自动化控制系统网络安全 |
| Linux Kernel BPF Docs | <https://docs.kernel.org/bpf/> | eBPF 文档 |

---

## 六、社区权威博客与演讲

| 作者 / 频道 | URL |
|:---|:---|
| Niko Matsakis | <https://smallcultfollowing.com/babysteps/> |
| Carl Lerche（Tokio 作者） | <https://tokio.rs/blog/> |
| Without Boats | <https://without.boats/> |
| Jon Gjengset | <https://thesquareplanet.com/blog/> · <https://www.youtube.com/@JonGjengset> |
| Ralf Jung | <https://www.ralfj.de/blog/> |
| dtolnay | <https://github.com/dtolnay> |

---

## 七、企业架构与软件工程标准

| 来源 | URL | 说明 | 项目映射 |
|:---|:---|:---|:---|
| TOGAF Standard, 10th Edition | <https://www.opengroup.org/togaf> | The Open Group 企业架构框架 | [`concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md`](../../06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) |
| ISO/IEC/IEEE 42010:2022 | <https://www.iso.org/standard/74296.html> | 系统与软件工程——架构描述 | [`concept/06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md`](../../06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md) |
| IEEE 1471-2000 | <https://standards.ieee.org/standard/1471-2000.html> | 软件密集型系统架构描述先驱标准 | [`concept/06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md`](../../06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md) |
| SWEBOK v3/v4 | <https://www.computer.org/education/bodies-of-knowledge/software-engineering> | IEEE Computer Society 软件工程知识体系 | [`concept/06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md`](../../06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md) |
| ISO/IEC/IEEE 12207:2017 | <https://www.iso.org/standard/63712.html> | 软件生命周期过程 | [`concept/06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md`](../../06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md) |
| ISO/IEC 25010:2023 SQuaRE | <https://www.iso.org/standard/35733.html> | 系统与软件质量模型 | [`concept/06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md`](../../06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md) |
| ISO/IEC/IEEE 5055 | <https://www.iso.org/standard/80623.html> | 自动化源代码质量度量 | [`concept/06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md`](../../06_ecosystem/14_enterprise_architecture/03_architecture_standards_alignment.md) |
| OMG Essence / SEMAT | <https://www.omg.org/spec/Essence/> | 软件工程方法与过程内核 | [`concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md`](../../06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) |
| CMMI v3.0 | <https://cmmiinstitute.com/cmmi> | 能力成熟度模型集成 | [`concept/06_ecosystem/14_enterprise_architecture/02_architecture_governance_and_adrs.md`](../../06_ecosystem/14_enterprise_architecture/02_architecture_governance_and_adrs.md) |
| BAPO Model | <https://www.gartner.com/en/newsroom/press-releases> (工业实践概念) | Business-Architecture-Process-Organization 视图 | [`concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md`](../../06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) |
| C4 Model | <https://c4model.com/> | 软件架构可视化模型 | [`concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md`](../../06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) |
| arc42 | <https://arc42.org/> | 实用软件架构文档模板 | [`concept/06_ecosystem/14_enterprise_architecture/02_architecture_governance_and_adrs.md`](../../06_ecosystem/14_enterprise_architecture/02_architecture_governance_and_adrs.md) |
| Kruchten 4+1 View Model | <https://www.cs.ubc.ca/~gregor/teaching/papers/4+1view-architecture.pdf> | 软件架构多视图模型 | [`concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md`](../../06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) |
| Rozanski & Woods — Software Systems Architecture | <https://www.viewpoints-and-perspectives.info/> | 架构视点与视角方法 | [`concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md`](../../06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) |
| Architecture Decision Records (ADR) | <https://adr.github.io/> | 架构决策记录社区实践 | [`concept/06_ecosystem/14_enterprise_architecture/02_architecture_governance_and_adrs.md`](../../06_ecosystem/14_enterprise_architecture/02_architecture_governance_and_adrs.md) |

---

## 八、系统工程与模型驱动工程

| 来源 | URL | 说明 | 项目映射 |
|:---|:---|:---|:---|
| INCOSE Systems Engineering Handbook v5 | <https://www.incose.org/incose-member-resources/se-handbook> | 系统工程实践手册 | [`concept/04_formal/09_system_semantics/06_systems_engineering_standards.md`](../../04_formal/09_system_semantics/06_systems_engineering_standards.md) |
| ISO/IEC/IEEE 15288:2023 | <https://www.iso.org/standard/81713.html> | 系统生命周期过程 | [`concept/04_formal/09_system_semantics/06_systems_engineering_standards.md`](../../04_formal/09_system_semantics/06_systems_engineering_standards.md) |
| OMG SysML v2 | <https://www.omgsysml.org/SysML-2.htm> | 系统建模语言第 2 版 | [`concept/04_formal/09_system_semantics/06_systems_engineering_standards.md`](../../04_formal/09_system_semantics/06_systems_engineering_standards.md) |
| OMG Model Driven Architecture (MDA) | <https://www.omg.org/mda/> | 模型驱动架构 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |
| OMG UML 2.5.1/2.6 | <https://www.omg.org/spec/UML/> | 统一建模语言 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |
| OMG MOF | <https://www.omg.org/spec/MOF/> | 元对象设施 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |
| OMG XMI | <https://www.omg.org/spec/XMI/> | XML 元数据交换 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |
| OMG QVT | <https://www.omg.org/spec/QVT/> | 模型转换语言 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |
| Eclipse EMF | <https://www.eclipse.org/modeling/emf/> | Eclipse 建模框架 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |
| Eclipse Epsilon | <https://www.eclipse.org/epsilon/> | 可扩展模型驱动开发平台 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |
| PlantUML | <https://plantuml.com/> | 文本化 UML/SysML 绘图工具 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |
| VIATRA / IncQuery | <https://www.eclipse.org/VIATRA/> | 基于模型的查询与转换 | [`concept/06_ecosystem/03_design_patterns/19_model_driven_engineering.md`](../../06_ecosystem/03_design_patterns/19_model_driven_engineering.md) |

---

## 九、语义工程、本体论与知识图谱

| 来源 | URL | 说明 | 项目映射 |
|:---|:---|:---|:---|
| W3C OWL 2 | <https://www.w3.org/TR/owl2-overview/> | Web 本体语言 | [`concept/04_formal/13_semantic_engineering/02_description_logic_and_owl.md`](../../04_formal/13_semantic_engineering/02_description_logic_and_owl.md) |
| W3C RDF 1.2 / RDF Schema | <https://www.w3.org/TR/rdf12-concepts/> | 资源描述框架 | [`concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md`](../../04_formal/13_semantic_engineering/03_knowledge_graph_construction.md) |
| W3C SPARQL 1.1 | <https://www.w3.org/TR/sparql11-overview/> | RDF 查询语言 | [`concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md`](../../04_formal/13_semantic_engineering/03_knowledge_graph_construction.md) |
| W3C SHACL | <https://www.w3.org/TR/shacl/> | 形状约束语言 | [`concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md`](../../04_formal/13_semantic_engineering/03_knowledge_graph_construction.md) |
| W3C SKOS | <https://www.w3.org/TR/skos-reference/> | 简单知识组织系统 | [`concept/04_formal/13_semantic_engineering/04_semantic_interoperability.md`](../../04_formal/13_semantic_engineering/04_semantic_interoperability.md) |
| ISO/IEC 21838-1 Top-Level Ontologies | <https://www.iso.org/standard/71954.html> | 顶层本体顶层标准 | [`concept/04_formal/13_semantic_engineering/01_ontology_engineering.md`](../../04_formal/13_semantic_engineering/01_ontology_engineering.md) |
| Basic Formal Ontology (BFO) | <https://basic-formal-ontology.org/> | 通用顶层本体 | [`concept/04_formal/13_semantic_engineering/01_ontology_engineering.md`](../../04_formal/13_semantic_engineering/01_ontology_engineering.md) |
| OBO Foundry | <https://obofoundry.org/> | 生物医学本体协同库 | [`concept/04_formal/13_semantic_engineering/01_ontology_engineering.md`](../../04_formal/13_semantic_engineering/01_ontology_engineering.md) |
| DOL / OntoIOp | <https://ontohub.org/dol/> | 分布式本体、建模与规范语言 | [`concept/04_formal/13_semantic_engineering/04_semantic_interoperability.md`](../../04_formal/13_semantic_engineering/04_semantic_interoperability.md) |
| schema.org | <https://schema.org/> | 搜索引擎与 Web 通用词汇表 | [`concept/04_formal/13_semantic_engineering/04_semantic_interoperability.md`](../../04_formal/13_semantic_engineering/04_semantic_interoperability.md) |
| DBpedia | <https://www.dbpedia.org/> | 从 Wikipedia 抽取的开放知识图谱 | [`concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md`](../../04_formal/13_semantic_engineering/03_knowledge_graph_construction.md) |
| Wikidata | <https://www.wikidata.org/> | 结构化知识库与 SPARQL 端点 | [`concept/04_formal/13_semantic_engineering/03_knowledge_graph_construction.md`](../../04_formal/13_semantic_engineering/03_knowledge_graph_construction.md) |
| W3C Linked Data Platform | <https://www.w3.org/TR/ldp/> | 链接数据平台协议 | [`concept/04_formal/13_semantic_engineering/04_semantic_interoperability.md`](../../04_formal/13_semantic_engineering/04_semantic_interoperability.md) |
| ISO/IEC 19763 (Metamodel framework) | <https://www.iso.org/standard/57373.html> | 互操作元模型框架 | [`concept/04_formal/13_semantic_engineering/04_semantic_interoperability.md`](../../04_formal/13_semantic_engineering/04_semantic_interoperability.md) |

---

## 十、AI 系统架构、MLOps/LLMOps 与安全对齐

| 来源 | URL | 说明 | 项目映射 |
|:---|:---|:---|:---|
| NIST AI Risk Management Framework | <https://www.nist.gov/itl/ai-risk-management-framework> | AI 风险管理框架 | [`concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md`](../../07_future/04_research_and_experimental/10_ai_safety_and_alignment.md) |
| ISO/IEC 42001:2023 | <https://www.iso.org/standard/81230.html> | AI 管理体系 | [`concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md`](../../07_future/04_research_and_experimental/10_ai_safety_and_alignment.md) |
| ISO/IEC 23053:2022 | <https://www.iso.org/standard/74438.html> | 使用 ML 的 AI 系统框架 | [`concept/07_future/04_research_and_experimental/09_mlops_and_llmops.md`](../../07_future/04_research_and_experimental/09_mlops_and_llmops.md) |
| MLCommons AI Safety | <https://mlcommons.org/ai-safety/> | AI 安全基准 | [`concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md`](../../07_future/04_research_and_experimental/10_ai_safety_and_alignment.md) |
| Google MLOps | <https://cloud.google.com/architecture/mlops-continuous-delivery-and-automation-pipelines-in-machine-learning> | MLOps 持续交付与自动化 | [`concept/07_future/04_research_and_experimental/09_mlops_and_llmops.md`](../../07_future/04_research_and_experimental/09_mlops_and_llmops.md) |
| Microsoft Responsible AI | <https://www.microsoft.com/en-us/ai/responsible-ai> | 负责任 AI 原则与工具 | [`concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md`](../../07_future/04_research_and_experimental/10_ai_safety_and_alignment.md) |
| Anthropic Responsible Scaling Policy | <https://www.anthropic.com/news/announcing-our-responsible-scaling-policy> | 负责任扩展政策 | [`concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md`](../../07_future/04_research_and_experimental/10_ai_safety_and_alignment.md) |
| OpenAI Preparedness Framework | <https://openai.com/preparedness/> | 前沿模型准备度框架 | [`concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md`](../../07_future/04_research_and_experimental/10_ai_safety_and_alignment.md) |
| OWASP LLM Top 10 | <https://genai.owasp.org/llm-top-10/> | LLM 应用安全风险 | [`concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md`](../../07_future/04_research_and_experimental/10_ai_safety_and_alignment.md) |
| OWASP ML Top 10 | <https://mltop10.info/> | ML 系统安全风险 | [`concept/07_future/04_research_and_experimental/10_ai_safety_and_alignment.md`](../../07_future/04_research_and_experimental/10_ai_safety_and_alignment.md) |
| MLSys Conference | <https://mlsys.org/> | ML 系统学术会议 | [`concept/07_future/04_research_and_experimental/08_llm_system_architecture.md`](../../07_future/04_research_and_experimental/08_llm_system_architecture.md) |
| MLflow | <https://mlflow.org/> | 开源 ML 生命周期平台 | [`concept/07_future/04_research_and_experimental/09_mlops_and_llmops.md`](../../07_future/04_research_and_experimental/09_mlops_and_llmops.md) |
| Kubeflow | <https://www.kubeflow.org/> | Kubernetes 上的 ML 工作流 | [`concept/07_future/04_research_and_experimental/09_mlops_and_llmops.md`](../../07_future/04_research_and_experimental/09_mlops_and_llmops.md) |
| LangChain / LangGraph | <https://python.langchain.com/docs/introduction/> | LLM 应用编排框架 | [`concept/07_future/04_research_and_experimental/08_llm_system_architecture.md`](../../07_future/04_research_and_experimental/08_llm_system_architecture.md) |
| Hugging Face | <https://huggingface.co/docs/transformers/> | Transformer 模型与推理生态 | [`concept/07_future/04_research_and_experimental/08_llm_system_architecture.md`](../../07_future/04_research_and_experimental/08_llm_system_architecture.md) |
| Weights & Biases | <https://wandb.ai/site> | 实验跟踪与模型观测 | [`concept/07_future/04_research_and_experimental/09_mlops_and_llmops.md`](../../07_future/04_research_and_experimental/09_mlops_and_llmops.md) |
| Ray / Anyscale | <https://docs.ray.io/> | 分布式 ML 与 LLM 服务 | [`concept/07_future/04_research_and_experimental/08_llm_system_architecture.md`](../../07_future/04_research_and_experimental/08_llm_system_architecture.md) |
| vLLM | <https://docs.vllm.ai/> | 高吞吐 LLM 推理引擎 | [`concept/07_future/04_research_and_experimental/08_llm_system_architecture.md`](../../07_future/04_research_and_experimental/08_llm_system_architecture.md) |

---

## 十一、国际课程与书籍

本节聚焦系统化的 Rust 学习课程与权威书籍，作为官方文档的补充。这些来源通常覆盖教学顺序、练习路径或领域实践，适合与 `concept/` 权威页形成“课程 → 深度”双向映射。

### 国际课程

| 来源 | URL | 说明 | 项目映射 |
|:---|:---|:---|:---|
| Comprehensive Rust (Google) | <https://google.github.io/comprehensive-rust/> | Google Android 团队维护的 4 天免费课程，覆盖基础到 Android/FFI 实践 | [`concept/00_meta/00_framework/comprehensive_rust_mapping.md`](../00_framework/comprehensive_rust_mapping.md) |
| The Little Book of Rust Books | <https://lborb.github.io/book/> | 官方与非官方 Rust 书籍索引 | 待建立映射（P2-1） |
| Rustlings | <https://github.com/rust-lang/rustlings> | 官方小练习集合 | [`exercises/`](../../../exercises/) |

### 权威书籍

| 来源 | URL | 说明 | 项目映射 |
|:---|:---|:---|:---|
| Rust Design Patterns | <https://rust-unofficial.github.io/patterns/> | 社区维护的设计模式书 | [`concept/06_ecosystem/03_design_patterns/01_patterns.md`](../../06_ecosystem/03_design_patterns/01_patterns.md)（P1-4 深化） |
| Rust Performance Book | <https://nnethercote.github.io/perf-book/> | 性能优化权威指南 | [`concept/06_ecosystem/10_performance/01_performance_optimization.md`](../../06_ecosystem/10_performance/01_performance_optimization.md)（P1-5 深化） |
| Zero To Production In Rust | <https://www.zero2prod.com/> | 生产级 Rust Web 应用实践 | [`concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md`](../../06_ecosystem/04_web_and_networking/03_web_frameworks.md) · [`concept/06_ecosystem/00_toolchain/03_devops_and_ci_cd.md`](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) |
| Rust for the Linux Kernel | <https://docs.kernel.org/rust/> | Linux 内核 Rust 开发官方文档 | [`concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md`](../../06_ecosystem/05_systems_and_embedded/03_embedded_systems.md) |
| Rust Cookbook | <https://rust-lang-nursery.github.io/rust-cookbook/> | 标准库与生态常用任务示例 | [`concept/01_foundation/05_collections/01_collections.md`](../../01_foundation/05_collections/01_collections.md) 等 L1-L2 权威页 |
| Rust for Rustaceans | <https://rustforrustaceans.com/> | 中高级 Rust 开发者进阶书 | [`concept/02_intermediate/00_traits/01_traits.md`](../../02_intermediate/00_traits/01_traits.md) · [`concept/03_advanced/02_unsafe/01_unsafe.md`](../../03_advanced/02_unsafe/01_unsafe.md) |
| Effective Rust | <https://www.lurklurk.org/effective-rust/> | 基于条目的 Rust 工程实践建议 | [`concept/02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md`](../../02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md) |
| The Little Book of Rust Books | <https://lborb.github.io/book/> | 官方与非官方 Rust 书籍索引 | 元索引（本文件） |

> **P2-1 说明**：本节来源从 3 扩展到 8；连同官方文档、形式化生态、工业生态、企业架构、系统工程、语义工程、AI 系统，项目国际权威来源索引总数从 60+ 扩展到 95+。

---

## 十二、使用建议

1. **新增 concept/ 文件时**：优先从此索引选取 2–4 个相关权威来源写入 frontmatter 的 `> **来源**: ...`。
2. **引用学术来源时**：给出论文标题、会议/期刊、DOI 或项目主页。
3. **引用生态库时**：使用 docs.rs 或官方文档的 stable 链接；避免链接到特定版本号（除非讨论版本差异）。
4. **引用企业架构 / 系统工程 / 语义工程 / AI 标准时**：优先链接到官方标准机构或已验证的公开摘要页；完整标准文本通常需购买，可在 concept/ 权威页中注明获取方式。
5. **定期校验**：运行 `scripts/audit_source_links.py` 与 `scripts/audit_remaining_source_placeholders.py`，修复失效或泛化链接。
6. **发现新权威来源**：先更新本索引，再在概念页中引用，保持单一权威来源清单。
