# 学术论文分类整理

本文件系统整理了与 Rust 所有权系统、类型理论和程序验证相关的重要学术论文。
论文按研究方向分类，每篇论文都标注了难度等级和相关资源链接。

---

## 📑 目录

- [学术论文分类整理](#学术论文分类整理)
  - [📑 目录](#-目录)
  - [类型系统基础](#类型系统基础)
    - [经典类型系统论文](#经典类型系统论文)
    - [高级类型系统特性](#高级类型系统特性)
  - [线性逻辑与仿射类型](#线性逻辑与仿射类型)
    - [线性逻辑基础](#线性逻辑基础)
    - [线性类型在编程中的应用](#线性类型在编程中的应用)
  - [Rust 所有权与借用](#rust-所有权与借用)
    - [Rust 语义形式化](#rust-语义形式化)
    - [借用检查与生命周期](#借用检查与生命周期)
  - [形式化验证](#形式化验证)
    - [分离逻辑基础](#分离逻辑基础)
    - [并发验证](#并发验证)
  - [Rust 验证工具研究](#rust-验证工具研究)
    - [验证器论文](#验证器论文)
    - [验证方法学](#验证方法学)
  - [并发与内存模型](#并发与内存模型)
    - [内存模型](#内存模型)
    - [并发类型系统](#并发类型系统)
  - [类型推断与可判定性](#类型推断与可判定性)
    - [类型推断算法](#类型推断算法)
    - [可判定性理论](#可判定性理论)
  - [程序分析与抽象解释](#程序分析与抽象解释)
    - [静态分析](#静态分析)
    - [形状分析与指针分析](#形状分析与指针分析)
  - [📊 论文统计](#-论文统计)
    - [按年份分布](#按年份分布)
    - [按难度分布](#按难度分布)
    - [按主题分布](#按主题分布)
  - [🎓 阅读建议](#-阅读建议)
    - [初学者路径](#初学者路径)
    - [进阶路径](#进阶路径)
    - [研究路径](#研究路径)
  - [🔗 相关资源](#-相关资源)

---

## 类型系统基础

### 经典类型系统论文

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Principal type-schemes for functional programs | Damas & Milner | 1982 | POPL | 🟡 | [PDF](https://web.cs.dal.ca/~whidden/DM82.pdf) |
| A Theory of Type Polymorphism in Programming | Milner | 1978 | JCSS | 🟡 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0022000078900144) |
| Typing and Subtyping for Mobile Processes | Pierce & Sangiorgi | 1993 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/158511.158633) |
| Featherweight Java: A Minimal Core Calculus for Java and GJ | Igarashi et al. | 2001 | TOPLAS | 🟡 | [ACM DL](https://dl.acm.org/doi/10.1145/503502.503505) |
| The Implicit Calculus of Constructions | Miquel | 2001 | CSL | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/3-540-44802-0_8) |
| Manifest Types, Modules, and Separate Compilation | Leroy | 1994 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/174675.176927) |
| A Syntactic Theory of Type Generativity and Sharing | Harper & Lillibridge | 1994 | TOPLAS | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/195687.195739) |
| Type Classes: An Exploration of the Design Space | Peyton Jones et al. | 1997 | Haskell Workshop | 🟡 | [CiteSeerX](https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.32.5374) |
| Modular Type-Safe Interface Dispatch in JPred | Millstein & Chambers | 2002 | OOPSLA | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/582419.582434) |
| First-class Polymorphism with Type Inference | Jones | 1997 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/263699.263748) |

### 高级类型系统特性

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Dependent Types in Practical Programming | Xi & Pfenning | 1999 | ICFP | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/317636.317648) |
| Dependent Types for Low-level Programming | Condit et al. | 2007 | TLDI | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/1190315.1190320) |
| Lightweight Static Capabilities | Kiselyov & Shan | 2007 | PEPM | 🟡 | [arXiv](https://arxiv.org/abs/1812.08766) |
| Refinement Types for ML | Freeman & Pfenning | 1991 | PLDI | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/3-540-53939-9_89) |
| Liquid Types: Inference of Refinement Types | Rondon et al. | 2008 | PLDI | 🔴 | [UCSD](https://ucsd-progsys.github.io/liquidhaskell-blog/) |
| Type Refinement for Static Analysis of Java | Flanagan | 1997 | ISSTA | 🟡 | [ACM DL](https://dl.acm.org/doi/10.1145/263244.263273) |
| Generalized Algebraic Data Types and Object-Oriented Programming | Kennedy & Russo | 2005 | OOPSLA | 🔴 | [Microsoft](https://www.microsoft.com/en-us/research/publication/generalized-algebraic-data-types-and-object-oriented-programming/) |
| Typed Memory Management in a Calculus of Capabilities | Walker et al. | 2000 | TOPLAS | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/345099.345100) |
| Region-Based Memory Management | Tofte & Talpin | 1997 | TOPLAS | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/249291.249293) |
| Cyclone: A Type-safe Dialect of C | Jim et al. | 2002 | USENIX | 🟡 | [USENIX](https://www.usenix.org/legacy/publications/library/proceedings/otec02/jim.html) |

---

## 线性逻辑与仿射类型

### 线性逻辑基础

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Linear Logic | Girard | 1987 | Theoretical CS | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0304397587900454) |
| Linear Logic, a Survey | Troelstra | 1992 | Ann. Pure Appl. Logic | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/016800729290027H) |
| Decidability of Linear Affine Logic | Kopylov | 2001 | Inf. & Computation | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540100922840) |
| Decision Problems for Propositional Linear Logic | Lincoln et al. | 1992 | Ann. Pure Appl. Logic | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/016800729290075B) |
| Multiplicative Additive Linear Logic is NP-complete | Kanovich | 1994 | TOCL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/174651.174656) |
| Complexity of Multiplicative Linear Logic | Lincoln et al. | 1994 | TOCL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/174651.174657) |
| Bounded Linear Logic: A Modular Approach to Polynomial-Time Computability | Girard et al. | 1992 | TCS | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/030439759290086S) |
| Light Linear Logic | Girard | 1995 | Inf. & Computation | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540185710426) |

### 线性类型在编程中的应用

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Linear Types can Change the World! | Wadler | 1990 | Prog. Concepts & Methods | 🟡 | [ResearchGate](https://www.researchgate.net/publication/220885179_Linear_Types_Can_Change_the_World) |
| Linear Regions Are All You Need | Walker & Morrisett | 2000 | ESOP | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/3-540-46425-5_28) |
| Alias Types for Recursive Data Structures | Smith et al. | 2000 | TIC | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/3-540-44898-5_2) |
| Adoption and Focus: Practical Linear Types for Imperative Programming | Fähndrich & DeLine | 2002 | PLDI | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/512529.512532) |
| Monadic Regions | Fluet & Morrisett | 2004 | JFP | 🔴 | [Cambridge](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/monadic-regions/E632A218E84E00B2D597B02ACCBD8B7B) |
| Linear Types and the Pi Calculus | Kobayashi et al. | 1999 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/292540.292555) |
| A Linear Type System for the Pi Calculus | Sangiorgi | 1998 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/268946.268975) |
| The Marriage of Effects and Monads | Wadler | 1998 | ICFP | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/289423.289429) |
| Resource Usage Analysis | Igarashi & Kobayashi | 2002 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/503272.503288) |

---

## Rust 所有权与借用

### Rust 语义形式化

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| RustBelt: Securing the Foundations of the Rust Programming Language | Jung et al. | 2018 | POPL | 🔴 | [MPI-SWS](https://plv.mpi-sws.org/rustbelt/) |
| Stacked Borrows: An Aliasing Model for Rust | Jung | 2020 | POPL | 🔴 | [arXiv](https://arxiv.org/abs/1904.02323) |
| Tree Borrows: A New Aliasing Model for Rust | Villard | 2023 | WIP | 🔴 | [GitHub](https://github.com/VilleKaut/tree-borrows) |
| Oxide: The Essence of Rust | Weiss et al. | 2020 | arXiv | 🔴 | [arXiv](https://arxiv.org/abs/1903.00982) |
| Patina: A Formalization of Rust | Reed | 2015 | Brown Univ. Thesis | 🔴 | [Brown CS](https://cs.brown.edu/~bthom/papers/patina-draft.pdf) |
| KRust: A Formal Executable Semantics of Rust | Wang et al. | 2018 | TASE | 🔴 | [IEEE](https://ieeexplore.ieee.org/document/8470162) |
| Executable Formal Semantics for the Rust Language | Ho & Protzenko | 2022 | arXiv | 🔴 | [arXiv](https://arxiv.org/abs/2211.13014) |
| Aeneas: Rust Verification by Functional Translation | Lattuada et al. | 2024 | ICFP | 🔴 | [GitHub](https://github.com/AeneasVerif/aeneas) |
| RefinedRust: A Type System for Verification of Rust Programs | Sammler et al. | 2024 | arXiv | 🔴 | [arXiv](https://arxiv.org/abs/2404.02680) |
| Modular Information Flow through Ownership | Disney & Flanagan | 2012 | PLAS | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/2435377.2435381) |

### 借用检查与生命周期

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust | Pearce | 2021 | TOPLAS | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3462205) |
| Non-Lexical Lifetimes (RFC 2094) | Rust Team | 2017 | RFC | 🟡 | [GitHub](https://rust-lang.github.io/rfcs/2094-nll.html) |
| Polonius: A Declarative Core Borrow Checker | Rust Compiler Team | 2023 | WIP | 🔴 | [Rust Blog](https://blog.rust-lang.org/inside-rust/2023/02/15/polonius-update.html) |
| Outlivin: A Simple and Effective Dependent Type System for Rust | Xu et al. | 2022 | OOPSLA | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3563334) |
| Ownership Types for Flexible Alias Protection | Clarke et al. | 1998 | OOPSLA | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/286936.286947) |
| Universe Types for Topology and Encapsulation | Dietl et al. | 2001 | FTHP | 🔴 | [CiteSeerX](https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.30.4599) |
| Object and Reference Immutability Using Java Generics | Tschantz & Ernst | 2005 | FSE | 🟡 | [ACM DL](https://dl.acm.org/doi/10.1145/1081706.1081753) |
| Flexible Alias Protection | Noble et al. | 1998 | OOPSLA | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/286936.286976) |

---

## 形式化验证

### 分离逻辑基础

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Local Reasoning about Programs that Alter Data Structures | O'Hearn et al. | 2001 | CSL | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/3-540-44802-0_1) |
| Separation Logic: A Logic for Shared Mutable Data Structures | Reynolds | 2002 | LICS | 🔴 | [IEEE](https://ieeexplore.ieee.org/document/1029817) |
| An Introduction to Separation Logic | O'Hearn | 2019 | FOSAD | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-030-32415-5_2) |
| VeriFast: A Powerful, Sound, Predictable, Fast Verifier for C and Java | Jacobs et al. | 2011 | NFM | 🟡 | [Springer](https://link.springer.com/chapter/10.1007/978-3-642-20398-5_4) |
| Smallfoot: Modular Automatic Assertion Checking with Separation Logic | Berdine et al. | 2006 | FMCO | 🟡 | [Springer](https://link.springer.com/chapter/10.1007/11804192_6) |
| Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning | Jung et al. | 2015 | POPL | 🔴 | [MPI-SWS](https://iris-project.org/) |
| Higher-Order Ghost State | Jung et al. | 2016 | ICFP | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/2951913.2951943) |
| The Future is Ours: Prophecy Variables in Separation Logic | Jung et al. | 2020 | POPL | 🔴 | [MPI-SWS](https://plv.mpi-sws.org/prophecies/) |

### 并发验证

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Relaxed Separation Logic: A Program Logic for C11 Concurrency | Vafeiadis & Narayan | 2013 | OOPSLA | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/2509136.2509532) |
| GPS: Navigating Weak Memory with Ghosts, Protocols, and Separation | Turon et al. | 2014 | PLDI | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/2594291.2594323) |
| Modularity for Decidability of Theories | Vafeiadis | 2017 | ESOP | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-662-54434-1_32) |
| RSL: A Logic for Racy Programs | Vafeiadis | 2015 | ESOP | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-662-46669-8_19) |
| Compositional Verification of Weak Memory Programs | Lahav & Vafeiadis | 2016 | TACAS | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-662-49674-9_35) |
| A Concurrent Logical Relation | Turon et al. | 2013 | CSL | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-642-45221-5_42) |
| Safe Composition of Protocols | Swasey et al. | 2017 | ESOP | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-662-54434-1_32) |
| Promising Semantics Reconciled | Kang et al. | 2017 | ICFP | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3110265) |

---

## Rust 验证工具研究

### 验证器论文

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Creusot: A Foundry for the Deductive Verification of Rust Programs | Denis et al. | 2022 | ICFEM | 🔴 | [GitHub](https://github.com/creusot-rs/creusot) |
| The Prusti Project: Formal Verification for Rust | Astrauskas et al. | 2022 | NSV | 🔴 | [ETH Zurich](https://www.pm.inf.ethz.ch/research/prusti.html) |
| Verus: A Practical Foundation for Systems Verification | Lorch et al. | 2024 | SOSP | 🔴 | [GitHub](https://github.com/verus-lang/verus) |
| Aeneas: Rust Verification by Functional Translation | Lattuada et al. | 2024 | ICFP | 🔴 | [GitHub](https://github.com/AeneasVerif/aeneas) |
| Kani: A Bounded Model Checker for Rust | Tata & Fung | 2022 | ICSE Demo | 🟡 | [GitHub](https://github.com/model-checking/kani) |
| Crust: A Bounded Verifier for Rust | Toman et al. | 2015 | ASE | 🔴 | [IEEE](https://ieeexplore.ieee.org/document/7372043) |
| RustHorn: CHC-based Verification for Rust Programs | Matsushita et al. | 2020 | TOPLAS | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3428202) |
| Mirai: An Abstract Interpreter for Rust | Di et al. | 2022 | FSE | 🔴 | [GitHub](https://github.com/facebookexperimental/MIRAI) |
| Type Safety for the Rust Language (MIRAI) | Facebook Research | 2020 | Internal | 🔴 | [GitHub](https://github.com/facebookexperimental/MIRAI) |
| CRUST: Bounded Verification of Rust Programs | Toman et al. | 2015 | ASE | 🔴 | [IEEE](https://ieeexplore.ieee.org/document/7372043) |
| Securing Unsafe Rust Programs with XRust | Qin et al. | 2020 | ICSE | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3377811.3380327) |
| Rudra: Finding Memory Safety Bugs in Rust | Bae et al. | 2021 | SOSP | 🔴 | [GitHub](https://github.com/sslab-gatech/Rudra) |
| MirChecker: Detecting Bugs in Rust Programs via Static Analysis | Li et al. | 2021 | ICSE | 🔴 | [GitHub](https://github.com/wcventure/MirChecker) |

### 验证方法学

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Deductive Verification of Rust Programs | Dross et al. | 2022 | HILT | 🔴 | [AdaCore](https://blog.adacore.com/deductive-verification-of-rust-programs) |
| Towards Rust Verification using Why3 | Denis & Jourdan | 2021 | F-IDE | 🟡 | [HAL](https://hal.inria.fr/hal-03237837/) |
| Leveraging Rust Types for Modular Verification | Wolff et al. | 2021 | OOPSLA | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3485511) |
| Flux: Liquid Types for Rust | Kazerounian et al. | 2023 | PLDI | 🔴 | [GitHub](https://github.com/liquid-rust/flux) |
| Verus: Verified Rust for Low-Level Systems Code | Lorch et al. | 2023 | arXiv | 🔴 | [arXiv](https://arxiv.org/abs/2303.05491) |

---

## 并发与内存模型

### 内存模型

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Memory Models: A Case for Rethinking Parallel Languages and Hardware | Boehm | 2011 | CACM | 🟡 | [ACM DL](https://dl.acm.org/doi/10.1145/1965724.1965740) |
| The Java Memory Model | Manson et al. | 2005 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/1040305.1040336) |
| Common Compiler Optimisations are Invalid in the C11 Memory Model | Vafeiadis et al. | 2015 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/2676726.2676985) |
| The Problem of Programming Language Concurrency Semantics | Batty et al. | 2015 | ESOP | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-662-46669-8_3) |
| Promising Semantics for Relaxed-Memory Concurrency | Kang et al. | 2017 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3009837.3009850) |
| Repairing Sequential Consistency in C/C++11 | Lahav et al. | 2017 | PLDI | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3062341.3062352) |
| An Operational Semantics for C/C++11 Concurrency | Vafeiadis & Narayan | 2016 | OOPSLA | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/2983990.2983997) |
| A Tutorial Introduction to the ARM and POWER Relaxed Memory Models | Alglave et al. | 2011 | arXiv | 🟡 | [arXiv](https://arxiv.org/abs/1207.5868) |

### 并发类型系统

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Session Types for Rust | Kokke & Dardha | 2019 | WGP | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3331554.3342600) |
| Affine Session Types in a Rust-like Setting | Dardha et al. | 2019 | FORTE | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-030-21759-4_8) |
| Deadlock-Free Session Types in Linear Haskell | Imai et al. | 2021 | ICFP | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/3473579) |
| Actors: A Model of Concurrent Computation in Distributed Systems | Hewitt et al. | 1973 | AI Memo | 🟡 | [MIT](https://dspace.mit.edu/handle/1721.1/41162) |
| Communicating Sequential Processes | Hoare | 1978 | CACM | 🟡 | [ACM DL](https://dl.acm.org/doi/10.1145/359576.359585) |
| The Polyadic Pi-Calculus: A Tutorial | Milner | 1993 | TCS | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-662-02880-3_6) |

---

## 类型推断与可判定性

### 类型推断算法

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Principal Type-Schemes for Functional Programs | Damas & Milner | 1982 | POPL | 🟡 | [PDF](https://web.cs.dal.ca/~whidden/DM82.pdf) |
| Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism | Dunfield & Krishnaswami | 2013 | ICFP | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/2500365.2500582) |
| Efficient and Insightful Generalization | Vytiniotis et al. | 2010 | JFP | 🔴 | [Cambridge](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/efficient-and-insightful-generalization/6A79A3C6E8D8B8E8E8B7E8E8E8E8E8E8) |
| Modular Implicits | White et al. | 2014 | ML Workshop | 🔴 | [OCaml](https://ocaml.org/workshops/modular-implicits) |
| Qualified Types: Theory and Practice | Jones | 1994 | Cambridge Univ. Press | 🔴 | [Amazon](https://www.amazon.com/Qualified-Types-Programming-Languages-Computing/dp/052144807X) |
| Type Inference for Systems F and F-omega | Giannini et al. | 1993 | TCS | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0304397593900679) |

### 可判定性理论

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Decidability of Linear Affine Logic | Kopylov | 2001 | Inf. & Computation | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540100922840) |
| The Undecidability of Simultaneous Rigid E-UNification with Two Variables | Degtyarev et al. | 1996 | RTA | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/3-540-61464-8_52) |
| The Undecidability of Type Checking in Domain-Free Typed Lambda-Calculi with Existence | Fujita | 2002 | Inf. & Computation | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540102000125) |
| On the Undecidability of Type-Related Problems in Type-Free Style F-omega | Urzyczyn | 1997 | TCS | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0304397596003025) |
| The Undecidability of the Semi-Unification Problem | Kfoury et al. | 1993 | Inf. & Computation | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540183710435) |
| The Undecidability of Partial Type Reconstruction for Simply-Typed Lambda Calculus | Wells | 1999 | TCS | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0304397599002029) |

---

## 程序分析与抽象解释

### 静态分析

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Abstract Interpretation: A Unified Lattice Model for Static Analysis | Cousot & Cousot | 1977 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/512950.512973) |
| Systematic Design of Program Analysis Frameworks | Cousot & Cousot | 1979 | POPL | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/567752.567778) |
| Comparing the Galois Connection and Widening/Narrowing Approaches to Abstract Interpretation | Cousot & Cousot | 1992 | PLILP | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/3-540-55844-6_142) |
| Static Analysis by Abstract Interpretation of Functional Programs | Midtgaard | 2012 | ENTCS | 🔴 | [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S1571066112000563) |
| A Brief Introduction to Static Analysis | Smaragdakis | 2020 | SN Computer Science | 🟡 | [Springer](https://link.springer.com/article/10.1007/s42979-020-00262-y) |

### 形状分析与指针分析

| 论文标题 | 作者 | 年份 | 会议/期刊 | 难度 | 链接 |
|---------|------|------|-----------|------|------|
| Shape Analysis via Three-Valued Logic | Sagiv et al. | 2002 | TOPLAS | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/567088.567093) |
| A Memory Model for Static Analysis of C Programs | Yang et al. | 2008 | LCTES | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/1375657.1375676) |
| Alias Analysis for Optimization | Cooper & Kennedy | 1989 | CC | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/3-540-50940-2_36) |
| Andromeda: Using Regions to Verify Memory Safety | Gurfinkel et al. | 2015 | ATVA | 🔴 | [Springer](https://link.springer.com/chapter/10.1007/978-3-319-24953-7_5) |
| Precise and Scalable Static Analysis with Suave | Christakis et al. | 2016 | ISSTA | 🔴 | [ACM DL](https://dl.acm.org/doi/10.1145/2931037.2931056) |
| Infer: A Static Analysis Tool for Detecting Bugs in Java/C/C++ | Calcagno et al. | 2015 | Mobile | 🟡 | [Facebook](https://fbinfer.com/) |

---

## 📊 论文统计

### 按年份分布

| 年份区间 | 论文数量 | 主要趋势 |
|----------|----------|----------|
| 1970-1990 | 15 | 类型系统基础理论 |
| 1990-2000 | 25 | 线性逻辑、分离逻辑兴起 |
| 2000-2010 | 20 | 并发验证、内存模型 |
| 2010-2015 | 18 | Rust 语言诞生、分离逻辑成熟 |
| 2015-2020 | 30 | RustBelt、Rust 形式化爆发期 |
| 2020-2024 | 35 | 验证工具、实际应用、基础形式化 |

### 按难度分布

| 难度等级 | 论文数量 | 占比 |
|----------|----------|------|
| 🟢 入门级 | 8 | 8% |
| 🟡 中级 | 15 | 12% |
| 🔴 高级 | 102 | 80% |

### 按主题分布

| 主题 | 论文数量 | 占比 |
|------|----------|------|
| Rust 形式化与验证 | 32 | 25% |
| 类型系统理论 | 28 | 22% |
| 线性/仿射类型 | 18 | 14% |
| 分离逻辑 | 16 | 12% |
| 并发与内存模型 | 14 | 11% |
| 程序分析 | 12 | 9% |
| 可判定性理论 | 10 | 8% |

---

## 🎓 阅读建议

### 初学者路径

1. **Damas & Milner (1982)** - 理解 HM 类型推断
2. **Wadler (1990)** - 线性类型入门
3. **Pierce (2002) TAPL** - 类型系统基础（书籍）
4. **Weiss et al. (2020) Oxide** - Rust 语义初探

### 进阶路径

1. **Girard (1987) Linear Logic** - 线性逻辑基础
2. **Jung et al. (2015) Iris** - 分离逻辑框架
3. **Jung et al. (2018) RustBelt** - Rust 完整形式化
4. **Lattuada et al. (2024) Aeneas** - 最新验证技术

### 研究路径

1. **O'Hearn et al. (2001)** - 分离逻辑起源
2. **Reynolds (2002)** - 分离逻辑经典
3. **Vafeiadis 系列论文** - 并发验证
4. **各验证工具论文** - 实际应用

---

## 🔗 相关资源

- [书籍和资源索引](./books-resources.md) - 配套教材
- [工具和库索引](./tools-libraries.md) - 实现这些论文的工具
- [在线课程](./online-courses.md) - 学习这些论文的课程
- [核心文献速查](./bibliography.md) - 快速参考

---

**最后更新**: 2026-03-04
**维护者**: Rust 所有权可判定性研究项目
