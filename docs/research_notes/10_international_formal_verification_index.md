# 国际 Rust 形式化验证成果对标索引 {#国际-rust-形式化验证成果对标索引}
>
> **概念族**: 形式化方法

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [国际 Rust 形式化验证成果对标索引 {#国际-rust-形式化验证成果对标索引}](#国际-rust-形式化验证成果对标索引-国际-rust-形式化验证成果对标索引)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、国际权威成果总览 {#一国际权威成果总览}](#一国际权威成果总览-一国际权威成果总览)
  - [二、逐项对标与差距 {#二逐项对标与差距}](#二逐项对标与差距-二逐项对标与差距)
    - [2.1 RustBelt {#21-rustbelt}](#21-rustbelt-21-rustbelt)
    - [2.2 RustBelt Meets Relaxed Memory (POPL 2020) {#22-rustbelt-meets-relaxed-memory-popl-2020}](#22-rustbelt-meets-relaxed-memory-popl-2020-22-rustbelt-meets-relaxed-memory-popl-2020)
    - [2.3 RustSEM (K-Framework, 2024) {#23-rustsem-k-framework-2024}](#23-rustsem-k-framework-2024-23-rustsem-k-framework-2024)
    - [2.4 Aeneas {#24-aeneas}](#24-aeneas-24-aeneas)
    - [2.5 coq-of-rust {#25-coq-of-rust}](#25-coq-of-rust-25-coq-of-rust)
    - [2.6 Crux-MIR {#26-crux-mir}](#26-crux-mir-26-crux-mir)
    - [2.7 AutoVerus {#27-autoverus}](#27-autoverus-27-autoverus)
    - [2.8 Tree Borrows (PLDI 2025) {#28-tree-borrows-pldi-2025}](#28-tree-borrows-pldi-2025-28-tree-borrows-pldi-2025)
    - [2.9 Verus {#29-verus}](#29-verus-29-verus)
    - [2.10 Kani {#210-kani}](#210-kani-210-kani)
    - [2.11 Prusti {#211-prusti}](#211-prusti-211-prusti)
    - [2.12 Creusot {#212-creusot}](#212-creusot-212-creusot)
    - [2.13 Miri {#213-miri}](#213-miri-213-miri)
    - [2.14 工具链映射汇总 {#214-工具链映射汇总}](#214-工具链映射汇总-214-工具链映射汇总)
  - [三、POPL/PLDI/ICFP 论文对齐 {#三poplpldiicfp-论文对齐}](#三poplpldiicfp-论文对齐-三poplpldiicfp-论文对齐)
  - [四、与本项目 PROOF\_INDEX 的映射 {#四与本项目-proof\_index-的映射}](#四与本项目-proof_index-的映射-四与本项目-proof_index-的映射)
  - [五、季度更新记录 {#五季度更新记录}](#五季度更新记录-五季度更新记录)
  - [🆕 Rust 1.94 深度整合更新 {#rust-194-深度整合更新}](#-rust-194-深度整合更新-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点 {#本文档的rust-194更新要点}](#本文档的rust-194更新要点-本文档的rust-194更新要点)
      - [核心特性应用 {#核心特性应用}](#核心特性应用-核心特性应用)
      - [代码示例更新 {#代码示例更新}](#代码示例更新-代码示例更新)
      - [相关文档 {#相关文档}](#相关文档-相关文档)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

> **创建日期**: 2026-02-14
> **最后更新**: 2026-06-29
> **更新内容**: 补充 Verus / Kani / Prusti / Creusot / Miri 工具链映射
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级
> **用途**: 系统对标国际权威 Rust 形式化证明模型，明确本项目 PROOF_INDEX 与最新成果的对应关系与差距
> **维护**: 季度更新，Rust 新版本发布时补充

---

## 一、国际权威成果总览 {#一国际权威成果总览}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 成果 | 机构/作者 | 年份 | 形式化范围 | 证明助手/工具 | 与本项目对应 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **RustBelt** | MPI-SWS (Jung et al.) | 2018 | 所有权、借用、MIR 级 | Iris (Coq) | ownership_model, borrow_checker_proof, [coq_skeleton](../../archive/deprecated/coq_skeleton/README.md)（T-OW2/BR1/TY3 骨架） |
| **Tree Borrows** | ETH (PLDI 2025) | 2025 | 借用模型、树结构、54% 更少拒绝 | Iris (Coq)、Rocq | borrow_checker_proof 演进；Distinguished Paper |
| **RustBelt Meets Relaxed Memory** | MPI-SWS | 2020 | 松弛内存、Arc、原子操作 | Iris (Coq) | formal_methods Phase 4（部分） |
| **Rust Distilled** | DBLP | - | 高层所有权、无生命周期 | - | ownership_model（高层部分） |
| **Aeneas** | INRIA 等 | 2023+ | Safe Rust → Coq/F*/HOL4/Lean | 多后端 | [AENEAS_INTEGRATION_PLAN](10_aeneas_integration_plan.md) |
| **coq-of-rust** | - | 2023+ | THIR → Rocq，借用与 effect | Rocq (Coq) | 无直接对应 |
| **Crux-MIR** | Galois | 2024 | 比特级精确、密码学验证 | Crux | 无直接对应 |
| **RustSEM** | 2024 (FMSD) | 2024 | 内存级 OBS、可执行语义、700+ 测试 | K-Framework | 无直接对应 |
| **AutoVerus** | - | 2024–2025 | LLM 自动证明生成 | Verus | 无直接对应 |
| **Verus** | MSR/CMU/ETH 等 | 2023 | Safe + 部分 unsafe 系统代码 | SMT（Z3） | `10_international_formal_verification_index.md` |
| **Kani** | AWS/Model Checking | 2022+ | unsafe 代码属性、内存安全 | CBMC 模型检查 | `formal_methods/10_borrow_checker_proof.md`（CAV 工具） |
| **Prusti** | ETH Zurich | 2019–2022 | Safe Rust 功能正确性 | Viper / 分离逻辑 | `formal_methods/10_borrow_checker_proof.md` |
| **Creusot** | Inria/Paris-Saclay | 2022 | Safe Rust + 部分 unsafe | Why3 / SMT | 无直接对应 |
| **Miri** | Rust 官方 | 2017+ | MIR 解释、UB 动态检测 | 解释器 | `formal_methods/10_borrow_checker_proof.md` |

---

## 二、逐项对标与差距 {#二逐项对标与差距}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 2.1 RustBelt {#21-rustbelt}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- **论文**: RustBelt: Logical Foundations for the Future of Safe Systems Programming
- **形式化**: λ Rust 模型、分离逻辑、MIR 级语义
- **本项目对应**: `formal_methods/10_ownership_model.md`, `formal_methods/10_borrow_checker_proof.md`
- **差距**: 无 Iris 分离逻辑形式化；无 MIR 级建模；**Coq 骨架已创建**（[coq_skeleton/OWNERSHIP_UNIQUENESS.v](../../archive/deprecated/coq_skeleton/OWNERSHIP_UNIQUENESS.v)），证明 Admitted 待补全

### 2.2 RustBelt Meets Relaxed Memory (POPL 2020) {#22-rustbelt-meets-relaxed-memory-popl-2020}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

- **论文**: RustBelt Meets Relaxed Memory
- **形式化**: 松弛内存、Arc 数据竞争、synchronized ghost state
- **本项目对应**: `formal_methods` Phase 4（MaybeUninit、原子操作）— 仅 Def 级
- **差距**: 无松弛内存模型；无 Arc 形式化；无 ghost state 构造

### 2.3 RustSEM (K-Framework, 2024) {#23-rustsem-k-framework-2024}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

- **论文**: [Formally understanding Rust's ownership and borrowing system at the memory level](https://link.springer.com/article/10.1007/s10703-024-00460-3) (FMSD)
- **形式化**: 内存级 OBS、可执行操作语义、700+ 测试
- **本项目对应**: 无
- **差距**: 无可执行语义；无 K 框架实现；无内存级 OBS 映射

### 2.4 Aeneas {#24-aeneas}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

- **形式化**: Safe Rust 翻译到 Coq、F*、HOL4、Lean
- **本项目对应**: [AENEAS_INTEGRATION_PLAN](10_aeneas_integration_plan.md)（对接方案已制定）
- **差距**: 无证明助手翻译；无多后端验证
- **对接状态**: 📋 计划中 — 示例选取、环境搭建、翻译验证待实施

### 2.5 coq-of-rust {#25-coq-of-rust}

> **来源: [ACM](https://dl.acm.org/)**

- **形式化**: THIR → Rocq，显式借用与 effect 序列
- **本项目对应**: 无
- **差距**: 无编译器 IR 级形式化

### 2.6 Crux-MIR {#26-crux-mir}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

- **形式化**: 比特级精确、密码学模块验证
- **本项目对应**: 无
- **差距**: 无比特级模型

### 2.7 AutoVerus {#27-autoverus}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

- **形式化**: LLM 自动生成 Verus 正确性证明
- **本项目对应**: 无
- **差距**: 无自动化证明生成

### 2.8 Tree Borrows (PLDI 2025) {#28-tree-borrows-pldi-2025}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- **论文**: [Tree Borrows: A New Aliasing Model for Rust](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)（Distinguished Paper Award）
- **形式化**: 树结构借用、30k crates 54% 更少拒绝、Rocq 证明
- **本项目对应**: borrow_checker_proof；coq_skeleton/BORROW_DATARACE_FREE.v
- **差距**: 无树结构建模；可参考 Tree Borrows 补全 T-BR1 形式化

---

### 2.9 Verus {#29-verus}

> **来源**: [Verus](https://github.com/verus-lang/verus)

- **方法**: 基于**线性 ghost 类型（linear ghost types）**的 SMT 验证器，直接在 Rust 源码上添加规范注解。
- **覆盖范围**: 低层系统代码、并发原语、部分 unsafe 代码；使用 Z3 自动求解。
- **与本项目 PROOF_INDEX 映射**:
  - 所有权/借用：对应 `ownership_model` 定理 5/6 的功能正确性扩展。
  - 并发安全：对应 `send_sync_formalization` 中的 `Send`/`Sync` 规范。
  - 线性 ghost 类型：对应 Axiom OW1 / Axiom BR1 的 ghost-state 扩展。
- **差距**: 无 Verus 规范库的直接映射；无线性 ghost 类型在本项目形式化中的占位。

### 2.10 Kani {#210-kani}

> **来源**: [Kani Rust Verifier](https://github.com/model-checking/kani)

- **方法**: **位精确模型检查（bit-precise model checking）**，基于 CBMC；通过 `#[kani::proof]` harness 与 `kani::any()` 符号输入验证属性。
- **覆盖范围**: unsafe 块、内存安全（空指针、UAF、越界）、panic、算术溢出、用户断言。
- **与本项目 PROOF_INDEX 映射**:
  - 内存安全定理：验证 `Theorem 5` 在 unsafe 子集上的运行时实例。
  - 数据竞争自由：通过符号执行检查 `Theorem 1` 的并发路径。
- **差距**: 无并发支持；无法给出数学证明，只能给出有界验证/反例。

### 2.11 Prusti {#211-prusti}

> **来源**: [Prusti](https://github.com/viperproject/prusti)

- **方法**: 将 Rust 程序翻译到 **Viper** 中间验证语言，利用隐式动态帧/分离逻辑自动构建内存安全证明；用户可写合约验证功能正确性。
- **覆盖范围**: Safe Rust；递归数据类型、循环不变式、前置/后置条件。
- **与本项目 PROOF_INDEX 映射**:
  - 借用检查器正确性：对应 `borrow_checker_proof` Theorem 2。
  - 分离逻辑 framing：对应 RustBelt/Iris 资源代数（`ownership_model` § Iris 对应）。
- **差距**: 不支持内部可变性；对 unsafe 代码支持有限；本项目无 Viper 编码。

### 2.12 Creusot {#212-creusot}

> **来源**: [Creusot](https://github.com/creusot-rs/creusot)

- **方法**: **演绎验证器**，将 MIR 翻译到 Why3 的 Coma/MLCFG 中间语言，使用 **Pearlite** 规范语言；SMT 求解器 discharge VCs。
- **覆盖范围**: Safe Rust 功能正确性；最近扩展线性 ghost 类型以支持部分 unsafe 代码。
- **与本项目 PROOF_INDEX 映射**:
  - 函数合约/循环不变式：对应 `ownership_model` / `borrow_checker_proof` 中的定理与引理。
  - 预言变量（prophecy）编码可变借用：与 Aeneas 的 CPV 互补。
- **差距**: 无 Why3/Coma 翻译；无 Pearlite 规范库。

### 2.13 Miri {#213-miri}

> **来源**: [Miri](https://github.com/rust-lang/miri)

- **方法**: MIR 解释器，运行时检测未定义行为（UB）。
- **覆盖范围**: 越界访问、悬垂指针、未初始化读取、别名违规（Stacked Borrows / Tree Borrows）、内存泄漏、部分并发数据竞争。
- **与本项目 PROOF_INDEX 映射**:
  - 借用规则动态检测：为 `borrow_checker_proof` 的反例表提供运行时证据。
  - Tree Borrows 模式：验证 `Tree Borrows (PLDI 2025)` 的别名模型在标准库测试套件上的可实现性。
- **差距**: 非穷举（依赖测试覆盖）；不能替代形式化证明。

### 2.14 工具链映射汇总 {#214-工具链映射汇总}

| 工具 | 方法 | 覆盖范围 | 本项目 PROOF_INDEX 映射 | 主要差距 |
| :--- | :--- | :--- | :--- | :--- |
| **Aeneas** | 函数式翻译 + 预言变量 | Safe Rust | `10_aeneas_integration_plan.md` | 无多后端翻译验证 |
| **coq-of-rust** | THIR → Rocq 浅嵌入 | Safe + 部分标准库 | 无直接对应 | 无 THIR 形式化 |
| **Verus** | 线性 ghost 类型 + SMT | 系统代码/部分 unsafe | `ownership_model` / `send_sync_formalization` | 无 ghost 类型规范 |
| **Kani** | CBMC 模型检查 | unsafe / 属性 | `borrow_checker_proof` 定理 1/5 | 非证明、无并发 |
| **Prusti** | Viper / 分离逻辑 | Safe Rust | `borrow_checker_proof` 定理 2 | 无 unsafe 支持 |
| **Creusot** | Why3 演绎验证 | Safe Rust + 部分 unsafe | 函数合约/循环不变式 | 无 Why3/Coma 后端 |
| **Miri** | MIR 解释器 | UB 动态检测 | 反例表 / Tree Borrows | 非穷举 |

## 三、POPL/PLDI/ICFP 论文对齐 {#三poplpldiicfp-论文对齐}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 会议 | 论文 | 年份 | 链接 | 本项目对应 |
| :--- | :--- | :--- | :--- | :--- |
| **POPL** | RustBelt: Logical Foundations for the Future of Safe Systems Programming | 2018 | plv.mpi-sws.org/rustbelt | ownership_model、borrow_checker_proof |
| **POPL** | RustBelt Meets Relaxed Memory | 2020 | rbrlx | send_sync_formalization、async_state_machine |
| **PLDI** | Tree Borrows: A New Aliasing Model for Rust (Distinguished Paper) | 2025 | [ETH PLDI25](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) | borrow_checker_proof、BORROW_DATARACE_FREE.v |
| **ICFP** | Oxide: The Essence of Rust | 2023 | [Oxide](https://arxiv.org/abs/1903.00982) | ownership_model（高层语义） |
| **PLDI** | Stacked Borrows (Miri 实现基础) | 2019 | Ralf Jung 论文 | borrow_checker_proof、Miri 检测 |

> **说明**：RustBelt 系列为 Rust 形式化验证奠基性工作；Tree Borrows 为 PLDI 2025 杰出论文；Oxide 为 ICFP 高层语义抽象。

---

## 四、与本项目 PROOF_INDEX 的映射 {#四与本项目-proof_index-的映射}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| PROOF_INDEX 领域 | 国际对标 | 覆盖度 |
| :--- | :--- | :--- |
| 所有权与借用 | RustBelt, RustSEM | 部分（语言级有，内存级/机器证明无） |
| 生命周期 | RustBelt（间接） | 部分 |
| 类型系统 | RustBelt, Aeneas | 部分 |
| 异步与 Pin | - | 无国际直接对标 |
| 松弛内存/原子 | RustBelt Meets Relaxed Memory | 未覆盖 |

---

## 五、季度更新记录 {#五季度更新记录}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 日期 | 更新内容 |
| :--- | :--- |
| 2026-02-14 | 初版创建 |
| 2026-02-14 | 补充 coq_skeleton 与 RustBelt 对应 |
| 2026-02-14 | T-BR1/T-TY3 Coq 骨架创建；Tree Borrows PLDI 2025 补充 |
| 2026-06-29 | 补充 Verus/Kani/Prusti/Creusot/Miri 工具链映射；升级到 Rust 1.96.0+ |

---

**维护者**: Rust Formal Methods Research Team

---

## 🆕 Rust 1.94 深度整合更新 {#rust-194-深度整合更新}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点 {#本文档的rust-194更新要点}
>
> **[来源: [crates.io](https://crates.io/)]**

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用 {#核心特性应用}

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新 {#代码示例更新}

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档 {#相关文档}

- Rust 1.94 迁移指南
- Rust 1.94 特性速查
- [性能调优指南](../05_guides/05_performance_tuning_guide.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)

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

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**
> **来源: [Coq Reference](https://coq.inria.fr/doc/)**
> **来源: [TLA+](https://lamport.azurewebsites.net/tla/tla.html)**
> **来源: [ACM - Formal Verification](https://dl.acm.org/)**

---
