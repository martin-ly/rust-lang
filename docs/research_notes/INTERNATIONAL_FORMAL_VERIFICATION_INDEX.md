# 国际 Rust 形式化验证成果对标索引

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 索引完成；季度更新
> **用途**: 系统对标国际权威 Rust 形式化证明模型，明确本项目 PROOF_INDEX 与最新成果的对应关系与差距
> **维护**: 季度更新，Rust 新版本发布时补充

---

## 一、国际权威成果总览

| 成果 | 机构/作者 | 年份 | 形式化范围 | 证明助手/工具 | 与本项目对应 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **RustBelt** | MPI-SWS (Jung et al.) | 2018 | 所有权、借用、MIR 级 | Iris (Coq) | ownership_model, borrow_checker_proof, [coq_skeleton](./coq_skeleton/)（T-OW2/BR1/TY3 骨架）|
| **Tree Borrows** | ETH (PLDI 2025) | 2025 | 借用模型、树结构、54% 更少拒绝 | Iris (Coq)、Rocq | borrow_checker_proof 演进；Distinguished Paper |
| **RustBelt Meets Relaxed Memory** | MPI-SWS | 2020 | 松弛内存、Arc、原子操作 | Iris (Coq) | formal_methods Phase 4（部分） |
| **Rust Distilled** | DBLP | - | 高层所有权、无生命周期 | - | ownership_model（高层部分） |
| **Aeneas** | INRIA 等 | 2023+ | Safe Rust → Coq/F*/HOL4/Lean | 多后端 | [AENEAS_INTEGRATION_PLAN](./AENEAS_INTEGRATION_PLAN.md) |
| **coq-of-rust** | - | 2023+ | THIR → Rocq，借用与 effect | Rocq (Coq) | 无直接对应 |
| **Crux-MIR** | Galois | 2024 | 比特级精确、密码学验证 | Crux | 无直接对应 |
| **RustSEM** | 2024 (FMSD) | 2024 | 内存级 OBS、可执行语义、700+ 测试 | K-Framework | 无直接对应 |
| **AutoVerus** | - | 2024–2025 | LLM 自动证明生成 | Verus | 无直接对应 |

---

## 二、逐项对标与差距

### 2.1 RustBelt

- **论文**: [RustBelt: Logical Foundations for the Future of Safe Systems Programming](https://plv.mpi-sws.org/rustbelt/)
- **形式化**: λ Rust 模型、分离逻辑、MIR 级语义
- **本项目对应**: `formal_methods/ownership_model.md`, `formal_methods/borrow_checker_proof.md`
- **差距**: 无 Iris 分离逻辑形式化；无 MIR 级建模；**Coq 骨架已创建**（[coq_skeleton/OWNERSHIP_UNIQUENESS.v](./coq_skeleton/OWNERSHIP_UNIQUENESS.v)），证明 Admitted 待补全

### 2.2 RustBelt Meets Relaxed Memory (POPL 2020)

- **论文**: [RustBelt Meets Relaxed Memory](https://plv.mpi-sws.org/rustbelt/rbrlx/)
- **形式化**: 松弛内存、Arc 数据竞争、synchronized ghost state
- **本项目对应**: `formal_methods` Phase 4（MaybeUninit、原子操作）— 仅 Def 级
- **差距**: 无松弛内存模型；无 Arc 形式化；无 ghost state 构造

### 2.3 RustSEM (K-Framework, 2024)

- **论文**: [Formally understanding Rust's ownership and borrowing system at the memory level](https://link.springer.com/article/10.1007/s10703-024-00460-3) (FMSD)
- **形式化**: 内存级 OBS、可执行操作语义、700+ 测试
- **本项目对应**: 无
- **差距**: 无可执行语义；无 K 框架实现；无内存级 OBS 映射

### 2.4 Aeneas

- **形式化**: Safe Rust 翻译到 Coq、F*、HOL4、Lean
- **本项目对应**: [AENEAS_INTEGRATION_PLAN](./AENEAS_INTEGRATION_PLAN.md)（对接方案已制定）
- **差距**: 无证明助手翻译；无多后端验证
- **对接状态**: 📋 计划中 — 示例选取、环境搭建、翻译验证待实施

### 2.5 coq-of-rust

- **形式化**: THIR → Rocq，显式借用与 effect 序列
- **本项目对应**: 无
- **差距**: 无编译器 IR 级形式化

### 2.6 Crux-MIR

- **形式化**: 比特级精确、密码学模块验证
- **本项目对应**: 无
- **差距**: 无比特级模型

### 2.7 AutoVerus

- **形式化**: LLM 自动生成 Verus 正确性证明
- **本项目对应**: 无
- **差距**: 无自动化证明生成

### 2.8 Tree Borrows (PLDI 2025)

- **论文**: [Tree Borrows: A New Aliasing Model for Rust](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)（Distinguished Paper Award）
- **形式化**: 树结构借用、30k crates 54% 更少拒绝、Rocq 证明
- **本项目对应**: borrow_checker_proof；coq_skeleton/BORROW_DATARACE_FREE.v
- **差距**: 无树结构建模；可参考 Tree Borrows 补全 T-BR1 形式化

---

## 三、与本项目 PROOF_INDEX 的映射

| PROOF_INDEX 领域 | 国际对标 | 覆盖度 |
| :--- | :--- | :--- |
| 所有权与借用 | RustBelt, RustSEM | 部分（语言级有，内存级/机器证明无） |
| 生命周期 | RustBelt（间接） | 部分 |
| 类型系统 | RustBelt, Aeneas | 部分 |
| 异步与 Pin | - | 无国际直接对标 |
| 松弛内存/原子 | RustBelt Meets Relaxed Memory | 未覆盖 |

---

## 四、季度更新记录

| 日期 | 更新内容 |
| :--- | :--- |
| 2026-02-14 | 初版创建 |
| 2026-02-14 | 补充 coq_skeleton 与 RustBelt 对应 |
| 2026-02-14 | T-BR1/T-TY3 Coq 骨架创建；Tree Borrows PLDI 2025 补充 |

---

**维护者**: Rust Formal Methods Research Team
