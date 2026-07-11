# RFC 深度论证链索引 {#rfc-深度论证链索引}

> **EN**: Rfc Argumentation Chain
> **Summary**: RFC 深度论证链索引 Rfc Argumentation Chain.
> **概念族**: 权威来源对齐 / RFC / 论证链
> **内容分级**: [核心级]
> **层级**: L0-L3
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [RFC 深度论证链索引 {#rfc-深度论证链索引}](#rfc-深度论证链索引-rfc-深度论证链索引)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、所有权与借用 RFC 链 {#二所有权与借用-rfc-链}](#二所有权与借用-rfc-链-二所有权与借用-rfc-链)
    - [RFC 1859 — Non-Lexical Lifetimes {#rfc-1859-non-lexical-lifetimes}](#rfc-1859--non-lexical-lifetimes-rfc-1859-non-lexical-lifetimes)
    - [RFC 2094 — NLL (Non-Lexical Lifetimes) 完整实现 {#rfc-2094-nll-non-lexical-lifetimes-完整实现}](#rfc-2094--nll-non-lexical-lifetimes-完整实现-rfc-2094-nll-non-lexical-lifetimes-完整实现)
  - [三、类型系统 RFC 链 {#三类型系统-rfc-链}](#三类型系统-rfc-链-三类型系统-rfc-链)
    - [RFC 0738 — Variance {#rfc-0738-variance}](#rfc-0738--variance-rfc-0738-variance)
    - [RFC 0195 — Associated Items {#rfc-0195-associated-items}](#rfc-0195--associated-items-rfc-0195-associated-items)
  - [四、异步与并发 RFC 链 {#四异步与并发-rfc-链}](#四异步与并发-rfc-链-四异步与并发-rfc-链)
    - [RFC 2394 — async/await {#rfc-2394-asyncawait}](#rfc-2394--asyncawait-rfc-2394-asyncawait)
  - [五、Edition 与工具链 RFC 链 {#五edition-与工具链-rfc-链}](#五edition-与工具链-rfc-链-五edition-与工具链-rfc-链)
    - [RFC 2052 — Epochs / Editions {#rfc-2052-epochs-editions}](#rfc-2052--epochs--editions-rfc-2052-epochs-editions)
    - [RFC 2957 — Cargo Features 2.0 {#rfc-2957-cargo-features-20}](#rfc-2957--cargo-features-20-rfc-2957-cargo-features-20)
  - [六、论证模式总结 {#六论证模式总结}](#六论证模式总结-六论证模式总结)
  - [七、未覆盖缺口 {#七未覆盖缺口}](#七未覆盖缺口-七未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将关键 Rust RFC 的 **Motivation → Design → Drawbacks → Rationale → Alternatives** 论证链与 `docs/research_notes/` 中的概念定义、反例边界、形式化证明建立映射，揭示 Rust 语言设计决策与项目知识体系之间的深层关联。

---

## 二、所有权与借用 RFC 链 {#二所有权与借用-rfc-链}

### RFC 1859 — Non-Lexical Lifetimes {#rfc-1859-non-lexical-lifetimes}

| 论证环节 | RFC 内容 | 项目文档 | 备注 |
|----------|----------|----------|------|
| Motivation | 词法生命周期（Lifetimes）过于严格，拒绝安全代码 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | NLL 前借用检查器限制 |
| Design | 基于 CFG 的数据流分析 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | NLL 算法 |
| Rationale | 提高表达能力而不损失安全 | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) | 反例仍被正确拒绝 |

### RFC 2094 — NLL (Non-Lexical Lifetimes) 完整实现 {#rfc-2094-nll-non-lexical-lifetimes-完整实现}

| 论证环节 | RFC 内容 | 项目文档 | 备注 |
|----------|----------|----------|------|
| Motivation | 统一 MIR-based 借用检查 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | MIR 层证明 |
| Design | two-phase borrow、mutable borrow 终止点 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | 两阶段借用 |

---

## 三、类型系统 RFC 链 {#三类型系统-rfc-链}

### RFC 0738 — Variance {#rfc-0738-variance}

| 论证环节 | RFC 内容 | 项目文档 | 备注 |
|----------|----------|----------|------|
| Motivation | 需要安全地处理泛型（Generics）生命周期子类型 | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | 型变规则动机 |
| Design | 定义协变/逆变/不变规则 | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | 型变表 |
| Rationale | 防止通过子类型破坏不变量 | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §1 | 型变误用反例 |

### RFC 0195 — Associated Items {#rfc-0195-associated-items}

| 论证环节 | RFC 内容 | 项目文档 | 备注 |
|----------|----------|----------|------|
| Motivation | 扩展 trait 支持关联类型和常量 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | trait 系统形式化 |
| Design | `type Item`、`const N` | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §6 | 关联类型歧义 |

---

## 四、异步与并发 RFC 链 {#四异步与并发-rfc-链}

### RFC 2394 — async/await {#rfc-2394-asyncawait}

| 论证环节 | RFC 内容 | 项目文档 | 备注 |
|----------|----------|----------|------|
| Motivation | 零成本抽象（Zero-Cost Abstraction）的异步 I/O | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | 异步动机 |
| Design | async 块编译为 Future 状态机 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | 状态机展开 |
| Drawbacks | Pin、自引用（Reference）复杂性 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) | Pin 引入原因 |
| Rationale | 与同步代码接近的语法 | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §4 | 同步锁跨 await 风险 |

---

## 五、Edition 与工具链 RFC 链 {#五edition-与工具链-rfc-链}

### RFC 2052 — Epochs / Editions {#rfc-2052-epochs-editions}

| 论证环节 | RFC 内容 | 项目文档 | 备注 |
|----------|----------|----------|------|
| Motivation | 在不破坏兼容性的前提下引入语言变更 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | Edition 机制 |
| Design | edition 关键字、cargo fix | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §6 | 迁移工具 |
| Rationale | 渐进式演进 | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) | 版本迁移反例 |

### RFC 2957 — Cargo Features 2.0 {#rfc-2957-cargo-features-20}

| 论证环节 | RFC 内容 | 项目文档 | 备注 |
|----------|----------|----------|------|
| Motivation | 旧 resolver 中 feature 统一启用导致问题 | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | feature 组合爆炸 |
| Design | resolver v2，按目标启用 feature | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 | resolver v2/v3 |

---

## 六、论证模式总结 {#六论证模式总结}

| 模式 | 描述 | 典型 RFC |
|------|------|----------|
| 表达能力扩展 | 在不破坏安全的前提下放宽限制 | NLL、GATs |
| 安全边界收紧 | 引入新的约束防止 UB | Pin、unsafe_op_in_unsafe_fn |
| 工程复杂度管理 | 通过 Edition/Feature resolver 管理演进 | Editions、Cargo Features 2.0 |
| 抽象机制引入 | trait、关联类型等扩展类型系统 | Associated Items、Specialization |

---

## 七、未覆盖缺口 {#七未覆盖缺口}

1. 宏系统 RFC（macro hygiene、proc-macro）的论证链可进一步展开。
2. const 泛型（Generics）、const eval 相关 RFC 的动机与设计可补充。
3. 每个 RFC 的「Alternatives」部分与项目中的设计模式反例可建立更多关联。

> **权威来源**: [Rust RFCs](https://rust-lang.github.io/rfcs/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [RFC 对齐索引](10_rfc_alignment_index.md)
- [论证脉络关系](10_argumentation_chain_and_flow.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneasverif.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
