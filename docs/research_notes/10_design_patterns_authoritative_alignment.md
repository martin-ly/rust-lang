# 设计模式权威来源对齐矩阵

> **概念族**: 权威来源对齐 / 设计模式
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录

- [设计模式权威来源对齐矩阵](#设计模式权威来源对齐矩阵)
  - [目录](#目录)
  - [一、对齐说明](#一对齐说明)
  - [二、GoF 设计模式](#二gof-设计模式)
  - [三、Rust 惯用法与模式](#三rust-惯用法与模式)
  - [四、企业级/分布式模式](#四企业级分布式模式)
  - [五、反模式](#五反模式)
  - [六、与项目文档的映射](#六与项目文档的映射)
  - [七、未覆盖缺口](#七未覆盖缺口)
  - [相关概念](#相关概念)
  - [学术权威参考](#学术权威参考)

---

## 一、对齐说明

本文档将 `docs/research_notes/` 中的设计模式内容与权威来源建立映射，覆盖 GoF 经典模式、Rust 社区惯用法、企业级/分布式模式以及反模式。

---

## 二、GoF 设计模式

| GoF 模式 | 项目文档 | Rust 实现要点 |
|----------|----------|---------------|
| [Singleton](https://refactoring.guru/design-patterns/singleton) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §1 | 避免全局可变状态，使用 `OnceLock` |
| [Observer](https://refactoring.guru/design-patterns/observer) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §2 | 使用 `Weak<dyn Observer>` 或 channel |
| [Builder](https://refactoring.guru/design-patterns/builder) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §4 | 类型状态模式 |
| [Strategy](https://refactoring.guru/design-patterns/strategy) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | trait 作为策略接口 |
| [Type State](https://rust-unofficial.github.io/patterns/patterns/behavioural/state.html) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §4 | 编译期状态迁移 |
| [Adapter](https://refactoring.guru/design-patterns/adapter) | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | newtype 包装 |

---

## 三、Rust 惯用法与模式

| 模式 | 来源 | 项目文档 | 备注 |
|------|------|----------|------|
| RAII | [Rust Book Ch 15](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | 资源获取即初始化 |
| Newtype | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/type-safety.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §5 | Orphan 规则、类型安全 |
| Sealed Trait | [API Guidelines](https://rust-lang.github.io/api-guidelines/future-proofing.html) | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) §3 | 防止外部实现 |
| Interior Mutability | [Rustonomicon](https://doc.rust-lang.org/nomicon/interior-mutability.html) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §3 | Cell / RefCell / Mutex |
| Deref Polymorphism | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/predictability.html) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §5 | 不滥用 Deref |

---

## 四、企业级/分布式模式

| 模式 | 来源 | 项目文档 | 备注 |
|------|------|----------|------|
| Saga | [microservices.io](https://microservices.io/patterns/data/saga.html) | [60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §2 | 补偿链幂等性 |
| Circuit Breaker | [Release It!](https://pragprog.com/titles/mnee2/release-it-second-edition/) | [software_design_theory/05_boundary_system/README.md](software_design_theory/05_boundary_system/README.md) | 边界系统 |
| Outbox | [microservices.io](https://microservices.io/patterns/data/transactional-outbox.html) | [60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §2 | 长事务 |
| Actor Model | [Rust Actors](https://ryhl.io/blog/actors-with-tokio/) | [60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §6 | 消息顺序 |

---

## 五、反模式

| 反模式 | 来源 | 项目文档 | 备注 |
|--------|------|----------|------|
| 全局可变状态 | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §1 | 单例反模式 |
| 过度泛型化 | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/anti_patterns/index.html) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §6 | 类型参数过多 |
| 滥用内部可变性 | [Rustonomicon](https://doc.rust-lang.org/nomicon/interior-mutability.html) | [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §3 | RefCell 过度使用 |

---

## 六、与项目文档的映射

| 项目文档 | 覆盖模式 | 权威来源 |
|----------|----------|----------|
| [01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | GoF 23 + Rust 特化 | GoF、Refactoring Guru |
| [60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) | 单例、Observer、Builder、内部可变性、Deref、过度泛型 | API Guidelines、Rustonomicon、Design Patterns |
| [06_rust_idioms.md](software_design_theory/06_rust_idioms.md) | RAII、Newtype、迭代器惯用法 | Rust Book、API Guidelines |
| [07_anti_patterns.md](software_design_theory/07_anti_patterns.md) | 反模式合集 | Rust Design Patterns |

---

## 七、未覆盖缺口

1. GoF 中 Structural Patterns（Composite、Decorator、Facade）与 Rust 的映射可细化。
2. 并发模式（Thread Pool、Work Stealing）与 tokio/rayon 的对齐待扩展。
3. 微服务模式（API Gateway、CQRS、Event Sourcing）可补充。

> **权威来源**: [Refactoring Guru](https://refactoring.guru/design-patterns) | [GoF Book](https://en.wikipedia.org/wiki/Design_Patterns) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | [microservices.io](https://microservices.io/) | [Release It!](https://pragprog.com/titles/mnee2/release-it-second-edition/)

## 相关概念

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [设计模式反例](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md)
- [社区最佳实践对齐](10_community_best_practices_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
