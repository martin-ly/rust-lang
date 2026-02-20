# Rust 核心特性完整链：定义→示例→论证→证明

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **目标**: 为 10–15 个核心特性建立统一「定义→概念→属性→关系→解释→示例→论证→形式化证明」链

---

## 📊 目录

- [Rust 核心特性完整链：定义→示例→论证→证明](#rust-核心特性完整链定义示例论证证明)
  - [📊 目录](#-目录)
  - [1. 所有权](#1-所有权)
  - [2. 借用](#2-借用)
  - [3. 生命周期](#3-生命周期)
  - [4. Pin](#4-pin)
  - [5. Send/Sync](#5-sendsync)
  - [6. Future](#6-future)
  - [7. Trait](#7-trait)
  - [8. 泛型](#8-泛型)
  - [9. match](#9-match)
  - [10. for](#10-for)
  - [11. Option/Result](#11-optionresult)
  - [12. 闭包](#12-闭包)
  - [13. ? 操作符](#13--操作符)
    - [相关思维表征](#相关思维表征)
  - [相关文档](#相关文档)

---

## 1. 所有权

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 每个值有唯一所有者；所有者离开作用域时值被丢弃；默认移动语义 |
| **概念** | 规则 1–3（[ownership_model](formal_methods/ownership_model.md)）；Def 1.1–1.3 |
| **属性** | 唯一性、RAII、无 GC |
| **关系** | 移动→借用下游；Copy 为移动的特例 |
| **解释** | 无 GC 下保证内存安全；移动即所有权转移 |
| **示例** | `let x = vec![1,2]; let y = x;` // x 已移动 |
| **论证** | [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) § 所有权 |
| **形式化** | [ownership_model](formal_methods/ownership_model.md) 定理 T2/T3、规则 1–8 |
| **反例** | 使用已移动值；见 [FORMAL_PROOF_SYSTEM_GUIDE](FORMAL_PROOF_SYSTEM_GUIDE.md) |

---

## 2. 借用

| 维度 | 内容 |
| :--- | :--- |
| **定义** | &T 不可变借用、&mut T 可变借用；可变独占、不可变可多 |
| **概念** | 借用规则 5–8（[borrow_checker_proof](formal_methods/borrow_checker_proof.md)） |
| **属性** | 零成本、编译期检查、数据竞争自由 |
| **关系** | 依赖所有权；与生命周期协同 |
| **解释** | 借用不转移所有权；&mut 互斥；& 与 &mut 互斥 |
| **示例** | `let r = &v; let r2 = &v;` // 允许多 &；`let m = &mut v;` 独占 |
| **论证** | [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) § 借用 |
| **形式化** | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) 定理 T1 |
| **反例** | 双重可变借用；悬垂引用 |

---

## 3. 生命周期

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 引用有效期；$\ell \subseteq \text{lft}$；NLL + 显式标注 |
| **概念** | outlives、区域类型（[lifetime_formalization](formal_methods/lifetime_formalization.md)） |
| **属性** | 引用有效性、无悬垂 |
| **关系** | 与借用协同；泛型生命周期 `'a` |
| **解释** | 引用不能比其引用对象活得更久 |
| **示例** | `fn f<'a>(x: &'a i32) -> &'a i32 { x }` |
| **论证** | [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) § 生命周期 |
| **形式化** | [lifetime_formalization](formal_methods/lifetime_formalization.md) 定理 T2 |
| **反例** | 返回局部引用 |

---

## 4. Pin

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 保证类型在内存中不移动；Unpin 可安全移动；!Unpin 需堆固定 |
| **概念** | Pin 不变式（[pin_self_referential](formal_methods/pin_self_referential.md)） |
| **属性** | 自引用安全、Future 位置稳定 |
| **关系** | Future 依赖 Pin；Unpin 为默认 |
| **解释** | 自引用结构移动→悬垂；Pin 禁止移动 |
| **示例** | `Box::pin(x)` 堆固定；`Pin::new(&mut x)` 仅 Unpin |
| **论证** | [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) § Pin 堆/栈区分 |
| **形式化** | [pin_self_referential](formal_methods/pin_self_referential.md) 定理 T1–T3 |
| **反例** | 非 Unpin 用 Pin::new；决策树见 DESIGN_MECHANISM_RATIONALE |

---

## 5. Send/Sync

| 维度 | 内容 |
| :--- | :--- |
| **定义** | Send=可安全转移至他线程；Sync=可安全多线程共享引用 |
| **概念** | 自动 trait；[async_state_machine](formal_methods/async_state_machine.md) |
| **属性** | 结构性质；编译器自动推导 |
| **关系** | `T: Sync` ⇔ `&T: Send`；Rc 非 Send |
| **解释** | 跨线程传递需 Send；共享需 Sync |
| **示例** | `thread::spawn(\|\| { ... })` 闭包需 Send |
| **论证** | [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) § Send/Sync |
| **形式化** | [async_state_machine](formal_methods/async_state_machine.md) SPAWN1、Send/Sync 语义 |
| **反例** | Rc 跨线程；见 05_boundary_system safe_unsafe_matrix |

---

## 6. Future

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 异步计算；Poll 状态机；Pin 保证自引用 |
| **概念** | async/await 语法糖；状态机生成（[async_state_machine](formal_methods/async_state_machine.md)） |
| **属性** | 惰性、可恢复、自引用 |
| **关系** | 依赖 Pin；跨 await 需 Send |
| **解释** | Future 不立即执行；poll 驱动步进 |
| **示例** | `async fn f() -> i32 { 1 }` |
| **论证** | [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) § 异步 |
| **形式化** | [async_state_machine](formal_methods/async_state_machine.md) 定理 T6.1–T6.3 |
| **反例** | 未 Pin 自引用；非 Send 跨 await |

---

## 7. Trait

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 行为抽象；trait 定义 + impl for |
| **概念** | 静态分发、对象安全（[trait_system_formalization](type_theory/trait_system_formalization.md)） |
| **属性** | 零成本、编译时单态化 |
| **关系** | 泛型约束；impl Trait / dyn Trait |
| **解释** | 接口即 trait；多态通过 impl |
| **示例** | `trait Display { fn fmt(...); } impl Display for i32 { ... }` |
| **论证** | [trait_system_formalization](type_theory/trait_system_formalization.md) |
| **形式化** | coherence、RPITIT、async fn、对象安全 |
| **反例** | 冲突 impl；Clone 非对象安全 |

---

## 8. 泛型

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 编译时多态；单态化 |
| **概念** | `fn f<T: Trait>(x: T)`；[type_system_foundations](type_theory/type_system_foundations.md) |
| **属性** | 零成本、无运行时类型信息 |
| **关系** | Trait 约束；关联类型；GAT |
| **解释** | 类型参数在编译时展开 |
| **示例** | `fn id<T>(x: T) -> T { x }` |
| **论证** | [type_system_foundations](type_theory/type_system_foundations.md) |
| **形式化** | 类型规则、保持性、进展性 |
| **反例** | 歧义 impl 需 turbofish |

---

## 9. match

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 穷尽模式匹配；必须覆盖所有变体 |
| **概念** | Def MATCH1（[borrow_checker_proof](formal_methods/borrow_checker_proof.md)） |
| **属性** | 穷尽性、模式解构 |
| **关系** | 与借用协同；迭代中 match 影响借用 |
| **解释** | 编译器强制全覆盖 |
| **示例** | `match x { Some(v) => v, None => 0 }` |
| **论证** | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) Def MATCH1 |
| **形式化** | 模式匹配规则、穷尽检查 |
| **反例** | 非穷尽 match 编译错误 |

---

## 10. for

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 基于 IntoIterator 的迭代 |
| **概念** | Def FOR1（[borrow_checker_proof](formal_methods/borrow_checker_proof.md)） |
| **属性** | 消费或借用迭代器 |
| **关系** | 与借用协同；迭代中修改集合违规 |
| **解释** | `for x in iter` 消费；`for x in &vec` 借用 |
| **示例** | `for x in &v { ... }` 不可修改 v |
| **论证** | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) Def FOR1 |
| **形式化** | 迭代与借用规则 |
| **反例** | 迭代中修改集合 |

---

## 11. Option/Result

| 维度 | 内容 |
| :--- | :--- |
| **定义** | Option 可选值；Result 错误处理；无 null |
| **概念** | 构造性、Some/None、Ok/Err（[DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) Def OR1） |
| **属性** | 显式处理、无空指针 |
| **关系** | ? 操作符早期返回；与 match 协同 |
| **解释** | 强制处理缺失与错误 |
| **示例** | `let x: Option<i32> = Some(1);` |
| **论证** | [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) 定理 OR-T1 |
| **形式化** | Def OR1、Axiom OR1 |
| **反例** | unwrap 空值 panic |

---

## 12. 闭包

| 维度 | 内容 |
| :--- | :--- |
| **定义** | 匿名函数；捕获环境；唯一匿名类型 |
| **概念** | Fn/FnMut/FnOnce（[RUST_193](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md)） |
| **属性** | 按引用/可变/移动捕获 |
| **关系** | 与 ownership/borrow 协同；Send 约束 |
| **解释** | 闭包类型由使用处唯一确定 |
| **示例** | `let f = \|x\| x + 1;` |
| **论证** | [type_system_foundations](type_theory/type_system_foundations.md) |
| **形式化** | 闭包类型规则 |
| **反例** | 跨线程传非 Send 闭包 |

---

## 13. ? 操作符

| 维度 | 内容 |
| :--- | :--- |
| **定义** | Result/Option 早期返回；错误传播 |
| **概念** | Def QUERY1（[borrow_checker_proof](formal_methods/borrow_checker_proof.md)） |
| **属性** | 简化错误处理 |
| **关系** | 与 Result、From 协同 |
| **解释** | `Ok(x)` 解开；`Err(e)` 提前返回 |
| **示例** | `let x = f()?;` |
| **论证** | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) Def QUERY1 |
| **形式化** | 控制流与错误传播规则 |
| **反例** | 非 Result 类型使用 ? |

---

### 相关思维表征

| 类型 | 位置 |
| :--- | :--- |
| 多维矩阵 | [UNIFIED_SYSTEMATIC_FRAMEWORK](UNIFIED_SYSTEMATIC_FRAMEWORK.md) 概念-公理-定理-证明方法-反例矩阵；[formal_methods/README §六篇并表](formal_methods/README.md#formal_methods-六篇并表) |
| 证明树 | [PROOF_INDEX](PROOF_INDEX.md)、各特性对应 formal_methods/type_theory 文档 |
| 决策树 | [DECISION_GRAPH_NETWORK](../04_thinking/DECISION_GRAPH_NETWORK.md)、[DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) 选型决策树 |

*依据*：[HIERARCHICAL_MAPPING_AND_SUMMARY](HIERARCHICAL_MAPPING_AND_SUMMARY.md) § 文档↔思维表征。

---

## 相关文档

| 文档 | 用途 |
| :--- | :--- |
| [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) | 92 项特性总览 |
| [UNIFIED_SYSTEMATIC_FRAMEWORK](UNIFIED_SYSTEMATIC_FRAMEWORK.md) | 全局矩阵与决策树 |
| [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) | 核心机制设计论证 |
| [FORMAL_PROOF_SYSTEM_GUIDE](FORMAL_PROOF_SYSTEM_GUIDE.md) | 反例索引 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
