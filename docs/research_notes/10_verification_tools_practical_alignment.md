# 形式化验证工具实战对齐矩阵 {#形式化验证工具实战对齐矩阵}

> **EN**: Verification Tools Practical Alignment
> **Summary**: 形式化验证工具实战对齐矩阵 Verification Tools Practical Alignment.
> **概念族**: 权威来源对齐 / 形式化验证工具
> **内容分级**: [核心级]
> **层级**: L3-L4
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [形式化验证工具实战对齐矩阵 {#形式化验证工具实战对齐矩阵}](#形式化验证工具实战对齐矩阵-形式化验证工具实战对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、Aeneas {#二aeneas}](#二aeneas-二aeneas)
  - [三、coq-of-rust {#三coq-of-rust}](#三coq-of-rust-三coq-of-rust)
  - [四、Kani {#四kani}](#四kani-四kani)
  - [五、Prusti {#五prusti}](#五prusti-五prusti)
  - [六、Creusot {#六creusot}](#六creusot-六creusot)
  - [七、工具对比与选型 {#七工具对比与选型}](#七工具对比与选型-七工具对比与选型)
  - [八、未覆盖缺口 {#八未覆盖缺口}](#八未覆盖缺口-八未覆盖缺口)
  - [九、示例 crate {#九示例-crate}](#九示例-crate-九示例-crate)
  - [相关概念 {#相关概念}](#相关概念-相关概念)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的核心概念、定理、反例与主流 Rust 形式化验证工具（Aeneas、coq-of-rust、Kani、Prusti、Creusot）的实战能力建立映射，帮助读者理解「哪些项目内容可被哪些工具验证」。

---

## 二、Aeneas {#二aeneas}

| 工具特性 | 项目对应内容 | 可验证性 | 备注 |
|----------|--------------|----------|------|
| 基于区域（region-based）的借用（Borrowing）模型 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ 高 | Aeneas 将借用编码为区域 |
| 纯函数子集 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ 高 | 支持无指针别名的函数 |
| Trait / 泛型（Generics） | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | 🔄 中 | 部分 trait 支持 |
| Unsafe / 裸指针 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | ⚠️ 低 | Aeneas 主要支持 safe Rust |
| 异步（Async）状态机 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | 🔄 中 | 实验性支持 |

> **权威来源**: [Aeneas](https://aeneasverif.github.io/)

---

## 三、coq-of-rust {#三coq-of-rust}

| 工具特性 | 项目对应内容 | 可验证性 | 备注 |
|----------|--------------|----------|------|
| 将 Rust 翻译为 Coq | [10_formal_language_and_proofs.md](10_formal_language_and_proofs.md) | ✅ 高 | 适合构造机器证明 |
| 所有权（Ownership） / 生命周期（Lifetimes） | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ 高 | 通过 Coq 编码 |
| Trait 实现 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | 🔄 中 | 需要手工编写 Coq 证明 |
| Unsafe 翻译 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | 🔄 中 | 翻译后需显式处理 UB |

> **权威来源**: [coq-of-rust](https://github.com/formal-land/coq-of-rust)

---

## 四、Kani {#四kani}

| 工具特性 | 项目对应内容 | 可验证性 | 备注 |
|----------|--------------|----------|------|
| 模型检查（CBMC） | [10_verification_tools_matrix.md](10_verification_tools_matrix.md) | ✅ 高 | 基于符号执行 |
| 并发安全（Send/Sync） | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | ✅ 高 | 可检测数据竞争 |
| 边界案例 / 反例 | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) | ✅ 高 | 可生成反例跟踪 |
| Unsafe 代码 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | 🔄 中 | 支持部分 unsafe |
| 异步代码 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ⚠️ 低 | 支持有限 |

> **权威来源**: [Kani](https://github.com/model-checking/kani)

---

## 五、Prusti {#五prusti}

| 工具特性 | 项目对应内容 | 可验证性 | 备注 |
|----------|--------------|----------|------|
| 基于 Viper 的合约验证 | [10_verification_tools_matrix.md](10_verification_tools_matrix.md) | ✅ 高 | 需要写前置/后置条件 |
| 所有权（Ownership） / 借用（Borrowing） | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | ✅ 高 | 自动处理借用 |
| Loop 不变量 | [crates/c08_algorithms/](../../crates/c08_algorithms/README.md) | ✅ 高 | 适合算法验证 |
| Trait 合约 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | 🔄 中 | 需要写抽象谓词 |

> **权威来源**: [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html)

---

## 六、Creusot {#六creusot}

| 工具特性 | 项目对应内容 | 可验证性 | 备注 |
|----------|--------------|----------|------|
| 基于 WhyML | [10_verification_tools_matrix.md](10_verification_tools_matrix.md) | ✅ 高 | 生成 Why3 验证条件 |
| 泛型（Generics） / Trait | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ 高 | 支持幽灵类型 |
| 不变量证明 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ 高 | 适合数据结构不变量 |
| Unsafe | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | ⚠️ 低 | 主要支持 safe Rust |

> **权威来源**: [Creusot](https://github.com/creusot-rs/creusot)

---

## 七、工具对比与选型 {#七工具对比与选型}

| 工具 | 适合验证 | 不适合验证 | 学习曲线 |
|------|----------|------------|----------|
| Aeneas | 借用、所有权、纯函数 | unsafe、复杂 trait | 中 |
| coq-of-rust | 完整机器证明 | 快速验证 | 高 |
| Kani | 边界案例、并发、unsafe 子集 | 高阶抽象证明 | 低 |
| Prusti | 算法、数据结构不变量 | 复杂泛型 trait | 中 |
| Creusot | 泛型数据结构、trait 合约 | unsafe | 中 |

---

## 八、未覆盖缺口 {#八未覆盖缺口}

1. 各工具的具体 `.rs` 示例文件可补充到 `examples/` 或 `crates/`。
2. 工具版本兼容性（Aeneas 0.x、Kani 0.x 等）需持续更新。
3. 与项目「核心定理完整证明」文档的逐项映射可进一步细化。

> **权威来源**: [Aeneas](https://aeneasverif.github.io/) | [coq-of-rust](https://github.com/formal-land/coq-of-rust) | [Kani](https://github.com/model-checking/kani) | [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html) | [Creusot](https://github.com/creusot-rs/creusot)
> **官方来源**: [Rust Reference](https://doc.rust-lang.org/reference/)

---

## 九、示例 crate {#九示例-crate}

为降低工具上手门槛，项目在 [`crates/c15_verification_tools`](../../crates/c15_verification_tools/README.md) 中提供了可直接编译的示例：

| 工具 | 示例文件 | 说明 |
|------|----------|------|
| Kani | [`kani_example.rs`](../../crates/c15_verification_tools/examples/kani_example.rs) | `safe_add` 溢出检查、`index_bounds` 数组越界检查 |
| Aeneas | [`aeneas_example.rs`](../../crates/c15_verification_tools/examples/aeneas_example.rs) | 递归求和与有序链表插入 |
| Prusti | [`prusti_example.rs`](../../crates/c15_verification_tools/examples/prusti_example.rs) | `abs`、`max`、`sum` 前置/后置条件 |
| 总览 | [`README.md`](../../crates/c15_verification_tools/README.md) | 官方文档链接、安装与运行命令 |

普通 `cargo check -p c15_verification_tools` 即可通过；各工具验证命令见 [`README.md`](../../crates/c15_verification_tools/README.md)。

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [国际形式化验证索引](10_international_formal_verification_index.md)
- [学术论文与形式化工具对齐索引](10_academic_papers_alignment.md)
- [核心定理完整证明](10_core_theorems_full_proofs.md)
- [知识图谱索引](10_knowledge_graph_index.md)
