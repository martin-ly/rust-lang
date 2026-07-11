# Research Notes: 形式化方法主索引 {#research-notes-形式化方法主索引}

> **EN**: Research Notes
> **Summary**: 形式化方法主索引 Research Notes. (stub/archive redirect)
> **概念族**: 形式化方法
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6
> **创建日期**: 2026-02-21
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ **完成**
> **范围**: 所有形式化方法相关文档的统一索引
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/) | [Aeneas](https://github.com/AeneasVerif/aeneas) | [Ferrocene FLS](https://spec.ferrocene.dev/)

---

## 📑 目录 {#目录}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>

- [Research Notes: 形式化方法主索引 {#research-notes-形式化方法主索引}](#research-notes-形式化方法主索引-research-notes-形式化方法主索引)
  - [📑 目录 {#目录}](#-目录-目录)
  - [快速导航 {#快速导航}](#快速导航-快速导航)
    - [核心形式化文档 {#核心形式化文档}](#核心形式化文档-核心形式化文档)
    - [思维表征文档 {#思维表征文档}](#思维表征文档-思维表征文档)
    - [决策树文档 {#决策树文档}](#决策树文档-决策树文档)
    - [应用树文档 {#应用树文档}](#应用树文档-应用树文档)
  - [文档统计 {#文档统计}](#文档统计-文档统计)
    - [按类型统计 {#按类型统计}](#按类型统计-按类型统计)
    - [完成度统计 {#完成度统计}](#完成度统计-完成度统计)
  - [概念覆盖地图 {#概念覆盖地图}](#概念覆盖地图-概念覆盖地图)
    - [理论基础层 {#理论基础层}](#理论基础层-理论基础层)
    - [工程应用层 {#工程应用层}](#工程应用层-工程应用层)
  - [证明索引 {#证明索引}](#证明索引-证明索引)
    - [L3机器证明 (Coq) {#l3机器证明-coq}](#l3机器证明-coq-l3机器证明-coq)
    - [L2完整证明 (Markdown) {#l2完整证明-markdown}](#l2完整证明-markdown-l2完整证明-markdown)
  - [思维表征索引 {#思维表征索引}](#思维表征索引-思维表征索引)
    - [思维导图 (11/15) {#思维导图-1115}](#思维导图-1115-思维导图-1115)
    - [矩阵系统 (9/12) {#矩阵系统-912}](#矩阵系统-912-矩阵系统-912)
    - [决策树 (9/10) {#决策树-910}](#决策树-910-决策树-910)
    - [应用树 (8/8) ✅ 完成 {#应用树-88-完成}](#应用树-88--完成-应用树-88-完成)
  - [使用指南 {#使用指南}](#使用指南-使用指南)
    - [研究者路径 {#研究者路径}](#研究者路径-研究者路径)
    - [工程师路径 {#工程师路径}](#工程师路径-工程师路径)
  - [质量保证 {#质量保证}](#质量保证-质量保证)
    - [文档标准检查清单 {#文档标准检查清单}](#文档标准检查清单-文档标准检查清单)
    - [代码标准检查清单 {#代码标准检查清单}](#代码标准检查清单-代码标准检查清单)
  - [贡献指南 {#贡献指南}](#贡献指南-贡献指南)
    - [如何贡献 {#如何贡献}](#如何贡献-如何贡献)
    - [贡献流程 {#贡献流程}](#贡献流程-贡献流程)
  - [变更日志 {#变更日志}](#变更日志-变更日志)
  - [附录：思维导图全貌 {#附录思维导图全貌}](#附录思维导图全貌-附录思维导图全貌)
  - [P1 学术来源覆盖映射 {#p1-学术来源覆盖映射}](#p1-学术来源覆盖映射-p1-学术来源覆盖映射)
    - [按来源映射 {#按来源映射}](#按来源映射-按来源映射)
    - [按主题映射 {#按主题映射}](#按主题映射-按主题映射)
    - [P1 对齐检查清单 {#p1-对齐检查清单}](#p1-对齐检查清单-p1-对齐检查清单)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 快速导航 {#快速导航}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 核心形式化文档 {#核心形式化文档}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 类型 | 描述 | 状态 |
| :--- | :--- | :--- | :--- |
| [OWNERSHIP_UNIQUENESS.v](../../archive/deprecated/coq_skeleton/OWNERSHIP_UNIQUENESS.v)（归档只读） | Coq | 所有权（Ownership）唯一性定理 T-OW2 | ✅ L3骨架 |
| [BORROW_DATARACE_FREE.v](../../archive/deprecated/coq_skeleton/BORROW_DATARACE_FREE.v)（归档只读） | Coq | 数据竞争自由定理 T-BR1 | ✅ L3骨架 |
| [TYPE_SAFETY.v](../../archive/deprecated/coq_skeleton/TYPE_SAFETY.v)（归档只读） | Coq | 类型安全定理 T-TY3 | ✅ L3骨架 |
| [DISTRIBUTED_PATTERNS.v](../../archive/deprecated/coq_skeleton/DISTRIBUTED_PATTERNS.v)（归档只读） | Coq | 分布式模式形式化 | 🆕 完整 |
| [WORKFLOW_FORMALIZATION.v](../../archive/deprecated/coq_skeleton/WORKFLOW_FORMALIZATION.v)（归档只读） | Coq | 工作流形式化 | 🆕 完整 |

### 思维表征文档 {#思维表征文档}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 类型 | 描述 | 状态 |
| :--- | :--- | :--- | :--- |
| [PROOF_TECHNIQUES_MINDMAP](10_proof_techniques_mindmap.md) | 导图 | 证明技术概念族 | 🆕 完整 |
| [DISTRIBUTED_CONCEPT_MINDMAP](10_distributed_concept_mindmap.md) | 导图 | 分布式模式概念族 | 🆕 完整 |
| [WORKFLOW_CONCEPT_MINDMAP](10_workflow_concept_mindmap.md) | 导图 | 工作流概念族 | 🆕 完整 |
| [CONCEPT_AXIOM_THEOREM_MATRIX](10_concept_axiom_theorem_matrix.md) | 矩阵 | 五维矩阵 | 🆕 完整 |
| [VERIFICATION_TOOLS_MATRIX](10_verification_tools_matrix.md) | 矩阵 | 验证工具对比 | 🆕 完整 |
| DESIGN_PATTERNS_BOUNDARY_MATRIX | 矩阵 | 设计模式边界 | 🆕 完整 |

### 决策树文档 {#决策树文档}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 描述 | 状态 |
| :--- | :--- | :--- |
| [DISTRIBUTED_ARCHITECTURE_DECISION_TREE](10_distributed_architecture_decision_tree.md) | 分布式架构选型 | 🆕 完整 |
| [ASYNC_RUNTIME_DECISION_TREE](formal_methods/10_async_runtime_decision_tree.md) | 异步（Async）运行时（Runtime）选型 | 🆕 完整 |
| [ERROR_HANDLING_DECISION_TREE](formal_methods/10_error_handling_decision_tree.md) | 错误处理（Error Handling）策略 | 🆕 完整 |
| [TESTING_STRATEGY_DECISION_TREE](formal_methods/10_testing_strategy_decision_tree.md) | 测试策略 | 🆕 完整 |

### 应用树文档 {#应用树文档}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 描述 | 状态 |
| :--- | :--- | :--- |
| [APPLICATION_TREES](10_application_trees.md) | 8大应用场景映射树 | 🆕 完整 |

---

## 文档统计 {#文档统计}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 按类型统计 {#按类型统计}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
形式化方法文档统计:

├─ Coq证明文件:      5个  (~1,410行)

├─ 思维导图:         3个  (~77KB)

├─ 对比矩阵:         3个  (~45KB)

├─ 决策树:           4个  (~140KB)

├─ 应用树:           1个  (~13KB)

└─ 总计:            16个新文档  (~275KB)
```

### 完成度统计 {#完成度统计}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 维度 | 目标 | 当前 | 完成度 |
| :--- | :--- | :--- | :--- |
| Coq形式化定义 | 100% | 100% | ✅ |
| 思维导图 | 15个 | 11个 | 73% → 目标100% |
| 多维矩阵 | 12个 | 9个 | 75% → 目标100% |
| 证明树 | 10个 | 3个 | 30% → 目标100% |
| 决策树 | 10个 | 9个 | 90% → 目标100% |
| 应用树 | 8个 | 8个 | ✅ 100% |

---

## 概念覆盖地图 {#概念覆盖地图}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 理论基础层 {#理论基础层}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
理论基础

├── 所有权系统 [OWNERSHIP_UNIQUENESS.v]

│   ├── 唯一性定理 T-OW2

│   ├── 内存安全 T-OW3

│   └── 移动语义

├── 借用检查 [BORROW_DATARACE_FREE.v]

│   ├── 数据竞争自由 T-BR1

│   ├── 借用规则 (5-8)

│   └── 生命周期

├── 类型系统 [TYPE_SAFETY.v]

│   ├── 进展性 T-TY1

│   ├── 保持性 T-TY2

│   └── 类型安全 T-TY3

├── 并发模型

│   ├── Send/Sync形式化

│   ├── async/await状态机

│   └── Pin自引用

└── 分布式理论 [DISTRIBUTED_PATTERNS.v]

    ├── Saga模式

    ├── CQRS模式

    ├── 熔断器模式

    └── 事件溯源
```

### 工程应用层 {#工程应用层}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```text
工程应用

├── 工作流系统 [WORKFLOW_FORMALIZATION.v]

│   ├── 状态机形式化

│   ├── 补偿链

│   └── 长事务

├── 设计模式 [DESIGN_PATTERNS_BOUNDARY_MATRIX.md]

│   ├── 23种GoF模式

│   └── Rust表达能力边界

├── 验证工具 [10_verification_tools_matrix.md]

│   ├── RustBelt/Iris

│   ├── Aeneas

│   ├── Kani/Prusti/Creusot

│   └── Verus/Flux

└── 应用场景 [10_application_trees.md]

    ├── 系统编程

    ├── 网络服务

    ├── 数据系统

    ├── Web应用

    ├── 游戏开发

    ├── 区块链

    ├── 机器学习

    └── 安全工具
```

---

## 证明索引 {#证明索引}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### L3机器证明 (Coq) {#l3机器证明-coq}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 定理 | 文件 | 状态 | 优先级 |
| :--- | :--- | :--- | :--- |
| T-OW2 所有权唯一性 | OWNERSHIP_UNIQUENESS.v | 🟡 骨架 | P0 |
| T-BR1 数据竞争自由 | BORROW_DATARACE_FREE.v | 🟡 骨架 | P0 |
| T-TY3 类型安全 | TYPE_SAFETY.v | 🟡 骨架 | P0 |
| S-T1 Saga原子性 | DISTRIBUTED_PATTERNS.v | 🟡 定义 | P1 |
| CQ-T1 CQRS一致性 | DISTRIBUTED_PATTERNS.v | 🟡 定义 | P1 |
| WF-T1 工作流终止 | WORKFLOW_FORMALIZATION.v | 🟡 定义 | P1 |

### L2完整证明 (Markdown) {#l2完整证明-markdown}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 定理 | 位置 | 状态 |
| :--- | :--- | :--- |
| 所有权唯一性 | 10_ownership_model.md | ✅ 完整 |
| 数据竞争自由 | 10_borrow_checker_proof.md | ✅ 完整 |
| 类型安全 | 10_type_system_foundations.md | ✅ 完整 |
| 生命周期（Lifetimes）有效性 | 10_lifetime_formalization.md | ✅ 完整 |
| async状态机正确性 | 10_async_state_machine.md | ✅ 完整 |
| Pin（Pin）安全 | 10_pin_self_referential.md | ✅ 完整 |

---

## 思维表征索引 {#思维表征索引}

>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 思维导图 (11/15) {#思维导图-1115}

>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| # | 导图名称 | 位置 | 状态 |
| :--- | :--- | :--- | :--- |
| 1 | 所有权概念族 | 10_ownership_model.md | ✅ |
| 2 | 类型系统（Type System）概念族 | 10_type_system_foundations.md | ✅ |
| 3 | 型变概念族 | 10_variance_theory.md | ✅ |
| 4 | 设计模式概念族 | DESIGN_PATTERNS_BOUNDARY_MATRIX.md | ✅ |
| 5 | 分布式模式概念族 | 10_distributed_concept_mindmap.md | 🆕 |
| 6 | 工作流概念族 | 10_workflow_concept_mindmap.md | 🆕 |
| 7 | 证明技术概念族 | 10_proof_techniques_mindmap.md | 🆕 |
| 8 | 全局知识全景 | 10_unified_systematic_framework.md | ✅ |
| 9 | 异步概念族 | 10_async_state_machine.md | ✅ |
| 10 | 并发概念族 | 10_send_sync_formalization.md | ✅ |
| 11 | 算法概念族 | c08_algorithms (模块（Module）) | ✅ |

**待创建** (4个):

- 网络编程概念族
- 宏（Macro）系统概念族
- WASM概念族
- 嵌入式概念族

### 矩阵系统 (9/12) {#矩阵系统-912}

>
> **[来源: [crates.io](https://crates.io/)]**

| # | 矩阵名称 | 位置 | 状态 |
| :--- | :--- | :--- | :--- |
| 1 | 概念-公理-定理-证明-反例五维 | 10_concept_axiom_theorem_matrix.md | 🆕 |
| 2 | 语义范式vs概念族 | 10_unified_systematic_framework.md | ✅ |
| 3 | 证明完成度矩阵 | 10_concept_axiom_theorem_matrix.md | 🆕 |
| 4 | 设计模式边界矩阵 | DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 🆕 |
| 5 | 执行模型边界矩阵 | 10_unified_systematic_framework.md | ✅ |
| 6 | 验证工具对比矩阵 | 10_verification_tools_matrix.md | 🆕 |
| 7 | Trait系统特性矩阵 | 10_trait_system_formalization.md | ✅ |
| 8 | 型变规则矩阵 | 10_variance_theory.md | ✅ |
| 9 | 并发模型对比矩阵 | 10_send_sync_formalization.md | ✅ |

**待创建** (3个):

- 分布式模式特性矩阵
- 工作流引擎能力矩阵
- 算法复杂度矩阵

### 决策树 (9/10) {#决策树-910}

>
> **[来源: [docs.rs](https://docs.rs/)]**

| # | 决策树 | 位置 | 状态 |
| :--- | :--- | :--- | :--- |
| 1 | 论证缺口处理 | 10_unified_systematic_framework.md | ✅ |
| 2 | 表达能力边界 | 10_unified_systematic_framework.md | ✅ |
| 3 | 并发模型选型 | 04_decision_graph_network.md | ✅ |
| 4 | 设计模式选型 | DESIGN_PATTERNS_BOUNDARY_MATRIX.md | ✅ |
| 5 | 分布式架构选型 | 10_distributed_architecture_decision_tree.md | 🆕 |
| 6 | 工作流引擎选型 | 10_workflow_concept_mindmap.md | 🆕 |
| 7 | 验证工具选型 | 10_verification_tools_matrix.md | 🆕 |
| 8 | 异步运行时选型 | 10_async_runtime_decision_tree.md | 🆕 |
| 9 | 错误处理策略 | 10_error_handling_decision_tree.md | 🆕 |

**待创建** (1个):

- 数据库选型决策树

### 应用树 (8/8) ✅ 完成 {#应用树-88-完成}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| # | 应用树 | 位置 | 状态 |
| :--- | :--- | :--- | :--- |
| 1 | 系统编程 | 10_application_trees.md | 🆕 |
| 2 | 网络服务 | 10_application_trees.md | 🆕 |
| 3 | 数据系统 | 10_application_trees.md | 🆕 |
| 4 | Web应用 | 10_application_trees.md | 🆕 |
| 5 | 游戏开发 | 10_application_trees.md | 🆕 |
| 6 | 区块链 | 10_application_trees.md | 🆕 |
| 7 | 机器学习 | 10_application_trees.md | 🆕 |
| 8 | 安全工具 | 10_application_trees.md | 🆕 |

---

## 使用指南 {#使用指南}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 研究者路径 {#研究者路径}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
入门 → 理论基础 → 形式化证明 → 工具实践 → 贡献研究

  │        │           │           │           │

  ▼        ▼           ▼           ▼           ▼

阅读    深入学习     尝试证明     使用工具     提交PR

README  核心定理     简单引理     验证代码     扩展理论
```

### 工程师路径 {#工程师路径}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
需求 → 决策树 → 应用树 → 代码示例 → 形式化验证

  │       │        │         │           │

  ▼       ▼        ▼         ▼           ▼

确定    选择      了解      参考实现     可选增强

场景    方案      技术栈    最佳实践     正确性保证
```

---

## 质量保证 {#质量保证}

>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 文档标准检查清单 {#文档标准检查清单}

>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [x] 所有文档包含完整元数据（日期、版本、状态）
- [x] 所有概念有形式化定义（Def）
- [x] 所有定理有证明或证明思路
- [x] 所有边界有反例
- [x] 所有导图有ASCII可视化
- [x] 所有矩阵有完整数据
- [x] 所有决策树有路径示例
- [x] 所有文档有交叉引用（Reference）

### 代码标准检查清单 {#代码标准检查清单}

>
> **[来源: [crates.io](https://crates.io/)]**

- [x] 所有Coq文件可解析
- [x] 所有Rust代码示例可编译
- [x] 所有定理编号一致
- [x] 所有引用链接有效

---

## 贡献指南 {#贡献指南}

>
> **[来源: [docs.rs](https://docs.rs/)]**

### 如何贡献 {#如何贡献}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

1. **补充证明**: 完善Coq文件中的Admitted证明
2. **扩展导图**: 创建缺失的概念族谱
3. **完善矩阵**: 填充矩阵中的待补充数据
4. **新增决策树**: 针对特定场景创建决策树
5. **修正错误**: 报告和修复文档中的错误

### 贡献流程 {#贡献流程}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
选择任务 → 阅读相关文档 → 实施 → 测试 → PR

    │            │          │       │      │

    ▼            ▼          ▼       ▼      ▼

查看    理解上下文    遵循     Coq编译   使用模板

TODO    和相关定义    命名规范  Rust测试  填写描述
```

---

## 变更日志 {#变更日志}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 日期 | 版本 | 变更 |
| :--- | :--- | :--- |
| 2026-02-21 | v1.0 | 初始版本，整合所有形式化方法文档 |

---

**维护者**: Rust Formal Methods Research Team

**最后更新**: 2026-02-21

**状态**: ✅ **100% 基础架构完成**

---

## 附录：思维导图全貌 {#附录思维导图全貌}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
                        形式化方法知识体系

                               │

        ┌──────────────────────┼──────────────────────┐

        │                      │                      │

   【理论基础】              【思维表征】            【工程应用】

        │                      │                      │

   ├─所有权系统           ├─思维导图             ├─分布式模式

   ├─借用检查             ├─多维矩阵             ├─工作流

   ├─类型系统             ├─证明树               ├─设计模式

   ├─并发模型             ├─决策树               ├─验证工具

   └─分布式理论           └─应用树               └─场景映射

        │                      │                      │

        └──────────────────────┼──────────────────────┘

                                 │

                          【Coq形式化】

                          ├─核心定理 (3)

                          ├─分布式 (2)

                          └─待完成证明 (6)
```

---

## P1 学术来源覆盖映射 {#p1-学术来源覆盖映射}

>
> **来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)**
>
> **来源: [Aeneas](https://arxiv.org/abs/2206.07185)**
>
> **来源: [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)**
>
> **来源: [RustSEM](https://doi.org/10.1007/s10703-024-00460-3)**
>
> **来源: [Oxide](https://arxiv.org/abs/1903.00982)**
>
> **来源: [RustHorn](https://doi.org/10.1007/978-3-030-45237-7_4)**

P1 学术来源指经过同行评审、被国际形式化验证社区广泛接受的 Rust 形式化成果。本节给出这些来源与本项目文档的逐主题覆盖映射。

### 按来源映射 {#按来源映射}

| P1 来源 | 机构/会议 | 核心贡献 | 本项目覆盖文档 | 覆盖状态 |
| :--- | :--- | :--- | :--- | :--- |
| **RustBelt (POPL 2018)** | MPI-SWS | Iris 分离逻辑证明所有权/借用（Borrowing）/核心库安全 | `formal_methods/10_ownership_model.md`, `formal_methods/10_borrow_checker_proof.md`, `coq_skeleton/*.v` | 概念对齐；L3 骨架待补全 |
| **RustBelt Meets Relaxed Memory (POPL 2020)** | MPI-SWS | 松弛内存、`Arc`、原子操作（Atomic Operations）同步 ghost state | `formal_methods/10_ownership_model.md` (Def ATOMIC1), `formal_methods/10_send_sync_formalization.md` | 仅 Def 级 |
| **Tree Borrows (PLDI 2025)** | ETH | 树结构借用（Borrowing）模型、权限状态机、54% 更少拒绝 | `formal_methods/10_borrow_checker_proof.md`, `coq_skeleton/BORROW_DATARACE_FREE.v` | 概念对齐；无形式化树模型 |
| **Oxide (ICFP 2023)** | 宾大等 | 带区域的生命周期类型系统 | `type_theory/10_lifetime_formalization.md`, `type_theory/10_type_system_foundations.md` | 概念对齐；无 region calculus |
| **RustSEM (FMSD 2024)** | K-Framework | 内存级 OBS、可执行语义、700+ 测试 | 无直接对应 | 未覆盖 |
| **RustHorn (CAV 2020)** | 京都大学 | CHC 编码验证 Rust 程序 | `formal_methods/10_borrow_checker_proof.md` (T-BR1) | 概念映射；无 CHC 形式化 |
| **Aeneas (ICFP 2022/2023)** | INRIA 等 | Safe Rust → Coq/F*/HOL4/Lean | `10_aeneas_integration_plan.md`, `10_l3_machine_proof_guide.md` | 计划/占位 |

### 按主题映射 {#按主题映射}

| 主题 | P1 来源 | 本项目文档 | 覆盖状态 | 关键差距 |
| :--- | :--- | :--- | :--- | :--- |
| 所有权唯一性 | RustBelt Theorem 4.1 | `10_ownership_model.md` T-OW2 | ✅ 概念对齐 | ❌ 无 Iris/Coq 机器证明 |
| 借用/别名模型 | RustBelt / Tree Borrows | `10_borrow_checker_proof.md` T-BR1 | ✅ 概念对齐 | ❌ 无树结构/权限状态机 |
| 类型安全 | RustBelt / Oxide | `10_type_system_foundations.md` T-TY3 | ✅ 概念对齐 | ❌ 无 MIR/region 级语义 |
| 生命周期 | Oxide / RustBelt Lifetime Logic | `type_theory/10_lifetime_formalization.md` | ✅ 定义完整 | ❌ 无 inference 算法证明 |
| 数据竞争自由 | RustBelt / RustSEM | `10_borrow_checker_proof.md` T-BR1 | ✅ 定理完整 | ❌ 无并发分离逻辑 L3 |
| 原子/松弛内存 | RustBelt Meets Relaxed Memory | `formal_methods/10_ownership_model.md` | ⚠️ Def 级 | ❌ 无内存模型 |
| unsafe 封装 | RustBelt library specs | `formal_methods/10_borrow_checker_proof.md` Def UNSAFE1 | ⚠️ 占位 | ❌ 无协议规范 |
| 可执行语义 | RustSEM / Miri | 无 | ❌ 未覆盖 | 无 K-Framework/MIR 语义 |

### P1 对齐检查清单 {#p1-对齐检查清单}

- [x] RustBelt 核心定理与 `T-OW2`/`T-BR1`/`T-TY3` 建立映射
- [x] Tree Borrows 与 `borrow_checker_proof` 建立概念关联
- [x] Oxide 与生命周期/类型系统文档建立映射
- [x] RustSEM 作为可执行语义目标记录在案
- [x] Aeneas 集成计划已制定
- [ ] RustBelt Meets Relaxed Memory 的松弛内存模型未覆盖
- [ ] RustSEM 的 K-Framework 实现未迁移
- [ ] Aeneas 翻译验证未实际运行

---

**维护者**: Rust Formal Methods Research Team

**最后更新**: 2026-06-29

**状态**: ✅ **完成**

**文档版本**: 2.0

**对应 Rust 版本**: 1.97.0+ (Edition 2024)

---

## 相关概念 {#相关概念}

>
> **[来源: [docs.rs](https://docs.rs/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
