> **内容分级**: [综述级]

# 语义分层映射索引

> **EN**: Semantic Layer Alignment Index
> **Summary**: A cross-layer index mapping algorithm semantics → system semantics → architecture semantics → enterprise architecture, showing refinement relationships and Rust engineering mappings for each layer.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者 / 进阶]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L0-L7
> **A/S/P 标记**: **S** — Structure（心智模型）
> **双维定位**: C×Ana — 统一算法、系统、架构与企业架构的语义精化关系
> **前置概念**:
> [Semantic Space](semantic_space.md) ·
> [Computational Semantics Framework](../../04_formal/11_computational_models/01_computational_semantics_framework.md) ·
> [Software Architecture Formalization](../../04_formal/10_architecture_semantics/01_software_architecture_formalization.md)
> **后置概念**:
> [Enterprise Architecture Frameworks](../../06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) ·
> [Strategic DDD in Rust](../../06_ecosystem/14_enterprise_architecture/05_strategic_domain_driven_design_in_rust.md)
> **主要来源**:
> [ISO/IEC/IEEE 42010:2022](https://www.iso.org/standard/74296.html) ·
> [ISO/IEC/IEEE 15288:2023](https://www.iso.org/standard/63711.html) ·
> [Shaw & Garlan 1996, *Software Architecture: Perspectives on an Emerging Discipline*](https://doi.org/10.5555/257572) ·
> [Herlihy & Shavit 2011, *The Art of Multiprocessor Programming*](https://www.sciencedirect.com/book/9780123973375/the-art-of-multiprocessor-programming)

---

> **Bloom 层级**: L3-L5
**变更日志**:

- v1.0 (2026-07-30): 初始版本——建立算法/系统/架构/企业架构四层映射索引

---

## 一、分层模型总览

本知识库将 Rust 语义空间组织为四个相互精化的层次：

```text
┌─────────────────────────────────────────────────────────────┐
│  L7 企业架构 (Enterprise Architecture)                        │
│  关注点：业务战略、组织边界、价值流、投资组合                 │
│  代表框架：TOGAF / Zachman / FEAF / DDD                      │
├─────────────────────────────────────────────────────────────┤
│  L5-L6 架构语义 (Architecture Semantics)                      │
│  关注点：视图/视点、组件、连接器、约束、模式                 │
│  代表标准：ISO 42010 / ADR / ATAM                            │
├─────────────────────────────────────────────────────────────┤
│  L3-L4 系统语义 (System Semantics)                            │
│  关注点：进程、消息、并发、分布、反应式、容错               │
│  代表模型：Actor / π / CSP / Reactive Manifesto              │
├─────────────────────────────────────────────────────────────┤
│  L4 算法语义 (Algorithm Semantics)                            │
│  关注点：正确性、终止性、复杂度、精化、等价                 │
│  代表方法：Hoare Logic / 精化演算 / 算法等价                │
└─────────────────────────────────────────────────────────────┘
```

**精化方向（Refinement）**：每一层向下层提供实现约束，向上层提供行为保证。

---

## 二、四层映射表

| 层次 | 核心问题 | 形式化工具 | Rust 工程映射 | 权威来源 |
|---|---|---|---|---|
| **算法语义** | 单个计算是否满足规约？ | Hoare 三元组、精化、不变式 | 函数契约、 unsafe 前置条件、迭代器正确性 | Hoare 1969；Back 1981；Dijkstra 1976 |
| **系统语义** | 多个计算如何交互？ | 进程代数、状态机、trace 语义 | `tokio`/`async-std`、`crossbeam`、Actor crate | Milner 1989；Hoare 1985；Harel 1987 |
| **架构语义** | 组件如何组织并满足质量属性？ | 视图/视点、连接器、约束 | workspace/crate/module、trait 作为契约、ADR | ISO 42010；Shaw & Garlan 1996 |
| **企业架构** | 系统组合如何支撑业务目标？ | 价值流、能力图、上下文映射 | workspace 组合、bounded context、防腐层 | TOGAF 10；Evans 2003；Vernon 2016 |

---

## 三、精化关系详解

### 3.1 算法语义 → 系统语义

- **精化含义**：一组满足各自 Hoare 契约的算法，在并发/分布式组合时是否仍满足全局规约？
- **关键问题**：原子性、线性化（linearizability）、组合推理（compositional reasoning）。
- **Rust 映射**：
  - `std::sync::Mutex` 提供互斥，但不保证组合无死锁；
  - `crossbeam::channel` 提供无锁/少锁消息传递；
  - `tokio::sync` 提供异步感知同步原语。
- **权威来源**：Herlihy & Shavit 2011（线性化与并发正确性）。

### 3.2 系统语义 → 架构语义

- **精化含义**：进程/消息/状态机等系统模型如何被封装为架构组件与连接器？
- **关键问题**：组件边界、接口契约、质量属性（性能、安全、可维护性）。
- **Rust 映射**：
  - crate = 组件；
  - trait = 端口/服务契约；
  - workspace = 架构视图；
  - ADR 记录关键架构决策。
- **权威来源**：ISO/IEC/IEEE 42010:2022（视图-视点-利益相关者-关注）。

### 3.3 架构语义 → 企业架构

- **精化含义**：多个系统/产品的架构如何对齐业务战略与组织能力？
- **关键问题**：子域分类、限界上下文、上下文映射、投资组合管理。
- **Rust 映射**：
  - workspace 组合对应业务能力组合；
  - bounded context 对应 crate 边界；
  - 防腐层（ACL）对应 FFI / HTTP / gRPC 边界。
- **权威来源**：TOGAF ADM；Evans — Domain-Driven Design。

---

## 四、Rust 工程决策树

```text
我需要论证什么？
├── 单个函数/算法的正确性
│   └── → 算法语义：Hoare 逻辑、Kani/Prusti/Creusot
├── 并发/异步交互的正确性
│   └── → 系统语义：Actor/CSP/π、Miri、loom
├── 模块/组件/质量属性
│   └── → 架构语义：ISO 42010 视图、ADR、ATAM
└── 业务战略与系统组合
    └── → 企业架构：TOGAF、DDD 上下文映射
```

---

## 五、反例与边界

### 反例："算法正确 ⟹ 系统正确"

**错误**。两个各自正确的算法组合后可能产生数据竞争、死锁或活性（liveness）失败。例如，两个线程分别持有不同锁并请求对方持有的锁，即使每个线程的局部算法正确，全局也会死锁。

### 反例："架构文档足够 ⟹ 企业目标达成"

**错误**。架构文档（ADR、视图）必须映射到业务能力与价值流；否则会出现"技术完美但业务无用"的系统。

### 边界：形式化成本

- 算法语义可高度形式化；
- 系统语义形式化成本上升（并发、分布、故障模型）；
- 架构与企业架构通常以半形式化决策框架（ATAM、TOGAF ADM）为主。

---

## 六、相关概念导航

| 主题 | 权威页 |
|---|---|
| 计算语义框架 | [`concept/04_formal/11_computational_models/01_computational_semantics_framework.md`](../../04_formal/11_computational_models/01_computational_semantics_framework.md) |
| 算法语义 | [`concept/04_formal/08_algorithm_semantics/01_hoare_logic_for_rust.md`](../../04_formal/08_algorithm_semantics/01_hoare_logic_for_rust.md) |
| 系统语义 | [`concept/04_formal/09_system_semantics/01_actor_model_semantics.md`](../../04_formal/09_system_semantics/01_actor_model_semantics.md) |
| 架构语义 | [`concept/04_formal/10_architecture_semantics/01_software_architecture_formalization.md`](../../04_formal/10_architecture_semantics/01_software_architecture_formalization.md) |
| 企业架构 | [`concept/06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md`](../../06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md) |
| 并发模型表达力 | [`concept/04_formal/12_concurrency_models/02_expressiveness_of_concurrent_models.md`](../../04_formal/12_concurrency_models/02_expressiveness_of_concurrent_models.md) |

---

## International Authority References（国际权威来源）

- [ISO/IEC/IEEE 42010:2022 — Systems and software engineering — Architecture description](https://www.iso.org/standard/74296.html)
- [ISO/IEC/IEEE 15288:2023 — Systems and software engineering — System life cycle processes](https://www.iso.org/standard/63711.html)
- [Shaw & Garlan 1996, *Software Architecture: Perspectives on an Emerging Discipline*](https://doi.org/10.5555/257572)
- [Herlihy & Shavit 2011, *The Art of Multiprocessor Programming*](https://www.sciencedirect.com/book/9780123973375/the-art-of-multiprocessor-programming)
- [TOGAF Standard, 10th Edition](https://pubs.opengroup.org/togaf-standard/)
- [Evans 2003, *Domain-Driven Design*](https://www.dddcommunity.org/book/evans_2003/)

---

## 嵌入式测验（Embedded Quiz）

### 测验 1：层次识别

**问题**：论证 `tokio::sync::Mutex` 在异步上下文中的正确使用属于哪一层语义？

- A. 算法语义
- B. 系统语义
- C. 架构语义
- D. 企业架构

**答案**：B。它关注并发/异步交互的正确性。

### 测验 2：精化方向

**问题**：企业架构中的限界上下文（bounded context）向下精化到 Rust 工程最可能对应什么？

- A. 单个函数
- B. crate / workspace 边界
- C. 一条 async/await 语句
- D. 一个测试用例

**答案**：B。限界上下文是组织/业务边界，向下映射为代码库边界。

---

## 🧭 思维导图（Mindmap）

```text
Semantic Layer Alignment
├── 算法语义
│   └── Hoare 逻辑 / 精化 / 终止性
├── 系统语义
│   └── Actor / CSP / π / Reactive
├── 架构语义
│   └── 视图/视点 / 组件 / 连接器 / ADR
└── 企业架构
    └── TOGAF / DDD / 上下文映射
```

---

> **版本信息**: v1.0 · 2026-07-30 · 对齐 Rust 1.97.1+ (Edition 2024)
