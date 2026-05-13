# 交叉概念一致性 Diff 报告

> 生成时间: 2026-05-13
> 核心概念数: 20
> 一致性警告: 424

## 原理

本工具检测**同一概念在多个文件中被定义**的情况。根据 SSO（Single Source of Truth）原则，
核心概念应在**唯一的主定义文件**中给出完整定义，其他文件只能使用链接引用，不得重复定义。

## 摘要

| 指标 | 数值 |
|:---|:---|
| 扫描文件数 | 45 |
| 检测核心概念 | 20 |
| 多文件定义概念 | 19 |
| 一致性警告 | 424 |

## 一致性警告详情

| 概念 | 主定义文件 | 重复定义文件 | 行号 | 上下文预览 |
|:---|:---|:---|:---|:---|
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 40 | \|:---\|:---\|:---\|:---\|:---\| \| **唯一所有权** \| 每个值有且仅有一个所有者 \| 检查赋值... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 42 | \| **作用域绑定** \| 所有者离开作用域时值被释放 \| 插入 `drop` 调用 \| 内存泄漏（Safe Rust ... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 181 | > **过渡**: 决策树回答"怎么做"的问题，而定理推理链回答"为什么能这么做"——通过引理、定理、推论的层层演绎，建... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 220 | > **推理链全景**: 引理 L1（所有权唯一性）⟹ 引理 L2（Move 语义一致性）⟹ 定理 T1（RAII 资源... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 224 | \|:---\|:---\|:---\|:---\|:---\|:---\|:---\| \| **L1: 所有权唯一性** \| 每个值有... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 226 | \| **L2: Move 语义一致性** \| 非 Copy 类型发生赋值/传参 \| 原变量标记为 moved，不可再访问... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 229 | \| **T3: 无 Use-After-Free** \| L2 + 区域类型（生命周期） \| 引用不会指向已释放内存 \|... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 232 | \| **T6: Copy trait 安全** \| 类型实现 `Copy` + 仅含标量 \| 按位复制语义等价于原值，无... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 233 | \| **C1: 无所有权 ⟹ 无 Drop 责任** \| 值被 `mem::forget` 或 `ManuallyDro... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 245 | > **一致性检查**: 上述 11 个定理/引理/推论之间无矛盾。完整推理链: > `L1(所有权唯一性) ⟹ L2(... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 772 | > **[来源: Rust Reference: Send]** Send trait 定义跨线程所有权转移的安全性，要... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 777 | > `T: Sync` 的形式化语义：`T: Sync ⇔ &T: Send`，即 T 的共享引用可以安全地跨线程共享。... |
| 所有权 | `01_foundation/03_lifetimes.md` | `01_foundation/02_borrowing.md` | 217 | > **[来源: RustBelt: POPL 2018]** Safe Rust 中不存在数据竞争的形式化定理，基于 ... |
| 所有权 | `01_foundation/03_lifetimes.md` | `02_intermediate/03_memory_management.md` | 51 | > **过渡到属性矩阵**: 从形式化定义出发，内存管理不仅是"堆 vs 栈"的二元区分，而是由多种所有权模型（独占、共... |
| 所有权 | `01_foundation/03_lifetimes.md` | `02_intermediate/03_memory_management.md` | 132 | > **过渡到定理推理链**: 思维导图呈现了内存管理的概念拓扑，但缺乏严格的逻辑推导关系。下一节通过"⟹"标注的定理链... |
| 所有权 | `01_foundation/03_lifetimes.md` | `02_intermediate/03_memory_management.md` | 215 | \|:---\|:---\|:---\|:---\|:---\|:---\|:---\| \| **引理**: Box ⟹ 堆分配 + 唯... |
| 所有权 | `01_foundation/03_lifetimes.md` | `02_intermediate/03_memory_management.md` | 216 | \| **引理**: Box ⟹ 堆分配 + 唯一所有权 \| 单线程 \| 堆内存安全释放 \| 线性逻辑 ⊗ \| 所有堆分配... |
| 所有权 | `01_foundation/03_lifetimes.md` | `02_intermediate/03_memory_management.md` | 224 | > **一致性检查**: Box（独占）⟹ Rc（单线程共享）⟹ Arc（多线程共享）⟹ RefCell（内部可变），形... |
| 所有权 | `01_foundation/03_lifetimes.md` | `02_intermediate/03_memory_management.md` | 226 | > > **关键洞察**: Rc/Arc/RefCell 的定理**不在 L4 形式化范围内**（运行时机制），是工程折... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 191 | > **[RustBelt: POPL 2017 (Jung et al.)]** Rust 的类型系统通过 Send/... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 193 | > **[RustBelt: POPL 2017]** `Send` and `Sync` are formally v... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 195 | > > **[TRPL: Ch16.0]** Fearless concurrency 强调：所有权和类型系统是消除并发... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 313 | > **[RustBelt: POPL 2017]** 定理：Safe Rust 的并发程序无数据竞争。前提为所有权规则... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 356 | \| T1 \| 类型系统排他性 \| `T: Send + Sync` + 借用检查通过 \| ⟹ 编译期排除数据竞争 \| A... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 358 | \| T3 \| Atomic 无锁安全 \| 正确使用 `Ordering` \| ⟹ 原子操作无撕裂 \| C11 内存模型 ... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 365 | > **对应标注**：T1 中"编译期排除数据竞争"为 [`01_foundation/01_ownership.md`... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 1022 | **定义**：`rayon` 是基于**工作窃取（work-stealing）**调度器的数据并行库。它将顺序迭代器（`... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/01_concurrency.md` | 1125 | > **定理**: `rayon` 的数据并行抽象通过 `ParallelIterator` trait 保持了 Rus... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/02_async.md` | 5 | > **层级一致性**: 本文件所有定理与定义均锚定于 L3 抽象层；涉及 L4 形式化公理处已显式标注。前置概念（L1... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/03_unsafe.md` | 653 | > > **新增跨层映射**: `L3::别名模型` ↔ [`L1::所有权`](../01_foundation/01... |
| 所有权 | `01_foundation/03_lifetimes.md` | `03_advanced/03_unsafe.md` | 1156 | > **定理**：`ptr::read` + `ptr::write` 组合 ≠ `*ptr` 解引用。前者是**内存层... |
| 所有权 | `01_foundation/03_lifetimes.md` | `04_formal/01_linear_logic.md` | 27 | > **[学术来源: Pierce 2002, *Types and Programming Languages* (T... |
| 所有权 | `01_foundation/03_lifetimes.md` | `04_formal/01_linear_logic.md` | 29 | > **[学术来源: RustBelt: POPL 2018, Jung et al. *RustBelt: Secur... |
| 所有权 | `01_foundation/03_lifetimes.md` | `04_formal/01_linear_logic.md` | 252 | T1(切消定理) ⟹ L1(线性命题) ⟹ C1(Rust所有权) ⟹ C2(仿射move语义)            ... |
| 所有权 | `01_foundation/03_lifetimes.md` | `04_formal/01_linear_logic.md` | 274 | > **一致性检查**: T1(切消) ⟹ L1(线性性) ⟹ T4(⊗组合) ⟹ C1(所有权) ⟹ C2(仿射mov... |
| 所有权 | `01_foundation/03_lifetimes.md` | `04_formal/02_type_theory.md` | 137 | \| **C2**: 高阶类型 \| System Fω ⟹ **关联类型/高阶 Trait bound** \| 类型构造子... |
| 所有权 | `01_foundation/03_lifetimes.md` | `04_formal/03_ownership_formal.md` | 649 | > **定理（Pin 地址不变性）**：若 `Pin<P<T>>` 被构造且 `T: !Unpin`，则 `P` 指向的... |
| 所有权 | `01_foundation/03_lifetimes.md` | `04_formal/03_ownership_formal.md` | 768 | > > 形式化的别名模型（SB/TB）和所有权逻辑（Oxide）是 Rust 编译器优化假设的理论根基，但程序员日常接触... |
| 所有权 | `01_foundation/03_lifetimes.md` | `05_comparative/01_rust_vs_cpp.md` | 1164 | - **公理**（5 条公设）：不可证明、不可分解的起点——对应软件的类型系统公理、所有权公理 - **演绎**（命题 ... |
| 所有权 | `01_foundation/03_lifetimes.md` | `PostgreSQL_LSIP_Unified_Model.md` | 429 | \| **冲突检测** \| SSI 危险结构检测 / 锁等待 \| 借用检查器（编译期拒绝冲突） \| 合并冲突检测（三向差异... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 220 | > **推理链全景**: 引理 L1（所有权唯一性）⟹ 引理 L2（Move 语义一致性）⟹ 定理 T1（RAII 资源... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 229 | \| **T3: 无 Use-After-Free** \| L2 + 区域类型（生命周期） \| 引用不会指向已释放内存 \|... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 230 | \| **T4: 所有权唯一性 ⟹ mutable borrow 唯一性** \| L1 + 借用检查器接受 \| 同一时间对... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/01_ownership.md` | 245 | > **一致性检查**: 上述 11 个定理/引理/推论之间无矛盾。完整推理链: > `L1(所有权唯一性) ⟹ L2(... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/02_borrowing.md` | 43 | > **过渡**: 权威定义从学术和官方来源确立了借用的语义，而概念属性矩阵则将这些语义转化为可操作的规则对比——&T ... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/02_borrowing.md` | 80 | > **过渡**: 属性矩阵展示了借用规则的静态特征，接下来需要深入其形式化根基——分离逻辑、别名-可变分离定理——以理... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/02_borrowing.md` | 198 | > **过渡**: 决策树回答"怎么做"的问题，而定理推理链回答"为什么能这么做"——通过引理、定理、推论的层层演绎，建... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/02_borrowing.md` | 237 | > **推理链全景**: 引理 L1（&T 共享读安全）⟹ 引理 L2（&mut T 独占写安全）⟹ 定理 T1（AXM... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/02_borrowing.md` | 241 | \|:---\|:---\|:---\|:---\|:---\|:---\|:---\| \| **L1: &T 共享读安全** \| 借用... |
| 借用 | `01_foundation/03_lifetimes.md` | `01_foundation/02_borrowing.md` | 242 | \| **L1: &T 共享读安全** \| 借用检查器接受 &T \| 多个 &T 共存不会导致数据竞争 \| 分离逻辑: 分... |

## 概念分布统计

| 概念 | 定义次数 | 涉及文件数 |
|:---|:---:|:---:|
| Trait | 70 | 10 |
| 泛型 | 59 | 12 |
| Sync | 47 | 11 |
| Unsafe | 47 | 13 |
| 所有权 | 41 | 12 |
| 借用 | 40 | 13 |
| 生命周期 | 37 | 14 |
| Send | 33 | 8 |
| async/await | 23 | 7 |
| Mutex | 13 | 6 |
| Drop | 11 | 3 |
| Copy | 9 | 4 |
| String | 8 | 6 |
| Box | 8 | 5 |
| Clone | 7 | 5 |
| Vec | 7 | 5 |
| Pin | 7 | 5 |
| Result | 5 | 2 |
| Arc | 4 | 3 |
| HashMap | 1 | 1 |
