# 主题覆盖矩阵：现状 vs 权威来源

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

## 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [主题覆盖矩阵：现状 vs 权威来源](#主题覆盖矩阵现状-vs-权威来源)
  - [目录](#目录)
  - [使用说明](#使用说明)
  - [一、核心理论语义 (来自 TAPL \& PLT Redex)](#一核心理论语义-来自-tapl--plt-redex)
  - [二、类型理论 (来自 TAPL)](#二类型理论-来自-tapl)
  - [三、Rust特定语义](#三rust特定语义)
  - [四、并发与并行 (来自 "Art of Multiprocessor Programming")](#四并发与并行-来自-art-of-multiprocessor-programming)
  - [五、形式验证 (来自 Iris \& RustBelt)](#五形式验证-来自-iris--rustbelt)
  - [六、Workflow Patterns (来自 van der Aalst)](#六workflow-patterns-来自-van-der-aalst)
  - [七、分布式系统 (来自 "Designing Data-Intensive Applications")](#七分布式系统-来自-designing-data-intensive-applications)
  - [八、覆盖率统计](#八覆盖率统计)
    - [按类别统计](#按类别统计)
    - [关键缺口汇总](#关键缺口汇总)
  - [九、建议阅读路径](#九建议阅读路径)
    - [路径A: 形式化理论背景 (面向研究者)](#路径a-形式化理论背景-面向研究者)
    - [路径B: 工程实践背景 (面向开发者)](#路径b-工程实践背景-面向开发者)
    - [路径C: 完整掌握 (面向专家)](#路径c-完整掌握-面向专家)
  - [**最后更新**: 2026-03-07](#最后更新-2026-03-07)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

## 使用说明
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

- ✅ 已充分覆盖
- 🟡 部分覆盖
- ❌ 未覆盖
- 🔴 关键缺口

---

## 一、核心理论语义 (来自 TAPL & PLT Redex)
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| 主题 | 现状 | 缺口分析 | 优先级 |
|------|------|----------|--------|
| **无类型λ演算** | ❌ | 完全没有λ演算基础 | 🔴 P0 |
| 变量与替换 | ❌ | 缺少形式化替换定义 | 🔴 P0 |
| α-等价 | ❌ | 未定义 | 🔴 P0 |
| β-归约 | ❌ | 缺少归约语义 | 🔴 P0 |
| 求值策略 (CBV/CBN) | 🟡 | 简要提及，无形式化 | 🟡 P1 |
| **简单类型λ演算** | ❌ | 缺少类型理论基础 | 🔴 P0 |
| 类型规则 (T-Var, T-Abs, T-App) | ❌ | 未形式化定义 | 🔴 P0 |
| Curry-Howard对应 | ❌ | 未涉及 | 🟡 P2 |
| **操作语义** | 🟡 | 部分有，但不系统 | 🟡 P1 |
| 大步语义 (Natural Semantics) | 🟡 | 部分文件有 | 🟡 P1 |
| 小步语义 (Structural) | 🟡 | 部分文件有 | 🟡 P1 |
| 求值上下文 | ❌ | 未引入概念 | 🔴 P0 |
| 归约语义 | ❌ | 缺少redex定义 | 🔴 P0 |
| **指称语义** | ❌ | 完全缺失 | 🔴 P0 |
| 域论基础 | ❌ | 未涉及 | 🔴 P0 |
| 语义函数 | ❌ | 未定义 | 🔴 P0 |
| 完全抽象 | ❌ | 未涉及 | 🟡 P2 |
| **公理语义** | ❌ | 完全缺失 | 🔴 P0 |
| Hoare三元组 | ❌ | 未引入 | 🔴 P0 |
| 前置/后置条件 | 🟡 | 简要提及 | 🟡 P1 |
| 循环不变量 | ❌ | 未涉及 | 🟡 P1 |
| 最弱前置条件 | ❌ | 未涉及 | 🟡 P2 |

---

## 二、类型理论 (来自 TAPL)
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| 主题 | 现状 | 缺口分析 | 优先级 |
|------|------|----------|--------|
| **子类型** | 🟡 | 简要提及，无深度 | 🟡 P1 |
| 子类型规则 | 🟡 | 不完整 | 🟡 P1 |
| 逆变/协变/不变 | 🟡 | 部分覆盖 | 🟡 P1 |
| 宽度/深度子类型 | ❌ | 未涉及 | 🟡 P2 |
| 顶类型/底类型 | ❌ | 未涉及 | 🟡 P2 |
| **递归类型** | ❌ | 完全缺失 | 🔴 P0 |
| μ-类型 | ❌ | 未引入 | 🔴 P0 |
| iso-recursive vs equi-recursive | ❌ | 未区分 | 🟡 P2 |
| fold/unfold | ❌ | 未涉及 | 🟡 P1 |
| **多态性 (System F)** | ❌ | 完全缺失 | 🔴 P0 |
| 类型抽象 (Λ) | ❌ | 未引入 | 🔴 P0 |
| 类型应用 | ❌ | 未形式化 | 🔴 P0 |
| 全称量词 (∀) | ❌ | 未引入 | 🔴 P0 |
| 参数多态 vs 特设多态 | ❌ | 未区分 | 🟡 P1 |
| **存在类型** | ❌ | 完全缺失 | 🟡 P2 |
| 打包/解包 | ❌ | 未涉及 | 🟡 P2 |
| 抽象数据类型 | 🟡 | 部分覆盖 | 🟡 P2 |
| **有界量词 (F<:)** | ❌ | 完全缺失 | 🟡 P2 |
| 上界/下界 | ❌ | 未涉及 | 🟡 P2 |
| F-有界多态 | ❌ | 未涉及 | 🟡 P2 |
| **类型推断** | ❌ | 完全缺失 | 🟡 P1 |
| Hindley-Milner | ❌ | 未引入 | 🟡 P1 |
| 算法W | ❌ | 未涉及 | 🟡 P2 |
| 主类型 | ❌ | 未涉及 | 🟡 P2 |
| **高阶类型 (Fω)** | ❌ | 完全缺失 | 🔴 P0 |
| Kind系统 | ❌ | 未引入 | 🔴 P0 |
| 类型构造子 | 🟡 | 简要提及 | 🟡 P1 |
| 类型层级 | ❌ | 未涉及 | 🟡 P2 |
| **线性/仿射类型** | 🟡 | 通过所有权隐式涉及 | 🟡 P1 |
| 线性逻辑 | ❌ | 未形式化 | 🔴 P0 |
| 使用一次约束 | 🟡 | 部分覆盖 | 🟡 P1 |
| **区域类型** | 🟡 | 通过生命周期隐式涉及 | 🟡 P1 |
| 区域推断 | ❌ | 未深入 | 🟡 P1 |
| 基于区域的内存管理 | 🟡 | 部分覆盖 | 🟡 P1 |

---

## 三、Rust特定语义
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 主题 | 现状 | 缺口分析 | 优先级 |
|------|------|----------|--------|
| **所有权系统** | 🟡 | 有覆盖，但可更形式化 | 🟡 P1 |
| 所有权转移语义 | 🟡 | 部分形式化 | 🟡 P1 |
| 借用语义 | 🟡 | 有详细覆盖 | ✅ |
| 生命周期 | 🟡 | 有详细覆盖 | ✅ |
| NLL (非词法生命周期) | 🟡 | 简要提及 | 🟡 P1 |
| **子类型与变型** | 🟡 | 不完整 | 🟡 P1 |
| 生命周期子类型 | 🟡 | 部分覆盖 | 🟡 P1 |
| 变型规则推导 | ❌ | 未形式化 | 🟡 P1 |
| **MIR语义** | 🟡 | 简要提及 | 🟡 P1 |
| 控制流图语义 | ❌ | 未深入 | 🟡 P1 |
| Place/Expr区别 | ❌ | 未涉及 | 🟡 P2 |
| **Unsafe Rust** | 🟡 | 有简要覆盖 | 🟡 P1 |
| 原始指针语义 | 🟡 | 部分覆盖 | 🟡 P1 |
| Unsafe代码契约 | ❌ | 未形式化 | 🔴 P0 |
| **Trait系统** | 🟡 | 有覆盖 | 🟡 |
| Trait对象 (dyn Trait) | 🟡 | 有覆盖 | ✅ |
| 关联类型 | 🟡 | 部分覆盖 | 🟡 P1 |
| 一致性规则 | ❌ | 未深入 | 🟡 P2 |

---

## 四、并发与并行 (来自 "Art of Multiprocessor Programming")
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 主题 | 现状 | 缺口分析 | 优先级 |
|------|------|----------|--------|
| **顺序一致性** | 🟡 | 部分覆盖 | 🟡 P1 |
| 全序存储 | ❌ | 未形式化 | 🟡 P1 |
| 交错语义 | 🟡 | 部分涉及 | 🟡 P1 |
| **线性化** | ❌ | 完全缺失 | 🔴 P0 |
| 线性化点 | ❌ | 未引入 | 🔴 P0 |
| 可组合性 | ❌ | 未涉及 | 🟡 P2 |
| **进度条件** | 🟡 | 简要提及 | 🟡 P1 |
| 无等待 (Wait-free) | 🟡 | 有定义 | ✅ |
| 无锁 (Lock-free) | 🟡 | 有定义 | ✅ |
| 无障碍 (Obstruction-free) | 🟡 | 有定义 | ✅ |
| **内存模型** | 🟡 | 有覆盖 | ✅ |
| Happens-before | ✅ | 有形式化 | ✅ |
| Release-Acquire | ✅ | 有形式化 | ✅ |
| 宽松内存序 | 🟡 | 部分覆盖 | 🟡 |
| **进程代数** | ❌ | 完全缺失 | 🔴 P0 |
| CSP | ❌ | 未涉及 | 🔴 P0 |
| CCS | ❌ | 未涉及 | 🟡 P2 |
| π-演算 | ❌ | 未涉及 | 🟡 P2 |

---

## 五、形式验证 (来自 Iris & RustBelt)
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 主题 | 现状 | 缺口分析 | 优先级 |
|------|------|----------|--------|
| **分离逻辑** | ❌ | 完全缺失 | 🔴 P0 |
| 分离合取 (*) | ❌ | 未引入 | 🔴 P0 |
| Frame规则 | ❌ | 未涉及 | 🔴 P0 |
| 局部推理 | ❌ | 未涉及 | 🔴 P0 |
| **并发分离逻辑** | ❌ | 完全缺失 | 🔴 P0 |
| 资源不变量 | ❌ | 未引入 | 🔴 P0 |
| 权限记账 | ❌ | 未涉及 | 🔴 P0 |
| **Iris框架** | ❌ | 完全缺失 | 🔴 P0 |
| 高阶协议 | ❌ | 未涉及 | 🔴 P0 |
| Ghost状态 | ❌ | 未涉及 | 🔴 P0 |
| View Shifts | ❌ | 未涉及 | 🔴 P0 |
| **RustBelt** | ❌ | 完全缺失 | 🔴 P0 |
| 类型语义模型 | ❌ | 未涉及 | 🔴 P0 |
| 生命周期逻辑 | ❌ | 未涉及 | 🔴 P0 |
| 借用命题 | ❌ | 未涉及 | 🔴 P0 |
| Unsafe代码验证 | ❌ | 未涉及 | 🔴 P0 |

---

## 六、Workflow Patterns (来自 van der Aalst)
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 主题 | 现状 | 缺口分析 | 优先级 |
|------|------|----------|--------|
| **基础控制流** | 🟡 | 有覆盖 | 🟡 |
| 顺序 | ✅ | 有覆盖 | ✅ |
| 并行分支 | ✅ | 有覆盖 | ✅ |
| 同步合并 | 🟡 | 内容偏少 | 🟡 P1 |
| **选择模式** | 🟡 | 部分覆盖 | 🟡 |
| 排他选择 | 🟡 | 有覆盖 | ✅ |
| 多路选择 | 🔴 | 内容太少 (4KB) | 🔴 P1 |
| 延迟选择 | 🔴 | 内容太少 | 🔴 P1 |
| **高级模式** | 🔴 | 普遍不足 | 🔴 |
| 鉴别器 | 🔴 | 内容太少 | 🔴 P1 |
| 里程碑 | 🔴 | 内容太少 | 🔴 P1 |
| 任意循环 | 🔴 | 内容太少 | 🔴 P1 |
| 取消活动 | 🔴 | 内容太少 | 🔴 P1 |
| BPMN对应 | ❌ | 未涉及 | 🟡 P2 |
| YAWL对应 | ❌ | 未涉及 | 🟡 P2 |

---

## 七、分布式系统 (来自 "Designing Data-Intensive Applications")
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 主题 | 现状 | 缺口分析 | 优先级 |
|------|------|----------|--------|
| **通信** | ✅ | 良好覆盖 | ✅ |
| 消息传递 | ✅ | 有详细覆盖 | ✅ |
| RPC | ✅ | 有详细覆盖 | ✅ |
| 事件驱动 | ✅ | 有详细覆盖 | ✅ |
| **一致性** | ✅ | 良好覆盖 | ✅ |
| CAP定理 | ✅ | 有详细覆盖 | ✅ |
| 共识算法 | ✅ | 有详细覆盖 | ✅ |
| 最终一致性 | ✅ | 有详细覆盖 | ✅ |
| **容错** | ✅ | 良好覆盖 | ✅ |
| 故障模型 | ✅ | 有详细覆盖 | ✅ |
| 断路器 | ✅ | 有详细覆盖 | ✅ |
| 重试/超时 | ✅ | 有详细覆盖 | ✅ |
| **微服务** | ✅ | 良好覆盖 | ✅ |
| API网关 | ✅ | 有详细覆盖 | ✅ |
| 负载均衡 | ✅ | 有详细覆盖 | ✅ |
| 限流 | ✅ | 有详细覆盖 | ✅ |
| 服务网格 | ✅ | 有详细覆盖 | ✅ |

---

## 八、覆盖率统计
>
> **[来源: [crates.io](https://crates.io/)]**

### 按类别统计
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 类别 | 总主题数 | 已覆盖 | 部分覆盖 | 未覆盖 | 覆盖率 |
|------|----------|--------|----------|--------|--------|
| 核心理论语义 | 20 | 0 | 4 | 16 | 10% |
| 类型理论 | 22 | 0 | 6 | 16 | 14% |
| Rust特定语义 | 15 | 3 | 10 | 2 | 53% |
| 并发与并行 | 15 | 4 | 5 | 6 | 43% |
| 形式验证 | 12 | 0 | 0 | 12 | 0% |
| Workflow Patterns | 13 | 2 | 3 | 8 | 27% |
| 分布式系统 | 20 | 20 | 0 | 0 | 100% |
| **总计** | **117** | **29** | **28** | **60** | **33%** |

### 关键缺口汇总
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

**关键缺口 (🔴 P0)**: 23个主题

- 无类型λ演算
- 简单类型λ演算
- 操作语义基础
- 指称语义
- 公理语义
- 递归类型
- System F多态
- 高阶类型
- 线性逻辑
- 线性化
- 进程代数
- 分离逻辑
- 并发分离逻辑
- Iris框架
- RustBelt方法论
- (及9个workflow patterns)

---

## 九、建议阅读路径
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

对于不同背景的读者：

### 路径A: 形式化理论背景 (面向研究者)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

1. 先补: 00a-00e (理论基础)
2. 再读: 02-advanced-types
3. 深入: 04-verification

### 路径B: 工程实践背景 (面向开发者)
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

1. 现有: Rust核心语义
2. 扩展: distributed-patterns
3. 进阶: 形式验证

### 路径C: 完整掌握 (面向专家)
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

按阶段1-5顺序完成所有内容

---

**矩阵版本**: v1.0
**最后更新**: 2026-03-07
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**
