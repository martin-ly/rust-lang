> **本节关键术语**: 偏序（Partial Order） · 逻辑时钟（Logical Clock） · 向量时钟（Vector Clock） · 因果序（Causal Order） · 并发（Concurrency） · 版本向量（Version Vector） — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)

# 因果序与向量时钟：Lamport 偏序的算法化

> **EN**: Causal Ordering and Vector Clocks
> **Summary**: Lamport's 1978 partial order and logical clocks, the Fidge/Mattern vector clock algorithm, concurrency detection and its counterexamples, causal ordering in Rust distributed libraries (tracing, version vectors), and the contrast with shared-memory happens-before.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶 / 工程 / 研究者]
> **内容分级**: [专家级]
> **Bloom 层级**: L4-L6
> **权威来源**: 本文件为 `concept/` 权威页：分布式因果序、逻辑时钟与向量时钟的唯一深度解释。
> **A/S/P 标记**: **S+A+P** — Structure + Application + Procedure
> **双维定位**: C×Ana — 分析分布式事件排序的形式基础与 Rust 工程应用
> **前置概念**: [L4 线性化与一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md) · [L5 五模型定义矩阵](../../05_comparative/00_paradigms/04_five_models_definition_matrix.md) · [L3 并发编程（共享内存 happens-before）](../../03_advanced/00_concurrency/01_concurrency.md)
> **后置概念**: [L6 CRDT 谱系](08_crdt_type_zoo.md) · [L6 分布式共识](06_distributed_consensus.md) · [L6 流处理生态](03_stream_processing_ecosystem.md)

---

> **来源**: [Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, CACM 21(7), 1978（作者主页 PDF）](https://lamport.azurewebsites.net/pubs/time-clocks.pdf) · [Mattern, *Virtual Time and Global States of Distributed Systems*, 1989（ETH 副本，含 Fidge 向量时钟算法）](https://www.vs.inf.ethz.ch/publ/papers/VirtTimeGlobStates.pdf) · Fidge, C. *Timestamps in Message-Passing Systems That Preserve the Partial Ordering*, Proc. 11th Australian Computer Science Conference, 1988 · [Wikipedia: Vector clock](https://en.wikipedia.org/wiki/Vector_clock) · [Wikipedia: Lamport timestamp](https://en.wikipedia.org/wiki/Lamport_timestamp)

---

## 📑 目录

- [因果序与向量时钟：Lamport 偏序的算法化](#因果序与向量时钟lamport-偏序的算法化)
  - [📑 目录](#-目录)
  - [一、Lamport 1978：偏序与逻辑时钟](#一lamport-1978偏序与逻辑时钟)
    - [1.1 happened-before 关系（分布式语境）](#11-happened-before-关系分布式语境)
    - [1.2 逻辑时钟条件与 Lamport 时钟](#12-逻辑时钟条件与-lamport-时钟)
  - [二、向量时钟：Fidge/Mattern 算法](#二向量时钟fidgemattern-算法)
  - [三、并发检测与反例](#三并发检测与反例)
    - [3.1 正确的并发检测](#31-正确的并发检测)
    - [3.2 反例：用 Lamport 标量做并发检测](#32-反例用-lamport-标量做并发检测)
    - [3.3 反例：向量时钟丢失分量](#33-反例向量时钟丢失分量)
  - [四、Rust 分布式生态中的应用](#四rust-分布式生态中的应用)
  - [五、与共享内存 happens-before 的对照](#五与共享内存-happens-before-的对照)
  - [六、反例与边界](#六反例与边界)
    - [反例：把向量时钟当全局时钟用](#反例把向量时钟当全局时钟用)
    - [反例：N 动态变化时复用定长向量](#反例n-动态变化时复用定长向量)
    - [边界：O(N) 空间的根本限制](#边界on-空间的根本限制)
  - [七、定理链与相关概念](#七定理链与相关概念)
  - [八、认知路径](#八认知路径)
  - [权威来源索引](#权威来源索引)

---

## 一、Lamport 1978：偏序与逻辑时钟

分布式系统没有全局时钟：各节点物理时钟有漂移，消息延迟不可预测。Lamport 在 1978 年的奠基论文中把问题重新表述为——**不需要知道事件的「真实时间」，只需要知道事件的「先后关系」**。

### 1.1 happened-before 关系（分布式语境）

```text
系统 = 进程集合 + 事件集合（发送、接收、本地事件）

happened-before 关系 →（Lamport 1978 定义，三条规则）：
  (HB1) 同一进程内：a 在 b 之前发生 ⟹ a → b；
  (HB2) 消息：send(m) → recv(m)；
  (HB3) 传递性：a → b ∧ b → c ⟹ a → c。

→ 是**偏序**：存在 a ↛ b 且 b ↛ a 的事件对——它们「并发」（concurrent），记 a ∥ b。
```

### 1.2 逻辑时钟条件与 Lamport 时钟

```text
时钟条件：为每个事件 e 赋予时间戳 C(e)，要求
  a → b  ⟹  C(a) < C(b)

Lamport 逻辑时钟算法（每个进程维护整数计数器 Cᵢ）：
  (LC1) 本地事件/发送前：Cᵢ := Cᵢ + 1；
  (LC2) 发送消息 m 时附带 Cᵢ；
  (LC3) 接收方：Cⱼ := max(Cⱼ, C(m)) + 1。

性质：满足时钟条件 ⟹ 可推出因果序。
缺陷：**逆命题不成立**——C(a) < C(b) 推不出 a → b（可能是并发事件恰好编号小）。
      ⟹ Lamport 时钟是「偏序的保守近似」：只能说先后，不能说并发。
```

> **过渡**: 要让「时间戳比较」精确对应因果序（双向），标量不够——需要每个进程一个槽位的向量。

---

## 二、向量时钟：Fidge/Mattern 算法

向量时钟（Fidge 1988；Mattern 1989 独立提出）把标量计数器推广为**长度为 N 的向量**（N = 进程数）：

```text
Vᵢ[j] 的语义：进程 i 所「知道」的进程 j 的最新事件序号。

算法（进程 i 维护向量 Vᵢ）：
  (VC1) 本地事件/发送前：Vᵢ[i] := Vᵢ[i] + 1；
  (VC2) 发送消息 m 时附带整个 Vᵢ；
  (VC3) 接收方 j：对一切 k，Vⱼ[k] := max(Vⱼ[k], V(m)[k])，然后 Vⱼ[j] := Vⱼ[j] + 1。

比较规则（逐分量）：
  V ≤ W   ⟺  对一切 k：V[k] ≤ W[k]
  V < W   ⟺  V ≤ W 且 V ≠ W
  a → b   ⟺  V(a) < V(b)              ⟵ 精确：双向都成立
  a ∥ b   ⟺  V(a) ≰ V(b) 且 V(b) ≰ V(a) ⟵ 并发可判定
```

```text
例（3 进程 P1,P2,P3）：
  P1 本地事件 a：V(a) = (1,0,0)
  P1 发送 m（附 (1,0,0)）；P2 接收后本地事件 b：V(b) = (1,1,0)
  P3 独立本地事件 c：V(c) = (0,0,1)
  比较：V(a) < V(b) ⟹ a → b ✓；V(b) 与 V(c) 不可比较 ⟹ b ∥ c ✓
```

代价与变种：

- **空间 O(N)**：节点数大时向量膨胀 ⟹ 剪枝（定期淘汰不活跃槽）、区间版本向量（RIVV）；
- **版本向量（version vector）**：同一结构用于数据复制——槽位是「副本」，值是「该副本已应用的更新数」，是 [CRDT MV-Register](08_crdt_type_zoo.md) 与 Dynamo 风格存储的并发检测机制（向量时钟侧重事件，版本向量侧重数据版本，数学同构）。

---

## 三、并发检测与反例

### 3.1 正确的并发检测

```text
场景：两个副本并发写同一 key
  副本 A 写 x=1，版本向量 V₁ = (1, 0)
  副本 B 写 x=2，版本向量 V₂ = (0, 1)
  V₁ 与 V₂ 不可比较 ⟹ 并发写 ⟹ 系统必须保留两个值（siblings）
  或按策略合并（MV-Register 语义，见 [L6 CRDT 谱系](08_crdt_type_zoo.md)）。
```

### 3.2 反例：用 Lamport 标量做并发检测

```text
反例（错误的并发判定）：
  P1 事件 a：Lamport 时钟 L(a) = 3
  P2 独立事件 b：L(b) = 2（b 与 a 无消息关系，纯属并发）
  L(b) < L(a) ⟹ 错误结论「b → a」✗

  根因：Lamport 时钟只满足时钟条件的单向（a → b ⟹ L(a) < L(b)），
       逆向不成立 ⟹ 标量比较会把「并发」误判为「先后」。
修正：需要精确并发检测时必须用向量时钟（或更紧凑的矩阵时钟）。
```

### 3.3 反例：向量时钟丢失分量

```text
反例（分量丢失导致因果倒置）：
  消息 m 从 P1 到 P2，但传输层重传时丢了附带向量中的 P3 分量（实现 bug）。
  P2 合并后 Vⱼ[3] 偏小 ⟹ 后续来自 P3 的旧消息被误判为「新」⟹
  已因果超前的状态回退 ⟹ 违反单调性，下游版本向量比较全部失真。
修正：向量作为不可变值整体传递（Rust 中用 `&[u64]` + 长度校验 + serde 版本化 schema）。
```

> **过渡**: 理论就绪后，看 Rust 生态把这些结构用在哪——追踪、存储、协作编辑是三个主战场。

---

## 四、Rust 分布式生态中的应用

| 应用场景 | 机制 | Rust 载体 |
|:---|:---|:---|
| 分布式追踪 | span 因果链（trace_id + parent span，逻辑时钟的特化） | `tracing` + OpenTelemetry（`opentelemetry` crate） |
| 版本化存储 | 版本向量检测并发写 | Dynamo 风格 KV（如 `riak_kv` 理念移植项目）、自研 CRDT 存储 |
| 协作编辑 | 操作 ID ≈ (site, counter) 对，等价于二维向量时钟 | [yrs / y-crdt](https://github.com/y-crdt/y-crdt)（YATA 算法） |
| 事件溯源 | 聚合版本号 = 单槽向量时钟 | `esrs` 等事件溯源 crate |

一个最小可运行的向量时钟骨架（教学版）：

```rust
// 向量时钟：V[k] = 进程 k 的最新已知事件序号
#[derive(Clone, PartialEq, Eq, Debug)]
struct VectorClock(Vec<u64>);

impl VectorClock {
    fn new(n: usize) -> Self { VectorClock(vec![0; n]) }

    // (VC1) 本地事件
    fn tick(&mut self, me: usize) { self.0[me] += 1; }

    // (VC3) 接收消息时合并
    fn merge(&mut self, other: &VectorClock, me: usize) {
        for (a, b) in self.0.iter_mut().zip(&other.0) { *a = (*a).max(*b); }
        self.0[me] += 1;
    }

    // 因果序：逐分量严格小于
    fn happens_before(&self, other: &VectorClock) -> bool {
        self.0.iter().zip(&other.0).all(|(a, b)| a <= b) && self != other
    }

    // 并发：互不可比较
    fn concurrent(&self, other: &VectorClock) -> bool {
        !self.happens_before(other) && !other.happens_before(self) && self != other
    }
}

fn main() {
    let (mut a, mut b) = (VectorClock::new(2), VectorClock::new(2));
    a.tick(0);                       // 进程 0 的事件 a：(1,0)
    let sent = a.clone();
    b.merge(&sent, 1);               // 进程 1 接收后事件 b：(1,1)
    let mut c = VectorClock::new(2);
    c.tick(1);                       // 进程 1 上无消息关系的独立事件 c：(0,1)
    assert!(a.happens_before(&b));   // (1,0) → (1,1)：消息因果
    assert!(a.concurrent(&c));       // (1,0) ∥ (0,1)：无因果 ⟹ 并发
    assert!(!b.concurrent(&c));      // (0,1) → (1,1)：同进程程序序
}
```

---

## 五、与共享内存 happens-before 的对照

Rust 程序员已在共享内存语境见过 happens-before（[L3 并发编程 §3](../../03_advanced/00_concurrency/01_concurrency.md) 的内存序一节）。两个语境的同名关系**形似而义不同**：

| 维度 | 共享内存 happens-before（C11/Rust 内存模型） | 分布式 happened-before（Lamport 1978） |
|:---|:---|:---|
| 事件 | 内存读/写/原子操作 | 发送/接收/本地步 |
| 建立方式 | `Release`/`Acquire` 同步、线程 spawn/join | 消息传递、进程内程序序 |
| 违反的代价 | **数据竞争 = 未定义行为** | 因果倒置 = 语义错误（非 UB） |
| 检测工具 | miri / ThreadSanitizer | 向量时钟运行时比较 |
| 偏序还是全序 | 偏序（并发访问非原子变量即 UB） | 偏序（并发事件合法且常见） |

关键洞察：内存模型的 happens-before 是**规范性**的（程序必须建立它，否则 UB）；Lamport 的 happened-before 是**描述性**的（它天然存在，问题只是如何观测）。向量时钟就是分布式语境下「观测因果」的标准仪器——正如 `Acquire`/`Release` 是共享内存语境下「建立因果」的标准指令。

---

## 六、反例与边界

### 反例：把向量时钟当全局时钟用

向量时钟给出的是**偏序**，不是时间：不能回答「a 和 b 谁离现在更近」「间隔多少毫秒」。需要物理时间界（如租约、TTL）时必须引入真实时钟并处理漂移（Google TrueTime 或 HLC 混合逻辑时钟）。

### 反例：N 动态变化时复用定长向量

节点动态加入/离开的集群中，`V[k]` 的「k」不再稳定 ⟹ 分量错位比较出虚假的因果序。修正：槽位用稳定的节点 ID（UUID）而非数组下标，或采用带代次（epoch）的向量协议。

### 边界：O(N) 空间的根本限制

Fidge/Mattern 已证明精确刻画因果序需要 Ω(N) 信息 ⟹ 向量时钟的 O(N) 是**最优的**，无法靠算法改进绕开；大规模系统只能放弃精确性（概率性因果追踪）或分层聚合。

---

## 七、定理链与相关概念

| 编号 | 命题 | 前提 | 结论 |
|:---|:---|:---|:---|
| T-VC-01 | 时钟条件 | Lamport 时钟算法 (LC1–LC3) | a → b ⟹ L(a) < L(b)（单向） |
| T-VC-02 | 向量时钟精确性 | 算法 (VC1–VC3) + 逐分量比较 | a → b ⟺ V(a) < V(b)（双向） |
| T-VC-03 | 并发可判定 | T-VC-02 的逆否 | V(a)、V(b) 不可比较 ⟺ a ∥ b |
| T-VC-04 | Ω(N) 下界 | 精确因果刻画需区分 N 个进程的历史 | 任何精确因果时钟 ⟹ 每事件至少 N 分量信息 |
| T-VC-05 | 标量误判并发 | T-VC-01 逆命题不成立 | L(a) < L(b) ⟹̸ a → b（反例 §3.2） |

**相关概念**:

- [L6 CRDT 谱系](08_crdt_type_zoo.md) —— 版本向量在 MV-Register 与 CmRDT 因果交付中的直接应用
- [L4 线性化与一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md) —— 因果一致性在谱系中的位置
- [L6 分布式共识](06_distributed_consensus.md) —— 用全序广播「抹平」偏序的另一条路线
- [L3 并发编程](../../03_advanced/00_concurrency/01_concurrency.md) —— 共享内存 happens-before（§五对照的另一极）
- [L5 五模型定义矩阵](../../05_comparative/00_paradigms/04_five_models_definition_matrix.md) —— 分布式模型的坐标
- [L6 流处理生态](03_stream_processing_ecosystem.md) —— 事件时间（event time）与因果序的工程交汇

---

## 八、认知路径

> **认知路径**: 无全局时钟 ⟹ Lamport 偏序 ⟹ 标量时钟（单向） ⟹ 向量时钟（双向精确） ⟹ 并发检测 ⟹ Rust 应用 ⟹ O(N) 边界。

学习顺序建议：先读 [Lamport 1978 原文 PDF](https://lamport.azurewebsites.net/pubs/time-clocks.pdf)（仅 10 页，是分布式计算史上可读性最高的论文之一），再读本页 §2 的向量时钟算法；§4 的 Rust 骨架建议手敲并扩展出第三个进程；最后回读 [L4 一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md) §4，把「因果一致性」从谱系图上的一个名字升级为可操作的判定算法。

**核心推理链**: 物理时钟不可靠 ⟹ 用偏序替代时间 ⟹ 向量编码偏序 ⟹ 并发可判定 ⟹ 版本向量支撑无协调复制——这条链是 Dynamo、CRDT、协作编辑三大工程体系共同的逻辑底座。

---

## 权威来源索引

- Lamport, L. *Time, Clocks, and the Ordering of Events in a Distributed System*. CACM 21(7), 1978, 558–565. [作者主页 PDF](https://lamport.azurewebsites.net/pubs/time-clocks.pdf) · [DOI](https://doi.org/10.1145/359545.359563)
- Fidge, C. *Timestamps in Message-Passing Systems That Preserve the Partial Ordering*. Proc. 11th Australian Computer Science Conference, 1988, 56–66.
- Mattern, F. *Virtual Time and Global States of Distributed Systems*. Proc. International Workshop on Parallel and Distributed Algorithms, 1989. [ETH 副本 PDF](https://www.vs.inf.ethz.ch/publ/papers/VirtTimeGlobStates.pdf)
- [Wikipedia: Vector clock](https://en.wikipedia.org/wiki/Vector_clock) · [Wikipedia: Lamport timestamp](https://en.wikipedia.org/wiki/Lamport_timestamp)

> **相关文件**: [同层：CRDT 谱系](08_crdt_type_zoo.md) · [同层：分布式共识](06_distributed_consensus.md) · [L4 一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md)
>
> **文档版本**: 1.0 ｜ **最后更新**: 2026-07-12 ｜ **状态**: ✅ W5-5 新建（Rust 1.97 对齐）
