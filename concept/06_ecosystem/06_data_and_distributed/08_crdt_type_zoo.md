> **本节关键术语**: CRDT · 状态基（State-based / CvRDT） · 操作基（Op-based / CmRDT） · 联结半格（Join Semilattice） · 单调性（Monotonicity） · 强最终一致性（Strong Eventual Consistency） — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)

# CRDT 谱系：状态基、操作基与合并格形式化

> **EN**: CRDT Type Zoo: State-based, Op-based, and the Merge Lattice
> **Summary**: The CRDT spectrum — state-based CvRDTs with semilattice merges (G-Counter, PN-Counter, OR-Set, LWW-Register, MV-Register, RGA), op-based CmRDTs with commutative operations, the merge-lattice formalization, Rust implementations (rust-crdt, yrs, automerge-rs), and divergence counterexamples from non-commutative merges.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶 / 工程 / 研究者]
> **内容分级**: [专家级]
> **Bloom 层级**: L4-L6
> **权威来源**: 本文件为 `concept/` 权威页：CRDT 谱系与合并格形式化的唯一深度解释；[L3 谱系页](../../03_advanced/00_concurrency/07_parallel_distributed_pattern_spectrum.md) §5.3 保留导航式概览并链接回本页。
> **A/S/P 标记**: **S+A+P** — Structure + Application + Procedure
> **双维定位**: C×Ana — 分析无协调复制数据类型的收敛证明与工程实现
> **前置概念**: [L4 线性化与一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md) · [L5 五模型定义矩阵](../../05_comparative/00_paradigms/04_five_models_definition_matrix.md) · [L3 谱系页 §5.3](../../03_advanced/00_concurrency/07_parallel_distributed_pattern_spectrum.md)
> **后置概念**: [L6 因果序与向量时钟](09_causal_ordering_vector_clocks.md) · [L6 分布式共识](06_distributed_consensus.md) · [L6 数据工程](05_data_engineering.md)

---

> **来源**: [Shapiro, Preguiça, Baquero, Zawirski, *A Comprehensive Study of Convergent and Commutative Replicated Data Types*, INRIA RR-7506 / SSS 2011（HAL 全文）](https://hal.inria.fr/inria-00555588/) · Shapiro et al., *Conflict-free Replicated Data Types*, SSS 2011 会议版（DOI：[10.1007/978-3-642-24550-3_29](https://doi.org/10.1007/978-3-642-24550-3_29)） · [rust-crdt 仓库](https://github.com/rust-crdt/rust-crdt) · [yrs / y-crdt 仓库](https://github.com/y-crdt/y-crdt) · [docs.rs/yrs](https://docs.rs/yrs/latest/yrs/) · [Wikipedia: Conflict-free replicated data type](https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type)
> **国际权威来源（2026-07-13 补录）**: **P0** [std::collections 官方文档](https://doc.rust-lang.org/std/collections/)（各 CRDT 实现所依托的标准库集合类型语义，curl 200 实测 2026-07-13）

---

## 📑 目录

- [CRDT 谱系：状态基、操作基与合并格形式化](#crdt-谱系状态基操作基与合并格形式化)
  - [📑 目录](#-目录)
  - [一、问题：无协调的复制](#一问题无协调的复制)
  - [二、状态基 CRDT（CvRDT）：合并格形式化](#二状态基-crdtcvrdt合并格形式化)
  - [三、CvRDT 类型动物园](#三cvrdt-类型动物园)
  - [四、操作基 CRDT（CmRDT）：交换律](#四操作基-crdtcmrdt交换律)
  - [五、Rust 实现生态](#五rust-实现生态)
    - [5.1 rust-crdt：教科书式 CvRDT 库](#51-rust-crdt教科书式-cvrdt-库)
    - [5.2 yrs：协作编辑的 CmRDT 引擎](#52-yrs协作编辑的-cmrdt-引擎)
    - [5.3 automerge-rs：工业级 CRDT 文档库](#53-automerge-rs工业级-crdt-文档库)
    - [5.4 选型速查](#54-选型速查)
  - [六、反例：非交换合并导致发散](#六反例非交换合并导致发散)
    - [反例 1：「最后写胜出」用本地墙钟](#反例-1最后写胜出用本地墙钟)
    - [反例 2：把非单调更新塞进 CvRDT](#反例-2把非单调更新塞进-cvrdt)
    - [反例 3：CmRDT 跑在会丢消息的通道上](#反例-3cmrdt-跑在会丢消息的通道上)
    - [反例 4：tombstone 无界增长](#反例-4tombstone-无界增长)
  - [七、定理链与相关概念](#七定理链与相关概念)
  - [八、认知路径](#八认知路径)
  - [权威来源索引](#权威来源索引)

---

## 一、问题：无协调的复制

分布式系统中，多个副本（replica）并发修改同一份数据，而网络分区使**协调**（锁、leader、共识）不可用或代价过高。问题：能否让副本**各自修改、事后合并**，且数学上保证所有副本**必然收敛**到同一状态？

Shapiro 等人（2011）的答案：**CRDT（Conflict-free Replicated Data Type，无冲突复制数据类型）**——把「合并」约束为带特定代数性质的操作，使收敛性成为**类型层面的保证**而非协议层面的祈祷。

```text
强最终一致性（SEC）= 最终一致性 + 收敛性：
  最终一致性：若无新更新，所有副本最终状态相同；
  收敛性    ：收到相同更新集的副本 ⟹ 状态相同（立即、无需等待）。

  CRDT 的目标：按构造保证 SEC ⟹ 无需共识、无需回滚、无需冲突解决人工介入。
```

> **过渡**: 实现 SEC 有两条路线——让**状态**可合并（CvRDT），或让**操作**可交换（CmRDT）。前者更易于推理，先从它开始。

---

## 二、状态基 CRDT（CvRDT）：合并格形式化

CvRDT 的形式定义（Shapiro 2011, §3）：

```text
CvRDT 是一个四元组 (S, s⁰, q, u, m)：
  S   : 状态集（副本的载荷）
  s⁰  : 初始状态
  q   : 查询函数（只读，不改状态）
  u   : 更新函数（本地修改状态）
  m   : 合并函数  m : S × S → S

收敛的充分条件（合并格定理）：
  (S, m) 构成联结半格（join semilattice），即 m 满足：
    幂等律  m(s, s)      = s
    交换律  m(s₁, s₂)    = m(s₂, s₁)
    结合律  m(m(s₁,s₂),s₃) = m(s₁,m(s₂,s₃))
  且所有更新 u 对由 m 诱导的偏序 ⊑ 单调：
    s ⊑ t  ⟺  m(s, t) = t          （t 至少包含 s 的全部信息）
    u 单调 ⟺  对一切 s： s ⊑ u(s)
```

**为什么这就够了**：半格的任意有限子集有**唯一**最小上界。各副本独立演化、以任意顺序、任意次数两两合并（幂等性吸收重复传递，交换/结合律吸收顺序差异）⟹ 全部收敛到更新集的唯一 join ⟹ SEC 得证。

**工程变体：δ-CRDT（增量状态）**。全量状态合并的传输成本随状态增长；δ-CRDT 只传播「自上次同步以来的状态增量」δ（要求增量本身也在同一半格中且与原状态可 join），周期性全量同步作兜底 ⟹ 保留合并格全部代数性质，把平均消息大小从 O（状态） 降到 O（增量）。这是 rust-crdt 与工业 Gossip 协议的标准优化。

> **过渡**: 形式骨架抽象，但整个 CRDT 动物园都是这一定理的实例——每个类型 = 一个具体的半格 + 一组单调更新。

---

## 三、CvRDT 类型动物园

| 类型 | 状态 S | 合并 m | 单调更新 | 查询 |
|:---|:---|:---|:---|:---|
| **G-Counter**（只增计数器） | `Map<NodeId, Nat>` | 逐键取 `max` | 只增本节点计数 | 所有键求和 |
| **PN-Counter**（可增减计数器） | 两个 G-Counter（P, N） | 两个半格分别合并 | 增 P / 增 N | sum(P) − sum(N) |
| **G-Set**（只增集合） | 元素集合 | 并集 `∪` | 添加元素 |  membership |
| **2P-Set**（两阶段集合） | 添加集 A + 删除集 R（均 G-Set） | A、R 分别并集 | 加入 A / 加入 R | x ∈ A ∧ x ∉ R |
| **OR-Set**（ Observed-Remove Set，可重加集合） | `Map<Elem, Set<Tag>>`（唯一标签） | 按键合并标签集（删除只移除观察到的标签） | add(e)：生成新 tag；remove(e)：移除当前观察到的全部 tag | tag 集非空 |
| **LWW-Register**（最后写胜出寄存器） | `(value, timestamp)` | 取时间戳大者（平手按预定义序，如节点序） | 写 `(v, now())` | value |
| **MV-Register**（多值寄存器） | `Set<(value, version)>`（版本向量） | 取版本向量极大元集（并发写全部保留） | 写时携带自己的新版本 | 并发值集合 |
| **RGA**（Replicated Growable Array，序列 CRDT） | 带唯一 ID `(timestamp, node)` 的节点集 + `insertAfter` 指针 | 节点集并集，按 ID 全序重排读出 | `insertAfter(id, v)`：生成新节点指向 id | 按 ID 序遍历的序列 |

三个关键设计直觉：

1. **G-Counter 的 max 合并**：每个节点只动自己的计数槽 ⟹ 更新单调；`max` 幂等/交换/结合 ⟹ 半格成立。
2. **OR-Set 的标签**：「删除」不是状态的逆操作（那会破坏单调性），而是**移除已观察到的标签**；删除后其他副本并发 add 生成的新标签存活 ⟹ 「并发 add 赢过 remove」（add-wins 语义）。
3. **LWW vs MV 的取舍**：LWW 用物理时钟选唯一胜者 ⟹ 简单但**丢并发写**；MV 保留所有并发写 ⟹ 不丢数据但把冲突暴露给应用层。选择取决于「数据丢失」与「冲突处理复杂度」哪个更可接受（对照 [L4 一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md)：CRDT 处于最终一致端，用收敛证明换取 AP 可用性）。
4. **RGA 的插入语义**：「在元素 a 之后插入 x」编码为「新节点携带 a 的唯一 ID」⟹ 并发插入同一位置按节点 ID 全序定先后，**无需操作变换（OT）、天然收敛**；节点只增不删（删除编码为 tombstone）保证单调性。这是协作编辑引擎（yrs、automerge）共同的代数底座。

---

## 四、操作基 CRDT（CmRDT）：交换律

CmRDT 不传递状态，而传递**操作**：

```text
CmRDT 收敛的充分条件（Shapiro 2011, §4）：
  所有「并发」操作两两交换：对任意并发（无因果序）的更新 op₁, op₂ 与状态 s，
    op₂(op₁(s)) = op₁(op₂(s))
  （因果相关的操作则按因果序交付——依赖 [L6 向量时钟](09_causal_ordering_vector_clocks.md) 或因果广播）

对偶定理（Shapiro 2011）：CvRDT 与 CmRDT 表达能力等价——
  状态合并 m(s₁,s₂)  对应  「把 s₂ 相对 s₁ 的增量作为操作重放」；
  ⟹ 选型不是表达力问题，而是传输开销（状态大小 vs 操作日志）与
    通道假设（CvRDT 容忍重复/乱序消息；CmRDT 要求恰好一次因果交付）问题。
```

| 维度 | CvRDT（状态基） | CmRDT（操作基） |
|:---|:---|:---|
| 消息内容 | 全量（或增量）状态 | 单个操作 |
| 通道要求 | 幂等容忍（重复/乱序无害） | 要求因果、恰好一次交付 |
| 合并点 | 接收方 merge | 接收方 apply |
| 典型场景 | 状态小、消息可丢（Gossip） | 操作小、通道可靠（协作编辑日志） |
| Rust 实例 | `rust-crdt` 的 `GCounter`/`Orswot` | `yrs` 的 YATA 操作序列 |

---

## 五、Rust 实现生态

### 5.1 rust-crdt：教科书式 CvRDT 库

[rust-crdt](https://github.com/rust-crdt/rust-crdt) 提供 `GCounter`、`PNCounter`、`Orswot`（OR-Set）、`MVReg` 等，类型参数化的「actor 标识」保证每个节点只动自己的槽：

```rust,ignore
use crdts::{GCounter, CmRDT};

let mut a: GCounter<&str> = GCounter::new();
let mut b: GCounter<&str> = GCounter::new();

a.apply(a.inc("node-a"));   // 操作也是值：CmRDT 风格的 apply
b.apply(b.inc("node-b"));
b.apply(b.inc("node-b"));

a.apply_merge(&b);          // CvRDT 风格的合并
assert_eq!(a.read(), 3);    // 1 + 2：交换/结合/幂等 ⟹ 顺序无关
```

### 5.2 yrs：协作编辑的 CmRDT 引擎

[yrs](https://github.com/y-crdt/y-crdt)（[docs.rs/yrs](https://docs.rs/yrs/latest/yrs/)）是 Yjs 的 Rust 移植，实现 YATA（Yet Another Transformation Approach）算法：把文档建模为带唯一 ID 的字符序列，插入操作携带左右邻居 ID ⟹ 并发插入天然交换，无需操作变换（OT）的中心化服务器。

```rust,ignore
use yrs::{Doc, GetString, Text, Transact};

let doc = Doc::new();
let text = doc.get_or_insert_text("doc");
let mut txn = doc.transact_mut();
text.insert(&mut txn, 0, "hello");
assert_eq!(text.get_string(&txn), "hello");
// 两个副本交换 update（操作日志）后收敛到同一文档——CmRDT 路线
```

### 5.3 automerge-rs：工业级 CRDT 文档库

[automerge-rs](https://github.com/automerge/automerge)（[docs.rs/automerge](https://docs.rs/automerge/latest/automerge/)）是 Automerge 的 Rust 核心实现（仓库原名 automerge-rs，已更名为 automerge；JS 绑定经 WASM 复用同一核心），把 JSON 文档建模为**操作日志 + RGA 风格序列**的 CmRDT：

- **数据模型**：map / list / text 三类容器 + 标量寄存器（MV 语义，并发写以冲突值集合保留）；
- **变更日志**：每次事务产生一个带哈希链的 change（可签名、可回溯任意历史版本），合并即重放对方缺失的 change；
- **收敛保证**：change 的应用幂等、交换、结合 ⟹ 满足 §二 合并格条件的操作基对偶，离线编辑后按任意顺序合并必收敛——这是「本地优先软件」（local-first）的存储底座。

```rust,ignore
use automerge::{transaction::Transactable, AutoMerge, ReadDoc, ROOT};

let mut doc = AutoMerge::new();
let mut tx = doc.transaction();
tx.put(&ROOT, "title", "hello")?;   // 寄存器写入 = 一条 change
tx.commit();
// 两个副本交换 change 后 doc.merge(&mut other)?——CmRDT 路线，与 yrs 同族
```

### 5.4 选型速查

| 场景 | 推荐 | 理由 |
|:---|:---|:---|
| 分布式计数/集合（指标、库存） | rust-crdt（CvRDT） | 状态小、Gossip 友好、幂等容忍 |
| 富文本协作编辑 | yrs（CmRDT/YATA） | 操作序列紧凑、与 Yjs 生态互通 |
| 寄存器/配置项 | LWW-Register（带时钟漂移警告）或 MV-Register | 按「可容忍丢并发写」与否二选一 |
| JSON 文档协作 / 本地优先应用 | automerge | 文档模型丰富、change 可签名、JS 生态互通 |
| 大状态 × 弱网环境的集合/计数同步 | δ-CRDT（增量状态）+ 周期全量兜底 | 平均消息从 O(状态) 降到 O(增量)，代数性质不变 |

共同判据：先看**通道假设**（可丢/乱序 ⟹ CvRDT；可靠因果交付 ⟹ CmRDT 可选），再看**状态/操作大小比**，最后看**生态互通**需求。

---

## 六、反例：非交换合并导致发散

### 反例 1：「最后写胜出」用本地墙钟

```text
反例：LWW 用不可靠的物理时钟
  节点 A（时钟快 5 分钟）写 x=1，节点 B（时钟准）后写 x=2。
  B 的写入时间戳 < A 的 ⟹ 合并后全网保留 x=1——
  「后写」输给了「快钟」⟹ 语义违反直觉，且时钟回拨时写入永久丢失。

修正：MV-Register（保留并发写）或用混合逻辑时钟（HLC）；
     见 [L6 因果序与向量时钟](09_causal_ordering_vector_clocks.md)。
```

### 反例 2：把非单调更新塞进 CvRDT

```rust,ignore
// ❌ 反例：PN-Counter 用单个 Map + 直接减法（而非 P/N 双计数器）
fn decrement_wrong(map: &mut HashMap<NodeId, i64>, me: NodeId) {
    *map.get_mut(&me).unwrap() -= 1; // 对 ⊑ 不单调：状态「变小」了
}
// 后果：合并（逐键 max）会「复活」已被减掉的计数 ⟹ 副本发散、计数虚高。
```

修正：PN-Counter 必须用**两个** G-Counter；减量编码为 N 计数器的**增量**——单调性是合并格定理的前提，违反它没有任何补救。

### 反例 3：CmRDT 跑在会丢消息的通道上

CmRDT 要求恰好一次、因果序交付；直接跑在 UDP/Gossip 上，一条 `remove` 操作丢失 ⟹ 某副本永远保留已删元素 ⟹ 发散且**不可自愈**（CvRDT 则靠下一次全量状态合并自愈）。选型错误比实现错误更致命。

### 反例 4：tombstone 无界增长

RGA/OR-Set 的「删除」不是移除状态，而是**追加墓碑**（tombstone：标记某标签/节点已删）——这是单调性的直接代价。于是：

```text
长期运行的文档/集合：状态大小 = 存活元素 + 全部历史删除的墓碑
  ⟹ 内存与合并开销随「写入+删除总量」单调增长，而非随「当前数据量」增长。
```

工程补救（都不改变收敛语义，只回收已达成共识的墓碑）：

1. **版本向量 GC**：当某墓碑的因果历史已被**所有**副本观察（用 [L6 向量时钟](09_causal_ordering_vector_clocks.md) 判定），则可安全物理删除；
2. **快照 + 重放截断**：automerge/yrs 类系统定期把历史压缩为快照，操作日志只保留快照之后的增量；
3. **分层存储**：冷墓碑下沉到只读段，热路径只合并近期标签。

共同前提：墓碑回收是**需要协调的优化**（证明「全网都已知」本身是一次轻量共识），而 CRDT 的收敛性不依赖它——这正是「正确性靠代数、性能靠工程」的分层。

---

## 七、定理链与相关概念

| 编号 | 命题 | 前提 | 结论 |
|:---|:---|:---|:---|
| T-CR-01 | 合并格定理 | m 幂等/交换/结合 + u 单调 | 任意合并序列 ⟹ 收敛到唯一 join ⟹ SEC |
| T-CR-02 | G-Counter 收敛 | `max` 是半格 join + 每节点只动己槽 | 任意消息顺序/重复 ⟹ 计数一致 |
| T-CR-03 | OR-Set add-wins | 标签唯一 + remove 只删已观察标签 | 并发 add(e) 与 remove(e) ⟹ e 存活 |
| T-CR-04 | CvRDT ≡ CmRDT（表达力） | 状态增量可重放为操作 | 两路线可互相模拟 ⟹ 选型是工程问题 |
| T-CR-05 | 非单调更新发散 | 违反 u 单调 | 合并可能复活旧信息 ⟹ SEC 不成立（反例 2） |

**相关概念**:

- [L4 线性化与一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md) —— CRDT 在谱系最终一致端的位置；线性化 ↔ SEC 的强度对照
- [L6 因果序与向量时钟](09_causal_ordering_vector_clocks.md) —— CmRDT 因果交付与 MV-Register 版本向量的形式基础
- [L6 分布式共识](06_distributed_consensus.md) —— 需要线性化时走共识；CRDT 是无共识路线
- [L3 谱系页 §5.3 CRDT 概览](../../03_advanced/00_concurrency/07_parallel_distributed_pattern_spectrum.md) —— 工程谱系视角（本页为形式化权威页）
- [L5 五模型定义矩阵](../../05_comparative/00_paradigms/04_five_models_definition_matrix.md) —— 分布式模型在坐标系中的位置
- [L6 数据工程](05_data_engineering.md) —— CRDT 在数据管道中的应用场景

---

## 八、认知路径

> **认知路径**: SEC 目标 ⟹ 合并格定理 ⟹ 类型动物园 ⟹ CvRDT/CmRDT 对偶 ⟹ Rust 生态 ⟹ 发散反例。

学习顺序建议：先在 [L4 一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md) 中定位 CRDT 的强度等级（最终一致但可证收敛），再读本页 §2 的合并格定理——全页只有这一个定理是真正需要吃透的；§3 动物园按 G-Counter → OR-Set → MV-Register 的顺序读（单调性技巧递进）；最后对照 [L6 向量时钟](09_causal_ordering_vector_clocks.md) 理解版本向量如何充当「偏序的压缩表示」。

**核心推理链**: 交换/结合/幂等 ⟹ 唯一 join ⟹ 无需协调的收敛 ⟹ AP 可用性——CRDT 用代数性质把「冲突解决」从运行时协议问题变成了编译期（类型层）的设计问题。

---

## 权威来源索引

- Shapiro, M., Preguiça, N., Baquero, C., Zawirski, M. *A Comprehensive Study of Convergent and Commutative Replicated Data Types*. INRIA Research Report 7506, 2011. [HAL 全文](https://hal.inria.fr/inria-00555588/)
- Shapiro, M., Preguiça, N., Baquero, C., Zawirski, M. *Conflict-free Replicated Data Types*. SSS 2011, LNCS 6976. [DOI](https://doi.org/10.1007/978-3-642-24550-3_29) · [Springer](https://link.springer.com/chapter/10.1007/978-3-642-24550-3_29)
- [rust-crdt — 教科书式 CRDT 库](https://github.com/rust-crdt/rust-crdt)
- [yrs — Yjs 的 Rust 移植（y-crdt 组织）](https://github.com/y-crdt/y-crdt) · [docs.rs/yrs](https://docs.rs/yrs/latest/yrs/)
- [automerge-rs — Automerge 的 Rust 核心（仓库已更名 automerge）](https://github.com/automerge/automerge) · [docs.rs/automerge](https://docs.rs/automerge/latest/automerge/)
- [Wikipedia: Conflict-free replicated data type](https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type)

> **相关文件**: [同层：因果序与向量时钟](09_causal_ordering_vector_clocks.md) · [同层：分布式共识](06_distributed_consensus.md) · [L4 一致性谱系](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md)
>
> **文档版本**: 1.0 ｜ **最后更新**: 2026-07-12 ｜ **状态**: ✅ W5-4 新建（Rust 1.97 对齐）

## ⚠️ 反例与陷阱

### 反例：CRDT 状态比较缺少 `PartialEq`（rustc 1.97.0 实测）

```rust,compile_fail,E0369
struct GCounter { counts: Vec<(u32, u64)> }

impl GCounter {
    fn merge(&mut self, other: &GCounter) {
        for (id, c) in &other.counts {
            if let Some(slot) = self.counts.iter_mut().find(|(i, _)| i == id) {
                slot.1 = slot.1.max(*c);
            }
        }
    }
}

fn main() {
    let a = GCounter { counts: vec![(1, 5)] };
    let b = GCounter { counts: vec![(1, 3)] };
    if a == b { println!("same"); } // ❌ 未实现 PartialEq
}
```

**错误**：`E0369 binary operation == cannot be applied to type GCounter`。

### ✅ 修正：derive 相等性

```rust
#[derive(PartialEq, Eq)]
struct GCounter { counts: Vec<(u32, u64)> }

impl GCounter {
    fn merge(&mut self, other: &GCounter) {
        for (id, c) in &other.counts {
            if let Some(slot) = self.counts.iter_mut().find(|(i, _)| i == id) {
                slot.1 = slot.1.max(*c);
            }
        }
    }
}
```

