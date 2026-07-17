# 测验：数据库与存储生态（L6）

> **EN**: Database and Storage Ecosystem Quiz
> **Summary**: L6 standalone quiz on the Rust database ecosystem: access libraries (SQLx/Diesel/SeaORM/Toasty), connection pooling, and Rust-built database systems (TiKV/Materialize/Meilisearch/SurrealDB).
> **受众**: [专家]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` L6 生态层独立测验。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**: [数据库访问](../06_data_and_distributed/02_database_access.md) · [数据库系统](../06_data_and_distributed/04_database_systems.md) · [sqlx docs](https://docs.rs/sqlx)（P2 生态权威 API 文档，curl 200 实测 2026-07-13）
>
> **前置概念**:
> [数据库访问](../06_data_and_distributed/02_database_access.md) ·
> [数据库系统](../06_data_and_distributed/04_database_systems.md) ·
> [分布式共识](../06_data_and_distributed/06_distributed_consensus.md) ·
> [Rust vs Go（数据基础设施对比）](../../05_comparative/01_systems_languages/03_rust_vs_go.md)

---

> **Bloom 层级**: L2-L4
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题 + 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`）的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: 验证学习者对 L6 数据与分布式子领域（访问层选型 + Rust 原生数据库系统）的掌握。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、数据库访问层选型

本节考查访问层选型：Q1 区分 SQLx 与传统 ORM，Q2 按 API 风格选择 ORM，Q3 考查生产环境连接管理实践。

### Q1. 🟢【单选】SQLx 区别于传统 ORM 的核心特性是？

- A. 类似 ActiveRecord 的运行时（Runtime）对象映射
- B. 编译期 SQL 验证（`query!` 宏（Macro））、零运行时开销、异步（Async）原生
- C. 由 derive 宏生成 schema 的同步查询构建器
- D. 仅支持 SQLite 的嵌入式驱动

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：按 [数据库访问](../06_data_and_distributed/02_database_access.md) §1.1，SQLx 的核心特性是编译期 SQL 验证（`query!` 宏在编译期连接数据库校验查询）、零运行时开销、异步原生——它不是 ORM。C 描述的是 Diesel（类型安全 ORM，schema 由 derive 宏生成）；A 风格接近 SeaORM（异步优先、类似 ActiveRecord 的 API）。

</details>

---

### Q2. 🟢 团队要求"异步优先 + 类似 ActiveRecord 的 API"的 ORM。按权威页定位，应选？

| 选项 | 判断 |
|:---|:---|
| A | Diesel：异步原生且 ActiveRecord 风格 |
| B | SeaORM：异步优先的 ORM，类似 ActiveRecord 的 API |
| C | SQLx：完整的 ActiveRecord ORM |
| D | 直连驱动手写 SQL 是唯一可行路径 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：[数据库访问](../06_data_and_distributed/02_database_access.md) §1.3 明确 SeaORM 的设计定位是"异步优先的 ORM，类似 ActiveRecord 的 API"。A 错：Diesel 是类型安全查询构建器路线（同步为主）；C 错：SQLx 是编译期检查的 SQL 库而非 ORM；D 与生态现状不符。同页 §1.4 还列出 Toasty——Tokio 团队的异步 ORM，定位为应用级查询引擎。

</details>

---

### Q3. 🟡【单选】生产服务访问数据库时，连接管理的推荐做法是？

- A. 每次请求新建 TCP 连接，用完即关
- B. 使用连接池（pool）复用连接，控制并发连接上限
- C. 全局共享一个永不关闭的连接
- D. 每个线程各自维护无上限的私有连接

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：[数据库访问](../06_data_and_distributed/02_database_access.md) §三「连接管理」以连接池（§3.1）为核心：池化复用避免建连开销，上限控制防止打爆数据库。A 建连开销高且易触发数据库连接数限制；C 单连接成为吞吐瓶颈且无法并发事务；D 无上限连接同样会耗尽数据库资源。

</details>

---

### Q4. 🟡 关于查询模式的三条路线，下列哪组对应关系正确？

| 选项 | 判断 |
|:---|:---|
| A | 原始 SQL — 编译期零校验，只能字符串拼接 |
| B | 查询构建器 — 类型安全组合查询；迁移管理 — 用版本化脚本演进 schema |
| C | 迁移管理 — 只能在数据库 GUI 中手工执行 |
| D | 三条路线互斥，一个项目只能选一种 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：[数据库访问](../06_data_and_distributed/02_database_access.md) §二「查询模式」分三条：原始 SQL（§2.1）、查询构建器（§2.2）、迁移管理（§2.3）。B 的对应准确；A 错——SQLx 的 `query!` 宏证明原始 SQL 也能编译期校验；C 错——迁移由版本化脚本工具链执行；D 错——实践中常组合使用（如构建器为主、复杂报表用原始 SQL）。

</details>

---

## 二、Rust 原生数据库系统

本节覆盖 Rust 原生数据库：Q5 考 TiKV 事务层，Q6 辨析 Materialize 的一致性（Coherence）级别，Q7 对比 Meilisearch 与 Elasticsearch 的架构。

### Q5. 🟡【多选】关于 TiKV 的事务层，下列说法正确的有？（选出所有正确项）

- A. 基于 Google 的 Percolator 协议
- B. 采用乐观并发控制（OCC）+ 两阶段提交（2PC）
- C. Prewrite 阶段获取 start_ts、检查锁冲突并写入数据与锁
- D. 使用悲观锁 + 单阶段提交作为唯一路径

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：按 [数据库系统](../06_data_and_distributed/04_database_systems.md) §2.1，TiKV 事务层基于 Google Percolator 协议，采用 OCC + 2PC；Prewrite 阶段获取所有 key 的当前版本号（start_ts）、检查是否被更大版本事务锁定、无冲突则写入数据（key + start_ts → value）与锁。D 与 Percolator 的乐观模型矛盾。

</details>

---

### Q6. 🟡【判断】Materialize 的核心保证是严格串行化（Strict Serializability）：所有查询看到全局一致的快照，即同一逻辑时间戳下的源数据。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：[数据库系统](../06_data_and_distributed/04_database_systems.md) §3.1 明确 Materialize 的核心保证是"所有查询看到全局一致的快照"，其示例强调查询看到的所有源数据处于同一逻辑时间戳。Materialize 的定位是流式 SQL 与增量视图维护，同页 §3.2 给出它与 CockroachDB 的对比。

</details>

---

### Q7. 🔴【单选】Meilisearch 相对 Elasticsearch 的架构优势，按权威页对比表，下列哪项**不成立**？

- A. 原生二进制（无 JVM、无 GC 暂停）
- B. 秒级启动（对比分钟级）
- C. 空实例内存占用约 100MB（对比 1GB+）
- D. 功能完整度全面超越 Elasticsearch，无任何取舍

<details>
<summary>✅ 答案与解析</summary>

**答案：D**

**解析**：[数据库系统](../06_data_and_distributed/04_database_systems.md) §4.1 的对比表列出 Meilisearch 的优势：原生二进制无 GC、秒级启动、空实例约 100MB 内存——它是"用 Rust 重新实现 Elasticsearch 的**核心功能**"的轻量级全文搜索引擎。D 的"全面超越、无取舍"过度推断：轻量化的代价正是功能面的取舍。

</details>

---

### Q8. 🔴 某实时分析平台要求"流式数据进来后，复杂 SQL 视图随数据增量更新且查询结果全局一致"。按权威页，哪项选型与机理匹配？

| 选项 | 判断 |
|:---|:---|
| A | TiKV：其 Percolator 事务直接提供增量物化视图 |
| B | Materialize：流式 SQL + 增量视图维护，严格串行化保证全局一致快照 |
| C | Meilisearch：全文索引天然支持增量 SQL 视图 |
| D | 只能自建：现有 Rust 数据库系统无此能力 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：题干两个关键词——"流式 + 增量视图维护"与"全局一致快照"——正是 [数据库系统](../06_data_and_distributed/04_database_systems.md) §三 Materialize 的定位（流式 SQL 与增量视图维护）与核心保证（严格串行化）。A 错：TiKV 是分布式 KV + 事务层，不做 SQL 物化视图；C 错：Meilisearch 是全文搜索引擎；D 与事实不符。

</details>

---

### Q9. 🔴【多选】评估"用 Rust 构建数据库系统"的生态论据时，按权威页内容，下列哪些系统属于 Rust 构建的代表？（选出所有正确项）

- A. TiKV（分布式事务 KV）
- B. Materialize（流式 SQL）
- C. SurrealDB（多模型数据库）
- D. Meilisearch（全文搜索引擎）

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C、D**

**解析**：[数据库系统](../06_data_and_distributed/04_database_systems.md) §一「Rust 数据库系统全景」依次覆盖：TiKV（§二，分布式事务与 Percolator 协议）、Materialize（§三，流式 SQL 与增量视图维护）、Meilisearch（§四，轻量级全文搜索引擎）、SurrealDB（§五，多模型数据库）。四者共同构成"Rust 适合构建数据基础设施"的生态论据。

</details>

---

### Q10. 🟡【判断】SQLx 的编译期 SQL 验证意味着 `query!` 宏在编译期连接真实数据库校验查询语法与类型，因此编译环境需要可达的数据库或离线数据。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：SQLx "编译期 SQL 验证"的机制（[数据库访问](../06_data_and_distributed/02_database_access.md) §1.1）要求编译时能校验查询——通常通过连接开发数据库完成，生态提供离线模式（`sqlx prepare` 生成的元数据）作为 CI/无数据库环境的绕行。这正是它"零运行时开销"换来的编译期约束。

</details>

---

## 三、分布式共识与 CRDT（W3-b 扩展）

本节（W3-b 扩展）考查分布式基础：Q11 共识算法判定，Q12 考 CvRDT 合并函数必须满足的代数性质。

### Q11. 🟢【单选】按 [分布式共识](../06_data_and_distributed/06_distributed_consensus.md)，Raft 相对 Paxos 的核心设计目标是？

- A. 更高的拜占庭容错能力
- B. 可理解性（understandability）：通过强 leader、日志复制与成员变更的分解降低实现与推理难度
- C. 完全消除网络分区的影响
- D. 支持无领导者的完全对等写入

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：Raft（Ongaro & Ousterhout 2014）的论文目标就是可理解性：把共识分解为 leader 选举、日志复制、安全性与成员变更几个相对独立的子问题。A 错——Raft 是 CFT（崩溃容错）算法，不防拜占庭节点（那是 PBFT/HotStuff 的领域）；C 违反 CAP 直觉，分区下一致性以可用性为代价保持；D 与 Raft 的强 leader 模型相反。Rust 实现代表为 raft-rs。

</details>

---

### Q12. 🟡 状态基 CRDT（CvRDT）的合并函数 `m` 必须满足哪组代数性质？

```rust,ignore
// 伪代码：CvRDT 的 merge 约束
trait CvRdt {
    fn merge(&self, other: &Self) -> Self;
}
// merge(a, b) 必须使 (S, merge) 构成联结半格
```

| 选项 | 判断 |
|:---|:---|
| A | 只需结合律 |
| B | 交换律 + 结合律 + 幂等律（构成 join semilattice），保证任意顺序/重复合并收敛 |
| C | 分配律 + 消去律 |
| D | 无需任何代数性质，靠时间戳裁决即可 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：按 [CRDT 类型谱系](../06_data_and_distributed/08_crdt_type_zoo.md) 的合并格形式化（Shapiro 2011）：状态基 CRDT 的 `merge` 必须满足交换律、结合律、幂等律，使状态集合构成**联结半格（join semilattice）**——三律共同保证副本以任意顺序、任意次数合并都收敛到同一状态（强最终一致性）。D 描述的 LWW 时间戳裁决只是半格的一种具体实例（取 max），不是对性质的豁免。

</details>

---

### Q13. 🟡【多选】关于向量时钟（Fidge/Mattern 算法），下列说法正确的有？（选出所有正确项）

- A. 每个进程维护一个长度为 N 的计数器向量，本地事件自增本地分量
- B. 两个事件的向量时钟不可比较（逐分量互有大小）时，二者是并发的
- C. Lamport 标量时钟与向量时钟表达能力完全等价
- D. 向量时钟可以精确检测因果序 `happens-before`，而标量时钟只能给出与因果序一致的偏序近似

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、D**

**解析**：按 [因果序与向量时钟](../06_data_and_distributed/09_causal_ordering_vector_clocks.md)：向量时钟每进程维护 N 维向量、本地事件自增、消息携带并逐分量取 max（A）；两时钟逐分量比较互有大小即判定并发（B）；D 正确——向量时钟精确刻画 Lamport 1978 定义的 happens-before 偏序，标量时钟只能保持"因果 ⟹ 序号小"的单向蕴含。C 错：标量时钟无法区分并发与因果，表达能力严格弱于向量时钟。

</details>

---

### Q14. 🔴【判断】协作编辑场景（如类 Google Docs）通常选用操作基 CRDT（CmRDT）实现（如 yrs），因为文本序列的并发插入用状态基合并难以天然收敛。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：按 [CRDT 类型谱系](../06_data_and_distributed/08_crdt_type_zoo.md) §5.2，yrs（y-crdt 的 Rust 实现）是协作编辑的 CmRDT 引擎：操作基 CRDT 通过可交换的操作传播（在可靠、至多一次、因果序投递的通道假设下）实现收敛，适合表达文本/序列上的并发插入删除；状态基合并需要把全量序列状态放进半格，工程上不可行。两类 CRDT 在表达能力上等价，但工程适配场景不同。

</details>

---

### Q15. 🔴 某数据平台同时评估流处理与共识组件。按权威页口径，下列哪组"场景—组件"匹配成立？

| 选项 | 匹配 |
|:---|:---|
| A | 需要跨节点就元数据达成一致 ⟹ 用流处理引擎投票 |
| B | 需要日志复制的崩溃容错共识 ⟹ raft-rs（Raft）；需要拜占庭容错 ⟹ PBFT/HotStuff 系实现 |
| C | 需要最终一致的离线协同数据结构 ⟹ 必须上共识算法，CRDT 不收敛 |
| D | 流式增量 SQL 视图 ⟹ 任何 OLTP 数据库都天然支持 |

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：B。

**解析**：B 与 [分布式共识](../06_data_and_distributed/06_distributed_consensus.md) 的算法谱系一致：Raft/Paxos 属 CFT（崩溃容错），PBFT/HotStuff 属 BFT（拜占庭容错），选型按故障模型分界。A 职责错位——共识是独立问题；C 错——CRDT 无需共识即可强最终一致（Q12 的半格性质），共识只在需要全序广播时才引入；D 与 [数据库系统](../06_data_and_distributed/04_database_systems.md) 中 Materialize 的增量视图维护定位矛盾——那是流式 SQL 引擎的专门能力。

</details>

---

> **变更记录**: 2026-07-12 新建（W3-b：L6 数据库/存储 quiz，10 题：单选 3 / 代码阅读 3 / 多选 2 / 判断 2；难度 🟢2 / 🟡5 / 🔴3）；2026-07-13 扩展至 15 题（+5 题「分布式共识与 CRDT」：Raft 设计目标、CvRDT 半格、向量时钟、CmRDT 协作编辑、共识选型；难度 🟢3 / 🟡7 / 🔴5）。
> **内容分级**: [综述级]
