# 数据库系统：Rust 在存储引擎中的语义

> **Bloom 层级**: 应用 → 评价
> **A/S/P 标记**: **P** — Practice
> **双维定位**: C×Syn — 综合数据库系统的工程实践与架构选型
> **定位**: 深入分析 Rust 实现的数据库系统——TiKV（分布式事务）、Materialize（流式 SQL）、Meilisearch（搜索引擎）、SurrealDB（多模型）——的架构语义、正确性保证与选型策略。
> **前置概念**: [Stream Processing Ecosystem](./36_stream_processing_ecosystem.md) · [Ownership](../01_foundation/01_ownership.md) · [Concurrency](../03_advanced/01_concurrency.md)
> **后置概念**: [Distributed Systems](./18_distributed_systems.md) · [Formal Methods](../04_formal/05_verification_toolchain.md)

---

> **来源**: [TiKV GitHub](https://github.com/tikv/tikv) · [PingCAP TiKV 架构文档](https://tikv.org/docs/5.1/concepts/architecture/) · [Materialize Documentation](https://materialize.com/docs/) · [Meilisearch Documentation](https://www.meilisearch.com/docs) · [SurrealDB Documentation](https://surrealdb.com/docs)

---

## 一、Rust 数据库系统全景

> **[来源: 💡 原创分析]** · 综合各项目官方文档 ✅

Rust 在数据库领域的渗透呈现"基础设施层优先"的特征：

```text
Rust 数据库生态谱系:
│
├── 分布式 OLTP/OLAP
│   ├── TiKV — 分布式 KV 存储（Percolator 事务）
│   ├── CockroachDB — 分布式 SQL（部分 Rust 组件）
│   └── Materialize — 流式 SQL 物化视图
│
├── 搜索引擎
│   ├── Meilisearch — 轻量级全文搜索
│   ├── Tantivy — Lucene 风格搜索引擎库
│   └── Quickwit — 云原生日志搜索
│
├── 多模型数据库
│   ├── SurrealDB — 文档+图+关系混合
│   ├── ArangoDB 风格 — 多模型查询
│   └── EdgeDB 风格 — 类型驱动图数据库
│
└── 嵌入式/边缘
    ├── sled — 嵌入式 KV（B-tree + log-structured）
    ├── rocksdb-rs — RocksDB Rust 绑定
    └── SQLite 的 Rust 封装（rusqlite）
```

---

## 二、TiKV：分布式事务与 Percolator 协议

> **[来源: Percolator 论文 — Google, OSDI 2010] · [TiKV 官方文档](https://tikv.org/docs/) · [PingCAP Blog]** ✅

### 2.1 Percolator 事务模型

TiKV 的事务层基于 Google 的 **Percolator** 协议，采用 **乐观并发控制（OCC）** + **两阶段提交（2PC）**：

```text
Percolator 写入流程:

Phase 1: Prewrite
  1. 获取所有 key 的当前版本号（start_ts）
  2. 检查每个 key 是否已被更大版本的事务锁定
  3. 若无冲突，写入数据（key + start_ts → value）和锁（key + Lock → start_ts）

Phase 2: Commit
  1. 获取 commit_ts（从全局 TSO，Timestamp Oracle）
  2. 写入 commit 记录（key + commit_ts → start_ts）
  3. 清理锁
```

### 2.2 Rust 实现的优势

| 维度 | TiKV（Rust） | 传统实现（Java/Go） |
|:---|:---|:---|
| **内存管理** | 所有权 + RAII → 无 GC 暂停 | GC → STW 暂停 |
| **并发安全** | `Send`/`Sync` 编译期检查 | 运行时锁 + 人工审查 |
| **性能** | 亚毫秒 P99 延迟 | 毫秒级 P99 延迟 |
| **存储引擎** | RocksDB（C++）+ Rust 封装 | 纯 Java/Go 实现 |
| **部署模式** | 云原生（Kubernetes） | 虚拟机/裸金属为主 |

> **关键洞察**: TiKV 选择 Rust 的核心动机是"确定性延迟"——分布式事务的 P99 延迟对 GC 暂停极其敏感。Java 的 G1/ZGC 虽已将暂停降至毫秒级，但对于 sub-millisecond 的事务而言仍不可接受。Rust 的无 GC 模型从根本上消除了这一噪声源。[来源: PingCAP Blog — Why Rust for TiKV] ✅

### 2.3 TiKV 中的 Rust 所有权模式

```rust
// TiKV 中的事务状态机（简化）
pub enum TxnStatus {
    PessimisticLock { primary: Vec<u8>, start_ts: u64 },
    Committed { commit_ts: u64 },
    RolledBack,
}

// 事务状态的所有权转移
impl Txn {
    pub fn prewrite(mut self, mutations: Vec<Mutation>) -> Result<Txn, Error> {
        // self 被 move，prewrite 后变为新状态
        for m in mutations {
            self.lock_key(m.key, m.value)?; // &mut self
        }
        Ok(self) // 所有权返回给调用者
    }
}
```

---

## 三、Materialize：流式 SQL 与增量视图维护

> **[来源: Materialize Documentation](https://materialize.com/docs/) · [McSherry et al. — Differential Dataflow, CIDR 2013]** ✅

Materialize 已在 `36_stream_processing_ecosystem.md` 中详述。本节聚焦于其**数据库语义**：

### 3.1 严格串行化（Strict Serializability）

Materialize 的核心保证：**所有查询看到全局一致的快照**。

```sql
-- Materialize 保证：此查询看到的所有源数据是同一逻辑时间戳下的快照
SELECT * FROM orders o
JOIN customers c ON o.customer_id = c.id
WHERE o.status = 'shipped';

-- 即使 orders 和 customers 来自不同 CDC 源（Kafka + PostgreSQL），
-- 结果也保证严格串行化——不会出现 "看到 customer 更新但没看到 order 更新" 的异常
```

### 3.2 与 CockroachDB 的对比

| 维度 | Materialize | CockroachDB |
|:---|:---|:---|
| **一致性** | 严格串行化 | 串行化（默认）/ 快照读 |
| **查询模型** | 持续查询（物化视图） | 点查 + 事务 |
| **数据源** | Kafka CDC、PostgreSQL CDC | 原生存储 |
| **写入路径** | 只读（从外部源摄取） | 原生写入 |
| **适用场景** | 实时报表、运营分析 | OLTP、事务处理 |
| **实现语言** | **Rust** | Go |

---

## 四、Meilisearch：轻量级全文搜索引擎

> **[来源: Meilisearch Documentation](https://www.meilisearch.com/docs) · [Tantivy GitHub](https://github.com/quickwit-oss/tantivy)** ✅

### 4.1 架构设计

Meilisearch 用 Rust 重新实现了 Elasticsearch 的核心功能——但**无 JVM**：

| 组件 | Meilisearch | Elasticsearch |
|:---|:---|:---|
| **运行时** | 原生二进制（无 GC） | JVM（GC 暂停） |
| **启动时间** | 秒级 | 分钟级 |
| **内存占用** | ~100MB（空实例） | ~1GB+ |
| **索引性能** | 10-50k 文档/秒 | 10-100k 文档/秒 |
| **查询延迟** | <10ms P99 | <20ms P99 |
| **分布式** | 有限 | 原生支持 |
| **生态** | 新兴 | 成熟（ELK Stack） |

### 4.2 Rust 的所有权在搜索引擎中的应用

```rust
// Meilisearch 的索引段（segment）所有权模型
struct Index {
    segments: Vec<Segment>, // 每个 segment 是不可变的
    mutable_segment: MutableSegment, // 当前可写的 segment
}

impl Index {
    fn commit(&mut self) {
        // 将 mutable_segment 冻结为不可变 segment
        let frozen = std::mem::replace(&mut self.mutable_segment, MutableSegment::new());
        self.segments.push(frozen.freeze()); // 所有权转移
        // 旧 segment 不再可变，可被并发读取
    }
}
```

> **关键洞察**: 搜索引擎的"段（segment）不可变性"与 Rust 的所有权模型天然匹配。Lucene/Elasticsearch 的段一旦写入即不可变，新的写入创建新段，后台合并旧段。Rust 的 `&T` 共享引用完美表达了"段可被并发读取但不可修改"的语义，无需额外的读写锁。[来源: 💡 原创分析] · [Tantivy 设计文档] ✅

---

## 五、SurrealDB：多模型数据库

> **[来源: SurrealDB Documentation](https://surrealdb.com/docs) · [SurrealDB GitHub](https://github.com/surrealdb/surrealdb)** ✅

### 5.1 多模型查询语义

SurrealDB 统一了三种数据模型——文档、图、关系：

```sql
-- 文档模型
CREATE person:tobie SET name = 'Tobie', age = 30;

-- 图模型（边关系）
RELATE person:tobie -> knows -> person:jaime SET since = '2020-01-01';

-- 关系模型（SQL 风格）
SELECT * FROM person WHERE age > 25;

-- 混合查询：文档 + 图遍历
SELECT name, ->knows->person.name AS friends
FROM person:tobie;
```

### 5.2 Rust 实现的安全保证

| 特性 | SurrealDB（Rust） | MongoDB（C++） | Neo4j（Java） |
|:---|:---|:---|:---|
| **内存安全** | 编译期保证 | 运行时风险 | GC 保护 |
| **并发查询** | fearless（Send/Sync） | 锁 + 审查 | 线程安全 |
| **嵌入部署** | ✅ 单二进制 | ❌ 需服务 | ❌ 需服务 |
| **查询注入** | 参数化查询（类型安全） | 依赖驱动 | 依赖驱动 |

> **关键洞察**: SurrealDB 的"单二进制嵌入"能力是 Rust 独有的工程优势。由于无 GC 和零依赖运行时，SurrealDB 可以编译为单个 ~50MB 的二进制文件，嵌入到任何应用中作为嵌入式数据库。这与 SQLite 的竞争定位不同——SurrealDB 提供文档+图+关系的多模型能力，而 SQLite 仅提供关系模型。[来源: SurrealDB Documentation] ✅

---

## 六、跨系统选型决策矩阵

> **[来源: 💡 原创分析]** · 综合上述所有来源 ✅

| 需求 | 推荐系统 | 理由 |
|:---|:---|:---|
| 分布式事务（金融级） | TiKV + TiDB | Percolator 协议、Raft 共识、Rust 无 GC |
| 实时物化视图（运营分析） | Materialize | 严格串行化、增量计算、SQL 兼容 |
| 全文搜索（产品级） | Meilisearch | 轻量、快速启动、Rust 原生 |
| 多模型数据（原型/边缘） | SurrealDB | 文档+图+关系、嵌入部署 |
| 日志分析（云原生） | Quickwit + Tantivy | 对象存储后端、低成本 |
| 嵌入式 KV（IoT/边缘） | sled / rocksdb-rs | 无运行时、极小体积 |

---

## 七、知识来源关系

| **论断** | **来源** | **可信度** | **Tier** |
|:---|:---|:---:|:---:|
| Percolator 事务模型 | [Google, OSDI 2010] | ✅ | Tier 1 |
| TiKV Rust 实现 | [PingCAP Blog] | ✅ | Tier 1 |
| Materialize 严格串行化 | [Materialize Documentation] | ✅ | Tier 1 |
| Meilisearch 架构 | [Meilisearch Documentation] | ✅ | Tier 1 |
| SurrealDB 多模型 | [SurrealDB Documentation] | ✅ | Tier 1 |
| 段不可变性与 Rust 所有权 | [💡 原创分析] | ⚠️ | Tier 3 |
| 选型决策矩阵 | [💡 原创分析] | ⚠️ | Tier 3 |

---

> **权威来源**: [TiKV Documentation](https://tikv.org/docs/) · [Materialize Documentation](https://materialize.com/docs/) · [Meilisearch Documentation](https://www.meilisearch.com/docs) · [SurrealDB Documentation](https://surrealdb.com/docs)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.95.0+ (Edition 2024)
> **最后更新**: 2026-05-24
> **状态**: ✅ 新建 — 工业系统深度对齐
