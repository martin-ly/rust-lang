# 一致性（Consistency）

- CAP 与 PACELC、线性一致性、顺序一致性、因果一致性、最终一致性
- 接口：`ConsistencyLevel`
- 课程参考：MIT 6.824、Stanford CS244B、UWash CSE452、CMU 15-440

## CAP/PACELC 简述

- CAP：网络分区下，强一致性与可用性难以同时满足
- PACELC：无分区时在延迟与一致性之间取舍（EL vs EC）

### Wiki/课程对齐

- Wikipedia CAP/PACELC：定义、常见误解与工程解读（如可用性定义差异）。
- 课程作业通常通过引入分区与超时模拟 CAP 的权衡；在无分区实验中验证 PACELC 的延迟-一致性取舍。

## 与接口的映射

- `Strong`：线性一致/多数派提交
- `Quorum`：读写多数派（可配置读写比）
- `Eventual`：最终一致/反熵同步

接口到语义：

- 线性一致读：若 `R + W > N` 且写在领导者任期提交，读触达新值。
- 因果读：维护会话向量或因果 token；读需满足 `deps ⊆ store`。
- 最终一致：反熵收敛；冲突通过 LWW、CRDT 或应用级决策解决。

## 线性一致性与会话保证

- 线性一致性（Linearizability）：每个操作看似在某一时间点原子生效；需要全序点与多数派交集（参见 `replication` 的 R/W 条件）。
- 会话保证：读己之写、单调读、单调写、写后读等；可通过会话向量或会话 token 实现。

实现提示：

- 读路径可使用 `read_index`（Raft）或 `lease read`（带时钟偏差安全界）降低延迟。
- 会话 token 可编码最近写入的 `(term,index)` 或向量时间戳。

## 因果一致性与顺序一致性

- 因果：若 A→B（A 发生在 B 之前并影响 B），所有节点应观察到 A 在 B 之前；无需全局全序。
- 顺序一致性：所有进程看到相同的操作顺序，但该顺序未必与真实时间一致。

工程映射：

- 因果一致可用 `vector clock`/`DSV` 实现；跨分片场景可通过 `sticky session` 或 `causal broadcast`。
- 顺序一致常见于单一副本内的多线程内存模型，对分布式需借助全序广播或单主序列化。

## 实践映射

- `ConsistencyLevel::Strong`：启用多数派写入与读；在超时紧张时可回退到 `Quorum`。
- `ConsistencyLevel::Quorum`：读写分别独立配置 R/W；满足 `R+W>N` 时具线性一致读。
- `ConsistencyLevel::Eventual`：后台反熵（gossip/repair）；读写延迟最佳但允许暂时不一致。

## 进一步阅读

- Wiki：`CAP theorem`、`Consistency models`、`Linearizability`、`Causal consistency`
- 课程：MIT 6.824 Lectures on Replication/Consistency；UWash CSE452 Consistency
- 论文：Spanner（TrueTime 与外部一致性）、Dynamo/Cassandra（最终一致与反熵）、Bayou（会话与因果）
