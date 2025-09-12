# 持续推进路线图（c20_distributed）

目标：按照“课程对标→概念落地→可验证实现→实验复现”的路径，逐步完善。

里程碑 M1：基础完备（当前）

- 文档：课程对标、Wiki 映射、概念模型、关键论证、README 导航（已完成）。
- 代码：`replication` 多数派、`transactions::Saga`、`topology` 一致性哈希、`storage` 幂等接口（已存在）。
- 任务：补充单元/属性测试样例，最小端到端 Demo。

里程碑 M2：一致性与复制增强

- 添加读写一致性策略示例（Strong/Quorum/Eventual 的观测差异）。
- 在 `replication` 增加可插拔仲裁策略（读/写不同策略）。
- 提供 Jepsen 风格历史生成与简单检验脚手架（本地版）。

里程碑 M3：SWIM 参数化与可视化

- 在 `swim` 增加参数：探测周期、fanout、间接探测开关。
- 输出事件轨迹，附带可视化脚本（数据→图）。

里程碑 M4：最小 Raft 实验路径

- 开启 `consensus-raft`：补齐 `AppendEntries`/`RequestVote` 的最小行为与状态机。
- 增加持久化日志接口对接与快照占位。

里程碑 M5：端到端事务样例

- 基于 `transactions::Saga` + `storage::IdempotencyStore`，实现跨分片两步支付/库存示例与补偿。

工程化与质量

- 为核心模块补充属性测试与基准；`benches/` 增加再均衡与 ACK 延迟分布基准。
- 增加 `docs` 中的“实验指南”与“常见陷阱”。

时间建议：M1→M2 1-2 周，M3 1 周，M4 2-3 周，M5 1-2 周（可并行）。
