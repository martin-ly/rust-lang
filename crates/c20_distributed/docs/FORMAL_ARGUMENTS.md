# 关键论证与公式概览（草案）

本文件给出与课程/维基定义一致的核心判据与可验证结论，配合本 crate 的实现接口。

1) Quorum 判据（多数派）：

   - 定义：`required_acks(N, Strong|Quorum) = floor(N/2)+1`，`Eventual = 1`。
   - 性质：任意两个多数派集合必相交，保证提交记录至少被一个交集副本持有。
   - 代码：`replication::MajorityQuorum::required_acks`。

2) 线性一致（Linearizability）要点：

   - 判据（口径）：存在将所有操作嵌入到全序中且尊重实时时间先后且符合顺序语义。
   - 实践：领导者写入 + 日志复制 + 读屏障（或租约/只读指数）。
   - 实验：构造并发读写历史，验证可线化（可对接 Jepsen 风格检查）。

3) 一致性哈希再均衡代价：

   - 结论：新增/移除节点时，期望移动数据比例约为 `1/(#nodes)`（含虚拟节点修正）。
   - 代码：`topology::ConsistentHashRing` 实验可观测键迁移比例。

4) Saga 安全性与幂等：

   - 要求：每步 `execute` 与 `compensate` 均应具备幂等性；失败回滚保持存储不变量。
   - 代码：`transactions::{Saga, SagaStep}` 的执行-补偿序列；`storage::IdempotencyStore`。

5) 故障检测（SWIM）与可达性：

   - 要点：基于随机采样与间接探测的概率式检测；误报率与超时参数相关。
   - 代码：`swim::{SwimMemberState, SwimEvent}`；通过仿真设置传播周期与 fanout。

后续计划：

- 引入更严格的规格（TLA+/Ivy/Coq 伪代码）片段与可执行检查点。
- 提供小型基准/属性测试以验证上述结论的可观测性。
