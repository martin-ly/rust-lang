# 实验指南（c20_distributed）

1) 复制与一致性

   - 运行：`cargo test -p c20_distributed --test replication_local`
   - 观察：不同 `ConsistencyLevel` 下的 ACK 阈值与成功/失败判据。

2) Saga 补偿

   - 运行：`cargo test -p c20_distributed --test saga` 或示例 `cargo run -p c20_distributed --example e2e_saga`
   - 观察：失败步触发逆序补偿，幂等性要求。

3) 一致性哈希与再均衡

   - 运行：`cargo test -p c20_distributed --test hashring_properties`
   - 观察：`nodes_for` 唯一性与新增节点后的键迁移比例。

4) SWIM 探测

   - 运行：`cargo test -p c20_distributed --test swim_pingreq -- --nocapture`
   - 观察：直接失败但间接探测成功的事件；`swim_round` 的一轮事件序列。

5) 基准（Criterion）

   - 运行：`cargo bench -p c20_distributed`
   - 观察：`ack_quorum_table` 的输出摘要（时间分布将随平台而异）。
