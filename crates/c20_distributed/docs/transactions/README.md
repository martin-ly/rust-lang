# 事务（Transactions）

- SAGA/TCC/2PC/幂等与隔离级别

## SAGA 最小示例

```rust
use c20_distributed::transactions::{Saga, SagaStep};

struct Step;
impl SagaStep for Step {
  fn execute(&mut self) -> Result<(), c20_distributed::DistributedError> { Ok(()) }
  fn compensate(&mut self) -> Result<(), c20_distributed::DistributedError> { Ok(()) }
}

let saga = Saga::new().then(Box::new(Step));
let _ = saga.run();
```

## SAGA 状态机与补偿

- 状态：Pending → Executing(i) → Completed | Compensating(j) → Compensated | Failed
- 每步提供 `execute/compensate`，要求补偿操作可重入且幂等。
- 失败策略：遇到不可恢复错误时自后向前补偿已完成步骤。

## TCC（Try-Confirm-Cancel）

- Try：预留资源；Confirm：提交最终变更；Cancel：释放资源。
- 与 SAGA 的差异：TCC 对资源做“先锁定后提交”，对一致性更强，但需要服务支持两阶段接口。

## 2PC 与协调者

- 协议：Prepare/Commit 两阶段；协调者负责收集参与者的投票并广播提交/中止。
- 局限：协调者单点、阻塞问题（需三阶段或基于共识的协调补救）。
- 工程：将协调者运行在具共识的日志上（如 Raft）以避免脑裂/遗失决定。

## 幂等与重复消息

- 每个事务/步骤带 `idempotency_key`；服务端记录并去重。
- 与 `transport::RetryPolicy` 协作，确保在重试/超时场景下不会产生重复副作用。

## 隔离级别与分布式事务

- 隔离级别：读未提交、读已提交、可重复读、可串行化。
- 可串行化实现：两阶段锁（2PL）或乐观并发控制（OCC）+ 验证；分布式需时间戳或全序日志。
- 外部一致性：依赖 `time/TrueTime` 并在提交时 `commit wait`（Spanner）。

## 进一步阅读

- Wiki：`Saga pattern`, `Two-phase commit`, `TCC`, `Isolation (database systems)`
- 课程：MIT 6.824（Transactions）、CMU 15-445（Concurrency/Recovery）
- 论文/实践：Spanner、Calvin（Deterministic DB）、Sagas（原论文）

## 与复制/一致性的交互

- 在 `replication` 采用多数派写入以确保确认后的步骤不会丢失。
- 在 `consistency` 选择合适的 R/W 配置以平衡延迟与一致性需求。
