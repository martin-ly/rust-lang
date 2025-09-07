# 分布式测试与混沌工程（Testing & Chaos Engineering）

- 单元/属性测试、仿真、故障注入、Jepsen
- 可重复实验与指标验证

## 分层测试

- 单元测试：接口与不变式（`storage`/`transport`/`consensus`）。
- 属性测试：模型检查/无穷测试（proptest/quickcheck）。
- 仿真：离线模拟网络（丢包/乱序/延迟/重复）与节点故障。

## Jepsen 与线性化检查

- 模型：为系统定义操作历史与预期一致性（如线性一致）。
- 检查：以 Knossos/Porcupine 等工具验证历史是否可线性化。
- 工作流：构造器（产生并发操作）→ 故障注入 → 收集历史 → 检查。

## 混沌工程

- 目标：在生产相近环境中验证系统在异常下的稳定性与恢复速度。
- 方法：受控地注入失败（kill -9、网络分区、磁盘满、时钟跃迁）。
- 指标：可用性、SLO 违约率、恢复时间、尾延迟（P99/P999）。

## 工程建议

- 可重复性：随机种子固定、场景脚本化、指标统一采集（tracing/metrics）。
- 安全网：灰度/金丝雀发布、自动回滚、读写保护闸。

## 进一步阅读

- Wiki：`Chaos engineering`, `Jepsen`、`Linearizability`
- 课程：MIT 6.824（Labs, Testing）、UWash CSE452（Testing distributed systems）
- 论文/实践：Jepsen 报告合集、Netflix Chaos Monkey、Porcupine（线性化检测）
