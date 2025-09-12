# 研究议程（Research Agenda）索引

## 目的

- 追踪 Rust 相关的研究课题、未解问题与前沿方向，指导样例与验证。

## 方向

- 类型与所有权：效果系统、线性/仿射类型、更强的借用推断
- 并发与异步：结构化并发、任务内存模型、时间/因果一致性
- 形式化与验证：Rust MIR 到验证工具的语义映射、自动化规格生成
- 性能与可预测：实时性、延迟上界、缓存/NUMA 感知优化

## 任务清单（示例）

- Kani/Prusti 对关键并发结构的性质验证最小集
- 异步背压与丢弃策略的 form/check 一致性定义
- MIR 级别的不可变借用强化与诊断提升原型

## 导航

- 返回根：[`rust-formal-engineering-system/README.md`](../README.md)
- 理论基础：[`../01_theoretical_foundations/00_index.md`](../01_theoretical_foundations/00_index.md)
- 质量保障：[`../10_quality_assurance/00_index.md`](../10_quality_assurance/00_index.md)
