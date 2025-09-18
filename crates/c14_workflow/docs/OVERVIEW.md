# 概览：工作流与编排（c14_workflow）

本模块聚焦业务/技术流程建模、状态机、模式与性能，覆盖多语言/多域工作流的组织与 Rust 实践。

---

## 目录导航

- 基础与模式
  - [workflow_fundamentals/concepts.md](./workflow_fundamentals/concepts.md)
  - [workflow_fundamentals/patterns.md](./workflow_fundamentals/patterns.md)
  - [workflow_fundamentals/state_machines.md](./workflow_fundamentals/state_machines.md)

- 性能与评测
  - [performance/benchmarking.md](./performance/benchmarking.md)
  - [performance/optimization.md](./performance/optimization.md)

- 程序化视角（Rust/Go）
  - [program/rust/rust_workflow01.md](./program/rust/rust_workflow01.md)
  - [program/rust/rust_type_define01.md](./program/rust/rust_type_define01.md)
  - [program/rust/rust_type_define02.md](./program/rust/rust_type_define02.md)
  - [program/go/go_workflow01.md](./program/go/go_workflow01.md)

- AI 与 IoT 视角
  - [ai/workflow_ai_view.md](./ai/workflow_ai_view.md)
  - [iot/workflow_iot_analysis01.md](./iot/workflow_iot_analysis01.md)
  - 智能家居：`iot/smart_home/*`

- 版本对齐
  - [RUST_189_DOCUMENTATION_ALIGNMENT_PLAN.md](./RUST_189_DOCUMENTATION_ALIGNMENT_PLAN.md)
  - [RUST_189_DOCUMENTATION_ALIGNMENT_SUMMARY.md](./RUST_189_DOCUMENTATION_ALIGNMENT_SUMMARY.md)

---

## 快速开始

1) 阅读 `workflow_fundamentals/*` 建立概念
2) 结合 `program/rust/*` 运行示例
3) 通过 `performance/*` 做性能验证

---

## 待完善

- 增补跨系统补偿/重试/幂等的统一策略清单
- 与 `c18_model` 的形式化状态机建模互链

### 跨系统补偿/重试/幂等策略清单（补全）

- 幂等键：请求幂等键生成与过期策略；侧存储防重复
- 重试策略：指数退避 + 抖动；区分幂等/非幂等操作
- 补偿设计：Saga 步骤补偿函数、重试与死信；外部副作用“预留+超时释放”
- 事务边界：本地事务+外部一致性；事件溯源与回放
- 观测与审计：TraceID/SpanID 贯穿；补偿审计与告警

### 互链

- 与 `c18_model`：将状态机规范映射为属性测试与模型检查约束
- 与 `c20_distributed`：在一致性级别与 ACK 策略下验证流程鲁棒性
