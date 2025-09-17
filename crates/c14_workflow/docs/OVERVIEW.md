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
