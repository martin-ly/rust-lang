# 工作流引擎能力矩阵

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.1+ (Edition 2024)

---

## 概述

工作流引擎能力矩阵对比主流工作流引擎的功能特性、适用场景和Rust集成能力，为技术选型提供参考。

---

## 引擎能力对比矩阵

### 核心功能

| 引擎 | 持久化 | 补偿 | 人工任务 | 可视化 | 监控 | 定时触发 | 子流程 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Temporal** | ✅ | ✅ | ⚠️ | ✅ | ✅ | ✅ | ✅ |
| **Cadence** | ✅ | ✅ | ❌ | ✅ | ✅ | ✅ | ✅ |
| **Camunda** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Netflix Conductor** | ✅ | ✅ | ❌ | ✅ | ✅ | ✅ | ✅ |
| **自研状态机** | ❌ | ⚠️ | ❌ | ❌ | ❌ | ⚠️ | ⚠️ |
| **tokio::fsm** | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ | ❌ |

### 技术特性

| 引擎 | 横向扩展 | 事件驱动 | Saga支持 | 并行执行 | 版本控制 | 多租户 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Temporal** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Cadence** | ✅ | ✅ | ✅ | ✅ | ⚠️ | ✅ |
| **Camunda** | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Netflix Conductor** | ✅ | ✅ | ✅ | ✅ | ⚠️ | ❌ |
| **自研状态机** | ❌ | ⚠️ | ⚠️ | ⚠️ | ❌ | ❌ |
| **tokio::fsm** | ❌ | ✅ | ❌ | ⚠️ | ❌ | ❌ |

### Rust支持

| 引擎 | Rust SDK | 异步支持 | 类型安全 | 维护状态 |
| :--- | :--- | :--- | :--- | :--- |
| **Temporal** | ✅ | ✅ | ✅ | 活跃 |
| **Cadence** | ❌ | N/A | N/A | 维护中 |
| **Camunda** | ❌ | N/A | N/A | 活跃 |
| **Netflix Conductor** | ❌ | N/A | N/A | 活跃 |
| **自研状态机** | ✅ | ✅ | ✅ | 自定义 |
| **tokio::fsm** | ✅ | ✅ | ✅ | 活跃 |

---

## 选型决策矩阵

### 按场景推荐

| 场景 | 推荐引擎 | 理由 | 注意事项 |
| :--- | :--- | :--- | :--- |
| 企业级工作流 | Temporal/Camunda | 功能完善，生态成熟 | 基础设施成本高 |
| 微服务编排 | Temporal/Conductor | 云原生，可扩展 | 学习曲线陡峭 |
| 纯Rust项目 | Temporal SDK/自研 | 类型安全，无FFI | 功能需自行扩展 |
| 简单状态机 | tokio::fsm/自研 | 轻量，无依赖 | 功能有限 |
| 人工审批流程 | Camunda | BPMN支持完善 | 需要Java生态 |
| 事务补偿(Saga) | Temporal | 原生Saga模式 | 需理解事件溯源 |

### 复杂度评估

```text
低复杂度 ────────────────────────────────────> 高复杂度

自研状态机 < tokio::fsm < Conductor < Cadence < Temporal < Camunda
   1周         2周          1月       1-2月       2-3月       3-6月
   (开发)     (集成)      (部署)    ( mastery)  (生产)     (企业)
```

---

## 深度对比

### Temporal vs Cadence

| 维度 | Temporal | Cadence |
| :--- | :--- | :--- |
| **起源** | Cadence分支 | Uber开发 |
| **社区** | 更活跃，CNCF | 较稳定 |
| **功能** | 更丰富的API | 核心功能完善 |
| **云托管** | Temporal Cloud | 第三方 |
| **Rust SDK** | 官方支持 | 社区维护 |
| **推荐** | 新项目首选 | 存量系统 |

### Camunda 7 vs 8

| 维度 | Camunda 7 | Camunda 8 |
| :--- | :--- | :--- |
| **架构** | 单体 | 云原生 |
| **扩展性** | 有限 | 高 |
| **部署** | 嵌入式/独立 | SaaS/自托管 |
| **BPMN支持** | 完整 | 完整 |
| **Rust集成** | 需HTTP Client | 需HTTP Client |
| **推荐** | 遗留系统 | 新项目 |

---

## Rust集成指南

### Temporal Rust SDK

```rust
use temporal_sdk::{ActivityOptions, WorkflowContext, workflow};

#[workflow]
async fn order_workflow(ctx: &mut WorkflowContext, order_id: String) -> Result<Order, Error> {
    // 执行活动
    let inventory = ctx.activity(
        "check_inventory",
        ActivityOptions::default(),
        order_id.clone(),
    ).await?;

    if inventory.available {
        ctx.activity("process_payment", ActivityOptions::default(), order_id).await?;
        ctx.activity("ship_order", ActivityOptions::default(), order_id).await?;
    }

    Ok(Order::completed(order_id))
}

// 补偿处理
async fn compensate_payment(ctx: &mut WorkflowContext, order_id: String) {
    ctx.activity("refund_payment", ActivityOptions::default(), order_id)
        .await
        .ok(); // 补偿不应失败
}
```

### 自研状态机模式

```rust
// Rust原生状态机实现
use std::collections::HashMap;

pub trait State: Send + Sync {
    fn name(&self) -> &'static str;
    fn on_enter(&mut self, context: &mut Context);
    fn on_event(&mut self, event: Event, context: &mut Context) -> Transition;
    fn on_exit(&mut self, context: &mut Context);
}

pub struct Workflow<S: State> {
    current: S,
    context: Context,
    history: Vec<StateEvent>,
}

impl<S: State> Workflow<S> {
    pub fn handle_event(&mut self, event: Event) -> Result<(), WorkflowError> {
        let old_state = self.current.name();

        self.current.on_exit(&mut self.context);

        match self.current.on_event(event, &mut self.context) {
            Transition::To(new_state) => {
                self.history.push(StateEvent {
                    from: old_state,
                    to: new_state.name(),
                    event,
                    timestamp: Instant::now(),
                });
                self.current = new_state;
                self.current.on_enter(&mut self.context);
                Ok(())
            }
            Transition::Stay => {
                self.current.on_enter(&mut self.context);
                Ok(())
            }
            Transition::Error(e) => Err(e),
        }
    }
}
```

---

## 设计模式映射

| 模式 | Temporal | 自研实现 | 适用性 |
| :--- | :--- | :--- | :--- |
| **Saga** | 原生Workflow | 状态机+补偿 | 分布式事务 |
| **状态机** | 隐式 | 显式 | 复杂状态流转 |
| **管道** | Activity链 | 函数组合 | 数据处理 |
| **分叉-合并** | Promise.all | join! | 并行执行 |
| **路由** | 条件分支 | match | 动态选择 |

---

## 风险评估矩阵

| 引擎 | 供应商锁定 | 运维复杂度 | 学习成本 | 社区风险 |
| :--- | :--- | :--- | :--- | :--- |
| Temporal | 中 | 高 | 高 | 低 |
| Cadence | 中 | 高 | 高 | 中 |
| Camunda | 中 | 中 | 中 | 低 |
| Conductor | 低 | 中 | 中 | 中 |
| 自研 | 无 | 低 | 低 | 可控 |

---

## 与Rust形式化方法关联

| 概念 | 形式化支持 | 应用 |
| :--- | :--- | :--- |
| 状态机 | ✅ 完全支持 | 自研实现可形式化验证 |
| 工作流正确性 | ⚠️ 部分支持 | Temporal提供确定性保证 |
| 补偿一致性 | ⚠️ 需自定义 | Saga模式需手动验证 |
| 类型安全 | ✅ Rust原生 | SDK提供类型安全 |

---

## 推荐学习路径

```text
入门 ────────────────────────────────────────> 精通

1. 理解状态机模式
   └── 自研简单状态机
       └── 集成Temporal SDK
           └── 掌握Saga模式
               └── 生产环境调优
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 工作流引擎能力矩阵完整版
