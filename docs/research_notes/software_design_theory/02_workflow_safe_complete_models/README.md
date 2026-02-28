# 工作流：23 安全 vs 43 完全模型

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 宗旨

建立「23 种安全设计模型」与「43 种完全模型」的形式边界与语义论证，明确安全子集与扩展目录的构成。

---

## 定义

| 概念 | 定义 |
| :--- | :--- |
| **23 安全模型** | GoF 23 种设计模式中，可**纯 Safe** 实现的子集 |
| **43 完全模型** | GoF 23 + 扩展 20（Fowler EAA/DDD：Domain Model、Repository、Service Layer、Gateway、DTO、Event Sourcing 等） |

---

## 文档索引

| 文档 | 内容 |
| :--- | :--- |
| [01_safe_23_catalog](01_safe_23_catalog.md) | 23 种安全设计模型索引 |
| [02_complete_43_catalog](02_complete_43_catalog.md) | 43 种完全模型索引 |
| [03_semantic_boundary_map](03_semantic_boundary_map.md) | 语义边界图 |
| [04_expressiveness_boundary](04_expressiveness_boundary.md) | 充分表达 vs 非充分表达论证 |

---

## 核心关系

- **23 安全 ⊆ 43 完全**：23 为纯 Safe 子集
- **扩展 20**：企业/分布式模式，绝大部分亦纯 Safe；Gateway 在 FFI 场景可能需 unsafe

---

## 使用流程

1. **查 23 安全**：模式是否纯 Safe → [01_safe_23_catalog](01_safe_23_catalog.md)
2. **查 43 完全**：扩展模式（Repository、DTO 等）→ [02_complete_43_catalog](02_complete_43_catalog.md)
3. **查语义边界**：选模式 → [03_semantic_boundary_map](03_semantic_boundary_map.md)
4. **查表达边界**：等价 vs 近似 → [04_expressiveness_boundary](04_expressiveness_boundary.md)

---

## 快速参考

| 需求 | 首选文档 |
| :--- | :--- |
| 我要选一个 GoF 模式 | 03_semantic_boundary_map → 按需求反向查模式 |
| 需要企业/分布式模式 | 02_complete_43_catalog → 扩展模式选型决策树 |
| 模式在 Rust 里能等价实现吗 | 04_expressiveness_boundary → 等价/近似/不可表达表 |
| 23 安全 vs 43 完全区别 | 本文档「核心关系」+ 01/02 索引 |

---

## 层次推进阅读路径

| 层次 | 读者 | 阅读顺序 | 产出 |
| :--- | :--- | :--- | :--- |
| **L1 基础** | 初学者 | 01_safe_23_catalog → 按分类索引 + 典型场景 | 熟悉 23 安全、快速示例 |
| **L2 选型** | 实践者 | 03_semantic_boundary_map → 模式选取示例 + 按需求反向查 | 能按需求选模式 |
| **L3 扩展** | 架构师 | 02_complete_43_catalog → 扩展模式代码 + 选型决策树 | 企业/分布式模式实现 |
| **L4 论证** | 理论关注 | 04_expressiveness_boundary → 等价/近似代码示例 | 理解 Rust 与 OOP 差异 |

---

## 23 vs 43 选型指南（实质内容）

| 场景 | 推荐 | 理由 |
| :--- | :--- | :--- |
| 纯业务逻辑、无持久化 | 23 安全 | GoF 足够；Factory、Strategy、State |
| 需持久化抽象 | 43 完全 → Repository | 见 [02_complete_43_catalog](02_complete_43_catalog.md) |
| 需用例编排、事务 | 43 完全 → Service Layer | 见 02_complete_43_catalog |
| 需跨边界传输 | 43 完全 → DTO | 见 02_complete_43_catalog |
| 需外部系统集成 | 43 完全 → Gateway | 需 FFI 时可能 unsafe |

**扩展模式深入**：20 种扩展模式均有 Rust 实现、核心意图、与 23 安全的关系；见 [02_complete_43_catalog](02_complete_43_catalog.md) 扩展模式选型决策树。

---

## 场景→模式→代码完整链条（实质内容）

### 链条 1：Web API 分层

**场景**：REST API 处理订单请求；需校验、持久化、返回 DTO。

**模式选取**：Service Layer（编排）+ Repository（持久化）+ DTO（跨边界）+ Domain Model（业务规则）。

**代码骨架**：

```rust
// 请求 DTO
struct PlaceOrderRequest { items: Vec<ItemDto> }
// 响应 DTO
struct OrderResponse { id: u64 }
// Domain Model
struct Order { id: u64, items: Vec<OrderItem> }
impl Order {
    fn from_req(req: &PlaceOrderRequest) -> Result<Self, String> { /* 校验 */ }
}
// Repository
trait OrderRepo { fn save(&mut self, o: Order) -> Result<u64, String>; }
// Service
impl OrderService {
    fn place_order(&mut self, req: PlaceOrderRequest) -> Result<OrderResponse, String> {
        let order = Order::from_req(&req)?;
        let id = self.repo.save(order)?;
        Ok(OrderResponse { id })
    }
}
```

### 链条 2：可撤销编辑器

**场景**：文本编辑器支持 undo/redo。

**模式选取**：Command（封装操作）+ Memento（快照，可选）+ State（编辑状态）。

**代码骨架**：见 [03_semantic_boundary_map](03_semantic_boundary_map.md) 示例 3。

---

## 工作流引擎表达力（状态机、补偿、Temporal 式）

| 能力 | 表达 | Rust 实现 | 说明 |
| :--- | :--- | :--- | :--- |
| **状态机** | 等价 | 枚举 + match；`#[derive(StateMachine)]` 宏；类型状态 | 与 23 安全 State 模式一致；穷尽匹配保证覆盖 |
| **补偿（Compensation）** | 近似 | `Result` + 补偿闭包；`async` 编排；显式 `rollback()` | 无内置 Saga 编排器；需显式实现补偿链 |
| **Temporal 式工作流** | 近似 | `temporal-sdk`、`cadence` 等 Rust 客户端 | 编排在服务端；Rust 实现 Activity/Workflow 定义；需外部运行时 |

**等价论证（状态机）**：Rust 枚举 + match 与有限状态机语义等价；类型状态可编译时约束非法转换。

**近似论证（补偿、Temporal）**：补偿需显式实现；Temporal 式需依赖外部编排服务；Rust 可表达 Activity 逻辑，但编排语义由引擎提供。

**引用**：[04_expressiveness_boundary 分布式模式](04_expressiveness_boundary.md#分布式模式形式化边界event-sourcingsagacqrs)、[06_boundary_analysis 并发选型](../03_execution_models/06_boundary_analysis.md)

---

## 权威对标

- **GoF (1994)**：23 种经典模式
- **Fowler EAA**：企业应用架构模式（Domain Model、Repository、Service Layer、Gateway、DTO 等）
- **Core J2EE**：表示层、业务层、集成层模式

---

## 23/43 与工作流关系（D3.4）

**Def WF-REL1（层次关系）**：23 安全、43 完全为**构建块层**（模式目录）；工作流为**编排层**（状态转换、补偿、长事务、人工任务）。二者**正交**：选型时先选模式（23/43），再选编排（状态机/补偿/Temporal）。

| 层次 | 内容 | 选型顺序 |
| :--- | :--- | :--- |
| **构建块** | 23 安全、43 完全（Domain Model、Repository、DTO、Event Sourcing 等） | 先选 |
| **编排** | 状态机、补偿链、Temporal 式工作流 | 后选 |

**工作流定义**：工作流 = 多步骤业务过程 + 状态转换 + 可选补偿 + 可选人工任务 + 超时/重试。与执行模型（同步/异步/并发/分布式）为不同维度：工作流关注**业务编排语义**，执行模型关注**运行时模型**。

**选型流程**：需求 → 选 23/43 模式（如 Repository、Service Layer、Event Sourcing）→ 选执行模型（如分布式）→ 选编排（状态机 / Saga 补偿 / Temporal）。

**引用**：[03_execution_models](../03_execution_models/README.md)、[04_expressiveness_boundary](04_expressiveness_boundary.md) 工作流引擎表达力、[COMPREHENSIVE_ARGUMENTATION_GAP_ANALYSIS_AND_PLAN](../COMPREHENSIVE_ARGUMENTATION_GAP_ANALYSIS_AND_PLAN.md)。
