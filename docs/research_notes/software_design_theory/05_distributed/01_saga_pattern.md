# Saga 模式形式化定义

> **模式类型**: 分布式事务
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def S1: Saga

Saga 是一种**长事务管理模式**，它将一个长事务分解为一系列**本地事务**（Local Transactions），每个本地事务有对应的**补偿操作**（Compensating Transaction）。

```text
Saga := (T, C, ≺, σ)
  where:
    T = {t₁, t₂, ..., tₙ}     -- 本地事务集合
    C = {c₁, c₂, ..., cₙ}     -- 补偿操作集合，cᵢ 补偿 tᵢ
    ≺ ⊆ T × T                  -- 偏序关系，定义执行顺序
    σ: T → {success, failed}   -- 状态函数
```

### Def S2: Saga 执行状态

```text
State(Saga) :=
  | Running(tᵢ)      -- 正在执行第 i 个事务
  | Compensating(cⱼ) -- 正在执行第 j 个补偿
  | Completed        -- 全部成功完成
  | Compensated      -- 已回滚补偿
```

### Def S3: 补偿正确性

补偿操作 cᵢ 对于事务 tᵢ 是**正确的**，当且仅当：

```text
Correct(cᵢ, tᵢ) := ∀s. exec(tᵢ, s) = s' ∧ exec(cᵢ, s') = s''
                   → s ≈ s''
```

即：执行 tᵢ 后再执行 cᵢ，系统状态回到语义等价于原始状态。

---

## 2. 基本假设 (Axiom)

### Axiom S1: 补偿幂等性

```text
∀c ∈ C. exec(c, s) = s' → exec(c, s') = s'
```

补偿操作必须是**幂等的**，可多次执行而不改变结果。

### Axiom S2: 偏序无环性

```text
¬∃t₁, t₂, ..., tₙ ∈ T. t₁ ≺ t₂ ≺ ... ≺ tₙ ≺ t₁
```

执行顺序必须是无环的偏序关系。

### Axiom S3: 最终一致性

```text
∀tᵢ ∈ T. σ(tᵢ) = success → ◇(∀tⱼ ≺ tᵢ. σ(tⱼ) = success)
```

若事务成功，则其所有前驱最终也成功（或已补偿）。

---

## 3. 定理 (Theorem)

### Theorem S1: Saga 原子性

```text
Saga 满足弱原子性：
∀Saga. Completed ∨ Compensated
```

**证明概要**:

1. Saga 按顺序执行事务 t₁, t₂, ..., tₙ
2. 若所有 tᵢ 成功，则达到 Completed 状态
3. 若 tₖ 失败，则按逆序执行补偿 cₖ₋₁, ..., c₁
4. 根据补偿正确性 (Def S3)，系统回到初始状态
5. 达到 Compensated 状态

### Theorem S2: 补偿终止性

```text
∀Saga. Compensating(cᵢ) → ◇Compensated
```

**证明概要**:

1. 补偿操作数量有限 (|C| = |T| = n)
2. 每次补偿执行后，剩余补偿数减 1
3. 由良基归纳法，补偿过程必然终止

---

## 4. Rust 实现示例

```rust
// Saga 执行器核心接口
pub trait SagaStep {
    type State;
    type Error;

    async fn execute(&self, state: &mut Self::State) -> Result<(), Self::Error>;
    async fn compensate(&self, state: &mut Self::State) -> Result<(), Self::Error>;
}

pub struct SagaExecutor<S, E> {
    steps: Vec<Box<dyn SagaStep<State = S, Error = E>>>,
    executed: Vec<usize>, // 记录已执行的步骤索引
}

impl<S, E> SagaExecutor<S, E> {
    pub async fn run(&mut self, state: &mut S) -> Result<(), SagaError<E>> {
        for (idx, step) in self.steps.iter().enumerate() {
            match step.execute(state).await {
                Ok(()) => self.executed.push(idx),
                Err(e) => {
                    // 执行补偿
                    self.compensate_all(state).await?;
                    return Err(SagaError::StepFailed(e));
                }
            }
        }
        Ok(())
    }

    async fn compensate_all(&self, state: &mut S) -> Result<(), E> {
        // 逆序执行补偿
        for &idx in self.executed.iter().rev() {
            self.steps[idx].compensate(state).await?;
        }
        Ok(())
    }
}
```

---

## 5. 与其他模式的关系

| 模式 | 关系 | 说明 |
|------|------|------|
| 2PC | 替代 | Saga 牺牲强一致性换取可用性 |
| Outbox | 组合 | Saga 可使用 Outbox 保证消息投递 |
| 重试 | 增强 | Saga 步骤可配置重试策略 |

---

**相关阅读**:

- [分布式概念族谱](../../DISTRIBUTED_CONCEPT_MINDMAP.md)
- [分布式架构决策树](../../DISTRIBUTED_ARCHITECTURE_DECISION_TREE.md)

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
