# 补偿链形式化定义

> **模式类型**: 事务回滚
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def CC1: 补偿链

补偿链是一系列**有序补偿操作**，用于撤销已完成的业务操作。

```text
CompensationChain := (O, C, ≺, status)
  where:
    O = [o₁, o₂, ..., oₙ]     -- 已执行的操作序列
    C = [c₁, c₂, ..., cₙ]     -- 对应的补偿操作，cᵢ 撤销 oᵢ
    ≺: 执行顺序关系
    status ∈ {Active, Compensating, Compensated, Failed}
```

### Def CC2: 补偿顺序

```text
CompensationOrder := Reverse(ExecutionOrder)

如果执行顺序是 o₁ → o₂ → o₃
则补偿顺序是 c₃ → c₂ → c₁
```

### Def CC3: 补偿状态机

```text
CompensationState :=
  | Active          -- 正常运行
  | Compensating(k) -- 正在补偿第 k 步
  | Compensated     -- 全部补偿完成
  | Failed(cᵢ, e)   -- 补偿 cᵢ 失败，错误 e
```

---

## 2. 基本假设 (Axiom)

### Axiom CC1: 补偿幂等性

```text
∀c ∈ C. exec(c) = s → exec(c, s) = s
```

补偿操作可安全地重复执行。

### Axiom CC2: 补偿完备性

```text
∀oᵢ ∈ O. ∃cᵢ ∈ C. Correct(cᵢ, oᵢ)
```

每个操作都有对应的正确补偿。

### Axiom CC3: 补偿原子性

```text
∀cᵢ. cᵢ 是原子的（要么成功，要么不改变状态）
```

---

## 3. 定理 (Theorem)

### Theorem CC1: 补偿一致性

```text
exec(O) = s' ∧ exec(C) = s'' → s'' ≈ s₀
```

**证明概要**:

1. O = [o₁, o₂, ..., oₙ] 按顺序执行
2. C = [cₙ, cₙ₋₁, ..., c₁] 逆序执行
3. 每个 cᵢ 正确撤销 oᵢ (Axiom CC2)
4. 因此最终状态 ≈ 初始状态

### Theorem CC2: 部分补偿安全性

```text
Compensating(k) → o₁..oₖ₋₁ 已补偿 ∧ oₖ..oₙ 待补偿
```

**证明概要**:

1. 补偿按逆序进行
2. 已完成 cₙ...cₖ，对应 oₙ...oₖ 已补偿
3. 待执行 cₖ₋₁...c₁，对应 oₖ₋₁...o₁ 待补偿
4. 状态一致：部分撤销，部分生效

---

## 4. Rust 实现示例

```rust
use std::collections::VecDeque;

// 可补偿操作特质
#[async_trait::async_trait]
pub trait CompensableAction: Send + Sync {
    type Context;
    type Error;

    async fn execute(&self, ctx: &mut Self::Context) -> Result<(), Self::Error>;
    async fn compensate(&self, ctx: &mut Self::Context) -> Result<(), Self::Error>;
    fn name(&self) -> &str;
}

// 补偿链
pub struct CompensationChain<A: CompensableAction> {
    executed: Vec<(usize, A)>,
    compensations: VecDeque<(usize, A)>,
    status: CompensationStatus,
}

impl<A: CompensableAction> CompensationChain<A> {
    pub fn new() -> Self {
        Self {
            executed: Vec::new(),
            compensations: VecDeque::new(),
            status: CompensationStatus::Active,
        }
    }

    /// 执行操作并记录
    pub async fn execute(
        &mut self,
        action: A,
        ctx: &mut A::Context,
    ) -> Result<(), CompensationError<A::Error>> {
        if !matches!(self.status, CompensationStatus::Active) {
            return Err(CompensationError::ChainNotActive);
        }

        let idx = self.executed.len();

        match action.execute(ctx).await {
            Ok(()) => {
                self.executed.push((idx, action));
                Ok(())
            }
            Err(e) => {
                // 执行失败，触发补偿
                Err(CompensationError::ExecutionFailed(e))
            }
        }
    }

    /// 执行补偿
    pub async fn compensate(
        &mut self,
        ctx: &mut A::Context,
    ) -> CompensationResult {
        self.status = CompensationStatus::Compensating;

        // 构建补偿队列（逆序）
        self.compensations = self.executed.iter()
            .rev()
            .map(|(idx, action)| (*idx, action.clone()))
            .collect();

        let mut compensated = Vec::new();

        while let Some((idx, action)) = self.compensations.pop_front() {
            match action.compensate(ctx).await {
                Ok(()) => {
                    compensated.push(idx);
                }
                Err(e) => {
                    self.status = CompensationStatus::Failed {
                        action_idx: idx,
                        error: format!("{:?}", e),
                    };
                    return CompensationResult::Partial {
                        compensated,
                        failed_at: idx,
                    };
                }
            }
        }

        self.status = CompensationStatus::Compensated;
        CompensationResult::Complete
    }

    /// 重试失败的补偿
    pub async fn retry_failed(
        &mut self,
        ctx: &mut A::Context,
    ) -> Result<(), CompensationError<A::Error>> {
        if let CompensationStatus::Failed { action_idx, .. } = &self.status {
            let (_, action) = self.executed.iter()
                .find(|(idx, _)| idx == action_idx)
                .ok_or(CompensationError::ActionNotFound)?;

            match action.compensate(ctx).await {
                Ok(()) => {
                    // 继续剩余补偿
                    self.compensate(ctx).await;
                    Ok(())
                }
                Err(e) => Err(CompensationError::CompensationFailed(e)),
            }
        } else {
            Ok(())
        }
    }
}

#[derive(Debug)]
pub enum CompensationStatus {
    Active,
    Compensating,
    Compensated,
    Failed { action_idx: usize, error: String },
}

#[derive(Debug)]
pub enum CompensationResult {
    Complete,
    Partial { compensated: Vec<usize>, failed_at: usize },
}

#[derive(Debug)]
pub enum CompensationError<E> {
    ChainNotActive,
    ExecutionFailed(E),
    CompensationFailed(E),
    ActionNotFound,
}

// 示例：银行转账补偿
#[derive(Clone)]
pub struct TransferAction {
    from_account: String,
    to_account: String,
    amount: f64,
}

#[async_trait::async_trait]
impl CompensableAction for TransferAction {
    type Context = BankContext;
    type Error = BankError;

    async fn execute(&self, ctx: &mut Self::Context) -> Result<(), Self::Error> {
        ctx.debit(&self.from_account, self.amount).await?;
        ctx.credit(&self.to_account, self.amount).await?;
        Ok(())
    }

    async fn compensate(&self, ctx: &mut Self::Context) -> Result<(), Self::Error> {
        // 反向操作：从收款方扣回，退回付款方
        ctx.debit(&self.to_account, self.amount).await?;
        ctx.credit(&self.from_account, self.amount).await?;
        Ok(())
    }

    fn name(&self) -> &str {
        "Transfer"
    }
}

// 使用示例
pub async fn execute_transfer_saga() -> Result<(), Box<dyn std::error::Error>> {
    let mut chain = CompensationChain::new();
    let mut ctx = BankContext::new();

    // 步骤1：扣款
    if let Err(e) = chain.execute(
        TransferAction {
            from_account: "A".to_string(),
            to_account: "B".to_string(),
            amount: 100.0,
        },
        &mut ctx,
    ).await {
        // 执行失败，自动补偿
        chain.compensate(&mut ctx).await;
        return Err(Box::new(std::io::Error::new(
            std::io::ErrorKind::Other,
            format!("Transfer failed: {:?}", e),
        )));
    }

    // 步骤2：通知（无需补偿）
    // ...

    Ok(())
}

pub struct BankContext;
pub struct BankError;

impl BankContext {
    async fn debit(&mut self, _account: &str, _amount: f64) -> Result<(), BankError> {
        Ok(())
    }
    async fn credit(&mut self, _account: &str, _amount: f64) -> Result<(), BankError> {
        Ok(())
    }
    fn new() -> Self { Self }
}
```

---

## 5. 补偿与 Saga 的关系

补偿链是 Saga 模式的核心实现机制：

```text
Saga = Workflow + CompensationChain
```

| 层面 | Saga | 补偿链 |
|------|------|--------|
| 抽象 | 业务概念 | 技术实现 |
| 范围 | 跨服务事务 | 单服务内操作 |
| 编排 | 协调者 | 执行器 |

---

**相关阅读**:

- [Saga 模式](../05_distributed/01_saga_pattern.md)
- [工作流状态机](./01_workflow_state_machine.md)
