# Circuit Breaker 模式形式化定义

> **模式类型**: 容错机制
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def CB1: Circuit Breaker

Circuit Breaker（熔断器）是一种**故障快速失败机制**，用于防止故障级联扩散。

```
CircuitBreaker := (S, T, f_threshold, t_timeout)
  where:
    S ∈ {Closed, Open, HalfOpen}  -- 状态
    T = {r₁, r₂, ..., rₙ}          -- 请求记录
    f_threshold ∈ ℕ                -- 故障阈值
    t_timeout ∈ Time               -- 超时时间
```

### Def CB2: 状态转换

```
State_Transition :=
  | Closed --(failures ≥ f_threshold)--> Open
  | Open --(t_timeout expired)--> HalfOpen
  | HalfOpen --(success)--> Closed
  | HalfOpen --(failure)--> Open
```

### Def CB3: 故障计数器

```
FailureCount(t) := |{r ∈ T | time(r) ∈ [t - window, t] ∧ result(r) = failure}|
```

滑动窗口内的故障请求计数。

---

## 2. 基本假设 (Axiom)

### Axiom CB1: 状态互斥

```
∀t. State(t) = Closed ⊕ Open ⊕ HalfOpen
```

任一时刻只处于一个状态。

### Axiom CB2: 故障阈值正性

```
f_threshold > 0
```

阈值必须为正整数。

### Axiom CB3: 超时单调性

```
t₁ < t₂ → CanRetry(t₁) → CanRetry(t₂)
```

一旦可以重试，之后一直可以重试（直到状态改变）。

---

## 3. 定理 (Theorem)

### Theorem CB1: 故障隔离

```
State = Open → ∀req. Reject(req)
```

**证明概要**:

1. 当状态为 Open 时，熔断器打开
2. 所有请求被立即拒绝
3. 下游服务被保护，不受故障影响

### Theorem CB2: 自恢复

```
State = Open ∧ (now - last_failure) > t_timeout
→ ◇(State = HalfOpen)
```

**证明概要**:

1. 超时时间到达后，状态自动转为 HalfOpen
2. 允许试探性请求通过
3. 若成功则完全恢复 (Closed)

---

## 4. Rust 实现示例

```rust
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};

pub enum CircuitState {
    Closed,     // 正常
    Open,       // 熔断
    HalfOpen,   // 半开试探
}

pub struct CircuitBreaker {
    state: std::sync::RwLock<CircuitState>,
    failure_count: AtomicU32,
    threshold: u32,
    timeout: Duration,
    last_failure: std::sync::Mutex<Option<Instant>>,
}

impl CircuitBreaker {
    pub async fn call<F, T, E>(&self, f: F) -> Result<T, CircuitError<E>>
    where
        F: FnOnce() -> Result<T, E>,
    {
        // 检查状态
        {
            let state = self.state.read().unwrap();
            match *state {
                CircuitState::Open => {
                    // 检查是否超时
                    let last = self.last_failure.lock().unwrap();
                    if let Some(t) = *last {
                        if t.elapsed() > self.timeout {
                            drop(state);
                            drop(last);
                            let mut s = self.state.write().unwrap();
                            *s = CircuitState::HalfOpen;
                        } else {
                            return Err(CircuitError::Open);
                        }
                    }
                }
                _ => {}
            }
        }

        // 执行请求
        match f() {
            Ok(result) => {
                self.on_success();
                Ok(result)
            }
            Err(e) => {
                self.on_failure();
                Err(CircuitError::Inner(e))
            }
        }
    }

    fn on_success(&self) {
        self.failure_count.store(0, Ordering::SeqCst);
        let mut state = self.state.write().unwrap();
        *state = CircuitState::Closed;
    }

    fn on_failure(&self) {
        let count = self.failure_count.fetch_add(1, Ordering::SeqCst) + 1;
        *self.last_failure.lock().unwrap() = Some(Instant::now());

        if count >= self.threshold {
            let mut state = self.state.write().unwrap();
            *state = CircuitState::Open;
        }
    }
}
```

---

## 5. 配置建议

| 场景 | threshold | timeout | 说明 |
|------|-----------|---------|------|
| 关键服务 | 5 | 30s | 保守策略 |
| 普通服务 | 10 | 60s | 平衡策略 |
| 内部服务 | 20 | 30s | 宽松策略 |

---

**相关阅读**:

- [分布式架构决策树](../../DISTRIBUTED_ARCHITECTURE_DECISION_TREE.md)
- [超时模式](./06_timeout_pattern.md)
