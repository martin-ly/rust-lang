# 状态机到协议验证全流程

> 返回索引：`docs/README.md`

本指南演示如何从业务状态机出发，逐步完成协议属性定义与时序逻辑验证。

## 目标

- 用 `FiniteStateMachine` 建模协议状态与转换
- 用 `TemporalFormula` 表达协议安全/活性属性
- 使用 `TemporalModelChecker` 进行模型检查并查看反例

## 前置条件

- Rust 1.70+，已添加依赖 `c18_model = "0.2.0"`

## 步骤 1：定义状态机

```rust
use c18_model::{FiniteStateMachine, State, Transition};

let mut fsm = FiniteStateMachine::new("idle".to_string());

let working = State::new("working".to_string())
    .with_property("busy".to_string(), true)
    .with_property("safe".to_string(), true);

fsm.add_state(working);

let t_start = Transition::new("idle".to_string(), "working".to_string(), "start".to_string());
fsm.add_transition(t_start);

assert_eq!(fsm.get_current_state().id, "idle");
fsm.transition("start").expect("必须能从 idle -> working");
assert_eq!(fsm.get_current_state().id, "working");
```

要点：

- `FiniteStateMachine::new` 接受初始状态 `String`
- `add_state` 与 `add_transition` 分别注册状态与转换
- `transition(&str)` 触发事件，返回 `Result<(), String>`

## 步骤 2：定义时序逻辑属性

```rust
use c18_model::TemporalFormula;

// 全局满足安全属性（G safe）
let safe_globally = TemporalFormula::Globally(Box::new(
    TemporalFormula::Atomic("safe".to_string())
));

// 最终达到 busy 状态（F busy）
let eventually_busy = TemporalFormula::Finally(Box::new(
    TemporalFormula::Atomic("busy".to_string())
));
```

要点：

- 常用算子：`Globally`(G), `Finally`(F), `Next`(X), `Until`(U)
- 原子命题通过 `Atomic(String)` 绑定到状态属性

## 步骤 3：模型检查与反例

```rust
use c18_model::TemporalModelChecker;

let checker = TemporalModelChecker::new(fsm.clone());
let ok = checker.check_formula(&safe_globally);
println!("G safe 是否满足: {}", ok);

if !ok {
    if let Some(cex) = checker.generate_counterexample(&safe_globally) {
        eprintln!("反例路径: {:?}", cex);
    }
}
```

要点：

- `TemporalModelChecker::new(fsm)` 持有 `FiniteStateMachine`
- `check_formula(&TemporalFormula) -> bool`
- `generate_counterexample(&TemporalFormula) -> Option<Vec<String>>`

## 步骤 4：常见检查清单

- 定义必要状态属性（如 `safe`, `busy`），避免属性缺失导致验证无效
- 检查可达性：`get_reachable_states()`
- 死锁检测：`has_deadlock()`
- 不变式检查：`check_invariant("prop")`

## 故障排查与常见反例

- 状态属性缺失导致原子命题恒未知
  - 现象：`Atomic("safe")` 总是失败或无意义
  - 解决：为所有可能到达的状态补齐 `safe` 属性，或在检查前执行属性存在性审计

- 不可达状态使得性质“表面满足”
  - 现象：`G p` 返回 true，但 `p` 从未在所有可达路径上检验
  - 解决：调用 `get_reachable_states()` 并限制模型检查在可达子图上

- 死锁未显式建模
  - 现象：无后继转换的状态未被视为错误，`F busy` 假阳性
  - 解决：在 `has_deadlock()` 失败时，将死锁视为违背活性性质

- 事件歧义或多义转换
  - 现象：同一事件指向多个目标但缺少守卫，导致非确定路径
  - 解决：为竞争转换添加互斥守卫或显式优先级

### 反例最小化建议

- 先执行可达性削减；对 LTL 采用最短违背路径启发式；在输出中包含 `(state, event)` 对序列

## 完整示例片段

```rust
use c18_model::{FiniteStateMachine, State, Transition, TemporalFormula, TemporalModelChecker};

let mut fsm = FiniteStateMachine::new("idle".to_string());
let working = State::new("working".to_string())
    .with_property("busy".to_string(), true)
    .with_property("safe".to_string(), true);
fsm.add_state(working);
fsm.add_transition(Transition::new("idle".to_string(), "working".to_string(), "start".to_string()));

let g_safe = TemporalFormula::Globally(Box::new(TemporalFormula::Atomic("safe".to_string())));
let checker = TemporalModelChecker::new(fsm);
assert!(checker.check_formula(&g_safe) || checker.generate_counterexample(&g_safe).is_some());
```

## 结论与下一步

- 将更多协议约束编码为 LTL 公式
- 将随机/非确定行为建模为多条转换与守卫
- 引入 `FormalMethodsToolkit` 统一组织检查与报告
