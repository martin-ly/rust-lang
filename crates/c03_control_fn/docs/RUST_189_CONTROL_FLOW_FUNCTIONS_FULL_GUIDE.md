# Rust 1.89 控制流与函数：完整详解与最佳实践

> 目标：系统梳理 Rust 1.89 在“控制流”和“函数”层面的稳定/增强特性，对齐本仓库实现，并给出实践建议与示例索引。

## 范围与版本

- Rust 版本：1.89.0（Edition 2024）
- 涵盖模块：`control_struct/`、`pattern_matching/`、`statements/`、`expressions/`、`closure/`、`async_control_flow*.rs`、`rust_189_enhanced_features.rs`

### 关键稳定/增强特性（1.89）

- let_chains：在 `if`/`while` 条件中链式使用 `let` 与布尔表达式（见 `rust_189_enhanced_features::let_chains_189`）
- cfg_boolean_literals：在 `#[cfg(..)]` 内使用 `true/false` 字面量（见 `cfg_boolean_literals_189`）
- 裸函数（配合 nightly 与 `asm!`）：底层与性能关键路径（见 `naked_functions_189`）
- 危险隐式引用与无效空指针参数相关 lint：指针安全实践（见 `dangerous_implicit_autorefs_189`、`invalid_null_arguments_189`）

### 控制流全景

- 表达式与语句：`expressions/define.rs`、`statements/define.rs`
- 分支与匹配：`control_struct/define.rs`、`pattern_matching/define.rs`
- 循环与迭代：`control_struct/`，异步循环见 `async_control_flow*.rs`
- 异步控制流：`async_control_flow.rs` 与 `async_control_flow_189.rs`

### 异步控制流 API（1.89 对齐）

- `AsyncControlFlowExecutor::async_if_else<F, G, T>(condition, if_branch, else_branch) -> T`
  - 要点：`if_branch` 与 `else_branch` 分别是 `Future<Output = T>`，可异步计算两分支。
- `AsyncControlFlowExecutor::async_loop<FnMut() -> bool, Future + Clone>(condition, body) -> Vec<T>`
  - 要点：
    - `condition` 是 `FnMut() -> bool`，用于同步判定是否继续循环。
    - `body` 需实现 `Clone` 的 `Future`，便于每次迭代克隆执行。
    - 可用 `std::future::ready(())` 作为可克隆占位体，或封装可克隆 future。
- `AsyncControlFlowExecutor::async_for<T, F, Fut>(items, processor) -> Vec<T>`
  - 要点：`processor: Fn(T) -> Fut`，逐项异步处理集合并返回新集合。

示例摘录（与 `examples/control_flow_functions_189.rs` 一致）：

```rust
let exec = AsyncControlFlowExecutor;

// 1) if/else
let v = exec.async_if_else(true, async { 10 }, async { 0 }).await;

// 2) loop（3 次）
let counter = std::rc::Rc::new(std::cell::Cell::new(0));
let remaining = std::cell::Cell::new(3);
let c = counter.clone();
exec.async_loop(
    move || {
        let r = remaining.get();
        if r > 0 { c.set(c.get() + 1); remaining.set(r - 1); true } else { false }
    },
    std::future::ready(()),
).await;

// 3) for each
let items = vec![1, 2, 3, 4, 5];
let processed = exec.async_for(items.clone(), |x| async move { x }).await;
let sum: i32 = processed.iter().copied().sum();
```

更多可运行示例见：`docs/snippets/async_control_flow_example.rs`

### 函数与闭包

- 常规函数与返回类型；零开销错误处理策略：`error_handling/`
- 闭包定义、捕获与设计：`closure/define.rs`、`closure/design.rs`
- 裸函数（nightly gated）：见增强模块 `naked_functions_189`

### 示例索引（建议运行顺序）

1. `examples/control_flow_example.rs`：基础控制流
2. `examples/rust_189_enhanced_features_demo.rs`：1.89 增强特性
3. `examples/rust_189_async_features.rs`：异步控制流
4. `examples/control_flow_functions_189.rs`：控制流+函数（本指南配套示例）

### 迁移与编程建议

- 用 let_chains 扁平化多层 `if let`；保留清晰的卫语句
- 对指针参数先判空再解引用；优先使用切片与引用语义
- 裸函数仅用于确有必要的极端场景，并隔离到 `feature = "nightly"`
- 对异步控制流，偏向 `async fn`+`await` 与组合器清晰表达

### 进一步阅读

- `docs/RUST_189_MIGRATION_GUIDE.md`
- `src/rust_189_enhanced_features.rs`
- `src/async_control_flow_189.rs`
