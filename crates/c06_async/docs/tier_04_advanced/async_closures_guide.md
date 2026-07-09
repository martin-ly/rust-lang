> **EN**: Async Closures Deep Dive
> **Summary**: Deep guide to Rust async closures (`async || {}`), the `AsyncFn`/`AsyncFnMut`/`AsyncFnOnce` trait family, migration from the old `|x| async move {}` pattern, and current limitations. General concept explanations are maintained in the canonical concept authority page.
>
> **权威来源**: [concept/03_advanced/01_async/24_async_closures.md](../../../../concept/03_advanced/01_async/24_async_closures.md)

# Async Closures 深度指南

*本 stub 按 AGENTS.md §6.4 保留路径，原通用概念内容已归并至上方权威来源页。可执行代码示例见 [`crates/c06_async/src`](../../../../crates/c06_async/src)。*

## 主题索引

| 主题 | 权威来源 |
|------|----------|
| Async Closures | [concept/03_advanced/01_async/24_async_closures.md](../../../../concept/03_advanced/01_async/24_async_closures.md) |
| Async/Await 基础 | [concept/03_advanced/01_async/02_async.md](../../../../concept/03_advanced/01_async/02_async.md) |
| Future / Executor 机制 | [concept/03_advanced/01_async/39_future_and_executor_mechanisms.md](../../../../concept/03_advanced/01_async/39_future_and_executor_mechanisms.md) |
| 异步模式 | [concept/03_advanced/01_async/26_async_patterns.md](../../../../concept/03_advanced/01_async/26_async_patterns.md) |
