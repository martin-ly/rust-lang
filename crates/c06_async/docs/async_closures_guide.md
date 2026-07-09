> **EN**: Async Closures Guide
> **Summary**: Deep guide to Rust async closures (`async || {}`), the `AsyncFn`/`AsyncFnMut`/`AsyncFnOnce` trait family, migration from the old `|x| async move {}` pattern, and current limitations. This crate document now redirects to the canonical concept page.

> **权威来源**: [concept/03_advanced/01_async/24_async_closures.md](../../../concept/03_advanced/01_async/24_async_closures.md)

## 主题速览

- `async || {}` 语法与捕获语义
- `AsyncFn*` trait 家族层级
- 旧范式 `|x| async move {}` 迁移路径
- 高阶异步回调与中间件模式
- 限制：`AsyncFn` 非 dyn-compatible、Send bound、递归

---

*本 stub 按 AGENTS.md §6.4 保留路径，原通用概念内容已归并至上方权威来源页。可执行代码示例见 [`crates/c06_async/src`](../../../crates/c06_async/src)。*
