# 错误处理（Error Handling）

## 1. 工程原理与定义（Principle & Definition）

错误处理是指系统在运行时对异常或不可预期情况的检测、报告与恢复。Rust 强制显式错误处理，提升健壮性。
Error handling refers to detecting, reporting, and recovering from exceptional or unexpected conditions at runtime. Rust enforces explicit error handling for robustness.

## 2. Rust 1.88 新特性工程化应用

- `try_blocks`：块级错误传播，简化复杂流程。
- `#[expect]`属性：可控lint，提升开发体验。
- `anyhow`/`thiserror`：主流错误链与自定义错误类型。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 使用 `Result`/`Option` 明确错误边界。
- `?` 运算符简化错误传播。
- `anyhow`/`thiserror` 统一错误链。
- `panic::catch_unwind` 捕获不可恢复错误。

**最佳实践：**

- 明确区分可恢复与不可恢复错误。
- 统一错误类型，便于追踪和日志。
- 使用 `#[expect]` 管理开发阶段警告。
- 结合自动化测试覆盖错误分支。

## 4. 常见问题 FAQ

- Q: Rust 如何实现统一的错误链？
  A: 推荐使用 `thiserror`/`anyhow`，支持自动转换和链式追踪。
- Q: 何时使用 panic!？
  A: 仅在不可恢复的致命错误场景下使用。
- Q: 如何处理异步任务中的错误？
  A: 通过 `JoinHandle::await` 统一收集和处理。

## 5. 参考与扩展阅读

- [Rust 官方错误处理文档](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [anyhow 错误处理库](https://docs.rs/anyhow)
- [thiserror 自定义错误类型](https://docs.rs/thiserror)
