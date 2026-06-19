> **生态状态提示**：本文档提及 `async-std` 与/或 `wasm32-wasi`。请注意：
>
> - `async-std` 项目已进入维护模式，2024 年后不再活跃开发；新项目建议优先评估 **Tokio** 或 **smol**。
> - `wasm32-wasi` 旧目标名已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**。

---

# C07 进程管理 - 待完善清单

> **最后更新**: 2026-02-13
> **追踪**: 00_MASTER_INDEX 中「待完善工作」的详细项

## 待完善项

| 序号 | 项目 | 说明 | 优先级 | 状态 |
| :--- | :--- | :--- | :--- | :--- || 1 | async_stdio_demo | 异步标准 IO（需 --features async） | 低 | ✅ 已实现 |
| 2 | 文档深度 | 部分实践示例文档可进一步扩展 | 低 | ✅ 11_practical_examples 导航已补全 |

## 完成情况

- [x] async_stdio_demo 完整实现（见 src/bin/async_stdio_demo.rs，默认启用 async feature）
- [x] 实践示例文档扩展（11_practical_examples/ 导航与重定向已创建）

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
