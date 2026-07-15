# 代码片段目录（snippets） {#snippets}

> **EN**: Code Snippets Directory (Exempted)
> **Summary**: Compilable code snippet referenced by crate tests; directory name exempted per AGENTS.md §4.0.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-07-12

## 豁免理由 {#豁免理由}

本目录不按 `tier_0N_*` 命名，属 AGENTS.md §4.0 命名规则的有记录豁免：

- `async_control_flow_example.rs` 被 crate 测试
  [`crates/c03_control_fn/tests/snippets_compile.rs`](../../tests/snippets_compile.rs)
  以路径 `docs/snippets/async_control_flow_example.rs` 直接引用并参与编译验证；
- 重命名将破坏测试编译路径，故保留 `snippets/` 原名。

## 文件索引 {#文件索引}

- [async_control_flow_example.rs](async_control_flow_example.rs) — 异步控制流片段，由 `tests/snippets_compile.rs` 编译校验
