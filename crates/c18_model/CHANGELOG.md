# Changelog

All notable changes to this project will be documented in this file.

## [0.2.0] - 2025-09-11

### Added
- 文档结构完善：新增并梳理 `docs/` 下的入口 README、getting-started 与 API 参考。
- 统一配置与错误基础设施：`src/config.rs` 与 `src/error.rs` 完整实现并导出。
- 基准测试套件：`benchmarks.rs` 提供算法/内存/并发基准，`BenchmarkSuite::run_full_suite` 汇总报告。

### Changed
- `lib.rs` 公共导出整理，确保与各模块实现一致。
- 微调多处实现以提升可读性与一致性（不破坏 API）：
  - `queueing_models.rs` 使用 `or_default()`
  - `benchmarks.rs` 使用 `saturating_sub`、优化 `push`、移除 `-> ()`
  - `visualization.rs` 移除不必要 `format!`，单字符使用 `push`

### Documentation
- 版本与用法示例同步至 `0.2.0`（依赖示例、README 标注）。

### Quality
- 运行 Clippy 并处理部分警告（保留建议性风格提示）。
- 测试：`cargo test` 87/87 通过；示例与脚本全通过。

---

遵循语义化版本。

