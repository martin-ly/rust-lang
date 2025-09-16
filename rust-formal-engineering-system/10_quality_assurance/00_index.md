# 质量保障（Quality Assurance）索引

## 目的

- 建立从单元测试到形式化验证的完整质量闭环。
- 汇总仓库内相关工具链与最佳实践，统一入口与术语。

## 版块

- 测试（Testing）：单元、集成、端到端、基准、属性测试（proptest/quickcheck）
- 静态分析（Static Analysis）：Clippy、Rustc lint、dead_code、unused_results
- 运行时检查（Runtime Checking）：Miri、asan/lsan/tsan（Nightly/工具链）
- 模糊测试（Fuzzing）：cargo-fuzz、AFL++、字典与语料管理
- 形式化验证（Formal）：Prusti、Kani、Creusot、Liquid Types（实验）
- 指标与可观测（Metrics & Obs）：prometheus、opentelemetry、tracing、pprof

## 仓库内参考

- 性能与并发：`crates/c05_threads/`、`crates/c06_async/`
- 中间件与网络：`crates/c12_middlewares/`、`crates/c10_networks/`、`crates/c13_microservice/`
- 质量专题：`docs/performance_guide/`、`formal_rust/` 相关验证示例

## 建议流程

1) 静态检查：`cargo clippy -- -D warnings`，`cargo udeps`（如使用）
2) 测试金字塔：单元→集成→端到端，覆盖关键路径并添加属性测试
3) 基准与剖析：`cargo bench` + 火焰图/pprof；记录 p50/p95
4) 运行时检查：Miri/ASAN/TSAN 在关键组件上按阶段启用
5) 形式化：对高风险模块采用 Kani/Prusti 做关键属性验证
6) 指标：统一 `/metrics` 输出，持续观测与 SLO 追踪

## 工具速查

- Clippy：`cargo clippy -- -D warnings`
- Miri：`cargo +nightly miri test`
- Fuzz：`cargo fuzz run fuzz_target_1`
- Kani：`cargo kani`
- Prusti：参见官方文档与 `cargo prusti`

## 规范入口（工具链映射）

- 包管理：[`../06_toolchain_ecosystem/02_package_manager/00_index.md`](../06_toolchain_ecosystem/02_package_manager/00_index.md)
- 构建工具：[`../06_toolchain_ecosystem/03_build_tools/00_index.md`](../06_toolchain_ecosystem/03_build_tools/00_index.md)
- 测试框架：[`../06_toolchain_ecosystem/04_testing_frameworks/00_index.md`](../06_toolchain_ecosystem/04_testing_frameworks/00_index.md)
- 代码分析：[`../06_toolchain_ecosystem/05_code_analysis/00_index.md`](../06_toolchain_ecosystem/05_code_analysis/00_index.md)
- 运行时检查（Miri）：[`../06_toolchain_ecosystem/03_miri/00_index.md`](../06_toolchain_ecosystem/03_miri/00_index.md)
- 模糊测试：[`../06_toolchain_ecosystem/04_fuzz/00_index.md`](../06_toolchain_ecosystem/04_fuzz/00_index.md)
- 形式化工具：[`../06_toolchain_ecosystem/05_formal/00_index.md`](../06_toolchain_ecosystem/05_formal/00_index.md)

## 导航

- 返回根：[`rust-formal-engineering-system/README.md`](../README.md)
- 设计模式：[`03_design_patterns/`](../03_design_patterns/)
- 编程范式：[`02_programming_paradigms/`](../02_programming_paradigms/)
