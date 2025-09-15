# 工具链与生态（Toolchain & Ecosystem）索引

## 目的

- 统一构建、检查、调试、基准、模糊与验证工具的入口与最佳实践。

## 工具速览

- 构建与脚本：`cargo`、`just`、工作区管理
- 代码质量：`clippy`、`cargo udeps`、格式化
- 运行时检查：`miri`、`asan/tsan/lsan`
- 模糊测试：`cargo-fuzz`、AFL++
- 基准与剖析：`criterion`、`perf`/`vtune`/`WPA`、`pprof`
- 形式化：`kani`、`prusti`、`creusot`

## 常用命令导航（最小）

- Lint：`cargo clippy -- -D warnings`
- Format：`cargo fmt --all`
- Fuzz（示例）：`cargo fuzz run fuzz_target_1`
- Miri：`cargo +nightly miri test`
- Bench：`cargo bench -p <crate>` 或 `--no-run`

## 仓库参考

- 质量保障：[`../10_quality_assurance/00_index.md`](../10_quality_assurance/00_index.md)
- 异步与线程：`crates/c06_async/`、`crates/c05_threads/`

## 导航

- 返回根：[`rust-formal-engineering-system/README.md`](../README.md)
- 软件工程：[`../05_software_engineering/00_index.md`](../05_software_engineering/00_index.md)
- 质量保障：[`../10_quality_assurance/00_index.md`](../10_quality_assurance/00_index.md)
