# 基准测试指南（Criterion）


## 📊 目录

- [基准测试指南（Criterion）](#基准测试指南criterion)
  - [📊 目录](#-目录)
  - [目标](#目标)
  - [运行](#运行)
  - [结果位置](#结果位置)
  - [回归判断建议](#回归判断建议)
  - [与 CI 配合](#与-ci-配合)
  - [附：场景基准](#附场景基准)


## 目标

- 指导如何运行与阅读本仓库的 Criterion 基准；
- 结合 CI 独立工作流进行可复现实验；
- 为回归判断提供简单可操作的门槛建议。

## 运行

```bash
# 本地运行全部基准
cargo bench | cat

# 启用 tokio 异步基准
cargo bench --features tokio-bench | cat
```

## 结果位置

- 报告目录：`target/criterion/*`
- 含 HTML/CSV 等输出，可在 CI 工作流产出 artifact 后下载查看。

## 回归判断建议

- 选定关键基准（如 `pattern_scenarios/*`、`rayon_parallel_sum`）。
- 与上一次基线对比：若 p95 时延回退 ≥5%，标记为潜在回归。
- 重试 3 次取均值，排除偶发波动；必要时固定 CPU 频率与隔离负载。

## 与 CI 配合

- 通过 `Bench` 工作流（`workflow_dispatch`）在稳定环境下运行，上传 `target/criterion` 目录与控制台输出。
- 可后续扩展：将选定指标扫描为 JSON 并做门槛校验，失败时置红阻断合并。

## 附：场景基准

- `benches/pattern_scenarios.rs`：包含责任链、装饰器、代理的轻量模拟。
- `benches/pattern_benchmarks.rs`：包含 `rayon` 并行与（可选）`tokio` 异步任务基准。
