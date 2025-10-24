# 质量保障（Quality Assurance）索引


## 📊 目录

- [质量保障（Quality Assurance）索引](#质量保障quality-assurance索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [版块](#版块)
  - [仓库内参考](#仓库内参考)
  - [建议流程](#建议流程)
    - [并发/异步专项最小清单](#并发异步专项最小清单)
    - [链接健壮性检查（指南）](#链接健壮性检查指南)
      - [脚本（Windows PowerShell）](#脚本windows-powershell)
  - [工具速查](#工具速查)
  - [规范入口（工具链映射）](#规范入口工具链映射)
  - [导航](#导航)


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

### 并发/异步专项最小清单

- 构建与干跑：
  - `cargo bench -p c05_threads --no-run | cat`
  - `cargo bench -p c06_async --no-run | cat`
- 运行与记录：
  - `cargo bench -p c05_threads | cat`、`cargo bench -p c06_async | cat`
  - 记录吞吐与 p95/p99；变更容量/并发/批量参数
- 可观测性：
  - 启用 `tracing`/metrics，在微服务端 `/metrics` 导出
- 交叉参考：
  - 最小基准指南：[`../02_programming_paradigms/11_benchmark_minimal_guide.md`](../02_programming_paradigms/11_benchmark_minimal_guide.md)
  - 并发/并行/响应式索引页中的文件级清单

### 链接健壮性检查（指南）

- 统一规则：优先相对路径；异步范式使用 `02_async` 主目录，`02_asynchronous` 仅保留跳转页。
- 新增文档：更新上层 `00_index.md` 与根 README 快速导航（如适用）。
- 快速检查：
  - IDE 中批量打开最近改动的链接并跳转验证。
  - Windows PowerShell：可用简易脚本遍历仓库内相对链接并检测目标是否存在（待工具脚本加入 `scripts/`）。
  - CI：建议加一条 `markdown-link-check` 步骤（可选）。

#### 脚本（Windows PowerShell）

```powershell
./scripts/ci/check_markdown_links.ps1
```

返回非零代表存在断链。可在 CI 中直接作为步骤执行。

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
