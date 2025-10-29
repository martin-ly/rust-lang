# 质量标准（Standards）索引

## 📊 目录

- [质量标准（Standards）索引](#质量标准standards索引)
  - [📊 目录](#-目录)
  - [目标](#目标)
  - [标准清单（示例）](#标准清单示例)
  - [合规流程（建议）](#合规流程建议)
  - [CI 建议与门槛](#ci-建议与门槛)
  - [导航](#导航)

## 目标

- 明确质量基线与合规流程，统一测试、度量与验证的准入门槛。

## 标准清单（示例）

- 代码风格：`rustfmt` 通过；`clippy -D warnings` 零警告
- 测试覆盖：核心路径单元+集成测试齐备；新增模块需含最小属性测试
- 基准门槛：关键接口提供基准；记录 p50/p95 与资源占用
- 运行时检查：关键 unsafe/并发组件通过 `miri` 或 ASAN/TSAN 阶段性检查
- 文档与导航：新增目录需含 `00_index.md` 与返回/交叉导航
- 提交规范：Conventional Commits；CHANGELOG 更新

## 合规流程（建议）

1) 本地：`cargo fmt` → `cargo clippy -- -D warnings` → `cargo test`
2) 性能：`cargo bench`（或 `--no-run`）并保留基线
3) 运行时检查：`cargo +nightly miri test` 或 ASAN/TSAN 按需
4) 形式化：对高风险模块采用 Kani/Prusti 做关键属性验证
5) 文档：更新对应 `00_index.md` 与上级索引导航

## CI 建议与门槛

- Lint 门槛：`cargo clippy -- -D warnings` 作为必过项
- Test 门槛：`cargo test --workspace` 必需通过（含失败快照）
- Bench 建议：关键 crate 建议保留 `--no-run` 与采样基线（PR 比较）
- Miri 建议：含 unsafe 的 crate 按周跑；失败阻断合并
- Fuzz 建议：解析/编解码库夜间跑限定时长；崩溃样例归档
- Formal 建议：关键并发结构按周跑最小验证集

## 导航

- 返回质量保障：[`../00_index.md`](../00_index.md)
- 根：[`../../README.md`](../../README.md)
- 工具链：[`../../06_toolchain_ecosystem/00_index.md`](../../06_toolchain_ecosystem/00_index.md)
