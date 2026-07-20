# 基准与深度分析指南（bench_report CLI）

## 📊 目录

- [基准与深度分析指南（bench\_report CLI）](#基准与深度分析指南bench_report-cli)
  - [📊 目录](#-目录)
  - [快速开始](#快速开始)
  - [可选参数](#可选参数)
  - [类别与涵盖算法](#类别与涵盖算法)
  - [常见用法场景](#常见用法场景)
    - [与成熟库的对照基准（可选）](#与成熟库的对照基准可选)

本指南介绍如何使用 `bench_report` 一键生成可分析的数据（CSV/JSON），覆盖排序/搜索/图/分治/动态规划/字符串/回溯等模块。

---

## 快速开始

```bash
# 生成 CSV 到文件
cargo run -p c08_algorithms --bin bench_report --format csv --output report.csv

# 仅测试字符串算法，重复 5 次取最优，并输出 JSON
cargo run -p c08_algorithms --bin bench_report --select strings --repeat 5 --format json --output report.json
```

输出列（CSV）：

- category, algo, variant, param, size, unit, micros

JSON 输出为数组，每项包含上述字段。

---

## 可选参数

- --format csv|json：输出格式（默认 csv）
- --output 文件：输出路径（默认 stdout）
- --select 关键字：选择类别（包含关键字匹配，示例：sorting、searching、graph、dac、dp、strings、backtracking）
- --preset 名称：规模预设（当前支持：default、quick）
- --repeat 次数：重复 N 次取最优值（默认 1）

---

## 类别与涵盖算法

- sorting：quick（sync/parallel）
- searching：binary（sync）、linear（parallel）
- graph：bfs（sync）、dijkstra（sync）
- dac：max_subarray（parallel）
- dp：lcs（parallel）
- strings：kmp（sync）、rk（sync）、ac（sync）
- backtracking：nqueens（parallel，计数）

---

## 常见用法场景

- 对比并行与同步：`--select sorting --repeat 5 --format csv`
- 大规模排序（quick 预设）：`--select sorting --preset quick --format json`
- 生成多类别综合报告：不带 `--select` 全类别输出，重定向至文件后用表格工具分析

### 与成熟库的对照基准（可选）

启用特性：

```bash
cargo bench -p c08_algorithms --features "with-petgraph with-aho" --bench alg_benches
```

建议对照项：

- 图：自研 `dijkstra_sync` vs `petgraph` dijkstra（相同图规模/分布）。
- 字符串：自研 `Trie::ac_search` vs `aho-corasick`（相同模式集/文本分布）。

注意：报告中记录编译器版本、CPU、feature 集及参数，以便复现。

---

更多性能调优建议见 `docs/performance_optimization.md`，各模块复杂度与实现入口见 `docs/algorithm_complexity.md`。
