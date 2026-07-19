# Miri 索引

## 📊 目录

- [Miri 索引](#miri-索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [常用命令](#常用命令)
  - [快速开始](#快速开始)
  - [CI 集成建议](#ci-集成建议)
  - [建议](#建议)
  - [导航](#导航)

## 目的

- 使用 Miri 进行未定义行为检测与借用规则的运行时检查。

## 常用命令

- 运行测试：`cargo +nightly miri test`
- 单用例：`cargo +nightly miri test -p <crate> <path::to::test>`
- 环境变量：`MIRIFLAGS=-Zmiri-strict-provenance`

## 快速开始

```bash
rustup toolchain install nightly
cargo +nightly miri setup
cargo +nightly miri test -p c05_threads
```

## CI 集成建议

- 在关键 crate 的 CI job 增加可选矩阵项运行 Miri（减少总体时长）
- 对含 unsafe 的路径按周跑 Miri，结果入库到工单系统

## 建议

- 对含 unsafe/并发细节的模块按阶段纳入 Miri 检查
- 记录发现的问题与规避策略在对应 `00_index.md`

## 导航

- 返回工具链：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

---

别名与规范说明：

- 本页为 Miri 专题页，编号为 `03_miri`。与“03_build_tools”编号冲突已通过规范入口化处理：
  - 构建工具规范入口：[`../03_build_tools/00_index.md`](../03_build_tools/00_index.md)
  - Miri 在代码分析/运行时检查的综述入口：[`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md)
