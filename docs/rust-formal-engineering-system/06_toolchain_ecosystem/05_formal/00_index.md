# 形式化工具（Formal Tools）索引


## 📊 目录

- [目标](#目标)
- [工具](#工具)
- [快速开始](#快速开始)
- [CI 集成建议](#ci-集成建议)
- [建议流程](#建议流程)
- [导航](#导航)


## 目标

- 在关键模块引入自动化/半自动化验证，提升正确性与可维护性。

## 工具

- Kani：基于模型检查的验证（`cargo kani`）
- Prusti：基于规范注解的验证（`cargo prusti`）
- Creusot：依赖 Coq 的证明体系（实验性）

## 快速开始

```bash
# Kani（需安装 kani 工具链）
cargo install kani-verifier
cargo kani --help

# Prusti（参考官方安装脚本）
cargo install prusti-launch
cargo prusti --help
```

## CI 集成建议

- 对关键并发结构和 unsafe 模块建立最小验证集的 CI job（按周跑）
- 将验证日志与证明工件归档，失败时阻断合并并回填工单

## 建议流程

1) 选择核心性质（如不死锁、队列有界、无越界访问）
2) 编写最小规格与 harness
3) 本地跑工具并修复问题后提交规格与结果

## 导航

- 返回工具链：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)

---

别名与规范说明：

- 本页为形式化工具专题页，编号为 `05_formal`。与“05_code_analysis”编号冲突已通过规范入口化处理：
  - 代码分析规范入口：[`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md)
  - 形式化工具亦在质量保障综述中：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
