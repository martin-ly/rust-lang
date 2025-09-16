# Clippy 索引

## 目的

- 以 `cargo clippy` 作为静态检查基线，统一门槛与例外管理。

## 常用命令

- 全仓库：`cargo clippy -- -D warnings`
- 指定 crate：`cargo clippy -p <crate> -- -D warnings`
- 忽略规则（例外）：在局部使用 `#[allow(lint_name)]`，并在 PR 说明理由

## 快速开始

```bash
# 全仓库
cargo clippy -- -D warnings

# 指定包
cargo clippy -p c05_threads -- -D warnings
```

## CI 集成建议

- 在 CI 阶段新增 step：`cargo clippy -- -D warnings`
- 允许特定目录临时豁免需在 PR 说明，并创建修复 Issue 绑定里程碑

## 建议门槛

- 默认：`-D warnings`
- 临时过渡：在迁移期允许 `-A clippy::restriction` 子集，但需列出关闭清单

## 导航

- 返回工具链：[`../00_index.md`](../00_index.md)
- 质量标准：[`../../10_quality_assurance/01_standards/00_index.md`](../../10_quality_assurance/01_standards/00_index.md)

---

别名与规范说明：

- 本页为 Clippy 专题页，编号为 `02_clippy`。与“02_package_manager”编号冲突已通过规范入口化处理：
  - 包管理规范入口：[`../02_package_manager/00_index.md`](../02_package_manager/00_index.md)
  - Clippy 作为代码分析/质量的子专题，相关综述也可在：[`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md)
