# 包管理与工作区（Package Manager & Workspace）索引

## 📊 目录

- [包管理与工作区（Package Manager \& Workspace）索引](#包管理与工作区package-manager--workspace索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心主题](#核心主题)
  - [常用命令](#常用命令)
  - [相关条目](#相关条目)
  - [导航](#导航)

## 💻 实际文档示例

将包管理器形式化理论知识应用到实际文档中：

- **[Cargo 工作空间指南](../../../../../docs/toolchain/02_cargo_workspace_guide.md)** - 完整的 Cargo 使用指南
  - Workspace 配置和管理
  - 依赖版本统一和治理
  - Feature 管理和条件编译
  - 构建优化和 CI/CD 集成
  - 私有 Registry 和发布流程

**学习路径**: 形式化理论 → 实际文档 → 应用实践

---

## 目的

- 统一 `cargo` 包管理、工作区与依赖治理的最佳实践入口。
- 衔接构建工具、测试框架与质量保障的规范导航。

## 核心主题

- 工作区管理：`Cargo.toml` workspace、成员选择、`default-members`
- 依赖治理：版本范围、`cargo update -p`、`patch`/`replace`、镜像
- 特性管理：`features`、`default`、可选依赖与编译矩阵
- 发布流程：`cargo publish`、pre-release 检查、`cargo deny`

## 常用命令

```bash
# 工作区内构建/测试/基准
cargo build
cargo test
cargo bench --no-run

# 依赖审计与更新
cargo tree -p <crate>
cargo update -p <crate>@<version>
```

## 相关条目

- 构建工具：[`../03_build_tools/00_index.md`](../03_build_tools/00_index.md)
- 测试框架：[`../04_testing_frameworks/00_index.md`](../04_testing_frameworks/00_index.md)
- 代码分析：[`../05_code_analysis/00_index.md`](../05_code_analysis/00_index.md)

## 导航

- 返回工具链：[`../00_index.md`](../00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
