# c12_model 项目重新组织计划 2025

## 项目概述

本计划旨在重新梳理和优化 c12_model 项目的结构，提高代码质量、文档组织和维护性，确保项目符合 Rust 最佳实践。

## 一、当前项目状态评估（已更新至精简版）

### 1.1 项目优势 ✅

- **核心功能聚焦**：保留排队论、机器学习、形式化方法、数学模型、性能模型与通用工具
- **构建稳定**：`cargo check -p c12_model` 通过
- **文档简洁**：仅保留 API、指南、入门与开发文档

### 1.2 已解决的问题 ✅

- 清理重复与过时文档，移除与标准合规/企业框架/课程对标等非核心内容
- 移除可视化、基准测试、异步/并行可选特性及相关依赖
- 精简示例，保留核心示例与 README，引导串行实现
- 移除可执行入口，保持纯库 crate

## 二、目标（精简后）

- 保持代码与文档聚焦核心模型
- 统一错误处理与配置模块（已保留）
- 维持构建稳定与最小依赖集

## 三、实施记录（已完成）

- 文档结构：保留 `docs/api-reference/`、`docs/guides/`、`docs/getting-started/`、`docs/development/`、`docs/README.md`
- 删除目录/文件：`docs/architecture/`、`docs/domain/`、`docs/patterns/`、`docs/formal/` 下非核心文件；`docs/examples/basic-usage.md`；`docs/university_course_alignment.md`
- 代码裁剪：移除 `visualization.rs`、`benchmarks.rs`、`standards_compliance.rs`、`university_course_alignment.rs`、`maturity_models.rs`、`enterprise_frameworks.rs`
- Cargo 精简：移除 `tokio`、`rayon`、`nalgebra`、`plotly`、`wasm-bindgen` 及 wasm 目标依赖，删除相关 features
- 示例精简：删除国际标准相关示例与综合示例，保留核心三类示例
- 移除脚本：`run_examples.bat`、`run_examples.sh`

## 四、后续建议（可选）

- 在需要时以外部工具完成可视化或基准评估，不在仓库内内置
- 保持 API 与文档一致，新增功能时同步更新 `api-reference`

## 五、状态

- [x] 代码与文档裁剪
- [x] Cargo 配置精简
- [x] 示例与脚本清理
- [x] 构建通过
- [x] 文档与示例说明同步
