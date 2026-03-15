# 📚 Rust 系统化学习文档中心

> 版本: Rust 1.94.0+ | Edition 2024 | 最后更新: 2026-03-15

---

## 📂 目录结构

```text
docs/
├── 00_MASTER_INDEX.md          # 主索引 - 从这里开始
├── 01_learning/                # 学习路径和教程
│   ├── LEARNING_PATH_PLANNING.md
│   ├── OFFICIAL_RESOURCES_MAPPING.md
│   └── quizzes/               # 互动测验
├── 02_reference/              # 参考资料
│   ├── quick_reference/       # 快速参考卡片
│   ├── ALIGNMENT_GUIDE.md
│   └── STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS.md
├── 04_thinking/               # 思维表示
│   ├── mindmaps/              # 思维导图
│   ├── matrices/              # 矩阵分析
│   └── decision_trees/        # 决策树
├── 05_guides/                 # 实用指南
│   ├── BEST_PRACTICES.md
│   ├── DESIGN_PATTERNS_USAGE_GUIDE.md
│   └── ASYNC_PROGRAMMING_USAGE_GUIDE.md
├── 06_toolchain/              # 工具链文档
├── 07_project/                # 项目文档
├── research_notes/            # 研究笔记
├── templates/                 # 文档模板
└── archive/                   # 归档文档
```

---

## 🚀 快速开始

### 新手入门

1. 阅读 [`crates/c01_ownership/README.md`](../crates/c01_ownership/README.md) - 所有权系统
2. 完成 [`crates/c01_ownership/exercises/`](../crates/c01_ownership/exercises/) - 配套练习
3. 参考 [`docs/02_reference/quick_reference/`](./02_reference/quick_reference/) - 快速参考

### 进阶学习

1. [`docs/05_guides/BEST_PRACTICES.md`](./05_guides/BEST_PRACTICES.md) - 最佳实践
2. [`docs/05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md`](./05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md) - 设计模式
3. [`content/`](../content/) - 生产实践和前沿特性

### 参考查阅

- [`docs/02_reference/ERROR_CODE_MAPPING.md`](./02_reference/ERROR_CODE_MAPPING.md) - 错误代码速查
- [`docs/02_reference/CROSS_LANGUAGE_COMPARISON.md`](./02_reference/CROSS_LANGUAGE_COMPARISON.md) - 语言对比

---

## 📊 文档统计

| 分类 | 文件数 | 核心文档 |
|------|--------|----------|
| 学习路径 | 4 | 学习规划、资源映射 |
| 参考资料 | 6 | 标准库分析、错误映射 |
| 思维表示 | 84 | 思维导图、矩阵、决策树 |
| 实用指南 | 15+ | 最佳实践、设计模式 |
| 研究笔记 | 30+ | 形式化方法、学术前沿 |

---

## 🔗 关联资源

- **源码**: [`crates/`](../crates/) - 12 个学习模块，1,312+ 测试
- **新内容**: [`content/`](../content/) - 生产实践、前沿特性
- **示例**: [`examples/`](../examples/) - 可运行代码示例
- **书籍**: [`book/`](../book/) - mdBook 格式教程

---

## 📝 贡献指南

1. 文档使用 Markdown 格式
2. 遵循 [EDITORCONFIG](../.editorconfig) 规范
3. 新增文档请更新本 README

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 100% 完成并持续维护
