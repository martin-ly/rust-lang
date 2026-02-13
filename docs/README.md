# 📚 Rust 学习系统 - 文档中心

> **项目主页**: [返回主 README](../README.md)
> **主索引**: [00_MASTER_INDEX.md](./00_MASTER_INDEX.md) - 按主题分类的完整文档导航

---

## 🎯 按主题快速导航

| 主题 | 入口 | 说明 |
|------|------|------|
| **学习路径** | [00_MASTER_INDEX § 01_learning](./00_MASTER_INDEX.md#01-学习路径与导航) | 学习规划、官方资源映射 |
| **速查参考** | [02_reference](#-核心文档系统) | 20 个速查卡、边界特例 |
| **形式化理论** | [03_theory](#-核心文档系统) | 研究笔记、证明索引 |
| **思维表征** | [04_thinking](./00_MASTER_INDEX.md#04-思维表征) | 思维导图、决策树、矩阵 |
| **专题指南** | [05_guides](./00_MASTER_INDEX.md#05-专题指南) | 异步、线程、WASM、Unsafe 等 |
| **工具链** | [06_toolchain](#-核心文档系统) | 编译器、Cargo、版本演进 |
| **项目元文档** | [07_project](./00_MASTER_INDEX.md#07-项目元文档) | 知识结构、版本追踪 |

---

## 🎯 按角色导航

- **初学者** → 学习路径 → 速查卡 → C01 模块
- **开发者** → 专题指南 → 速查卡 → 边界特例
- **研究者** → 形式化理论 → 思维表征 → 证明索引
- **维护者** → 项目元文档 → 版本追踪

---

## 🚀 核心文档系统

### 1. 快速参考（quick_reference/）

**用途**: 快速查找 Rust 语法、模式、最佳实践

**入口**: [quick_reference/README.md](./02_reference/quick_reference/README.md)

**包含**: 20 个速查卡（含 AI/ML、类型、所有权、异步、泛型、错误处理、线程、宏、测试等）

**特色**: 所有 20 个速查卡已完成交叉引用、反例速查，版本 Rust 1.93.0+

---

### 2. 研究笔记（research_notes/）

**用途**: 形式化方法、类型理论、软件设计理论

**入口**: [research_notes/README.md](./research_notes/README.md) | [形式化工程系统](./rust-formal-engineering-system/00_master_index.md)（索引层，映射到 research_notes）

**说明**: 形式化理论以 **research_notes** 为主内容，**rust-formal-engineering-system** 为索引映射层。

---

### 3. 工具链文档（06_toolchain/）

**用途**: 编译器、Cargo、rustdoc、Rust 1.89–1.93 版本演进

**入口**: [06_toolchain/README.md](./06_toolchain/README.md)

---

### 4. 完整文档索引

**所有根目录文档按主题分类** → [00_MASTER_INDEX.md](./00_MASTER_INDEX.md)

---

## 📊 文档统计

### 文档系统统计

- **快速参考**: 20 个速查卡 ⭐ (含 AI/ML、进程管理、网络编程、算法、设计模式、WASM)
- **研究笔记**: 45+ 个研究文档（研究笔记系统100%完成）
- **形式化系统**: 500+ 个理论文档
- **工具链文档**: 5 个工具指南（包含 Rust 1.93 vs 1.92 对比）
- **归档文件**: 100 个文件已归档
- **文档完善度**: 100% ✅（20/20 速查卡已统一添加「📚 相关文档 + 🧩 相关示例代码」）
- **交叉引用**: 100% ✅ (所有19个速查卡已完成交叉引用增强)
- **高级主题文档**: 100% ✅ (8个高级主题深度文档)
- **综合最佳实践**: 100% ✅ (10个最佳实践主题)

### rust-formal-engineering-system/ - 形式化系统

- **总数**: 500+ 个文件
- **模块**: 10 个主要模块
- **深度**: 理论 + 实践完整覆盖
- **状态**: ✅ 持续更新

---

## 🛠️ 文档管理

### 📦 归档说明

与主题不相关的文件已归档，保持主目录简洁：

- [归档说明](./archive/README.md) - 归档文件分类说明
- [归档总结报告](./archive/ARCHIVE_SUMMARY_2025_11_15.md) - 归档详情统计
- [归档完成报告](./archive/FINAL_ARCHIVE_COMPLETION_2025_11_15.md) - 归档工作总结

### 🧹 执行归档

如果需要整理文档结构：

```bash
# Linux/Mac
./scripts/archive_docs.sh

# Windows
scripts\archive_docs.bat
```

---

## 🔍 搜索文档

### 使用搜索工具

```bash
# 搜索关键词
cargo run -p rust-doc-search -- search "ownership"

# 正则表达式搜索
cargo run -p rust-doc-search -- search --regex "async.*await"

# 模糊搜索
cargo run -p rust-doc-search -- search --fuzzy "borrowing"
```

### 在线搜索

访问 mdBook 平台后，使用内置搜索功能（快捷键: `S`）

---

## 📞 获取帮助

### 问题和讨论

- 🐛 报告问题: [GitHub Issues](https://github.com/your-repo/rust-lang/issues)
- 💬 讨论交流: [GitHub Discussions](https://github.com/your-repo/rust-lang/discussions)

### 文档贡献

参见: [归档文件说明](./archive/README.md) - 查看归档的文件列表

---

## 🎉 最新更新

### 2026-02-13 🆕

- ✅ **主索引创建**：00_MASTER_INDEX.md 按主题分类导航
- ✅ **README 重构**：按主题分块展示，链至主索引
- ✅ **主题目录重组**：01_learning、02_reference、04_thinking、05_guides、06_toolchain、07_project
- ✅ **最佳实践合并**：BEST_PRACTICES_GUIDE + COMPREHENSIVE_BEST_PRACTICES → BEST_PRACTICES.md
- ✅ **版本文档归档**：RUST_192_* → archive/version_reports/；过程性文档 → archive/process_reports/
- ✅ **docs/docs 迁移**：14_workflow → 05_guides/workflow/
- ✅ **链接修复 100%**：MODULE_1.93、DOCUMENTATION_CROSS_REFERENCE_GUIDE、quick_reference、PROJECT_STRUCTURE、CONTRIBUTING、guides 等

### 2026-01-27 🆕

- ✅ **高级主题文档**：高级主题深度指南已创建（8个高级主题）
- ✅ **综合最佳实践**：综合最佳实践指南已创建（10个最佳实践主题）
- ✅ **性能测试报告**：性能测试报告已创建（46个基准测试文件汇总）
- ✅ **文档完善**：文档完善度达到 95%，整体项目完成度达到 90-95%

### 2026-01-26 🆕

- ✅ **交叉引用增强**：为所有19个速查卡统一添加/增强"相关资源"部分
- ✅ **版本一致性**：所有速查卡已更新到 Rust 1.93.0+
- ✅ **断链修复**：修复所有发现的文档断链
- ✅ **工具链文档**：Rust 1.93 vs 1.92 对比文档已整合
- ✅ **文档索引增强**：文档索引已增强，添加所有12个核心模块的文档和示例链接
- ✅ **文档完善**：文档完善度达到 87%，整体项目完成度达到 83%
- ✅ **高级主题文档**：高级主题深度指南已创建
- ✅ **综合最佳实践**：综合最佳实践指南已创建

### 2025-11-15

- ✅ 完成文件归档工作（101 个文件）
- ✅ 修复核心文档中的断开链接
- ✅ 更新文档结构说明
- ✅ 完善快速参考索引
- ✅ 优化文档导航

### 2025-10-30

- ✅ 创建文档导航中心
- ✅ 完成文档结构分析
- ✅ 提供归档自动化脚本
- ✅ mdBook 在线平台上线

---

**维护团队**: Rust Learning Community
**最后更新**: 2026-02-13
**状态**: ✅ **Rust 1.93.0 更新完成**

---

🦀 **开始探索 Rust 学习之旅！** 🦀
