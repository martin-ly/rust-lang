# 📚 Rust 学习系统 - 文档中心

> **项目主页**: [返回主 README](../README.md)
> **核心文档导航**: [docs/README.md](./docs/README.md)
> **在线文档**: [mdBook 平台](../book/README.md)

---

## 🎯 文档结构概览

```text
docs/
├── docs/                          # 📋 核心文档和报告
│   ├── README.md                 # 🌟 文档导航中心（从这里开始）
│   ├── 最新动态报告 (6个)        # 项目最新进展
│   ├── 学习指南 (8个)            # 学习路径和资源
│   ├── 质量报告 (6个)            # 代码和文档质量
│   ├── 完成报告 (6个)            # 各任务完成情况
│   └── archive/                  # 历史文档归档
│
├── rust-formal-engineering-system/ # 🔬 形式化工程系统
│   ├── 01_theoretical_foundations/  # 理论基础
│   ├── 02_programming_paradigms/    # 编程范式
│   ├── 03_design_patterns/          # 设计模式
│   └── ... (10个专业模块)
│
└── backup/                        # 💾 备份文件
```

---

## 🚀 快速入口

### 🌟 核心文档（必读）

**从这里开始** → [📋 文档导航中心](./docs/README.md)

这个页面包含：

- ✅ 最新项目动态（2025-10-30）
- ✅ 完整学习指南
- ✅ 质量保证报告
- ✅ 系统文档索引

### 📚 三大文档系统

#### 1. 核心文档（docs/docs/）

**用途**: 项目报告、学习指南、质量文档

**入口**: [docs/docs/README.md](./docs/README.md)

**包含**:

- 最新动态和里程碑
- 学习路线和实战项目
- 代码审查和质量报告
- 完成报告和系统文档

#### 2. 形式化工程系统（rust-formal-engineering-system/）

**用途**: 深入的理论和实践文档

**入口**: [rust-formal-engineering-system/README.md](./rust-formal-engineering-system/README.md)

**包含**:

- 01 - 理论基础（类型系统、内存安全、所有权等）
- 02 - 编程范式（同步、异步、函数式等）
- 03 - 设计模式（创建型、结构型、行为型）
- 04 - 应用领域（金融、游戏、IoT、AI等）
- 05 - 软件工程（架构、微服务、测试等）
- 06 - 工具链生态（编译器、Clippy、Miri等）
- 07 - 跨语言比较（与C++、Go、Python等对比）
- 08 - 实用示例
- 09 - 研究议程
- 10 - 质量保障

#### 3. 在线文档平台（book/）

**用途**: 在线阅读的 mdBook 文档

**入口**: [book/README.md](../book/README.md)

**功能**:

- 🌐 在线访问
- 🔍 全文搜索
- 🌙 暗色主题
- 📱 移动友好

---

## 🎯 按角色导航

### 👨‍🎓 学习者

**推荐路径**:

1. [学习路线图](./docs/CROSS_MODULE_LEARNING_ROADMAP_2025_10_25.md)
2. [学习路径指南](./docs/LEARNING_PATH_GUIDE_2025_10_24.md)
3. [实战项目集](./docs/CROSS_MODULE_PRACTICAL_PROJECTS_2025_10_25.md)
4. [进度追踪模板](./docs/LEARNING_PROGRESS_TRACKER_TEMPLATE_2025_10_25.md)

### 👨‍💻 开发者

**推荐路径**:

1. [代码审查报告](./docs/D1_CODE_REVIEW_REPORT_2025_10_25.md)
2. [代码示例验证](./docs/CODE_EXAMPLES_COMPREHENSIVE_VERIFICATION_2025_10_25.md)
3. [文档标准](./docs/DOCUMENTATION_STANDARDS.md)
4. [形式化工程系统](./rust-formal-engineering-system/README.md)

### 👨‍🔧 维护者

**推荐路径**:

1. [项目推进总结](./docs/PROJECT_ADVANCEMENT_SUMMARY_2025_10_30.md)
2. [剩余工作方向](./docs/REMAINING_WORK_DIRECTIONS_2025_10_25.md)
3. [部署清单](./docs/DEPLOYMENT_READY_CHECKLIST_2025_10_25.md)
4. [文档归档指南](./ARCHIVE_QUICK_GUIDE.md)

---

## 📊 文档统计

### docs/docs/ - 核心文档

- **总数**: 30 个核心文档
- **类型**: 报告、指南、标准、总结
- **状态**: ✅ 活跃维护
- **归档**: 85 个历史文档在 `archive/`

### rust-formal-engineering-system/ - 形式化系统

- **总数**: 500+ 个文件
- **模块**: 10 个主要模块
- **深度**: 理论 + 实践完整覆盖
- **状态**: ✅ 持续更新

---

## 🛠️ 文档管理

### 📦 归档说明

历史文档已归档，保持主目录简洁：

- [查看归档索引](./docs/archive/ARCHIVE_INDEX.md)
- [归档快速指南](./ARCHIVE_QUICK_GUIDE.md)
- [文档分析报告](./docs/DOCS_ANALYSIS_AND_CLASSIFICATION_2025_10_30.md)

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

参见: [文档标准](./docs/DOCUMENTATION_STANDARDS.md)

---

## 🎉 最新更新

### 2025-10-30

- ✅ 创建文档导航中心
- ✅ 完成文档结构分析
- ✅ 提供归档自动化脚本
- ✅ mdBook 在线平台上线

### 2025-10-25

- ✅ 完成 100% 核心任务
- ✅ 全文搜索功能上线
- ✅ 代码质量全面验证

---

**维护团队**: Rust Learning Community
**最后更新**: 2025-10-30
**状态**: ✅ **活跃维护中**

---

🦀 **开始探索 Rust 学习之旅！** 🦀
