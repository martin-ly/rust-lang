# 📚 Rust 学习系统 - 文档中心

> **项目主页**: [返回主 README](../README.md)
> **核心文档导航**: [docs/README.md](./README.md)（本文件）

---

## 🎯 文档结构概览

```text
docs/
├── README.md                      # 📋 文档中心主索引（本文件）
│
├── quick_reference/               # ⚡ 快速参考速查卡
│   ├── README.md
│   └── [19个速查卡文件] ⭐ (新增进程管理、网络编程、算法、设计模式、WASM速查卡)
│
├── research_notes/                # 🔬 研究笔记系统
│   ├── README.md
│   ├── formal_methods/            # 形式化方法研究
│   ├── type_theory/               # 类型理论研究
│   └── experiments/               # 实验研究
│
├── rust-formal-engineering-system/ # 🎓 形式化工程系统
│   ├── 00_master_index.md         # 主索引
│   ├── README.md
│   ├── 01_theoretical_foundations/  # 理论基础
│   ├── 02_programming_paradigms/    # 编程范式
│   ├── 03_design_patterns/          # 设计模式
│   └── ... (10个专业模块)
│
├── toolchain/                     # 🔧 工具链文档
│   ├── README.md
│   └── [4个工具链指南]
│
├── docs/                          # 📚 深度文档
│   └── [语言特性、参考文档等]
│
├── archive/                       # 📦 归档文件
│   ├── README.md                  # 归档说明
│   ├── spell_check/               # 拼写检查相关
│   ├── status/                    # 项目状态报告
│   ├── updates/                   # 更新报告
│   ├── reports/                   # 各种报告
│   └── temp/                      # 临时文件
│
└── backup/                        # 💾 备份文件（.rar）
```

---

## 🚀 快速入口

### 🌟 核心文档（必读）

**从这里开始** → [📋 文档中心主索引](./README.md)（本文件）

**主要文档系统**：

1. **[快速参考](./quick_reference/)** - 19个速查卡 ⭐ (新增进程管理、网络编程、算法、设计模式、WASM速查卡)，快速查找语法和模式
2. **[研究笔记](./research_notes/)** - 形式化方法、类型理论、实验研究
3. **[形式化工程系统](./rust-formal-engineering-system/)** - 完整的理论体系
4. **[工具链文档](./toolchain/)** - 编译器、Cargo、rustdoc 等工具指南

### 📚 四大文档系统

#### 1. 快速参考（quick_reference/）

**用途**: 快速查找 Rust 语法、模式、最佳实践

**入口**: [quick_reference/README.md](./quick_reference/README.md)

**包含**:

- 类型系统速查卡
- 所有权系统速查卡
- 异步编程速查卡
- 泛型编程速查卡
- 错误处理速查卡
- 线程与并发速查卡
- 宏系统速查卡
- 测试速查卡
- 控制流与函数速查卡
- 集合与迭代器速查卡
- 智能指针速查卡
- 模块系统速查卡
- 字符串与格式化速查卡
- Cargo 速查卡
- 进程管理速查卡 ⭐ NEW
- 网络编程速查卡 ⭐ NEW
- 算法与数据结构速查卡 ⭐ NEW
- 设计模式速查卡 ⭐ NEW
- WASM 速查卡 ⭐ NEW

**特色**:
- ✅ 所有19个速查卡已完成交叉引用增强
- ✅ 统一格式：官方文档、项目内部文档、相关速查卡
- ✅ 版本一致性：所有速查卡已更新到 Rust 1.93.0+

#### 2. 研究笔记（research_notes/）

**用途**: 深入的研究和形式化方法文档

**入口**: [research_notes/README.md](./research_notes/README.md)

**包含**:

- 形式化方法研究（所有权模型、借用检查器、异步状态机等）
- 类型理论研究（类型系统基础、Trait系统、生命周期等）
- 实验研究（性能基准、内存分析、编译器优化等）

#### 3. 形式化工程系统（rust-formal-engineering-system/）

**用途**: 完整的理论体系和实践文档

**入口**: [rust-formal-engineering-system/00_master_index.md](./rust-formal-engineering-system/00_master_index.md)

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

#### 4. 工具链文档（toolchain/）

**用途**: Rust 工具链使用指南

**入口**: [toolchain/README.md](./toolchain/README.md)

**包含**:

- 编译器特性详解
- Cargo 工作空间和依赖管理
- rustdoc 高级用法
- Rust 1.93 vs 1.92 对比 🆕
- Rust 1.91 vs 1.90 对比

---

## 🎯 按角色导航

### 👨‍🎓 学习者

**推荐路径**:

1. [快速参考](./quick_reference/README.md) - 快速查找语法和模式
2. [研究笔记](./research_notes/README.md) - 深入理解 Rust 核心概念
3. [形式化工程系统](./rust-formal-engineering-system/00_master_index.md) - 完整的理论体系
4. [工具链文档](./toolchain/README.md) - 工具使用指南

### 👨‍💻 开发者

**推荐路径**:

1. [快速参考](./quick_reference/) - 语法和模式速查
2. [研究笔记](./research_notes/) - 形式化方法和类型理论
3. [形式化工程系统](./rust-formal-engineering-system/) - 设计模式和实践
4. [工具链文档](./toolchain/) - Cargo、编译器、rustdoc

### 👨‍🔧 维护者

**推荐路径**:

1. [文档归档说明](./archive/README.md) - 归档文件说明
2. [归档总结报告](./archive/ARCHIVE_SUMMARY_2025_11_15.md) - 归档详情
3. [项目结构说明](../PROJECT_STRUCTURE.md) - 项目结构
4. [主 README](../README.md) - 项目概览

---

## 📊 文档统计

### 文档系统统计

- **快速参考**: 19 个速查卡 ⭐ (新增进程管理、网络编程、算法、设计模式、WASM速查卡)
- **研究笔记**: 45+ 个研究文档（研究笔记系统100%完成）
- **形式化系统**: 500+ 个理论文档
- **工具链文档**: 5 个工具指南（包含 Rust 1.93 vs 1.92 对比）
- **归档文件**: 100 个文件已归档
- **文档完善度**: 85% ✅
- **交叉引用**: 100% ✅ (所有19个速查卡已完成交叉引用增强)

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

### 2026-01-26 🆕

- ✅ **交叉引用增强**：为所有19个速查卡统一添加/增强"相关资源"部分
- ✅ **版本一致性**：所有速查卡已更新到 Rust 1.93.0+
- ✅ **断链修复**：修复所有发现的文档断链
- ✅ **工具链文档**：Rust 1.93 vs 1.92 对比文档已整合
- ✅ **文档索引增强**：文档索引已增强，添加所有12个核心模块的文档和示例链接
- ✅ **文档完善**：文档完善度达到 87%，整体项目完成度达到 83%

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
**最后更新**: 2026-01-26
**状态**: ✅ **Rust 1.93.0 更新完成**

---

🦀 **开始探索 Rust 学习之旅！** 🦀
