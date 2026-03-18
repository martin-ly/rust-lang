# 文档中心

> **项目**: Rust系统化学习项目
> **版本**: 2026.03
> **最后更新**: 2026-03-18

---

## 📚 文档导航

### 核心文档

| 文档 | 描述 | 推荐人群 |
|------|------|---------|
| [00_MASTER_INDEX.md](00_MASTER_INDEX.md) | 文档总索引 | 所有人 |
| [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md](2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md) | **2026生态梳理（权威引用版）** | 所有开发者 |
| [AUTHORITATIVE_SOURCES_AND_CITATIONS.md](AUTHORITATIVE_SOURCES_AND_CITATIONS.md) | 学术论文引用汇总 | 研究人员 |
| [MIGRATION_GUIDE_2026.md](MIGRATION_GUIDE_2026.md) | 2026迁移指南 | 升级用户 |
| [TERMINOLOGY_STANDARD.md](TERMINOLOGY_STANDARD.md) | 术语标准 | 所有人 |

### 学习文档

| 文档 | 描述 | 位置 |
|------|------|------|
| 学习路径指南 | 学习路线规划 | [01_learning/](01_learning/) |
| 跨模块导航 | 模块间导航 | [01_learning/](01_learning/) |
| 跨模块学习路线图 | 详细学习路线 | [01_learning/](01_learning/) |
| 跨模块实战项目 | 实践项目指南 | [03_practice/](03_practice/) |

### 子目录分类

| 目录 | 内容类型 | 文件数 |
|------|---------|--------|
| [01_learning/](01_learning/) | 学习规划 | 7 |
| [02_reference/](02_reference/) | 参考资料 | 31 |
| [03_practice/](03_practice/) | 实践练习 | 2 |
| [04_thinking/](04_thinking/) | 思维方法 | 7 |
| [05_guides/](05_guides/) | 使用指南 | 30 |
| [06_toolchain/](06_toolchain/) | 工具链 | 21 |
| [07_project/](07_project/) | 项目管理 | 14 |

---

## 🎯 快速开始

### 新用户推荐路径

```
1. [项目README](../README.md)
   ↓
2. [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md](2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md)
   ↓
3. [01_learning/LEARNING_PATH_GUIDE_2025_10_24.md](01_learning/LEARNING_PATH_GUIDE_2025_10_24.md)
   ↓
4. [MIGRATION_GUIDE_2026.md](MIGRATION_GUIDE_2026.md)
```

### 研究人员路径

```
1. [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md](2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md)
   ↓
2. [AUTHORITATIVE_SOURCES_AND_CITATIONS.md](AUTHORITATIVE_SOURCES_AND_CITATIONS.md)
   ↓
3. [04_thinking/](04_thinking/) 和 [research_notes/](research_notes/)
```

---

## 📁 文档组织

```
docs/
├── 核心文档 (6个)          # 放在根目录，快速访问
│   ├── 00_MASTER_INDEX.md
│   ├── 2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md
│   ├── AUTHORITATIVE_SOURCES_AND_CITATIONS.md
│   ├── MIGRATION_GUIDE_2026.md
│   ├── TERMINOLOGY_STANDARD.md
│   └── README.md
│
├── 01_learning/            # 学习规划
├── 02_reference/           # 参考资料
├── 03_practice/            # 实践练习
├── 04_thinking/            # 思维方法
├── 05_guides/              # 使用指南
├── 06_toolchain/           # 工具链
├── 07_project/             # 项目管理
├── archive/                # 归档
├── backup/                 # 备份
├── research_notes/         # 研究笔记
├── rust-formal-engineering-system/  # 形式化工程
├── rust-ownership-decidability/     # 所有权可判定性
└── templates/              # 模板
```

---

## 🔬 权威来源

本项目引用以下权威来源：

### 学术论文

- **Tree Borrows**: PLDI 2025 Distinguished Paper (DOI: 10.1145/3735592)
- **Miri**: POPL 2026 (DOI: 10.1145/3704904)

### 官方来源

- Rust官方博客 (blog.rust-lang.org)
- Rust Edition Guide
- Miri官方文档

详见 [AUTHORITATIVE_SOURCES_AND_CITATIONS.md](AUTHORITATIVE_SOURCES_AND_CITATIONS.md)

---

## 📝 文档维护

### 命名规范

- 核心文档: 大写 snake_case
- 子目录文档: 使用连字符或下划线
- 日期标记: YYYY_MM_DD 格式

### 更新策略

1. **跟随Rust发布**: 每6周更新工具链文档
2. **学术跟踪**: 关注PLDI/POPL/ICFP等顶会
3. **定期归档**: 过时报告移入archive/

---

**返回项目主页**: [../README.md](../README.md)
**贡献指南**: [../CONTRIBUTING.md](../CONTRIBUTING.md)
