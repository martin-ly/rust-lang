# 项目重组计划

> **目标**: 基于已完成的Rust 1.94现代化工作，全面重组项目结构
> **日期**: 2026-03-18
> **状态**: 执行中

---

## 当前问题分析

### 1. 根目录混乱

- 30+个重复/相似的完成报告（RUST_194_*, FINAL_*等）
- 多个版本的README和索引
- 大量临时/过程性文档堆积

### 2. 文档结构不清晰

- docs目录有8个子目录，但分类逻辑不够明确
- 40个md文件分散，难以快速定位
- 缺少统一的导航和索引

### 3. 重复内容

- 多个"100%完成报告"内容重复
- 决策树、路线图等文档版本过多
- 归档策略不统一

---

## 新组织架构设计

### 核心理念

```
清晰层级 + 单一真相源 + 权威引用 + 易于导航
```

### 新目录结构

```
rust-lang/
├── README.md                      # 项目主入口，简洁清晰
├── CONTRIBUTING.md                # 贡献指南
├── LICENSE                        # 许可证
├── Cargo.toml                     # Workspace配置
├── Cargo.lock                     # 依赖锁定
├── rust-toolchain.toml            # 工具链配置
│
├── 00_meta/                       # 元数据与项目治理
│   ├── project_charter.md         # 项目章程
│   ├── governance.md              # 治理结构
│   └── history/                   # 项目历史
│       └── 2026_reorganization.md # 本次重组记录
│
├── 01_docs/                       # 核心文档（精简整合）
│   ├── 00_index.md                # 文档总索引
│   ├── 01_getting_started.md      # 快速开始
│   ├── 02_ecosystem_review/       # 生态梳理（权威引用版）
│   │   └── 2026_comprehensive_review.md
│   ├── 03_authoritative_sources/  # 权威来源汇总
│   │   └── citations.md
│   ├── 04_guides/                 # 使用指南
│   │   ├── migration_2026.md
│   │   └── best_practices.md
│   └── 05_roadmap/                # 路线图
│       └── 2026_roadmap.md
│
├── 02_crates/                     # 代码crate（保持现有）
│   ├── c01_ownership_borrow_scope/
│   ├── c02_type_system/
│   ├── c03_control_fn/
│   ├── c04_generic/
│   ├── c05_threads/
│   ├── c06_async/
│   ├── c07_process/
│   ├── c08_algorithms/
│   ├── c09_design_pattern/
│   ├── c10_networks/
│   ├── c11_interop/
│   └── c12_wasm/
│
├── 03_examples/                   # 示例代码（整合）
│   ├── 01_basic/
│   ├── 02_advanced/
│   └── 03_real_world/
│
├── 04_scripts/                    # 脚本工具（整合）
│   ├── setup/
│   ├── maintenance/
│   └── archive/
│
├── 05_tests/                      # 测试（整合）
│   ├── unit/
│   ├── integration/
│   └── miri/
│
├── 06_archive/                    # 归档（统一）
│   ├── 2026_03_reorganization/    # 本次重组归档
│   ├── deprecated_content/        # 过时内容
│   └── historical_reports/        # 历史报告
│
├── 07_config/                     # 配置文件（整合）
│   ├── .cargo/
│   ├── .github/
│   ├── .vscode/
│   ├── clippy.toml
│   └── rustfmt.toml
│
└── 08_assets/                     # 静态资源
    ├── images/
    └── diagrams/
```

---

## 文件迁移计划

### 根目录文件迁移

| 当前文件 | 操作 | 目标位置 |
|---------|------|---------|
| README.md | 重写 | README.md（精简版） |
| README.en.md | 迁移 | 01_docs/README.en.md |
| MASTER_INDEX_AUTO.md | 重写 | 01_docs/00_index.md |
| PROJECT_STRUCTURE.md | 删除 | 内容整合到新README |
| KNOWLEDGE_STRUCTURE.md | 迁移 | 01_docs/02_ecosystem_review/ |
| DECISION_TREES.md | 迁移 | 01_docs/05_roadmap/ |
| LEARNING_CHECKLIST.md | 迁移 | 01_docs/01_getting_started.md |
| VERSION_INDEX.md | 删除 | 内容整合 |
| CONTRIBUTING.md | 保持 | CONTRIBUTING.md |
| LICENSE | 保持 | LICENSE |

### 完成报告整合

**当前问题**: 20+个完成报告文件

**解决方案**: 整合为3个核心文档

| 新文档 | 整合来源 |
|-------|---------|
| 06_archive/2026_03_reorganization/COMPLETION_REPORT_FINAL.md | 所有RUST_194_*报告 |
| 06_archive/2026_03_reorganization/AUTHORITATIVE_ALIGNMENT_REPORT.md | FINAL_AUTHORITATIVE_ALIGNMENT_REPORT.md |
| 01_docs/02_ecosystem_review/2026_comprehensive_review.md | 2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW_WITH_CITATIONS.md |

### docs目录重组

**当前**: 8个子目录 + 40个文件
**新结构**: 5个核心目录

```
01_docs/
├── 00_index.md                          # 新：统一索引
├── 01_getting_started.md                # 整合：快速开始
├── 02_ecosystem_review/                 # 保留：生态梳理
│   └── 2026_comprehensive_review.md     # 迁移+权威引用
├── 03_authoritative_sources/            # 新：权威来源
│   └── citations.md
├── 04_guides/                           # 整合：原05_guides + 其他
│   ├── migration_2026.md
│   ├── best_practices.md
│   └── tree_borrows_guide.md
└── 05_roadmap/                          # 整合：路线图
    ├── 2026_roadmap.md
    └── sustainable_plan.md              # SUSTAINABLE_DEVELOPMENT_PLAN
```

---

## 新README设计

### 结构

```markdown
# Rust系统化学习项目

## 快速开始
- 项目简介（3句话）
- 系统要求
- 安装步骤

## 项目结构
（清晰的目录说明）

## 文档导航
- 生态梳理
- 使用指南
- 权威来源

## 贡献指南
## 许可证
```

---

## 实施步骤

### 阶段1: 创建新结构

1. 创建新目录
2. 移动现有文件到新位置
3. 删除重复/过时文件

### 阶段2: 整合文档

1. 合并重复的完成报告
2. 重写README
3. 创建统一索引

### 阶段3: 验证

1. 检查所有链接
2. 验证文件完整性
3. 更新CI配置

---

## 预期成果

### 文件数量对比

| 位置 | 当前 | 重组后 | 变化 |
|------|------|-------|------|
| 根目录md | 30+ | 3-5 | -80% |
| 核心文档 | 40 | 10-15 | -60% |
| 总文件数 | 大量 | 精简 | -70% |

### 导航体验

- 新用户可以在3步内找到任何文档
- 单一真相源，无重复内容
- 清晰的层级结构

---

## 风险评估

| 风险 | 概率 | 影响 | 缓解措施 |
|------|------|------|---------|
| 链接断裂 | 中 | 高 | 批量检查脚本 |
| 内容丢失 | 低 | 高 | 先复制后删除 |
| 历史记录丢失 | 中 | 中 | 保留原始文件到archive |

---

**批准**: 待确认
**执行**: 预计2-3小时
**验证**: 完成后全面检查
