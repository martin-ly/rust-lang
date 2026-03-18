# 项目目录重构计划

## 当前问题诊断

### 1. 根目录混乱 (严重)
- 18个报告文件直接放根目录
- 7个Python脚本散落根目录
- 难以一眼识别项目结构

### 2. 文档入口混乱 (严重)
| 目录 | 文件数 | 用途 |
|------|--------|------|
| docs/ | 1381 | 旧文档中心 |
| knowledge/ | 43 | 新知识库 |
| content/ | 19 | 内容中心 |
| guides/ | 3 | 指南 |
| RUST_SAFETY_CRITICAL_ECOSYSTEM/ | 大量 | 安全关键生态 |

### 3. 报告泛滥
- 根目录: 18个报告
- archive/: 28个报告
- reports/: 5个报告
- 总计: 50+ 个报告文件

### 4. 脚本分散
- scripts/: 30个
- 根目录: 7个
- tools/: 4个

---

## 重构方案

### 目标结构

```
rust-lang/                          ← 项目根目录
├── README.md                       ← 项目主入口
├── Cargo.toml                      ← 工作区配置
├── LICENSE
├── CONTRIBUTING.md
├── CHANGELOG.md
├── FAQ.md
│
├── .github/                        ← CI/CD配置
├── .vscode/                        ← IDE配置
├── .cargo/                         ← Cargo配置
│
├── crates/                         ← 12个学习crate
│   ├── c01_ownership_borrow_scope/
│   ├── c02_type_system/
│   └── ...
│
├── knowledge/                      ← 📚 统一知识库 (主入口)
│   ├── INDEX.md                    ← 知识库索引
│   ├── README.md
│   ├── 00_start/                   ← 入门
│   ├── 01_fundamentals/            ← 基础
│   ├── 02_intermediate/            ← 进阶
│   ├── 03_advanced/                ← 高级
│   ├── 04_expert/                  ← 专家
│   ├── 05_reference/               ← 参考
│   ├── 06_ecosystem/               ← 生态
│   └── 99_archive/                 ← 归档
│
├── examples/                       ← 代码示例
│
├── exercises/                      ← 练习题
│
├── scripts/                        ← 所有脚本统一放这里
│   ├── maintenance/                ← 维护脚本
│   │   ├── analyze_doc_structure.py
│   │   ├── auto_add_structure.py
│   │   └── cleanup_unused_aliases.py
│   ├── fixes/                      ← 修复脚本
│   │   ├── find_cfg_gap.py
│   │   ├── find_clippy_issue.py
│   │   └── find_issue.py
│   └── utils/                      ← 工具脚本
│       └── enhance_placeholder_files.py
│
├── archive/                        ← 所有归档报告统一放这里
│   ├── reports/                    ← 历史报告
│   │   ├── 2026_03/
│   │   └── 2025/
│   └── deprecated/                 ← 废弃内容
│
└── tools/                          ← 开发工具
    └── doc_search/


### 废弃/合并的目录

```
docs/           → 内容合并到 knowledge/ 后删除
content/        → 内容合并到 knowledge/06_ecosystem/ 后删除
guides/         → 内容合并到 knowledge/05_reference/ 后删除
RUST_SAFETY_CRITICAL_ECOSYSTEM/ → 内容合并到 knowledge/04_expert/ 后删除
reports/        → 内容移动到 archive/reports/ 后删除
```

---

## 执行步骤

### Phase 1: 清理根目录 (优先)
1. 所有 `*_REPORT_*.md`, `*_COMPLETION_*.md`, `100_PERCENT_*.md` 移到 `archive/reports/2026_03/`
2. 所有 `.py` 脚本移到 `scripts/` 对应子目录
3. 根目录只保留核心文件 (README, Cargo.toml, LICENSE等)

### Phase 2: 统一文档入口
1. 确认 `knowledge/` 为主文档入口
2. 检查 `docs/` 内容，将有效内容迁移到 `knowledge/`
3. 检查 `content/`, `guides/`, `RUST_SAFETY_CRITICAL_ECOSYSTEM/` 内容
4. 合并后删除废弃目录

### Phase 3: 整理脚本
1. 所有脚本按功能分类到 `scripts/maintenance/`, `scripts/fixes/`, `scripts/utils/`
2. 删除重复或过期的脚本

### Phase 4: 验证
1. 验证所有链接有效
2. 验证 CI/CD 正常工作
3. 更新 README 指向新位置

---

## 文件清单

### 需要移动的报告文件 (根目录)
- 100_PERCENT_COMPLETION_FINAL_REPORT.md
- 100_PERCENT_COMPLETION_VERIFICATION_REPORT_2026_03_19.md
- 100_PERCENT_INTERNATIONAL_AUTHORITY_ALIGNMENT.md
- COMPLETION_100_PERCENT_SUMMARY.txt
- DOC_FIXES_REPORT.md
- FINAL_100_PERCENT_COMPLETION_REPORT_2026_03_19.md
- FINAL_100_PERCENT_VERIFICATION.md
- FINAL_COMPREHENSIVE_COMPLETION_REPORT.md
- KNOWLEDGE_BASE_COMPLETION_REPORT.md
- PROJECT_RESTructuring_COMPLETION_REPORT_2026_03_19.md
- INTERNATIONAL_CITATIONS_UPDATE_SUMMARY.md

### 需要移动的Python脚本 (根目录)
- analyze_doc_structure.py → scripts/maintenance/
- auto_add_structure.py → scripts/maintenance/
- cleanup_unused_aliases.py → scripts/maintenance/
- enhance_placeholder_files.py → scripts/utils/
- find_cfg_gap.py → scripts/fixes/
- find_clippy_issue.py → scripts/fixes/
- find_issue.py → scripts/fixes/

### 需要整合的目录
- docs/ → 合并到 knowledge/
- content/ → 合并到 knowledge/06_ecosystem/
- guides/ → 合并到 knowledge/05_reference/
- RUST_SAFETY_CRITICAL_ECOSYSTEM/ → 合并到 knowledge/04_expert/
- reports/ → 移动到 archive/reports/

---

## 预期结果

重构后:
- 根目录清晰: 只有核心文件
- 单一文档入口: knowledge/
- 脚本统一: scripts/
- 归档清晰: archive/
- 易于维护: 逻辑清晰
