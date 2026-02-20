# docs 目录结构与格式审计报告

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 全面梳理 docs 所有文件的结构和格式，识别拼写和结构格式问题
> **上位文档**: [DOCS_STRUCTURE_OVERVIEW](./DOCS_STRUCTURE_OVERVIEW.md)

---

## 📊 目录

- [docs 目录结构与格式审计报告](#docs-目录结构与格式审计报告)
  - [📊 目录](#-目录)
  - [一、目录结构总览](#一目录结构总览)
    - [1.1 顶层结构（9 大模块）](#11-顶层结构9-大模块)
    - [1.2 各模块详细结构](#12-各模块详细结构)
      - [01\_learning（学习路径）](#01_learning学习路径)
      - [02\_reference（参考与速查）](#02_reference参考与速查)
      - [04\_thinking（思维表征）](#04_thinking思维表征)
      - [05\_guides（专题指南）](#05_guides专题指南)
      - [06\_toolchain（工具链与版本）](#06_toolchain工具链与版本)
      - [07\_project（项目元文档）](#07_project项目元文档)
  - [二、文件统计](#二文件统计)
  - [三、统一格式规范](#三统一格式规范)
    - [3.1 元信息规范（所有 .md 文件必需）](#31-元信息规范所有-md-文件必需)
    - [3.2 标题层级规范](#32-标题层级规范)
    - [3.3 目录块规范](#33-目录块规范)
    - [3.4 表格格式规范](#34-表格格式规范)
    - [3.5 链接格式规范](#35-链接格式规范)
    - [3.6 文末元信息块（核心研究笔记）](#36-文末元信息块核心研究笔记)
  - [四、常见格式问题清单](#四常见格式问题清单)
    - [4.1 元信息问题](#41-元信息问题)
    - [4.2 标题问题](#42-标题问题)
    - [4.3 表格问题](#43-表格问题)
    - [4.4 链接问题](#44-链接问题)
    - [4.5 中文格式问题](#45-中文格式问题)
  - [五、拼写检查配置](#五拼写检查配置)
    - [5.1 cspell.json 配置](#51-cspelljson-配置)
    - [5.2 常用 Rust 生态词汇（已在 cspell.json 中）](#52-常用-rust-生态词汇已在-cspelljson-中)
    - [5.3 添加新词汇](#53-添加新词汇)
  - [六、修复建议](#六修复建议)
    - [6.1 自动化检查脚本建议](#61-自动化检查脚本建议)
    - [6.2 批量修复任务](#62-批量修复任务)
    - [6.3 质量门禁建议](#63-质量门禁建议)
    - [6.4 季度复核建议](#64-季度复核建议)
  - [七、相关文档](#七相关文档)

---

## 一、目录结构总览

### 1.1 顶层结构（9 大模块）

```text
docs/
├── 00_MASTER_INDEX.md          # 文档中心主索引
├── DOCS_STRUCTURE_OVERVIEW.md  # 完整结构总览（本格式）
├── README.md                   # 文档中心入口
├── REFACTORING_COMPLETION_2026_02.md  # 重构完成报告
├── 01_learning/                # 学习路径与导航 (3 文件)
├── 02_reference/               # 参考与速查 (6 + 22 速查卡)
├── 04_thinking/                # 思维表征 (7 文件)
├── 05_guides/                  # 专题指南 (19 + workflow/)
├── 06_toolchain/               # 工具链与版本 (13 文件)
├── 07_project/                 # 项目元文档 (14 文件)
├── archive/                    # 归档文件 (120+ 文件)
├── backup/                     # 备份文件 (.rar/.zip)
├── research_notes/             # 研究笔记 (80+ 文件)
├── rust-formal-engineering-system/  # 形式化工程系统索引 (26+ 文件)
└── research_notes/             # 研究笔记子目录
    ├── formal_methods/         # 形式化方法 (6 篇核心)
    ├── type_theory/            # 类型理论 (4+ 文件)
    ├── software_design_theory/ # 软件设计理论 (23 模式 + 43 完全)
    ├── experiments/            # 实验 (5 文件)
    ├── coq_skeleton/           # Coq 证明骨架
    └── ...
```

### 1.2 各模块详细结构

#### 01_learning（学习路径）

| 文件 | 用途 |
| :--- | :--- |
| README.md | 模块入口 |
| LEARNING_PATH_PLANNING.md | 学习路径规划 |
| OFFICIAL_RESOURCES_MAPPING.md | 官方资源映射 |

#### 02_reference（参考与速查）

| 文件 | 用途 |
| :--- | :--- |
| README.md | 模块入口 |
| ALIGNMENT_GUIDE.md | 对齐知识综合 |
| CROSS_LANGUAGE_COMPARISON.md | 跨语言对比 |
| EDGE_CASES_AND_SPECIAL_CASES.md | 边界特例 |
| ERROR_CODE_MAPPING.md | 错误码映射 |
| STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 标准库分析 |
| quick_reference/ | 22 个速查卡 |

**quick_reference 速查卡列表**（22 个）:

- ownership_cheatsheet.md
- error_handling_cheatsheet.md
- async_patterns.md
- generics_cheatsheet.md
- type_system.md
- design_patterns_cheatsheet.md
- threads_concurrency_cheatsheet.md
- macros_cheatsheet.md
- algorithms_cheatsheet.md
- ai_ml_cheatsheet.md
- network_programming_cheatsheet.md
- process_management_cheatsheet.md
- smart_pointers_cheatsheet.md
- collections_iterators_cheatsheet.md
- strings_formatting_cheatsheet.md
- testing_cheatsheet.md
- wasm_cheatsheet.md
- cargo_cheatsheet.md
- control_flow_functions_cheatsheet.md
- modules_cheatsheet.md
- ANTI_PATTERN_TEMPLATE.md
- README.md

#### 04_thinking（思维表征）

| 文件 | 用途 |
| :--- | :--- |
| README.md | 模块入口 |
| THINKING_REPRESENTATION_METHODS.md | 思维表征方法 |
| DECISION_GRAPH_NETWORK.md | 决策图网络 |
| PROOF_GRAPH_NETWORK.md | 证明图网络 |
| MIND_MAP_COLLECTION.md | 思维导图集合 |
| MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | 多维概念矩阵 |
| APPLICATIONS_ANALYSIS_VIEW.md | 应用场景分析 |

#### 05_guides（专题指南）

| 文件 | 用途 |
| :--- | :--- |
| README.md | 模块入口 |
| ASYNC_PROGRAMMING_USAGE_GUIDE.md | 异步编程 |
| THREADS_CONCURRENCY_USAGE_GUIDE.md | 线程并发 |
| DESIGN_PATTERNS_USAGE_GUIDE.md | 设计模式 |
| MACRO_SYSTEM_USAGE_GUIDE.md | 宏系统 |
| WASM_USAGE_GUIDE.md | WASM |
| UNSAFE_RUST_GUIDE.md | Unsafe Rust |
| AI_RUST_ECOSYSTEM_GUIDE.md | AI+Rust 生态 |
| CLI_APPLICATIONS_GUIDE.md | CLI 应用 |
| EMBEDDED_RUST_GUIDE.md | 嵌入式 Rust |
| TROUBLESHOOTING_GUIDE.md | 故障排查 |
| PERFORMANCE_TUNING_GUIDE.md | 性能调优 |
| PERFORMANCE_TESTING_REPORT.md | 性能测试报告 |
| TESTING_COVERAGE_GUIDE.md | 测试覆盖 |
| BEST_PRACTICES.md | 最佳实践 |
| ADVANCED_TOPICS_DEEP_DIVE.md | 高级主题 |
| CROSS_MODULE_INTEGRATION_EXAMPLES.md | 跨模块集成 |
| FINAL_DOCUMENTATION_COMPLETION_GUIDE.md | 文档完善指南 |
| workflow/01_workflow_theory.md | 工作流理论 |
| workflow/05_workflow_models.md | 工作流模型 |

#### 06_toolchain（工具链与版本）

| 文件 | 用途 |
| :--- | :--- |
| README.md | 模块入口 |
| 00_rust_2024_edition_learning_impact.md | 2024 Edition 影响 |
| 01_compiler_features.md | 编译器特性 |
| 02_cargo_workspace_guide.md | Cargo 工作空间 |
| 03_rustdoc_advanced.md | rustdoc 高级 |
| 04_rust_1.91_vs_1.90_comparison.md | 1.91 vs 1.90 |
| 05_rust_1.93_vs_1.92_comparison.md | 1.93 vs 1.92 |
| 06_rust_1.93_compatibility_notes.md | 1.93 兼容性 |
| 07_rust_1.93_full_changelog.md | 1.93 完整变更 |
| 08_rust_version_evolution_1.89_to_1.93.md | 1.89-1.93 演进 |
| 09_rust_1.93_compatibility_deep_dive.md | 1.93 深度兼容 |
| 10_rust_1.89_to_1.93_cumulative_features_overview.md | 累积特性 |
| 11_rust_1.93_cargo_rustdoc_changes.md | Cargo/rustdoc 变更 |

#### 07_project（项目元文档）

| 文件 | 用途 |
| :--- | :--- |
| README.md | 模块入口 |
| KNOWLEDGE_STRUCTURE_FRAMEWORK.md | 知识结构框架 |
| MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 模块知识结构 |
| DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 文档交叉引用 |
| DOCUMENTATION_THEME_ORGANIZATION_PLAN.md | 文档主题规划 |
| PROJECT_ARCHITECTURE_GUIDE.md | 项目架构 |
| RUST_RELEASE_TRACKING_CHECKLIST.md | 版本追踪 |
| TASK_INDEX.md | 任务索引 |
| MODULE_1.93_ADAPTATION_STATUS.md | 1.93 适配状态 |
| ONE_PAGE_SUMMARY_TEMPLATE.md | 一页纸模板 |
| PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md | 项目评估 |
| INTERNATIONAL_BENCHMARK_CRITICAL_EVALUATION_2026_02.md | 国际对标 |
| ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md | 对齐知识评估 |
| AUTHORITATIVE_ALIGNMENT_CRITICAL_EVALUATION_2026_02.md | 权威对齐评估 |

---

## 二、文件统计

| 模块 | Markdown 文件数 | 状态 |
| :--- | :--- | :--- |
| 01_learning | 3 | ✅ |
| 02_reference | 6 + 22 | ✅ |
| 04_thinking | 7 | ✅ |
| 05_guides | 19 + 2 | ✅ |
| 06_toolchain | 13 | ✅ |
| 07_project | 14 | ✅ |
| research_notes | 80+ | ✅ |
| archive | 120+ | ✅ 归档 |
| rust-formal-engineering-system | 26+ | ✅ 索引层 |
| **总计** | **405+** | ✅ |

---

## 三、统一格式规范

### 3.1 元信息规范（所有 .md 文件必需）

```markdown
> **创建日期**: YYYY-MM-DD
> **最后更新**: YYYY-MM-DD
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 📋 规划中 / 🔄 进行中 / ✅ 已完成
> **用途**: （可选）文档定位、推荐读者
```

**格式要求**:

- 每行一条 `> **key**: value`
- key 与冒号间无空格，冒号后一空格
- 日期格式统一为 `YYYY-MM-DD`
- Rust 版本统一为 `1.93.0+ (Edition 2024)`

### 3.2 标题层级规范

| 层级 | 规范 | 示例 |
| :--- | :--- | :--- |
| 一级标题（#） | **不含 emoji** | `# 文档标题` |
| 二级标题（##） | 可选 emoji，同类文档统一 | `## 📊 目录` 或 `## 目录` |
| 三级标题（###） | 视内容需要 | `### 子节标题` |

### 3.3 目录块规范

```markdown
## 📊 目录

- [链接文本](#锚点)
  - [子节](#子节锚点)
```

**要求**:

- 统一使用 `## 📊 目录` 作为目录标题
- 至少包含到三级标题
- 使用标准 Markdown 链接格式

### 3.4 表格格式规范

```markdown
| 列名 1 | 列名 2 | 列名 3 |
| :--- | :--- | :--- |
| 内容 | 内容 | 内容 |
```

**要求**:

- 分隔行统一使用 `| :--- | :--- | :--- |`（左对齐）
- 列名清晰、简洁
- 同一文档内表格风格一致

### 3.5 链接格式规范

```markdown
[链接文本](相对路径)
```

**要求**:

- 使用相对路径（相对于 docs 根或当前目录）
- 格式：`[文本](路径)`
- 避免使用绝对路径或 URL（外部链接除外）

### 3.6 文末元信息块（核心研究笔记）

```markdown
---

**维护者**: 团队名称
**最后更新**: YYYY-MM-DD
**状态**: ✅ 已完成 / 🔄 进行中 / 📋 规划中
```

**适用文档**:

- formal_methods/ 下所有文档
- type_theory/ 下所有文档
- software_design_theory/ 下所有文档
- experiments/ 下所有文档

---

## 四、常见格式问题清单

### 4.1 元信息问题

| 问题 | 错误示例 | 正确示例 |
| :--- | :--- | :--- |
| 缺少 Rust 版本 | 无 | `> **Rust 版本**: 1.93.0+ (Edition 2024)` |
| 日期格式不一致 | `2026/2/20` | `2026-02-20` |
| key 后多余空格 | `> **创建日期** : 2026-02-20` | `> **创建日期**: 2026-02-20` |
| 冒号后无空格 | `> **创建日期**:2026-02-20` | `> **创建日期**: 2026-02-20` |
| 状态标记不统一 | `已完成`、`完成`、`Done` | `✅ 已完成` |

### 4.2 标题问题

| 问题 | 错误示例 | 正确示例 |
| :--- | :--- | :--- |
| 一级标题含 emoji | `# 📚 文档标题` | `# 文档标题` |
| 目录标题不统一 | `## 目录`、`## Table of Contents` | `## 📊 目录` |
| 层级跳跃 | `# 标题` → `### 子节` | `# 标题` → `## 节` → `### 子节` |

### 4.3 表格问题

| 问题 | 错误示例 | 正确示例 |
| :--- | :--- | :--- |
| 分隔行不对齐 | `| --- | --- |` | `| :--- | :--- | :--- |` |
| 列数不一致 | 两行列数不同 | 每行列数相同 |
| 混用对齐方式 | `|:---:|` 与 `|:---|` 混用 | 统一使用 `|:---|` |

### 4.4 链接问题

| 问题 | 错误示例 | 正确示例 |
| :--- | :--- | :--- |
| 绝对路径 | `[文本](/docs/path)` | `[文本](./path)` |
| 路径层级混乱 | `../../path` 过度使用 | 使用相对当前目录的合理层级 |
| 断链 | 指向不存在的文件 | 确保文件存在 |

### 4.5 中文格式问题

| 问题 | 错误示例 | 正确示例 |
| :--- | :--- | :--- |
| 中英文混排空格 | `Rust 编程` | `Rust编程` |
| 标点混用 | `Hello, 世界。` | `Hello，世界。` |
| 术语不统一 | `泛型` / `generics` | 统一使用 `泛型` |

---

## 五、拼写检查配置

### 5.1 cspell.json 配置

项目根目录已配置 `cspell.json`，支持：

- **语言**: 英语 (en) + 简体中文 (zh-CN)
- **文件类型**: markdown, rust, toml, yaml, json, javascript, typescript
- **忽略路径**: node_modules, target, .git, *.lock 等
- **自定义词典**: 已包含 250+ Rust 生态相关词汇

### 5.2 常用 Rust 生态词汇（已在 cspell.json 中）

```json
[
  "rustc", "rustup", "rustfmt", "clippy",
  "tokio", "serde", "actix", "axum", "hyper",
  "crossbeam", "rayon", "futures",
  "WASM", "WebAssembly", "wasm32",
  "const", "async", "await", "impl", "dyn",
  "RAII", "GATs", "RPITIT", "AFIT", "TAIT"
]
```

### 5.3 添加新词汇

如需添加新词汇到拼写检查白名单，编辑 `cspell.json` 的 `words` 数组：

```json
{
  "words": [
    "现有词汇",
    "新词汇"
  ]
}
```

---

## 六、修复建议

### 6.1 自动化检查脚本建议

建议创建以下检查脚本：

```powershell
# check_docs_format.ps1
# 检查文档格式合规性

# 1. 检查元信息完整性
# 2. 检查日期格式
# 3. 检查表格格式
# 4. 检查链接有效性
# 5. 检查标题层级
```

### 6.2 批量修复任务

| 优先级 | 任务 | 影响范围 |
| :--- | :--- | :--- |
| P0 | 补全缺失的 Rust 版本行 | 所有含 blockquote 的 .md |
| P0 | 统一日期格式为 YYYY-MM-DD | 所有 .md |
| P0 | 修复表格分隔行格式 | 所有含表格的 .md |
| P1 | 统一目录块标题为 `## 📊 目录` | 所有 .md |
| P1 | 移除一级标题中的 emoji | 所有 .md |
| P1 | 添加文末元信息块（核心研究笔记） | formal_methods/, type_theory/, software_design_theory/ |
| P2 | 统一术语使用 | 所有 .md |
| P2 | 修复中英文混排空格 | 所有 .md |

### 6.3 质量门禁建议

在 [CONTRIBUTING.md](research_notes/CONTRIBUTING.md) 中明确：

1. 新文档必须包含完整元信息
2. 表格必须使用 `:---` 左对齐格式
3. 一级标题不得使用 emoji
4. 所有内部链接必须有效
5. 日期格式必须为 YYYY-MM-DD

### 6.4 季度复核建议

在 [MAINTENANCE_GUIDE.md](research_notes/MAINTENANCE_GUIDE.md) 中增加：

1. 格式统一抽查
2. 链接有效性检查
3. 元信息完整性检查
4. 新增文档纳入 DOCS_STRUCTURE_OVERVIEW

---

## 七、相关文档

| 文档 | 说明 |
| :--- | :--- |
| [DOCS_STRUCTURE_OVERVIEW](./DOCS_STRUCTURE_OVERVIEW.md) | 完整结构总览 |
| [00_MASTER_INDEX](./00_MASTER_INDEX.md) | 文档中心主索引 |
| [QUALITY_CHECKLIST](research_notes/QUALITY_CHECKLIST.md) | 质量检查清单 |
| [FORMAT_AND_CONTENT_ALIGNMENT_PLAN](research_notes/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md) | 格式统一计划 |
| [CONTRIBUTING](research_notes/CONTRIBUTING.md) | 贡献指南 |
| [MAINTENANCE_GUIDE](research_notes/MAINTENANCE_GUIDE.md) | 维护指南 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-20
**状态**: ✅ **审计完成**
