# C08 Algorithms 文档重组计划

## 🗂️ 新的目录结构

```text
c08_algorithms/
├── README.md                          # 主入口文档（简洁版）
├── Cargo.toml
├── CONTRIBUTING.md
├── CHANGELOG.md
│
├── docs/                              # 📚 文档根目录
│   ├── README.md                      # docs 入口（学习指南）
│   ├── 00_MASTER_INDEX.md            # 主索引（唯一索引）
│   ├── FAQ.md                         # 常见问题
│   ├── Glossary.md                    # 术语表
│   │
│   ├── guides/                        # 📖 指南文档
│   │   ├── README.md
│   │   ├── quickstart.md             # 快速开始
│   │   ├── algorithm_complexity.md    # 复杂度分析
│   │   ├── data_structures.md         # 数据结构
│   │   ├── async_algorithms.md        # 异步算法
│   │   ├── performance_optimization.md # 性能优化
│   │   └── benchmarking_guide.md      # 基准测试
│   │
│   ├── theory/                        # 🔬 理论文档
│   │   ├── README.md
│   │   ├── ALGORITHM_CLASSIFICATION_AND_MODELS.md
│   │   ├── FORMAL_ALGORITHM_MODELS.md
│   │   ├── ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md
│   │   ├── CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md
│   │   ├── DESIGN_PATTERNS_SEMANTICS_MAPPING.md
│   │   ├── ACTOR_REACTOR_CSP_PATTERNS.md
│   │   └── ASYNC_RECURSION_ANALYSIS.md
│   │
│   ├── advanced/                      # 🚀 高级专题
│   │   ├── README.md
│   │   ├── 01_type_design_for_algorithms.md    # exp01
│   │   ├── 02_advanced_sorting.md              # exp02
│   │   ├── 03_graph_algorithms.md              # exp03
│   │   ├── 04_dynamic_programming.md           # exp04
│   │   ├── 05_string_algorithms.md             # exp05
│   │   ├── 06_data_structures.md               # exp06
│   │   ├── 07_parallel_algorithms.md           # exp07
│   │   ├── 08_execution_models.md              # exp08
│   │   ├── 09_async_patterns.md                # exp09
│   │   ├── 10_optimization_techniques.md       # exp10
│   │   ├── 11_formal_verification.md           # exp11
│   │   ├── 12_distributed_algorithms.md        # exp12
│   │   ├── 13_machine_learning.md              # exp13
│   │   └── 14_algorithm_engineering.md         # exp14
│   │
│   ├── rust-features/                 # ✨ Rust 特性文档
│   │   ├── README.md
│   │   ├── rust_189_features.md
│   │   ├── RUST_189_FEATURES_GUIDE.md
│   │   ├── RUST_190_FEATURES_APPLICATION.md
│   │   └── Edition_2024_Features.md
│   │
│   ├── references/                    # 📚 参考文档
│   │   ├── README.md
│   │   ├── algorithm_index.md         # 算法索引
│   │   ├── ALGORITHM_INDEX_RUST_189.md
│   │   └── 08_algorithms_basics.md    # 从根目录移过来
│   │
│   └── archives/                      # 📦 归档文档
│       ├── README.md
│       ├── OVERVIEW.md                # 旧版概览
│       └── DOCUMENTATION_INDEX.md     # 旧版索引
│
├── examples/                          # 💻 示例代码
│   ├── README.md
│   ├── actor_reactor_csp_complete.rs
│   ├── async_recursion_comprehensive.rs
│   ├── comprehensive_algorithm_demo.rs
│   ├── comprehensive_formal_verification_demo.rs
│   └── rust_2024_features_demo.rs
│
├── src/                               # 源代码
├── tests/                             # 测试代码
├── benches/                           # 基准测试
│
└── reports/                           # 📊 项目报告（新建）
    ├── README.md
    ├── FINAL_PROJECT_STATUS.md
    ├── PROJECT_COMPLETION_SUMMARY_2025.md
    ├── RUST_190_ALIGNMENT_COMPLETION_FINAL.md
    └── ... (其他报告文件)
```

## 📋 执行步骤

### Phase 1: 清理和归档 (步骤 1-3)

- [ ] 1. 创建 `reports/` 目录并移动所有报告文件
- [ ] 2. 移动 `08_algorithms.md` 到 `docs/references/08_algorithms_basics.md`
- [ ] 3. 归档旧的索引文件到 `docs/archives/`

### Phase 2: 重组 docs 目录 (步骤 4-8)

- [ ] 4. 创建新的子目录结构 (guides/, theory/, advanced/, rust-features/, references/, archives/)
- [ ] 5. 重命名并移动 algorithm_exp*.md 文件到 advanced/ 目录
- [ ] 6. 移动理论文档到 theory/ 目录
- [ ] 7. 移动指南文档到 guides/ 目录
- [ ] 8. 移动 Rust 特性文档到 rust-features/ 目录

### Phase 3: 创建新的导航系统 (步骤 9-12)

- [ ] 9. 创建新的主索引 `docs/00_MASTER_INDEX.md`
- [ ] 10. 为每个子目录创建 README.md
- [ ] 11. 更新 FAQ.md 和 Glossary.md
- [ ] 12. 更新主 README.md

### Phase 4: 更新交叉引用 (步骤 13-14)

- [ ] 13. 更新所有文档中的链接
- [ ] 14. 验证所有链接的正确性

## 📝 文档映射表

### algorithm_exp 系列重命名

| 原文件 | 新文件 | 主题 |
 param($match) $match.Value -replace '[-:]+', ' --- ' -------- param($match) $match.Value -replace '[-:]+', ' --- ' 
| algorithm_exp01.md | 01_type_design_for_algorithms.md | Rust类型设计准则 |
| algorithm_exp02.md | 02_advanced_sorting.md | 高级排序算法 |
| algorithm_exp03.md | 03_graph_algorithms.md | 图算法 |
| algorithm_exp04.md | 04_dynamic_programming.md | 动态规划 |
| algorithm_exp05.md | 05_string_algorithms.md | 字符串算法 |
| algorithm_exp06.md | 06_data_structures.md | 数据结构 |
| algorithm_exp07.md | 07_parallel_algorithms.md | 并行算法 |
| algorithm_exp08.md | 08_execution_models.md | 执行模型 |
| algorithm_exp09.md | 09_async_patterns.md | 异步模式 |
| algorithm_exp10.md | 10_optimization_techniques.md | 优化技术 |
| algorithm_exp11.md | 11_formal_verification.md | 形式化验证 |
| algorithm_exp12.md | 12_distributed_algorithms.md | 分布式算法 |
| algorithm_exp13.md | 13_machine_learning.md | 机器学习 |
| algorithm_exp14.md | 14_algorithm_engineering.md | 算法工程 |

### 根目录报告文件归档

将以下文件移动到 `reports/` 目录：

- ASYNC_RECURSION_AND_CONCURRENCY_PATTERNS_SUMMARY.md
- COMPREHENSIVE_ENHANCEMENT_COMPLETE_REPORT.md
- COMPREHENSIVE_ENHANCEMENT_REPORT.md
- CONTINUOUS_DEVELOPMENT_PLAN.md
- FINAL_COMPLETION_REPORT.md
- FINAL_COMPLETION_SUMMARY.md
- FINAL_COMPREHENSIVE_SUMMARY.md
- FINAL_PROJECT_COMPLETION_SUMMARY.md
- FINAL_PROJECT_STATUS.md
- PROJECT_COMPLETION_REPORT.md
- PROJECT_COMPLETION_STATUS.md
- PROJECT_COMPLETION_SUMMARY_2025.md
- RUST_190_ALIGNMENT_COMPLETION_FINAL.md
- RUST_190_ALIGNMENT_COMPLETION_REPORT.md
- RUST_190_COMPREHENSIVE_UPGRADE_REPORT.md
- TASK_PROGRESS_REPORT.md

## ✅ 成功标准

1. 根目录只保留必要的顶级文件
2. docs 目录有清晰的分类结构
3. 所有文档有统一的格式和元数据
4. 单一的主索引文件
5. 所有链接都正确无误
6. 每个目录都有 README.md 导航

## 🎯 后续改进

1. 为每个文档添加统一的元数据（版本、作者、更新时间）
2. 创建自动化的文档链接检查工具
3. 建立文档更新规范
4. 添加更多示例和教程
