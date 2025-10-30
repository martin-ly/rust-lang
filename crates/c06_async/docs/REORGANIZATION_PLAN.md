# C06 异步编程文档重组方案

## 🎯 新目录结构

```text
docs/
├── README.md                          # 主入口文档
├── 00_MASTER_INDEX.md                # 完整索引导航
├── FAQ.md                            # 常见问题
├── Glossary.md                       # 术语表
│
├── guides/                           # 📚 学习指南
│   ├── 01_quick_start.md            # 快速开始（合并）
│   ├── 02_basics.md                 # 基础指南
│   ├── 03_advanced_topics.md        # 高级主题
│   ├── 04_best_practices.md         # 最佳实践
│   ├── 05_style_guide.md            # 代码风格
│   └── 06_run_guide.md              # 运行指南
│
├── core/                             # 🎓 核心概念系列
│   ├── 01_introduction_and_philosophy.md
│   ├── 02_runtime_and_execution_model.md
│   ├── 03_pinning_and_unsafe_foundations.md
│   ├── 04_streams_and_sinks.md
│   ├── 05_async_in_traits_and_ecosystem.md
│   └── 06_critical_analysis_and_advanced_topics.md
│
├── runtimes/                         # ⚙️ 运行时指南
│   ├── 01_comparison_2025.md        # 运行时对比
│   ├── 02_tokio_best_practices.md   # Tokio最佳实践
│   ├── 03_smol_best_practices.md    # Smol最佳实践
│   └── 04_cookbook.md               # 实战手册
│
├── patterns/                         # 📐 模式与实践
│   ├── 01_patterns_comparison.md    # 模式对比
│   ├── 02_patterns_and_pitfalls.md  # 模式与陷阱
│   └── 03_advanced_patterns.md      # 高级模式
│
├── performance/                      # ⚡ 性能优化
│   ├── 01_optimization_guide.md     # 优化指南
│   ├── 02_benchmark_analysis.md     # 基准分析
│   └── 03_benchmark_results.md      # 测试结果
│
├── ecosystem/                        # 🌐 生态系统
│   ├── 01_ecosystem_analysis_2025.md # 生态分析（合并）
│   ├── 02_language_features_190.md   # Rust 1.90特性
│   └── 03_formal_methods.md          # 形式化方法
│
├── references/                       # 📖 API参考
│   ├── api_reference.md             # API参考
│   ├── utils_reference.md           # 工具参考
│   └── msrv_compatibility.md        # 版本兼容性
│
├── comprehensive/                    # 📘 综合指南
│   ├── comprehensive_guide_2025.md  # 2025综合指南
│   └── ultimate_guide_cn.md         # 终极中文指南
│
├── views/                            # 👁️ 多视角分析
│   ├── README.md                    # 视角导航
│   ├── basic/                       # 基础视角
│   │   ├── view01.md
│   │   ├── ... view14.md
│   │   └── README.md
│   └── specialized/                 # 专题视角
│       ├── async_sync_view01.md
│       ├── async_sync_view02.md
│       ├── cpu_async_view01.md
│       ├── cpu_gpu_view01.md
│       ├── cpu_gpu_view02.md
│       ├── cpu_gpu_view03.md
│       └── README.md
│
├── tools/                            # 🔧 工具与配置
│   ├── tokio_console_tracing.md     # 调试工具
│   └── dashboards/                   # 监控面板
│       ├── gateway_dashboard.json
│       └── hybrid_dashboard.json
│
└── archives/                         # 📦 归档文档
    ├── README.md                     # 归档说明
    ├── old_readmes/                  # 旧README
    │   ├── README_OLD.md
    │   ├── README_OLD_BACKUP.md
    │   └── README_2.md
    ├── completion_reports/           # 完成报告
    │   ├── project_completion_summary.md
    │   ├── C06_ASYNC_完成总结_2025_10_19.md
    │   └── 异步编程全面梳理最终报告_2025_10_06.md
    └── deprecated/                   # 已废弃文档
        └── ai.md
```

---

## 📝 文件重命名规范

### 命名规则

1. **使用英文小写+下划线**: `async_basics_guide.md`
2. **添加编号前缀**: `01_quick_start.md`, `02_basics.md`
3. **去除冗余日期**: `comparison_2025.md` → `01_comparison_2025.md`
4. **简化过长名称**: `RUST_ASYNC_ECOSYSTEM_COMPREHENSIVE_ANALYSIS_2025.md` → `ecosystem_analysis_2025.md`

### 文件映射表

| 旧文件名 | 新文件名 | 操作 |
|---------|---------|------|
| `quick_start.md` + `QUICK_START_2025.md` | `guides/01_quick_start.md` | 合并 |
| `async_basics_guide.md` | `guides/02_basics.md` | 移动+重命名 |
| `async_advanced_topics.md` | `guides/03_advanced_topics.md` | 移动+重命名 |
| `async_best_practices.md` | `guides/04_best_practices.md` | 移动+重命名 |
| `async_style_guide.md` | `guides/05_style_guide.md` | 移动+重命名 |
| `run_guide.md` | `guides/06_run_guide.md` | 移动+重命名 |
| `ASYNC_RUNTIME_COMPARISON_2025.md` | `runtimes/01_comparison_2025.md` | 移动+重命名 |
| `tokio_best_practices_2025.md` | `runtimes/02_tokio_best_practices.md` | 移动+重命名 |
| `smol_best_practices_2025.md` | `runtimes/03_smol_best_practices.md` | 移动+重命名 |
| `async_cookbook_tokio_smol.md` | `runtimes/04_cookbook.md` | 移动+重命名 |
| `ASYNC_PATTERNS_COMPARISON_2025.md` | `patterns/01_patterns_comparison.md` | 移动+重命名 |
| `async_patterns_and_pitfalls.md` | `patterns/02_patterns_and_pitfalls.md` | 移动 |
| `advanced_patterns_summary.md` | `patterns/03_advanced_patterns.md` | 移动+重命名 |
| `async_performance_optimization_2025.md` | `performance/01_optimization_guide.md` | 移动+重命名 |
| `benchmark_analysis_guide.md` | `performance/02_benchmark_analysis.md` | 移动+重命名 |
| `benchmark_results.md` | `performance/03_benchmark_results.md` | 移动 |
| `RUST_ASYNC_ECOSYSTEM_...2025.md` + 2个 | `ecosystem/01_ecosystem_analysis_2025.md` | 合并 |
| `async_language_features_190.md` | `ecosystem/02_language_features_190.md` | 移动 |
| `formal_methods_async.md` | `ecosystem/03_formal_methods.md` | 移动+重命名 |
| `ASYNC_COMPREHENSIVE_GUIDE_2025.md` | `comprehensive/comprehensive_guide_2025.md` | 移动 |
| `ULTIMATE_ASYNC_GUIDE_2025_CN.md` | `comprehensive/ultimate_guide_cn.md` | 移动+重命名 |
| `tokio_console_and_tracing.md` | `tools/tokio_console_tracing.md` | 移动+重命名 |
| `view01.md` ... `view14.md` | `views/basic/view01.md` ... | 移动 |
| `views/*` | `views/specialized/*` | 移动并重命名 |

---

## 🔄 执行步骤

### 阶段1: 准备工作

- [x] 创建重组方案文档
- [ ] 备份当前文档目录
- [ ] 创建新的目录结构

### 阶段2: 核心文档迁移

- [ ] 移动核心概念系列 (01-06) 到 `core/`
- [ ] 整理并移动学习指南到 `guides/`
- [ ] 移动运行时文档到 `runtimes/`

### 阶段3: 专题文档迁移

- [ ] 移动模式文档到 `patterns/`
- [ ] 移动性能文档到 `performance/`
- [ ] 合并生态系统文档到 `ecosystem/`

### 阶段4: 参考与工具

- [ ] 移动参考文档到 `references/`
- [ ] 移动综合指南到 `comprehensive/`
- [ ] 整理工具文档到 `tools/`

### 阶段5: View与归档

- [ ] 重组view文档到 `views/`
- [ ] 归档旧文档到 `archives/`
- [ ] 删除冗余文件

### 阶段6: 更新与验证

- [ ] 更新主索引 `00_MASTER_INDEX.md`
- [ ] 更新主README `README.md`
- [ ] 更新所有文档内链接
- [ ] 验证所有链接有效性
- [ ] 更新上级目录的引用

---

## 📋 待处理文档清单

### 需要合并的文档

1. **快速开始指南** (2个 → 1个)
   - `quick_start.md`
   - `QUICK_START_2025.md`
   - 合并为: `guides/01_quick_start.md`

2. **生态系统分析** (3个 → 1个)
   - `RUST_ASYNC_ECOSYSTEM_COMPREHENSIVE_ANALYSIS_2025.md`
   - `async_ecosystem_comprehensive_analysis_2025.md`
   - `async_ecosystem_comprehensive_analysis.md`
   - 合并为: `ecosystem/01_ecosystem_analysis_2025.md`

3. **综合指南** (5个 → 2个)
   - 保留最新和最全的2个
   - 其他归档

### 需要归档的文档

1. **旧README** (3个)
   - `README_OLD.md`
   - `README_OLD_BACKUP.md`
   - `README (2).md`

2. **完成报告** (3个)
   - `project_completion_summary.md`
   - `C06_ASYNC_完成总结_2025_10_19.md`
   - `异步编程全面梳理最终报告_2025_10_06.md`

3. **其他** (3个)
   - `ai.md`
   - `ASYNC_SEMANTICS_COMPREHENSIVE_GUIDE.md` (如果与其他综合指南重复)
   - `COMPREHENSIVE_ASYNC_IMPLEMENTATION_SUMMARY_2025.md` (如果是报告)

---

## ✅ 重组后的优势

### 1. 清晰的层次结构

- 按功能分类的独立目录
- 每个目录专注一个主题
- 易于导航和查找

### 2. 统一的命名规范

- 英文小写+下划线
- 有序的编号前缀
- 简洁明了的名称

### 3. 减少冗余

- 合并重复内容
- 归档过时文档
- 保留最新最全版本

### 4. 更好的可维护性

- 模块化组织
- 便于更新维护
- 易于扩展新内容

### 5. 改进的学习体验

- 明确的学习路径
- 快速定位文档
- 降低学习曲线

---

## 🚨 注意事项

1. **保留所有原文件**: 先复制后移动，确保不丢失内容
2. **更新所有链接**: 文档间的相互引用需要批量更新
3. **验证功能**: 确保示例代码和测试仍能正常运行
4. **通知用户**: 如果是公开项目，需要发布迁移公告
5. **保留Git历史**: 使用 `git mv` 而非直接移动

---

**方案制定**: 2025-10-19
**预计执行时间**: 2-3小时
**风险等级**: 🟡 中等（主要是链接更新）
