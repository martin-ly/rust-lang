# 项目结构说明

> **完整目录结构与导航指南**

---

## 根目录文件

| 文件 | 说明 |
|:---|:---|
| [README.md](README.md) | 主入口，快速导航 |
| [PROJECT_STRUCTURE.md](PROJECT_STRUCTURE.md) | 本文件，目录结构说明 |

---

## 一级目录结构

```text
rust-ownership-decidability/
│
├── README.md                          # 主入口
├── PROJECT_STRUCTURE.md               # 目录结构说明
│
├── archive/                           # 归档文档
│   └── README.md
│
├── actor-specialty/                   # Actor模型专题
│   ├── README.md                      # 专题导航
│   ├── mindmaps/                      # 思维导图
│   ├── matrices/                      # 对比矩阵
│   ├── decision-trees/                # 决策树
│   ├── scenario-trees/                # 应用场景
│   ├── formal-proofs/                 # 定理证明
│   ├── theory/                        # 理论基础
│   ├── implementations/               # 实现对比
│   ├── patterns/                      # 设计模式
│   ├── distributed/                   # 分布式Actor
│   ├── case-studies/                  # 案例研究
│   └── examples/                      # 实战示例
│
├── async-specialty/                   # 异步编程专题
│   ├── README.md
│   ├── authoritative/                 # 权威来源
│   ├── ecosystem/                     # 生态系统
│   ├── embedded/                      # 嵌入式
│   ├── network/                       # 网络
│   └── practices/                     # 最佳实践
│
├── comprehensive-analysis/            # 综合分析专题
│   ├── README.md                      # 专题导航
│   ├── mindmaps/                      # 思维导图
│   ├── matrices/                      # 对比矩阵
│   ├── decision-trees/                # 决策树
│   ├── scenario-trees/                # 应用场景
│   ├── formal-framework/              # 形式化框架
│   ├── proofs/                        # 定理证明
│   ├── authoritative-sources/         # 权威来源
│   ├── case-studies/                  # 案例研究
│   ├── extensions/                    # 高级扩展
│   ├── design-patterns-comprehensive.md
│   ├── architecture-models-comparison.md
│   ├── open-source-analysis.md
│   └── COMPLETION_REPORT.md
│
├── case-studies/                      # 案例研究(总)
│   └── README.md
│
├── formal-proofs/                     # 形式化证明
│   └── README.md
│
├── formal-theory/                     # 形式化理论
│   └── README.md
│
├── comparative-analysis/              # 对比分析
│   └── README.md
│
├── core-concepts/                     # 核心概念
│   └── README.md
│
├── extensions/                        # 扩展内容
│   └── README.md
│
├── concepts/                          # 概念解析
│   └── README.md
│
├── visualizations/                    # 可视化
│   └── README.md
│
├── exercises/                         # 练习
│   └── README.md
│
├── audit_reports/                     # 审计报告
│   └── README.md
│
└── [编号目录]                          # 编号主题目录
    ├── 00-foundations/                # 理论基础
    ├── 01-core-concepts/              # 核心概念
    ├── 02-formal-models/              # 形式化模型
    ├── 03-verification-tools/         # 验证工具
    ├── 04-decidability-analysis/      # 可判定性
    ├── 05-comparative-study/          # 对比研究
    ├── 06-visualizations/             # 可视化
    ├── 07-references/                 # 参考文献
    ├── 08-advanced-topics/            # 高级主题
    ├── 09-exercises/                  # 练习
    ├── 10-research-frontiers/         # 研究前沿
    ├── 11-design-patterns/            # 设计模式
    ├── 12-concurrency-patterns/       # 并发模式
    ├── 13-architecture-patterns/      # 架构模式
    ├── 13-distributed-systems/        # 分布式系统
    ├── 14-architecture-patterns/      # 架构模式(扩展)
    └── 15-application-domains/        # 应用领域
```

---

## 目录说明

### 专题目录

| 目录 | 说明 | 文档数 |
|:---|:---|:---:|
| [actor-specialty/](actor-specialty/) | Actor模型完整专题 | 15 |
| [async-specialty/](async-specialty/) | 异步编程专题 | 9 |
| [comprehensive-analysis/](comprehensive-analysis/) | 综合分析专题 | 21 |

### 支持目录

| 目录 | 说明 |
|:---|:---|
| [case-studies/](case-studies/) | 案例分析总目录 |
| [formal-proofs/](formal-proofs/) | 形式化证明 |
| [formal-theory/](formal-theory/) | 形式化理论 |
| [comparative-analysis/](comparative-analysis/) | 对比分析 |
| [core-concepts/](core-concepts/) | 核心概念 |
| [extensions/](extensions/) | 扩展内容 |
| [concepts/](concepts/) | 概念解析 |
| [visualizations/](visualizations/) | 可视化 |
| [exercises/](exercises/) | 练习 |
| [audit_reports/](audit_reports/) | 审计报告 |
| [archive/](archive/) | 归档文档 |

### 编号主题目录

| 目录 | 主题 | 内容 |
|:---|:---|:---|
| [00-foundations/](00-foundations/) | 理论基础 | 线性逻辑、仿射类型、分离逻辑 |
| [01-core-concepts/](01-core-concepts/) | 核心概念 | 所有权、借用、生命周期 |
| [02-formal-models/](02-formal-models/) | 形式化模型 | RustBelt、语义模型 |
| [03-verification-tools/](03-verification-tools/) | 验证工具 | Miri、Kani、Creusot |
| [04-decidability-analysis/](04-decidability-analysis/) | 可判定性 | 复杂度分析 |
| [05-comparative-study/](05-comparative-study/) | 对比研究 | 类型系统对比 |
| [06-visualizations/](06-visualizations/) | 可视化 | 图表、流程图 |
| [07-references/](07-references/) | 参考文献 | 论文引用 |
| [08-advanced-topics/](08-advanced-topics/) | 高级主题 | 高级技巧 |
| [09-exercises/](09-exercises/) | 练习 | 练习题 |
| [10-research-frontiers/](10-research-frontiers/) | 研究前沿 | 最新进展 |
| [11-design-patterns/](11-design-patterns/) | 设计模式 | 模式目录 |
| [12-concurrency-patterns/](12-concurrency-patterns/) | 并发模式 | 并发模式 |
| [13-architecture-patterns/](13-architecture-patterns/) | 架构模式 | 架构模式 |
| [13-distributed-systems/](13-distributed-systems/) | 分布式系统 | 分布式 |
| [14-architecture-patterns/](14-architecture-patterns/) | 架构模式(扩展) | 扩展 |
| [15-application-domains/](15-application-domains/) | 应用领域 | 应用场景 |

---

## 快速导航

### 按主题查找

| 主题 | 推荐目录 |
|:---|:---|
| 理论基础 | 00-foundations/, formal-theory/ |
| 核心概念 | 01-core-concepts/, core-concepts/ |
| 形式化证明 | formal-proofs/, comprehensive-analysis/proofs/ |
| Actor模型 | actor-specialty/ |
| 异步编程 | async-specialty/, 02-formal-models/ |
| 设计模式 | 11-design-patterns/, comprehensive-analysis/ |
| 并发模式 | 12-concurrency-patterns/ |
| 架构模式 | 13-architecture-patterns/ |
| 案例研究 | case-studies/, comprehensive-analysis/case-studies/ |
| 练习题 | exercises/, 09-exercises/ |

### 按学习路径

**初学者**: 00-foundations/ → 01-core-concepts/ → comprehensive-analysis/

**进阶**: 02-formal-models/ → formal-proofs/ → actor-specialty/

**专家**: case-studies/ → 10-research-frontiers/ → extensions/

---

## 统计信息

```text
总目录数: 35+
总文件数: 300+
总行数: 130,000+
总定理: 1000+
```

---

**更新日期**: 2026-03-05
