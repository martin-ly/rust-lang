# C08 Algorithms - 主索引

## 🗂️ 文档目录结构

```text
docs/
├── 00_MASTER_INDEX.md                         # 📍 本文档（主索引）
├── README.md                                  # 文档入口
├── FAQ.md                                     # 常见问题
├── Glossary.md                                # 术语表
│
├── 🆕 KNOWLEDGE_GRAPH.md                      # 📊 算法知识图谱
├── 🆕 MULTIDIMENSIONAL_MATRIX_COMPARISON.md   # 🎯 多维矩阵对比
├── 🆕 MIND_MAP.md                             # 🧠 思维导图
├── 🆕 RUST_190_RICH_EXAMPLES.md               # 💻 Rust 1.90 丰富示例
├── 🆕 INTERACTIVE_LEARNING_GUIDE.md           # 🎓 交互式学习指南
├── 🆕 VISUAL_CODE_EXAMPLES.md                 # 🎨 可视化示例库
│
├── guides/                                    # 📖 实用指南（基础到中级）
│   ├── README.md
│   ├── algorithm_complexity.md
│   ├── data_structures.md
│   ├── async_algorithms.md
│   ├── performance_optimization.md
│   └── benchmarking_guide.md
│
├── theory/                                    # 🔬 理论文档（高级）
│   ├── README.md
│   ├── ALGORITHM_CLASSIFICATION_AND_MODELS.md
│   ├── FORMAL_ALGORITHM_MODELS.md
│   ├── ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md
│   ├── CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md
│   ├── DESIGN_PATTERNS_SEMANTICS_MAPPING.md
│   ├── ACTOR_REACTOR_CSP_PATTERNS.md
│   └── ASYNC_RECURSION_ANALYSIS.md
│
├── advanced/                                  # 🚀 高级专题（中级到高级）
│   ├── README.md
│   └── algorithm_exp01-14.md                  # 14个专题文档
│
├── rust-features/                             # ✨ Rust 特性
│   ├── README.md
│   ├── rust_189_features.md
│   ├── RUST_189_FEATURES_GUIDE.md
│   ├── RUST_190_FEATURES_APPLICATION.md
│   └── Edition_2024_Features.md
│
├── references/                                # 📚 参考资料
│   ├── README.md
│   ├── algorithm_index.md
│   ├── ALGORITHM_INDEX_RUST_189.md
│   └── 08_algorithms_basics.md
│
└── archives/                                  # 📦 归档文档
    ├── README.md
    ├── OVERVIEW.md
    └── DOCUMENTATION_INDEX.md
```

---

## 📖 按类别浏览

### 1. 实用指南 (guides/)

适合日常开发和学习使用的实用文档。

| 文档 | 主要内容 | 适合人群 |
|------|---------|---------|
| [algorithm_complexity.md](./guides/algorithm_complexity.md) | 时间/空间复杂度、Big-O、主定理、摊还分析 | 初学者、面试准备 |
| [data_structures.md](./guides/data_structures.md) | 线性表、树、图、高级数据结构 | 所有开发者 |
| [async_algorithms.md](./guides/async_algorithms.md) | 异步算法设计、Tokio、Futures | 异步编程学习者 |
| [performance_optimization.md](./guides/performance_optimization.md) | 编译期优化、运行时优化、SIMD | 性能优化工程师 |
| [benchmarking_guide.md](./guides/benchmarking_guide.md) | Criterion、性能测试、对比分析 | 性能调优人员 |

**学习路径**: algorithm_complexity → data_structures → async_algorithms → performance_optimization

### 2. 理论文档 (theory/)

深入的形式化理论、数学模型和证明方法。

| 文档 | 主要内容 | 难度 |
|------|---------|------|
| [ALGORITHM_CLASSIFICATION_AND_MODELS.md](./theory/ALGORITHM_CLASSIFICATION_AND_MODELS.md) | 算法分类、形式化定义、计算模型、语义模型 | ⭐⭐⭐ |
| [FORMAL_ALGORITHM_MODELS.md](./theory/FORMAL_ALGORITHM_MODELS.md) | 算法形式化、图灵机、λ演算、霍尔逻辑 | ⭐⭐⭐ |
| [DESIGN_PATTERNS_SEMANTICS_MAPPING.md](./theory/DESIGN_PATTERNS_SEMANTICS_MAPPING.md) | 设计模式、语义模型、等价关系 | ⭐⭐⭐ |
| [ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md](./theory/ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md) | 异步同步等价性、CPS变换、证明 | ⭐⭐⭐ |
| [CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md](./theory/CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md) | 控制流形式化、状态机、等价性定理 | ⭐⭐⭐ |
| [ACTOR_REACTOR_CSP_PATTERNS.md](./theory/ACTOR_REACTOR_CSP_PATTERNS.md) | Actor模型、Reactor模式、CSP理论 | ⭐⭐⭐ |
| [ASYNC_RECURSION_ANALYSIS.md](./theory/ASYNC_RECURSION_ANALYSIS.md) | 异步递归、不动点理论、实现模式 | ⭐⭐⭐ |

**学习路径（理论研究）**: ALGORITHM_CLASSIFICATION → FORMAL_ALGORITHM_MODELS → ASYNC_SYNC_EQUIVALENCE

**学习路径（异步专家）**: ASYNC_SYNC_EQUIVALENCE → ACTOR_REACTOR_CSP → ASYNC_RECURSION

### 3. 高级专题 (advanced/)

深入的算法专题，涵盖各个领域。

| 文档 | 主题 | 关键词 |
|------|------|--------|
| [algorithm_exp01.md](./advanced/algorithm_exp01.md) | Rust类型设计准则 | 类型系统、泛型、策略模式 |
| [algorithm_exp02.md](./advanced/algorithm_exp02.md) | 高级排序算法 | 排序、自适应、并行 |
| [algorithm_exp03.md](./advanced/algorithm_exp03.md) | 图算法 | 图遍历、最短路径、MST |
| [algorithm_exp04.md](./advanced/algorithm_exp04.md) | 动态规划 | DP、状态压缩、优化 |
| [algorithm_exp05.md](./advanced/algorithm_exp05.md) | 字符串算法 | KMP、后缀数组、AC自动机 |
| [algorithm_exp06.md](./advanced/algorithm_exp06.md) | 高级数据结构 | 平衡树、线段树、跳表 |
| [algorithm_exp07.md](./advanced/algorithm_exp07.md) | 并行算法 | 并行模型、数据并行、任务并行 |
| [algorithm_exp08.md](./advanced/algorithm_exp08.md) | 执行模型全景 | 控制流、异步模型、形式化 |
| [algorithm_exp09.md](./advanced/algorithm_exp09.md) | 异步编程模式 | Future、状态机、执行器 |
| [algorithm_exp10.md](./advanced/algorithm_exp10.md) | 优化技术 | 缓存、内存、SIMD |
| [algorithm_exp11.md](./advanced/algorithm_exp11.md) | 形式化验证 | 类型证明、并发证明 |
| [algorithm_exp12.md](./advanced/algorithm_exp12.md) | 分布式算法 | Raft、Paxos、一致性 |
| [algorithm_exp13.md](./advanced/algorithm_exp13.md) | 机器学习算法 | 监督学习、神经网络 |
| [algorithm_exp14.md](./advanced/algorithm_exp14.md) | 算法工程 | 工程实践、调优、部署 |

**按兴趣选择**:

- 算法竞赛：exp02-05
- 系统编程：exp07-09
- 理论研究：exp08, exp11
- 分布式系统：exp12

### 4. Rust 特性 (rust-features/)

Rust 语言特性在算法中的应用。

| 文档 | 版本 | 主要内容 |
|------|------|---------|
| [rust_189_features.md](./rust-features/rust_189_features.md) | 1.89 | 特性概览 |
| [RUST_189_FEATURES_GUIDE.md](./rust-features/RUST_189_FEATURES_GUIDE.md) | 1.89 | 详细指南 |
| [RUST_190_FEATURES_APPLICATION.md](./rust-features/RUST_190_FEATURES_APPLICATION.md) | 1.90 | Async traits、GATs、应用 |
| [Edition_2024_Features.md](./rust-features/Edition_2024_Features.md) | 2024 | 新语法特性 |

**特性亮点**:

- ✅ Async traits（1.90+）
- ✅ GATs 稳定（1.90+）
- ✅ 常量泛型增强（1.90+）
- ✅ Edition 2024 语法

### 5. 参考资料 (references/)

快速查阅和索引文档。

| 文档 | 用途 | 适合场景 |
|------|------|---------|
| [algorithm_index.md](./references/algorithm_index.md) | 算法索引 | 快速查找算法 |
| [ALGORITHM_INDEX_RUST_189.md](./references/ALGORITHM_INDEX_RUST_189.md) | Rust 1.89索引 | 版本特定查询 |
| [08_algorithms_basics.md](./references/08_algorithms_basics.md) | 基础教程 | 入门学习 |

---

## 🎓 推荐学习路径

### 路径 1: 初学者 (2-3 周)

**目标**: 掌握基础算法和数据结构

```text
Week 1: 基础知识
  Day 1-2: references/08_algorithms_basics.md
  Day 3-4: guides/algorithm_complexity.md
  Day 5-7: guides/data_structures.md + 实践

Week 2: 算法实现
  Day 1-3: 查看 src/ 中的排序、搜索实现
  Day 4-5: 图算法实现
  Day 6-7: 动态规划实现

Week 3: 综合练习
  Day 1-5: 完成 examples/ 中的示例
  Day 6-7: 做 LeetCode/竞赛题目
```

### 路径 2: 中级开发者 (3-4 周)

**目标**: 掌握异步编程和性能优化

```text
Week 1: 异步基础
  guides/async_algorithms.md
  theory/ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md
  examples/async_*.rs

Week 2: 异步进阶
  theory/ACTOR_REACTOR_CSP_PATTERNS.md
  theory/ASYNC_RECURSION_ANALYSIS.md
  advanced/algorithm_exp08-09.md

Week 3: 性能优化
  guides/performance_optimization.md
  guides/benchmarking_guide.md
  advanced/algorithm_exp10.md

Week 4: 实战项目
  实现一个高性能算法库
  进行性能测试和优化
```

### 路径 3: 高级研究者 (持续学习)

**目标**: 精通算法理论和形式化方法

```text
阶段 1: 理论基础 (2-3 周)
  theory/ALGORITHM_CLASSIFICATION_AND_MODELS.md
  theory/FORMAL_ALGORITHM_MODELS.md
  theory/DESIGN_PATTERNS_SEMANTICS_MAPPING.md

阶段 2: 异步理论 (2-3 周)
  theory/ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md
  theory/CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md
  theory/ACTOR_REACTOR_CSP_PATTERNS.md
  theory/ASYNC_RECURSION_ANALYSIS.md

阶段 3: 高级专题 (4-6 周)
  advanced/algorithm_exp11.md (形式化验证)
  advanced/algorithm_exp12.md (分布式算法)
  advanced/algorithm_exp08.md (执行模型)

阶段 4: 研究与创新
  阅读相关论文
  实现新算法
  发表研究成果
```

### 路径 4: 工程师 (按需学习)

**目标**: 解决实际工程问题

```text
按需查阅:
  references/algorithm_index.md     # 快速找算法
  guides/performance_optimization.md # 性能问题
  guides/benchmarking_guide.md      # 性能测试
  advanced/algorithm_exp14.md       # 工程实践

系统学习（可选）:
  按兴趣选择 advanced/ 中的专题
  按需学习 Rust 特性
```

---

## 🔍 快速查找

### 按主题查找

- **排序算法** → guides/data_structures.md, advanced/algorithm_exp02.md, src/sorting/
- **搜索算法** → references/algorithm_index.md, src/searching/
- **图算法** → advanced/algorithm_exp03.md, src/graph/
- **动态规划** → advanced/algorithm_exp04.md, src/dynamic_programming/
- **字符串算法** → advanced/algorithm_exp05.md, src/string_algorithms/
- **异步编程** → guides/async_algorithms.md, theory/ASYNC_*.md
- **性能优化** → guides/performance_optimization.md, advanced/algorithm_exp10.md
- **形式化** → theory/FORMAL_*.md, advanced/algorithm_exp11.md

### 按难度查找

- **⭐ 初级**: guides/, references/08_algorithms_basics.md
- **⭐⭐ 中级**: guides/async_algorithms.md, advanced/exp01-07, exp10, exp14
- **⭐⭐⭐ 高级**: theory/, advanced/exp08-09, exp11-13

### 按 Rust 版本查找

- **Rust 1.89**: rust-features/rust_189_features.md, RUST_189_FEATURES_GUIDE.md
- **Rust 1.90**: rust-features/RUST_190_FEATURES_APPLICATION.md
- **Edition 2024**: rust-features/Edition_2024_Features.md

---

## 💻 代码资源

### 源代码

- **[src/](../src/)** - 算法实现源码
  - `algorithms/` - 主题化算法实现
  - `data_structure/` - 数据结构实现
  - `sorting/`, `searching/`, `graph/` 等

### 示例代码

- **[examples/](../examples/)** - 完整示例程序
  - `actor_reactor_csp_complete.rs` - Actor/Reactor/CSP 模式
  - `async_recursion_comprehensive.rs` - 异步递归
  - `comprehensive_algorithm_demo.rs` - 算法演示
  - `comprehensive_formal_verification_demo.rs` - 形式化验证
  - `rust_2024_features_demo.rs` - Rust 2024 特性

### 测试与基准

- **[tests/](../tests/)** - 集成测试
- **[benches/](../benches/)** - 性能基准测试

---

## 📝 文档约定

### 文档格式

所有文档遵循以下格式：

```markdown
# 文档标题

**版本**: x.x.x
**Rust版本**: 1.xx+
**最后更新**: YYYY-MM-DD

## 内容...
```

### 难度标识

- ⭐ - 初级（适合初学者）
- ⭐⭐ - 中级（需要一定基础）
- ⭐⭐⭐ - 高级（需要深入理解）

### 状态标识

- ✅ - 完成
- 🚧 - 进行中
- 📦 - 归档
- ⚠️ - 需要更新

---

## 🔗 相关资源

### 项目资源

- [主 README](../README.md) - 项目主页
- [CONTRIBUTING](../CONTRIBUTING.md) - 贡献指南
- [CHANGELOG](../CHANGELOG.md) - 更新日志
- [Cargo.toml](../Cargo.toml) - 依赖配置

### 外部资源

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust 异步编程书](https://rust-lang.github.io/async-book/)
- [算法导论 (CLRS)](https://mitpress.mit.edu/books/introduction-algorithms)
- [类型和编程语言 (TAPL)](https://www.cis.upenn.edu/~bcpierce/tapl/)

---

## 🆘 获取帮助

### 常见问题

查看 [FAQ.md](./FAQ.md) 获取常见问题的解答。

### 术语查询

查看 [Glossary.md](./Glossary.md) 了解专业术语。

### 问题反馈

- 提交 Issue
- 查看 CONTRIBUTING.md
- 参与讨论

---

## 📊 文档统计

| 类别 | 文档数 | 状态 |
|------|--------|------|
| 实用指南 | 5 | ✅ |
| 理论文档 | 7 | ✅ |
| 高级专题 | 14 | ✅ |
| Rust特性 | 4 | ✅ |
| 参考资料 | 3 | ✅ |
| **总计** | **33** | **✅** |

---

**版本**: 2.0.0
**文档重组日期**: 2025-10-19
**维护状态**: ✅ 活跃维护

🚀 **欢迎使用 C08 Algorithms 文档体系！**
