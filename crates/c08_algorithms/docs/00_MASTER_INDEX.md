# C08 Algorithms - 主索引

📄 **一页纸总结**: [ONE_PAGE_SUMMARY](./ONE_PAGE_SUMMARY.md) - 核心概念、常见坑、速选表、学习路径

## 📚 官方资源映射

| 官方资源 | 链接 | 与本模块对应 |
| :--- | :--- | :--- |
| **RBE 练习** | [Vectors](https://doc.rust-lang.org/rust-by-example/std/vec.html) · [HashMap](https://doc.rust-lang.org/rust-by-example/std/hash.html) · [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html) | 集合与迭代器实践 |
| **Rust std** | [std::collections](https://doc.rust-lang.org/std/collections/), [std::iter](https://doc.rust-lang.org/std/iter/) | 标准库数据结构 |
| **Algorithm courses** | MIT 6.006, CLRS | 算法复杂度理论 |

**Rust 1.93 兼容性**: [兼容性注意事项](../../../docs/06_toolchain/06_rust_1.93_compatibility_notes.md) | [深度解析](../../../docs/06_toolchain/09_rust_1.93_compatibility_deep_dive.md)
**思维表征**: [决策图网](../../../docs/04_thinking/DECISION_GRAPH_NETWORK.md) | [证明图网](../../../docs/04_thinking/PROOF_GRAPH_NETWORK.md) | [思维表征方式](../../../docs/04_thinking/THINKING_REPRESENTATION_METHODS.md)

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
├── 🆕 RUST_192_RICH_EXAMPLES.md               # 💻 Rust 1.93 丰富示例
├── 🆕 INTERACTIVE_LEARNING_GUIDE.md           # 🎓 交互式学习指南
├── 🆕 VISUAL_CODE_EXAMPLES.md                 # 🎨 可视化示例库
│
├── tier_01_foundations/                       # 📖 基础层
├── tier_02_guides/                            # 📖 实践指南（原 guides/）
│   ├── 01_算法快速入门.md
│   ├── 02_数据结构实践.md
│   ├── 03_算法复杂度分析.md
│   ├── 04_性能优化实践.md
│   └── 05_并行与异步算法.md
├── tier_03_references/                        # 📚 技术参考（原 references/）
├── tier_04_advanced/                          # 🔬 高级专题（原 theory/ + advanced/）
│
└── archive/                                   # 📦 归档文档
    ├── README.md
    ├── C08_ENHANCEMENT_COMPLETION_REPORT_2025_10_19.md
    ├── LEETCODE_FINAL_SUMMARY_2025_11_01.md
    ├── LEETCODE_INTEGRATION_SUMMARY_2025_11_01.md
    └── PROGRESS_UPDATE_2025_11_01.md
```

---

## 📖 按类别浏览

### 1. 实用指南 (tier_02_guides/)

适合日常开发和学习使用的实用文档。

| 文档  | 主要内容 | 适合人群 |
| :--- | :--- | :--- |
| [03_算法复杂度分析](./tier_02_guides/03_算法复杂度分析.md)         | 时间/空间复杂度、Big-O、主定理、摊还分析 | 初学者、面试准备 |
| [02_数据结构实践](./tier_02_guides/02_数据结构实践.md)             | 线性表、树、图、高级数据结构             | 所有开发者       |
| [05_并行与异步算法](./tier_02_guides/05_并行与异步算法.md)         | 异步算法设计、Tokio、Futures             | 异步编程学习者   |
| [04_性能优化实践](./tier_02_guides/04_性能优化实践.md)             | 编译期优化、运行时优化、SIMD             | 性能优化工程师   |
| [04_算法性能参考](./tier_03_references/04_算法性能参考.md)         | Criterion、性能测试、对比分析            | 性能调优人员     |

**学习路径**: 03_算法复杂度分析 → 02_数据结构实践 → 05_并行与异步算法 → 04_性能优化实践

### 2. 理论文档 (tier_04_advanced/)

深入的形式化理论、数学模型和证明方法。

| 文档  | 主要内容 | 难度   |
| :--- | :--- | :--- |
| [01_形式化算法理论](./tier_04_advanced/01_形式化算法理论.md)           | 算法分类、形式化定义、计算模型 | ⭐⭐⭐ |
| [02_并发算法模式](./tier_04_advanced/02_并发算法模式.md)               | Actor、Reactor、CSP          | ⭐⭐⭐ |
| [03_分布式算法](./tier_04_advanced/03_分布式算法.md)                  | 分布式系统算法               | ⭐⭐⭐ |
| [04_算法工程实践](./tier_04_advanced/04_算法工程实践.md)              | 工程应用最佳实践             | ⭐⭐⭐ |
| [05_前沿算法技术](./tier_04_advanced/05_前沿算法技术.md)              | 机器学习与前沿研究           | ⭐⭐⭐ |

**学习路径**: 01_形式化算法理论 → 02_并发算法模式 → 03_分布式算法

### 3. 高级专题 (tier_04_advanced/)

详见 [tier_04_advanced/README.md](./tier_04_advanced/README.md)

**按兴趣选择**:

- 算法竞赛：02_数据结构实践、03_算法复杂度分析
- 系统编程：02_并发算法模式、05_并行与异步算法
- 理论研究：01_形式化算法理论
- 分布式系统：03_分布式算法

### 4. Rust 特性 (tier_03_references/)

| 文档  | 版本 | 主要内容 |
| :--- | :--- | :--- |
| [03_Rust190特性参考](./tier_03_references/03_Rust190特性参考.md) | 1.90 | 特性应用     |
| [RUST_192_ALGORITHMS_IMPROVEMENTS](./RUST_192_ALGORITHMS_IMPROVEMENTS.md) | 1.93 | 算法特性 ⭐  |

### 5. 参考资料 (tier_03_references/)

| 文档  | 用途  | 适合场景  |
| :--- | :--- | :--- |
| [01_算法分类参考](./tier_03_references/01_算法分类参考.md)       | 算法索引      | 快速查找算法 |
| [02_数据结构参考](./tier_03_references/02_数据结构参考.md)        | 数据结构 API  | 技术参考     |
| [04_算法性能参考](./tier_03_references/04_算法性能参考.md)       | 性能基准      | 性能调优     |

---

## 🎓 推荐学习路径

### 路径 1: 初学者 (2-3 周)

**目标**: 掌握基础算法和数据结构

```text
Week 1: 基础知识
  Day 1-2: tier_02_guides/01_算法快速入门.md
  Day 3-4: tier_02_guides/03_算法复杂度分析.md
  Day 5-7: tier_02_guides/02_数据结构实践.md + 实践

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
  tier_02_guides/05_并行与异步算法.md
  tier_04_advanced/02_并发算法模式.md
  examples/async_*.rs

Week 2: 异步进阶
  ../../c09_design_pattern/docs/ACTOR_REACTOR_PATTERNS.md
  ../../c09_design_pattern/docs/ASYNC_RECURSION_ANALYSIS.md
  tier_04_advanced/02_并发算法模式.md

Week 3: 性能优化
  tier_02_guides/04_性能优化实践.md
  tier_03_references/04_算法性能参考.md
  tier_04_advanced/04_算法工程实践.md

Week 4: 实战项目
  实现一个高性能算法库
  进行性能测试和优化
```

### 路径 3: 高级研究者 (持续学习)

**目标**: 精通算法理论和形式化方法

```text
阶段 1: 理论基础 (2-3 周)
  tier_04_advanced/01_形式化算法理论.md

阶段 2: 异步理论 (2-3 周)
  tier_04_advanced/02_并发算法模式.md
  ../../c09_design_pattern/docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md
  ../../c09_design_pattern/docs/ASYNC_RECURSION_ANALYSIS.md

阶段 3: 高级专题 (4-6 周)
  tier_04_advanced/01_形式化算法理论.md (形式化验证)
  tier_04_advanced/03_分布式算法.md
  tier_04_advanced/02_并发算法模式.md (执行模型)

阶段 4: 研究与创新
  阅读相关论文
  实现新算法
  发表研究成果
```

### 路径 4: 工程师 (按需学习)

**目标**: 解决实际工程问题

```text
按需查阅:
  tier_03_references/01_算法分类参考.md
  tier_02_guides/04_性能优化实践.md
  tier_03_references/04_算法性能参考.md
  tier_04_advanced/04_算法工程实践.md

系统学习（可选）:
  按兴趣选择 tier_04_advanced/ 中的专题
  按需学习 Rust 特性
```

---

## 🔍 快速查找

### 按主题查找

- **排序算法** → tier_02_guides/02_数据结构实践.md, src/sorting/
- **搜索算法** → tier_03_references/01_算法分类参考.md, src/searching/
- **图算法** → tier_02_guides/02_数据结构实践.md, src/graph/
- **动态规划** → tier_04_advanced/04_算法工程实践.md, src/dynamic_programming/
- **字符串算法** → tier_02_guides/02_数据结构实践.md, src/string_algorithms/
- **异步编程** → tier_02_guides/05_并行与异步算法.md, tier_04_advanced/02_并发算法模式.md
- **性能优化** → tier_02_guides/04_性能优化实践.md, tier_04_advanced/04_算法工程实践.md
- **形式化** → tier_04_advanced/01_形式化算法理论.md

### 按难度查找

- **⭐ 初级**: tier_02_guides/, tier_02_guides/01_算法快速入门.md
- **⭐⭐ 中级**: tier_02_guides/05_并行与异步算法.md, tier_04_advanced/
- **⭐⭐⭐ 高级**: tier_04_advanced/

### 按 Rust 版本查找

- **Rust 1.90**: tier_03_references/03_Rust190特性参考.md
- **Rust 1.93.1**: RUST_192_ALGORITHMS_IMPROVEMENTS.md

---

## 💻 代码资源

### 源代码

- **[src/](../src/README.md)** - 算法实现源码
  - `algorithms/` - 主题化算法实现
  - `data_structure/` - 数据结构实现
  - `sorting/`, `searching/`, `graph/` 等

### 示例代码

- **[examples/](../examples/README.md)** - 完整示例程序
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

| 类别     | 文档数 | 状态   |
| :--- | :--- | :--- |
| 实用指南 | 5      | ✅     |
| 理论文档 | 7      | ✅     |
| 高级专题 | 14     | ✅     |
| Rust特性 | 4      | ✅     |
| 参考资料 | 3      | ✅     |
| **总计** | **33** | **✅** |

---

**版本**: 2.1.0
**文档重组日期**: 2025-12-11
**维护状态**: ✅ 活跃维护
**重组完成**: ✅ 归档目录已创建，历史报告已归档

🚀 **欢迎使用 C08 Algorithms 文档体系！**
