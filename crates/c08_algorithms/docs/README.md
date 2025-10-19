# C08 Algorithms 文档体系

欢迎来到 Rust 算法与数据结构的完整文档体系！

**版本**: 2.0.0  
**Rust版本**: 1.90+  
**Edition**: 2024  
**最后更新**: 2025-10-19  
**文档状态**: ✅ 重组完成

---

## 🎯 快速开始

### 📍 主索引

**[→ 查看主索引 (00_MASTER_INDEX.md)](./00_MASTER_INDEX.md)**

主索引提供完整的文档导航、分类浏览和学习路径，是您探索本文档体系的最佳起点。

### 🆕 新用户指南

如果您是第一次使用，建议按以下顺序阅读：

1. **[主 README](../README.md)** - 了解项目概览和安装方法
2. **[本文档](#-文档体系结构)** - 理解文档组织方式
3. **[算法基础](./references/08_algorithms_basics.md)** - 学习基础知识
4. **[主索引](./00_MASTER_INDEX.md)** - 开始系统学习

### ⚡ 快速查找

- **找算法** → [algorithm_index.md](./references/algorithm_index.md)
- **学基础** → [guides/](./guides/)
- **看理论** → [theory/](./theory/)
- **查特性** → [rust-features/](./rust-features/)

---

## 📚 文档体系结构

本文档体系按内容类型和难度分为 6 个主要目录：

### 1. 📖 实用指南 (guides/)

**难度**: ⭐~⭐⭐ (初级到中级)  
**适合**: 日常开发、学习使用

包含算法复杂度、数据结构、异步编程、性能优化等实用指南。

- [algorithm_complexity.md](./guides/algorithm_complexity.md) - 复杂度分析
- [data_structures.md](./guides/data_structures.md) - 数据结构
- [async_algorithms.md](./guides/async_algorithms.md) - 异步算法
- [performance_optimization.md](./guides/performance_optimization.md) - 性能优化
- [benchmarking_guide.md](./guides/benchmarking_guide.md) - 基准测试

**[→ 查看完整指南目录](./guides/README.md)**

### 2. 🔬 理论文档 (theory/)

**难度**: ⭐⭐⭐ (高级)  
**适合**: 理论研究、深入学习

包含算法的形式化理论、数学模型、证明方法和语义分析。

- 算法分类与形式化
- 异步同步等价性
- 控制流执行流分析
- Actor/Reactor/CSP 模式
- 设计模式语义映射

**[→ 查看完整理论目录](./theory/README.md)**

### 3. 🚀 高级专题 (advanced/)

**难度**: ⭐⭐~⭐⭐⭐ (中级到高级)  
**适合**: 深入学习特定主题

包含 14 个深入的算法专题文档：

- 类型设计、排序、图算法
- 动态规划、字符串算法、数据结构
- 并行算法、执行模型、异步模式
- 优化技术、形式化验证
- 分布式算法、机器学习、算法工程

**[→ 查看完整专题目录](./advanced/README.md)**

### 4. ✨ Rust 特性 (rust-features/)

**难度**: ⭐⭐ (中级)  
**适合**: 了解 Rust 新特性

包含 Rust 1.89、1.90 和 Edition 2024 的特性文档。

- Rust 1.89/1.90 特性
- Async traits、GATs
- Edition 2024 新语法
- 特性应用指南

**[→ 查看完整特性目录](./rust-features/README.md)**

### 5. 📚 参考资料 (references/)

**难度**: ⭐~⭐⭐ (初级到中级)  
**适合**: 快速查阅

包含算法索引、基础教程等参考资料。

- 算法索引（按类别）
- Rust 1.89 算法索引
- 算法与数据结构基础

**[→ 查看完整参考目录](./references/README.md)**

### 6. 📦 归档文档 (archives/)

已被新版本替代的旧文档，保留用于历史参考。

**[→ 查看归档目录](./archives/README.md)**

---

## 🎓 学习路径推荐

### 🌱 初学者路径 (2-3 周)

```text
1. 基础知识
   ├─ references/08_algorithms_basics.md
   ├─ guides/algorithm_complexity.md
   └─ guides/data_structures.md

2. 实践
   ├─ 查看 src/ 中的实现
   ├─ 运行 examples/ 中的示例
   └─ 完成练习题

3. 巩固
   └─ 做算法题目（LeetCode 等）
```

### 🚀 进阶路径 (3-4 周)

```text
1. 异步编程
   ├─ guides/async_algorithms.md
   ├─ theory/ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md
   └─ theory/ACTOR_REACTOR_CSP_PATTERNS.md

2. 性能优化
   ├─ guides/performance_optimization.md
   ├─ guides/benchmarking_guide.md
   └─ advanced/algorithm_exp10.md

3. 实战项目
   └─ 实现高性能算法库
```

### 🎯 专家路径 (持续学习)

```text
1. 理论基础
   └─ theory/ 目录下所有文档

2. 高级专题
   └─ advanced/ 目录按兴趣选择

3. 研究创新
   └─ 实现新算法、发表论文
```

---

## 🔍 如何查找内容

### 按主题查找

查看 **[主索引](./00_MASTER_INDEX.md)** 的"按主题查找"部分。

### 按难度查找

- **⭐ 初级**: guides/, references/
- **⭐⭐ 中级**: guides/async_algorithms.md, advanced/ (部分), rust-features/
- **⭐⭐⭐ 高级**: theory/, advanced/ (部分)

### 按类型查找

- **教程**: guides/, references/08_algorithms_basics.md
- **理论**: theory/
- **专题**: advanced/
- **参考**: references/

---

## 💡 使用建议

### 📚 系统学习

1. 从 **references/08_algorithms_basics.md** 开始
2. 按 **[学习路径](#-学习路径推荐)** 逐步学习
3. 结合 **源代码** 和 **示例** 实践
4. 完成 **练习** 巩固知识

### 🔍 快速查阅

1. 使用 **[algorithm_index.md](./references/algorithm_index.md)** 查找算法
2. 查看对应的源码实现
3. 运行相关示例
4. 参考文档了解细节

### 🎯 问题解决

1. 查看 **[FAQ.md](./FAQ.md)** 常见问题
2. 查阅 **[Glossary.md](./Glossary.md)** 术语表
3. 搜索相关文档
4. 查看源码和测试

---

## 📖 文档约定

### 元数据格式

所有文档包含以下元数据：

```markdown
**版本**: x.x.x
**Rust版本**: 1.xx+
**最后更新**: YYYY-MM-DD
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

- **[主 README](../README.md)** - 项目主页
- **[源代码](../src/)** - 算法实现
- **[示例](../examples/)** - 完整示例
- **[测试](../tests/)** - 测试用例
- **[基准测试](../benches/)** - 性能测试

### 外部资源

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust 异步编程书](https://rust-lang.github.io/async-book/)
- [算法导论 (CLRS)](https://mitpress.mit.edu/books/introduction-algorithms)

---

## 🆘 获取帮助

### 常见问题

查看 **[FAQ.md](./FAQ.md)** 获取常见问题的解答。

### 术语查询

查看 **[Glossary.md](./Glossary.md)** 了解专业术语。

### 问题反馈

- 提交 Issue
- 查看 [CONTRIBUTING.md](../CONTRIBUTING.md)
- 参与讨论

---

## 📊 文档统计

| 目录 | 文档数 | 难度 | 状态 |
|------|--------|------|------|
| guides/ | 5 | ⭐~⭐⭐ | ✅ |
| theory/ | 7 | ⭐⭐⭐ | ✅ |
| advanced/ | 14 | ⭐⭐~⭐⭐⭐ | ✅ |
| rust-features/ | 4 | ⭐⭐ | ✅ |
| references/ | 3 | ⭐~⭐⭐ | ✅ |
| **总计** | **33** | - | **✅** |

---

## 🎉 文档重组完成

本文档体系已于 **2025-10-19** 完成重组，具有以下特点：

✅ **清晰的目录结构** - 按内容类型和难度分类  
✅ **完整的导航系统** - 主索引 + 子目录 README  
✅ **灵活的学习路径** - 适合不同水平的学习者  
✅ **丰富的参考资料** - 33 个文档全面覆盖  
✅ **统一的文档格式** - 便于阅读和维护

---

**开始探索**: [→ 查看主索引](./00_MASTER_INDEX.md)

🚀 **祝您学习愉快！**
