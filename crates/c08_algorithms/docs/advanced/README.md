# 高级算法专题

本目录包含深入的算法专题文档，涵盖类型设计、执行模型、并发模式、优化技术等高级主题。

## 📚 专题列表

### 类型与设计

- **[algorithm_exp01.md](./algorithm_exp01.md)** - Rust 类型设计准则：算法设计视角
  - 特征作为算法抽象
  - 泛型算法设计
  - 策略模式实现
  - 类型状态模式
  - 零成本抽象

### 排序与搜索

- **[algorithm_exp02.md](./algorithm_exp02.md)** - 高级排序算法
  - 排序算法理论与实现
  - 自适应排序
  - 外部排序
  - 并行排序

### 图论算法

- **[algorithm_exp03.md](./algorithm_exp03.md)** - 图算法深度剖析
  - 图遍历算法
  - 最短路径算法
  - 最小生成树
  - 网络流算法

### 动态规划

- **[algorithm_exp04.md](./algorithm_exp04.md)** - 动态规划高级技巧
  - DP 问题建模
  - 状态压缩技术
  - 优化方法
  - 经典问题详解

### 字符串算法

- **[algorithm_exp05.md](./algorithm_exp05.md)** - 字符串算法专题
  - 字符串匹配（KMP、BM、Rabin-Karp）
  - 后缀数组与后缀树
  - Aho-Corasick 自动机
  - 字符串压缩

### 数据结构

- **[algorithm_exp06.md](./algorithm_exp06.md)** - 高级数据结构
  - 平衡树（AVL、红黑树、B树）
  - 线段树与树状数组
  - 跳表与布隆过滤器
  - LRU/LFU 缓存

### 并行算法

- **[algorithm_exp07.md](./algorithm_exp07.md)** - 并行算法设计
  - 并行计算模型
  - 数据并行
  - 任务并行
  - 分治并行

### 执行模型

- **[algorithm_exp08.md](./algorithm_exp08.md)** - Rust 算法与执行模型全景
  - 控制流算法
  - 数据流算法
  - 并发控制算法
  - 异步执行模型
  - 形式化分析

### 异步模式

- **[algorithm_exp09.md](./algorithm_exp09.md)** - 异步编程模式
  - Future 与 Poll 模型
  - 异步数据流
  - 异步状态机
  - 执行器设计

### 优化技术

- **[algorithm_exp10.md](./algorithm_exp10.md)** - 算法优化技术
  - 缓存优化
  - 内存优化
  - SIMD 优化
  - 编译器优化

### 形式化验证

- **[algorithm_exp11.md](./algorithm_exp11.md)** - 形式化验证方法
  - 类型安全证明
  - 所有权证明
  - 并发系统证明
  - 模型检验

### 分布式算法

- **[algorithm_exp12.md](./algorithm_exp12.md)** - 分布式算法
  - 一致性算法（Raft、Paxos）
  - 分布式存储
  - 分布式计算
  - 容错机制

### 机器学习

- **[algorithm_exp13.md](./algorithm_exp13.md)** - 机器学习算法
  - 监督学习算法
  - 无监督学习算法
  - 神经网络
  - 优化算法

### 算法工程

- **[algorithm_exp14.md](./algorithm_exp14.md)** - 算法工程实践
  - 算法选择策略
  - 性能调优
  - 工程化实践
  - 生产环境部署

## 🎯 使用建议

### 按主题阅读

- **类型系统爱好者**: exp01 → exp06 → exp11
- **异步编程学习**: exp08 → exp09 → exp12
- **算法竞赛**: exp02 → exp03 → exp04 → exp05
- **性能优化**: exp07 → exp10 → exp14

### 按难度递进

- **初级**: exp02、exp03、exp04、exp05
- **中级**: exp01、exp06、exp07、exp10
- **高级**: exp08、exp09、exp11、exp12、exp13

## 📝 说明

这些文档原名为 `algorithm_exp01-14.md`，现已归类到本目录。每个文档都是独立的专题，可以单独阅读，也可以按照学习路径系统学习。

## 🔗 相关资源

- **理论基础** → 查看 [../theory/](../theory/)
- **实用指南** → 查看 [../guides/](../guides/)
- **源代码实现** → 查看 [../../src/](../../src/)
- **完整示例** → 查看 [../../examples/](../../examples/)

---

**目录状态**: ✅ 完整（14个专题）  
**难度等级**: ⭐⭐~⭐⭐⭐ 中级到高级  
**最后更新**: 2025-10-19
