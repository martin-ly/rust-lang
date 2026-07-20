# 算法理论文档

本目录包含算法的形式化理论、数学模型和证明方法。适合理论研究者和算法设计师深入学习。

## 📚 理论文档列表

### 核心理论

- **[ALGORITHM_CLASSIFICATION_AND_MODELS.md](./ALGORITHM_CLASSIFICATION_AND_MODELS.md)** ⭐⭐⭐
  - **主题**: 算法分类、模型与形式化体系（全新重构）
  - **内容**:
    - 算法的形式化定义（五元组表示）
    - 完整算法分类体系（按设计范式、按问题域）
    - 设计范式深度解析：分治、动态规划、贪心、回溯
    - 计算模型：图灵机、RAM模型、λ演算
    - 语义模型：操作语义、指称语义、公理语义
    - 复杂度理论：主定理、摊还分析
    - 正确性证明：循环不变量、数学归纳法
    - Rust 1.90 特性映射

- **[FORMAL_ALGORITHM_MODELS.md](./FORMAL_ALGORITHM_MODELS.md)** ⭐⭐⭐
  - **主题**: 算法形式化模型与分类体系
  - **内容**:
    - 算法的数学定义
    - 计算模型理论
    - 语义模型（指称语义、霍尔逻辑、分离逻辑）
    - 复杂度理论
    - 正确性证明方法

### 设计模式与语义

- **[DESIGN_PATTERNS_SEMANTICS_MAPPING.md](./DESIGN_PATTERNS_SEMANTICS_MAPPING.md)** ⭐⭐⭐
  - **主题**: 设计模式与算法语义模型映射
  - **内容**:
    - 经典设计模式（Strategy、Template Method、Iterator、Observer）
    - 算法专属模式（Memoization、Lazy Evaluation、CPS变换）
    - 并发模式（Actor、Pipeline）
    - 语义模型映射（类型系统、所有权与分离逻辑）
    - Rust 特有模式（Typestate、Newtype）
    - 等价关系分析

### 异步与同步理论

- **[ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md](./ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md)** ⭐⭐⭐
  - **主题**: 异步与同步算法的等价关系
  - **内容**:
    - 图灵等价性证明
    - 执行模型对比（调用栈 vs 状态机）
    - 阻塞 vs 挂起机制
    - CPS 变换与异步转换
    - 形式化证明与等价性
    - Rust 实现对比

- **[CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md](./CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md)** ⭐⭐⭐
  - **主题**: 控制流与执行流等价性证明
  - **内容**:
    - 控制流形式化定义
    - 执行流状态机模型
    - 五大等价性定理及证明
    - CPS 变换完整推导
    - 性能等价性分析

### 异步编程专题

- **[ACTOR_REACTOR_CSP_PATTERNS.md](./ACTOR_REACTOR_CSP_PATTERNS.md)** ⭐⭐⭐
  - **主题**: Actor/Reactor模式与CSP语义模型
  - **内容**:
    - Actor 模型的形式化定义
    - Reactor 模式与事件驱动
    - CSP 通信顺序进程理论
    - Golang CSP vs Rust Async 对比
    - 三大调度机制原理
    - 形式化验证

- **[ASYNC_RECURSION_ANALYSIS.md](./ASYNC_RECURSION_ANALYSIS.md)** ⭐⭐⭐
  - **主题**: 异步递归的形式化分析与实现
  - **内容**:
    - 递归理论基础（不动点定理）
    - 异步递归的类型系统挑战
    - 四大实现模式（Box+Pin、宏、尾递归、Stream）
    - 终止性与等价性证明
    - 算法应用与性能分析

## 🎓 学习路径

### 路径 1: 算法理论研究者

```text
1. ALGORITHM_CLASSIFICATION_AND_MODELS.md  # 掌握算法分类与形式化
2. FORMAL_ALGORITHM_MODELS.md             # 深入计算模型理论
3. ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md   # 理解等价关系
4. CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md # 证明技术
```

### 路径 2: 异步编程专家

```text
1. ASYNC_SYNC_EQUIVALENCE_ALGORITHMS.md   # 异步同步基础
2. ACTOR_REACTOR_CSP_PATTERNS.md          # 调度机制
3. ASYNC_RECURSION_ANALYSIS.md            # 异步递归
4. CONTROL_FLOW_EXECUTION_FLOW_EQUIVALENCE.md # 深入理解
```

### 路径 3: 软件架构师

```text
1. DESIGN_PATTERNS_SEMANTICS_MAPPING.md   # 设计模式
2. ALGORITHM_CLASSIFICATION_AND_MODELS.md # 算法分类
3. ACTOR_REACTOR_CSP_PATTERNS.md          # 并发模式
```

## 🔗 相关资源

- **实用指南** → 查看 [../guides/](../guides/)
- **高级专题** → 查看 [../advanced/](../advanced/)
- **代码示例** → 查看 [../../examples/](../../examples/)
  - `examples/actor_reactor_csp_complete.rs` - Actor/Reactor/CSP 完整实现
  - `examples/async_recursion_comprehensive.rs` - 异步递归综合示例
  - `examples/comprehensive_formal_verification_demo.rs` - 形式化验证演示

## 📖 推荐阅读

### 外部资源

- *Introduction to Algorithms* (CLRS)
- *Types and Programming Languages* (Pierce)
- *Concrete Semantics with Isabelle/HOL* (Nipkow)
- *Communicating Sequential Processes* (Hoare)
- Rust 官方异步编程书

---

**目录状态**: ✅ 完整  
**难度等级**: ⭐⭐⭐ 高级  
**最后更新**: 2025-10-19
