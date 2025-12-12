# 研究笔记术语表

> **创建日期**: 2025-01-27
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.92.0+ (Edition 2024) ✅
> **状态**: 持续更新中 📝

---

## 📊 目录

- [研究笔记术语表](#研究笔记术语表)
  - [📊 目录](#-目录)
  - [🔤 术语索引](#-术语索引)
    - [按字母顺序](#按字母顺序)
  - [📚 形式化方法术语](#-形式化方法术语)
    - [A](#a)
    - [B](#b)
    - [L](#l)
    - [O](#o)
    - [P](#p)
  - [🔬 类型理论术语](#-类型理论术语)
    - [A](#a-1)
    - [C](#c)
    - [G](#g)
    - [I](#i)
    - [T](#t)
    - [V](#v)
  - [⚡ 性能优化术语](#-性能优化术语)
    - [B](#b-1)
    - [C](#c-1)
    - [M](#m)
    - [P](#p-1)
  - [🛠️ 工具术语](#️-工具术语)
    - [C](#c-2)
    - [K](#k)
    - [L](#l-1)
    - [M](#m-1)
    - [P](#p-2)
    - [V](#v-1)
  - [📖 研究方法术语](#-研究方法术语)
    - [E](#e)
    - [F](#f)
    - [T](#t-1)
  - [🔗 相关资源](#-相关资源)
    - [核心文档](#核心文档)
    - [研究笔记](#研究笔记)

---

## 🔤 术语索引

### 按字母顺序

- [A](#a)
- [B](#b)
- [C](#c)
- [E](#e)
- [F](#f)
- [G](#g)
- [I](#i)
- [L](#l)
- [M](#m)
- [O](#o)
- [P](#p)
- [T](#t)
- [V](#v)

---

## 📚 形式化方法术语

### A

**抽象解释 (Abstract Interpretation)**:

- **定义**: 一种静态分析技术，用于在程序执行前推断程序的性质
- **应用**: 在 Rust 中用于借用检查器的实现
- **相关**: [借用检查器证明](./formal_methods/borrow_checker_proof.md)

**异步状态机 (Async State Machine)**:

- **定义**: 用于建模异步程序执行的状态机
- **应用**: Rust 的 async/await 机制可以转换为状态机
- **相关**: [异步状态机形式化](./formal_methods/async_state_machine.md)

### B

**借用检查器 (Borrow Checker)**:

- **定义**: Rust 编译器的核心组件，用于检查借用规则
- **功能**: 确保内存安全，防止数据竞争
- **相关**: [借用检查器证明](./formal_methods/borrow_checker_proof.md)

**借用规则 (Borrowing Rules)**:

- **定义**: Rust 的所有权系统中的规则，控制值的借用
- **规则**:
  - 同一时间只能有一个可变借用或多个不可变借用
  - 借用不能超过值的生命周期
- **相关**: [所有权模型形式化](./formal_methods/ownership_model.md)

### L

**生命周期 (Lifetime)**:

- **定义**: Rust 中引用有效的时间范围
- **表示**: 使用 `'a` 等生命周期参数
- **相关**: [生命周期形式化](./formal_methods/lifetime_formalization.md)

**线性类型 (Linear Type)**:

- **定义**: 一种类型系统，要求每个值恰好使用一次
- **应用**: 用于建模 Rust 的所有权转移
- **相关**: [所有权模型形式化](./formal_methods/ownership_model.md)

### O

**所有权 (Ownership)**:

- **定义**: Rust 的核心概念，每个值都有一个所有者
- **规则**:
  - 每个值只有一个所有者
  - 当所有者离开作用域时，值被释放
- **相关**: [所有权模型形式化](./formal_methods/ownership_model.md)

### P

**Pin (Pin)**:

- **定义**: Rust 的类型，用于固定值在内存中的位置
- **应用**: 用于自引用类型和异步编程
- **相关**: [Pin 和自引用类型形式化](./formal_methods/pin_self_referential.md)

**过程宏 (Procedural Macro)**:

- **定义**: 在编译时执行的宏，可以生成代码
- **类型**: 函数式宏、派生宏、属性宏
- **相关**: [宏展开性能](./experiments/macro_expansion_performance.md)

---

## 🔬 类型理论术语

### A

**关联类型 (Associated Type)**:

- **定义**: Trait 中定义的占位符类型
- **示例**: `Iterator` trait 中的 `Item` 类型
- **相关**: [Trait 系统形式化](./type_theory/trait_system_formalization.md)

### C

**常量泛型 (Const Generics)**:

- **定义**: 使用常量值作为泛型参数
- **示例**: `[T; N]` 中的 `N` 是常量泛型参数
- **相关**: [高级类型特性](./type_theory/advanced_types.md)

**协变 (Covariance)**:

- **定义**: 类型参数在子类型关系中的变化方向
- **示例**: `&'a T` 在 `'a` 上是协变的
- **相关**: [型变理论](./type_theory/variance_theory.md)

### G

**泛型关联类型 (Generic Associated Types, GATs)**:

- **定义**: 允许在 Trait 中使用泛型参数的关联类型
- **应用**: 提供更灵活的类型抽象
- **相关**: [高级类型特性](./type_theory/advanced_types.md)

### I

**逆变 (Contravariance)**:

- **定义**: 类型参数在子类型关系中的反向变化
- **示例**: 函数参数类型是逆变的
- **相关**: [型变理论](./type_theory/variance_theory.md)

**不变 (Invariance)**:

- **定义**: 类型参数不允许子类型关系变化
- **示例**: `&mut T` 在 `T` 上是不变的
- **相关**: [型变理论](./type_theory/variance_theory.md)

### T

**Trait (Trait)**:

- **定义**: Rust 的类型系统特性，类似于接口
- **功能**: 定义类型必须实现的方法
- **相关**: [Trait 系统形式化](./type_theory/trait_system_formalization.md)

**Trait 对象 (Trait Object)**:

- **定义**: 使用动态分发的 Trait 实现
- **表示**: `dyn Trait`
- **相关**: [Trait 系统形式化](./type_theory/trait_system_formalization.md)

**类型推导 (Type Inference)**:

- **定义**: 编译器自动推断类型的能力
- **应用**: 减少显式类型注解的需要
- **相关**: [类型系统基础](./type_theory/type_system_foundations.md)

**类型系统 (Type System)**:

- **定义**: 编程语言中用于类型检查和类型安全的机制
- **功能**: 防止类型错误，提供类型安全保证
- **相关**: [类型系统基础](./type_theory/type_system_foundations.md)

### V

**型变 (Variance)**:

- **定义**: 描述类型参数在子类型关系中的变化方式
- **类型**: 协变、逆变、不变
- **相关**: [型变理论](./type_theory/variance_theory.md)

---

## ⚡ 性能优化术语

### B

**基准测试 (Benchmark)**:

- **定义**: 用于测量程序性能的测试
- **工具**: Criterion.rs、cargo bench
- **相关**: [性能基准测试](./experiments/performance_benchmarks.md)

### C

**编译器优化 (Compiler Optimization)**:

- **定义**: 编译器自动改进代码性能的技术
- **类型**: 内联、循环优化、死代码消除
- **相关**: [编译器优化](./experiments/compiler_optimizations.md)

**并发性能 (Concurrency Performance)**:

- **定义**: 多线程程序的性能特征
- **考虑**: 线程开销、锁竞争、数据竞争
- **相关**: [并发性能](./experiments/concurrency_performance.md)

### M

**内存分析 (Memory Analysis)**:

- **定义**: 分析程序的内存使用情况
- **工具**: Miri、Valgrind、heaptrack
- **相关**: [内存分析](./experiments/memory_analysis.md)

**内存布局 (Memory Layout)**:

- **定义**: 数据在内存中的排列方式
- **优化**: 字段重排序、对齐优化
- **相关**: [内存分析](./experiments/memory_analysis.md)

### P

**性能分析 (Performance Profiling)**:

- **定义**: 测量和分析程序性能的过程
- **工具**: perf、flamegraph、cargo-flamegraph
- **相关**: [性能基准测试](./experiments/performance_benchmarks.md)

---

## 🛠️ 工具术语

### C

**Coq**:

- **定义**: 交互式定理证明器
- **应用**: 形式化验证、数学证明
- **相关**: [工具使用指南 - Coq](./TOOLS_GUIDE.md#coq)

**Criterion.rs**:

- **定义**: Rust 的基准测试框架
- **功能**: 统计分析、性能测量
- **相关**: [工具使用指南 - Criterion.rs](./TOOLS_GUIDE.md#criterionrs)

### K

**Kani**:

- **定义**: Rust 的模型检查工具
- **应用**: 验证 Rust 程序的正确性
- **相关**: [工具使用指南 - Kani](./TOOLS_GUIDE.md#kani)

### L

**Lean**:

- **定义**: 函数式编程语言和证明助手
- **应用**: 形式化数学和程序验证
- **相关**: [工具使用指南 - Lean](./TOOLS_GUIDE.md#lean)

### M

**Miri**:

- **定义**: Rust 的 MIR 解释器
- **功能**: 检测未定义行为、内存错误
- **相关**: [工具使用指南 - Miri](./TOOLS_GUIDE.md#miri)

### P

**Prusti**:

- **定义**: Rust 的形式化验证工具
- **应用**: 验证 Rust 程序的规范
- **相关**: [工具使用指南 - Prusti](./TOOLS_GUIDE.md#prusti)

### V

**Valgrind**:

- **定义**: 内存调试和性能分析工具
- **功能**: 检测内存泄漏、未初始化内存
- **相关**: [工具使用指南 - Valgrind](./TOOLS_GUIDE.md#valgrind)

---

## 📖 研究方法术语

### E

**实验研究 (Experimental Research)**:

- **定义**: 通过实验验证假设的研究方法
- **步骤**: 假设、实验设计、数据收集、分析
- **相关**: [研究方法论](./research_methodology.md)

**实证研究 (Empirical Research)**:

- **定义**: 基于观察和经验的研究方法
- **应用**: 性能分析、实际案例研究
- **相关**: [研究方法论](./research_methodology.md)

### F

**形式化方法 (Formal Methods)**:

- **定义**: 使用数学方法描述和验证系统
- **工具**: 定理证明器、模型检查器
- **相关**: [研究方法论](./research_methodology.md)

### T

**理论研究 (Theoretical Research)**:

- **定义**: 基于理论分析和推导的研究方法
- **应用**: 类型理论、形式化语义
- **相关**: [研究方法论](./research_methodology.md)

---

## 🔗 相关资源

### 核心文档

- [主索引](./README.md) - 完整的研究笔记索引
- [快速参考](./QUICK_REFERENCE.md) - 快速查找指南
- [研究方法论](./research_methodology.md) - 研究方法框架

### 研究笔记

- [形式化方法研究](./formal_methods/README.md) - 形式化方法索引
- [类型理论研究](./type_theory/README.md) - 类型理论索引
- [实验研究](./experiments/README.md) - 实验研究索引

---

**维护团队**: Rust Research Community
**最后更新**: 2025-11-15
**状态**: 📝 **持续更新中**
