# 异步编程主题索引

## 目录结构

### 1. 理论基础
1. [形式化异步系统](01_formal_async_system.md)
2. [异步编程理论](02_async_theory.md)
3. [异步编程实现](03_async_implementation.md)
4. [异步编程应用](04_async_applications.md)

### 2. 参考资料
5. [代码示例](05_examples.md)
6. [定理证明](06_theorems.md)
7. [参考文献](07_references.md)

## 主题概述

Rust异步编程系统提供了高性能的并发编程能力，通过Future、async/await语法、执行器等核心组件实现零成本抽象。本主题涵盖：

- **核心概念**：Future、async/await、执行器、任务、唤醒器
- **工作原理**：状态机转换、轮询机制、零成本抽象
- **高级特性**：异步运行时、任务调度、错误处理
- **形式化理论**：异步执行模型的形式化表示和验证

## 核心概念

### Future系统
- `Future` trait 和 `Poll` 枚举
- 状态机转换和轮询机制
- 零成本抽象和性能保证

### async/await语法
- `async` 函数和块
- `await` 表达式和暂停点
- 生成器转换和状态机生成

### 执行器模型
- 单线程和多线程执行器
- 任务调度和优先级管理
- 工作窃取和负载均衡

### 任务系统
- 任务创建和生命周期
- 任务间通信和同步
- 错误传播和取消机制

## 交叉引用

- 与[控制流](../03_control_flow/00_index.md)的集成
- 与[并发系统](../05_concurrency/00_index.md)的关系
- 与[工作流](../14_workflow/00_index.md)的交互
- 与[网络编程](../10_networking/00_index.md)的应用

## 数学符号说明

本文档使用以下数学符号：
- $F$：Future
- $T$：任务
- $E$：执行器
- $\rightarrow$：状态转换
- $\Rightarrow$：求值关系
- $\vdash$：类型推导
- $\bot$：未完成状态
- $\top$：完成状态
