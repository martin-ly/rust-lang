# 控制流主题索引

## 目录结构

### 1. 理论基础

1. [形式化控制流系统](01_formal_control_flow.md)
2. [控制流理论](02_control_flow_theory.md)
3. [控制流实现](03_control_flow_implementation.md)
4. [控制流应用](04_control_flow_applications.md)

### 2. 参考资料

5. [代码示例](05_examples.md)
6. [定理证明](06_theorems.md)
7. [参考文献](07_references.md)

## 主题概述

Rust控制流系统提供了强大的程序执行控制能力，与所有权、借用、生命周期系统深度集成，确保类型安全和内存安全。本主题涵盖：

- **基础控制结构**：条件控制、循环控制、函数控制流
- **高级控制特性**：模式匹配、错误处理、异步控制流
- **安全保证**：控制流与所有权系统的集成
- **形式化理论**：控制流的形式化定义和验证

## 核心概念

### 条件控制

- `if`、`if let`、`match` 表达式
- 模式匹配和守卫条件
- 穷尽性检查和类型安全

### 循环控制

- `loop`、`while`、`for` 循环
- 迭代器和集合遍历
- 循环控制和所有权转移

### 函数控制流

- 函数调用和返回
- 闭包和高阶函数
- 递归和尾递归优化

### 错误处理

- `Result` 和 `Option` 类型
- `?` 操作符和错误传播
- `panic!` 和异常处理

## 交叉引用

- 与[所有权与借用系统](../01_ownership_borrowing/00_index.md)的集成
- 与[类型系统](../02_type_system/00_index.md)的交互
- 与[异步编程](../06_async_await/00_index.md)的关系
- 与[错误处理](../06_error_handling/00_index.md)的集成

## 数学符号说明

本文档使用以下数学符号：

- $S$：语句
- $E$：表达式
- $\Gamma$：环境
- $\vdash$：推导关系
- $\rightarrow$：执行步骤
- $\Rightarrow$：求值关系
- $\bot$：未定义值
- $\top$：真值
