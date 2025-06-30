# C03. 控制流与函数 (Control Flow & Functions)

本分册深入探讨 Rust 语言的控制流机制及其与核心系统（尤其是所有权与类型系统）的交互。内容从基础的条件、循环结构，延伸至函数、闭包、错误处理，并最终覆盖异步编程和类型状态模式等高级主题。

在 Rust 中，控制流不仅是指令的执行顺序，更是一种经过静态验证、确保内存和线程安全的精密构造。本分册的目标是形式化地、系统地解析这些构造，揭示其设计哲学与内部工作原理。

## 章节目录

- **`01_foundations_of_control_flow.md`**: 控制流基础
  - *核心概念：控制流的定义与设计哲学*
  - *形式化视角：类型与所有权约束概览*
- **`02_conditional_expressions.md`**: 条件表达式
  - *核心概念：`if`, `let`, `match` 的形式化与应用*
  - *特性：穷尽性检查、模式与守卫*
- **`03_iterative_constructs.md`**: 循环结构
  - *核心概念：`for`, `while`, `loop` 的语义与所有权*
  - *特性：`IntoIterator` trait, 带标签的 `break`*
- **`04_functions_and_closures.md`**: 函数与闭包
  - *核心概念：函数作为控制流转移，闭包与环境捕获*
  - *特性：发散函数 (`!`), `Fn` traits, `move` 关键字*
- **`05_error_handling_as_control_flow.md`**: 作为控制流的错误处理
  - *核心概念：`Option`/`Result` 作为路径分叉*
  - *特性：`?` 运算符的脱糖与提前返回*
- **`06_advanced_control_flow.md`**: 高级控制流模式
  - *核心概念：异步控制流与类型状态模式*
  - *特性：`Future` trait, 编译时状态机*

<!-- LATER_CHAPTERS -->