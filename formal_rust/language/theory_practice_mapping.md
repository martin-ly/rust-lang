# 理论-实践映射梳理 - 阶段一产出

## 1. 主要理论概念

- 所有权与借用
- 生命周期
- 类型系统
- 并发与异步
- 错误处理
- 宏系统

## 2. 实际代码/工具/应用映射

| 理论概念   | 代码/工具/应用示例 |
|------------|-------------------|
| 所有权     | Box, Rc, Arc, borrow checker |
| 生命周期   | 'a, 'static, 生命周期注解 |
| 类型系统   | trait, impl, 泛型、GAT |
| 并发/异步  | async/await, tokio, rayon |
| 错误处理   | Result, Option, ? 运算符 |
| 宏系统     | macro_rules!, procedural macro |

## 3. 典型案例分析

- 选取典型理论与实践结合案例，分析落地路径。

> 本文档为 theory_practice_integration.md 阶段一产出，后续将持续补充完善。
