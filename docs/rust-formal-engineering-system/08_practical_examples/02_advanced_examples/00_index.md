# 高级示例（Advanced Examples）索引


## 📊 目录

- [高级示例（Advanced Examples）索引](#高级示例advanced-examples索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心示例](#核心示例)
    - [高级类型系统](#高级类型系统)
    - [宏系统](#宏系统)
    - [异步编程](#异步编程)
    - [并发编程](#并发编程)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)


## 目的

- 提供 Rust 高级概念和技术的实用示例。
- 帮助有经验的开发者深入理解 Rust 的高级特性。

## 核心示例

### 高级类型系统

- 高级泛型示例
- 关联类型示例
- 高级生命周期示例
- 类型级编程示例

### 宏系统

- 声明宏示例
- 过程宏示例
- 派生宏示例
- 属性宏示例

### 异步编程

- Future 实现示例
- 异步流示例
- 异步迭代器示例
- 异步错误处理示例

### 并发编程

- 高级同步原语示例
- 无锁数据结构示例
- 工作窃取示例
- 并发模式示例

## 实践与样例

- 高级示例：参见 [crates/c04_generic](../../../crates/c04_generic/)
- 并发编程：[crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)

### 文件级清单（精选）

- `crates/c04_generic/src/`：
  - `advanced_generics.rs`：高级泛型示例
  - `associated_types.rs`：关联类型示例
  - `type_level_programming.rs`：类型级编程示例
- `crates/c05_threads/src/`：
  - `advanced_synchronization.rs`：高级同步原语
  - `lockfree_structures.rs`：无锁数据结构
  - `work_stealing.rs`：工作窃取示例

## 相关索引

- 理论基础（Trait 系统）：[`../../01_theoretical_foundations/05_trait_system/00_index.md`](../../01_theoretical_foundations/05_trait_system/00_index.md)
- 理论基础（宏系统）：[`../../01_theoretical_foundations/08_macro_system/00_index.md`](../../01_theoretical_foundations/08_macro_system/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 基础示例：[`../01_basic_examples/00_index.md`](../01_basic_examples/00_index.md)
- 真实案例：[`../03_real_world_cases/00_index.md`](../03_real_world_cases/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
