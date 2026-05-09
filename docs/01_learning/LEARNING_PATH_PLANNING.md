# 学习路径规划文档

**创建日期**: 2025-12-11
**最后更新**: 2026-05-08
**Rust 版本**: 1.95.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录

- [学习路径规划文档](#学习路径规划文档)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🎯 学习路径分类](#-学习路径分类)
    - [路径 1: 完全新手（0 基础）](#路径-1-完全新手0-基础)
    - [路径 2: 有编程经验（其他语言）](#路径-2-有编程经验其他语言)
    - [路径 3: 中级开发者（有 Rust 基础）](#路径-3-中级开发者有-rust-基础)
    - [路径 4: 高级开发者（专家级）](#路径-4-高级开发者专家级)
  - [📊 学习进度跟踪](#-学习进度跟踪)
    - [进度检查清单](#进度检查清单)
      - [基础阶段（C01-C03）](#基础阶段c01-c03)
      - [进阶阶段（C04-C06）](#进阶阶段c04-c06)
      - [高级阶段（C07-C10）](#高级阶段c07-c10)
      - [专家阶段（C11-C12）](#专家阶段c11-c12)
      - [新特性与前沿阶段（本轮新增）](#新特性与前沿阶段本轮新增)
  - [💻 学习路径代码示例](#-学习路径代码示例)
    - [路径 1 代码示例：基础语法实践](#路径-1-代码示例基础语法实践)
    - [路径 2 代码示例：并发编程实践](#路径-2-代码示例并发编程实践)
    - [路径 3 代码示例：异步编程实践](#路径-3-代码示例异步编程实践)
    - [路径 4 代码示例：高级特性实践](#路径-4-代码示例高级特性实践)
  - [🎯 学习建议](#-学习建议)
    - [1. 理论与实践结合](#1-理论与实践结合)
    - [2. 项目驱动学习](#2-项目驱动学习)
    - [3. 持续复习](#3-持续复习)
    - [4. 社区参与](#4-社区参与)
  - [📚 推荐学习资源](#-推荐学习资源)
    - [官方资源](#官方资源)
    - [项目资源](#项目资源)
    - [社区资源](#社区资源)
    - [Coursera 在线课程](#coursera-在线课程)
      - [Rust Programming Specialization (Duke University)](#rust-programming-specialization-duke-university)
      - [Programming in Rust (University of Colorado Boulder)](#programming-in-rust-university-of-colorado-boulder)
      - [Practical System Programming in Rust (Coursera Project)](#practical-system-programming-in-rust-coursera-project)
  - [🔄 学习路径调整](#-学习路径调整)
    - [根据目标调整](#根据目标调整)
    - [根据时间调整](#根据时间调整)
  - [📈 学习效果评估](#-学习效果评估)
    - [自我评估](#自我评估)
    - [项目评估](#项目评估)
  - [👤 四类学习者详细学习路径](#-四类学习者详细学习路径)
    - [路径 A: 初学者（零编程基础）](#路径-a-初学者零编程基础)
    - [路径 B: 有经验的开发者（其他语言背景）](#路径-b-有经验的开发者其他语言背景)
    - [路径 C: 研究者（形式化方法方向）](#路径-c-研究者形式化方法方向)
    - [路径 D: 维护者/贡献者（Rust 生态方向）](#路径-d-维护者贡献者rust-生态方向)
  - [📚 相关文档](#-相关文档)
    - [学习支持](#学习支持)
    - [形式化研究（研究者路径）](#形式化研究研究者路径)
  - [Rust 1.95+ 学习路径](#rust-195-学习路径)
    - [1.95+ 新特性学习要点](#195-新特性学习要点)
    - [本轮新增模块学习路径](#本轮新增模块学习路径)
      - [学习路径递进关系](#学习路径递进关系)
    - [学习资源](#学习资源)
  - [Rust 1.95+ 持续更新更新](#rust-195-持续更新更新)
    - [本文档的Rust 1.95+更新要点](#本文档的rust-195更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)

---

## 📋 概述

本文档为不同背景的学习者提供系统化的 Rust 学习路径规划，帮助制定学习计划并跟踪进度。

---

## 🎯 学习路径分类

### 路径 1: 完全新手（0 基础）

**目标**: 掌握 Rust 基础语法和核心概念

**时间**: 4-6 周

**学习顺序**:

1. **第 1-2 周: 基础语法**
   - C01: 所有权与借用（重点）
   - C03: 控制流与函数
   - 实践: 编写简单的 CLI 工具

2. **第 3-4 周: 类型系统**
   - C02: 类型系统
   - C04: 泛型编程（基础部分）
   - 实践: 实现简单的数据结构

3. **第 5-6 周: 综合实践**
   - 完成第一个项目: 文件处理工具
   - 复习和巩固

**推荐资源**:

- [所有权速查卡](../02_reference/quick_reference/ownership_cheatsheet.md)
- [控制流速查卡](../02_reference/quick_reference/control_flow_functions_cheatsheet.md)
- [类型系统速查卡](../02_reference/quick_reference/type_system.md)

---

### 路径 2: 有编程经验（其他语言）

**目标**: 快速掌握 Rust 特性并应用到实际项目

**时间**: 6-8 周

**学习顺序**:

1. **第 1-2 周: Rust 核心特性**
   - C01: 所有权与借用（重点理解）
   - C02: 类型系统
   - C03: 控制流与函数
   - 实践: 对比其他语言的差异

2. **第 3-4 周: 高级特性**
   - C04: 泛型编程
   - C05: 线程与并发
   - C06: 异步编程
   - 实践: 并发/异步项目

3. **第 5-6 周: 系统编程**
   - C07: 进程管理
   - C10: 网络编程
   - 实践: 网络服务器项目

4. **第 7-8 周: 专业领域**
   - C08: 算法与数据结构（含 [算法决策树](../../crates/c08_algorithms/src/algorithm_decision_trees.rs)）
   - C09: 设计模式
   - 实践: 综合项目

5. **第 9-10 周: 进阶专题（本轮新增）**
   - c01: [Pin 与自引用结构](../../crates/c01_ownership_borrow_scope/src/pin_and_self_referential.rs)（高级所有权深入）
   - exercises: [Rust 1.95 特性练习](../../exercises/src/rust_195_feature_exercises.rs)
   - 实践: 理解异步状态机底层与自引用安全

**推荐资源**:

- [线程并发使用指南](../05_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md)
- [异步编程使用指南](../05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md)
- [网络编程速查卡](../02_reference/quick_reference/network_programming_cheatsheet.md)
- [Pin 与自引用结构形式化](../research_notes/formal_methods/pin_self_referential.md)

---

### 路径 3: 中级开发者（有 Rust 基础）

**目标**: 深入掌握高级特性和最佳实践

**时间**: 8-12 周

**学习顺序**:

1. **第 1-2 周: 并发与异步**
   - C05: 线程与并发（深入）
   - C06: 异步编程（深入）
   - 实践: 高性能并发应用

2. **第 3-4 周: 系统编程**
   - C07: 进程管理（完整）
   - C10: 网络编程（完整）
   - 实践: 分布式系统

3. **第 5-6 周: 算法与设计**
   - C08: 算法与数据结构（深入）
   - C09: 设计模式（完整）
   - 实践: 算法优化项目

4. **第 7-8 周: 高级主题**
   - C11: 宏系统
   - C12: WASM
   - c01: [Pin 与自引用结构](../../crates/c01_ownership_borrow_scope/src/pin_and_self_referential.rs)（深入 `Pin<P>`、`Unpin`、自引用安全）
   - c02: [类型系统前沿](../../crates/c02_type_system/src/type_system_frontier.rs)（Never type `!`、TAIT、RPITIT/AFIT）
   - c08: [算法决策树](../../crates/c08_algorithms/src/algorithm_decision_trees.rs)（根据场景选择最优算法）
   - 实践: 宏、WASM、高性能算法与类型系统结合项目

5. **第 9-10 周: 新特性巩固**
   - exercises: [Rust 1.95 特性练习](../../exercises/src/rust_195_feature_exercises.rs)（`if let` guards、`cfg_select!`、`Atomic::update` 等）
   - content/emerging/: [前沿特性跟踪](../../content/emerging/README.md)（Generic Const Expressions、Async Closures 等）
   - content/ecosystem/: [生态深度](../../content/ecosystem/README.md)（Tokio、Axum、SQLx 内部原理）
   - 实践: 综合运用新特性重构旧代码

6. **第 11-12 周: 综合项目**
   - 完成大型综合项目
   - 性能优化实践
   - 代码审查和重构

**推荐资源**:

- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)
- [项目最佳实践指南](../05_guides/BEST_PRACTICES.md)
- [设计模式使用指南](../05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md)

---

### 路径 4: 高级开发者（专家级）

**目标**: 掌握 Rust 生态系统和架构设计

**时间**: 持续学习

**学习重点**:

1. **架构设计**
   - 大型项目架构
   - 模块化设计
   - 性能优化

2. **生态系统**
   - 主流库和框架
   - 工具链深入
   - 社区最佳实践

3. **专业领域**
   - 嵌入式 Rust
   - 区块链开发
   - 系统编程

4. **前沿特性跟踪（本轮新增）**
   - content/emerging/: [前沿特性跟踪](../../content/emerging/README.md)（Async Closures、Generic Const Expressions、TAIT 等）
   - content/ecosystem/: [生态深度](../../content/ecosystem/README.md)（Tokio 运行时、Axum 服务抽象、SQLx 编译时检查）
   - 跟踪最新稳定版本特性，保持技术敏锐度

5. **形式化与验证（研究者路径）**
   - [形式化证明系统指南](../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md)
   - [核心定理完整证明](../research_notes/CORE_THEOREMS_FULL_PROOFS.md)
   - [国际对标索引](../research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)

**推荐资源**:

- [项目架构指南](../07_project/PROJECT_ARCHITECTURE_GUIDE.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)
- [故障排查指南](../05_guides/TROUBLESHOOTING_GUIDE.md)

---

## 📊 学习进度跟踪

### 进度检查清单

#### 基础阶段（C01-C03）

- [ ] 理解所有权和借用规则
- [ ] 掌握生命周期基础
- [ ] 能够编写基本的控制流代码
- [ ] 理解函数和闭包
- [ ] 完成基础项目

#### 进阶阶段（C04-C06）

- [ ] 掌握泛型编程
- [ ] 理解 Trait 系统
- [ ] 能够编写并发代码
- [ ] 掌握异步编程基础
- [ ] 完成并发/异步项目

#### 高级阶段（C07-C10）

- [ ] 掌握进程管理
- [ ] 理解 IPC 机制
- [ ] 能够编写网络应用
- [ ] 掌握常用算法
- [ ] 完成系统编程项目

#### 专家阶段（C11-C12）

- [ ] 掌握宏系统
- [ ] 能够编写 WASM 应用
- [ ] 理解 Rust 内部机制
- [ ] 完成专业领域项目

#### 新特性与前沿阶段（本轮新增）

- [ ] 掌握 `Pin<P>` 与自引用结构（c01 `pin_and_self_referential.rs`）
- [ ] 理解 Never type `!` 与类型系统前沿（c02 `type_system_frontier.rs`）
- [ ] 能够根据场景选择合适算法（c08 `algorithm_decision_trees.rs`）
- [ ] 完成 Rust 1.95 特性练习（exercises `rust_195_feature_exercises.rs`）
- [ ] 了解前沿特性跟踪（content/emerging/）与生态深度（content/ecosystem/）

---

## 💻 学习路径代码示例

### 路径 1 代码示例：基础语法实践

```rust
// 所有权与借用基础示例
fn main() {
    // 所有权转移
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权转移到 s2
    // println!("{}", s1);  // 错误：s1 不再有效
    println!("{}", s2);     // 正确

    // 借用示例
    let len = calculate_length(&s2);
    println!("'{}' 长度: {}", s2, len);  // s2 仍然可用
}

fn calculate_length(s: &String) -> usize {
    s.len()
}
```

### 路径 2 代码示例：并发编程实践

```rust
use std::thread;
use std::sync::mpsc;

// 多线程消息传递示例
fn main() {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let msg = String::from("来自子线程的消息");
        tx.send(msg).unwrap();
    });

    let received = rx.recv().unwrap();
    println!("收到: {}", received);
}
```

### 路径 3 代码示例：异步编程实践

```rust
use tokio::time::{sleep, Duration};

// 异步函数示例
async fn fetch_data() -> String {
    sleep(Duration::from_secs(1)).await;
    "数据获取完成".to_string()
}

#[tokio::main]
async fn main() {
    let result = fetch_data().await;
    println!("{}", result);
}
```

### 路径 4 代码示例：高级特性实践

```rust
// 宏系统示例
macro_rules! say_hello {
    ($name:expr) => {
        println!("Hello, {}!", $name);
    };
}

// 泛型与 Trait 边界示例
fn process<T: ToString>(item: T) -> String {
    format!("处理结果: {}", item.to_string())
}

fn main() {
    say_hello!("Rust");
    println!("{}", process(42));
    println!("{}", process("文本"));
}
```

---

## 🎯 学习建议

### 1. 理论与实践结合

- 每学习一个概念，立即编写代码实践
- 完成每个模块的示例程序
- 尝试修改示例代码，观察结果

### 2. 项目驱动学习

- 每完成一个阶段，完成一个项目
- 从简单项目开始，逐步增加复杂度
- 参考项目示例，但尝试自己实现

### 3. 持续复习

- 定期回顾已学内容
- 使用速查卡快速复习
- 参与代码审查和讨论

### 4. 社区参与

- 阅读 Rust 社区博客
- 参与开源项目
- 参加 Rust 会议和活动

---

## 📚 推荐学习资源

### 官方资源

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust Book](https://doc.rust-lang.org/book/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)

### 项目资源

- [快速参考卡片](../02_reference/quick_reference/README.md)
- [使用指南](../05_guides/README.md)
- [最佳实践指南](../05_guides/BEST_PRACTICES.md)

### 社区资源

- [Rust 社区论坛](https://users.rust-lang.org/)
- [Rust 中文社区](https://rustcc.cn/)
- [Rust 周报](https://this-week-in-rust.org/)

### Coursera 在线课程

#### Rust Programming Specialization (Duke University)

- **链接**: <https://www.coursera.org/specializations/rust-programming>
- **内容**: Rust基础、数据结构、并发编程
- **适合路径**:
  - 路径 1: 完全新手（0 基础）
  - 路径 2: 有编程经验（其他语言）
- **与本文档对齐**:

  | Coursera 模块 | 本文档对应章节 |
| :--- | :--- |
  | Rust Basics | C01-C03 基础阶段 |
  | Data Structures | C04 集合与错误 |
  | Concurrency | C08 并发编程 |

#### Programming in Rust (University of Colorado Boulder)

- **链接**: <https://www.coursera.org/learn/programming-in-rust>
- **内容**: Rust编程基础
- **适合路径**: 路径 1: 完全新手（0 基础）
- **与本文档对齐**: C01-C03 基础阶段

#### Practical System Programming in Rust (Coursera Project)

- **内容**: 系统编程实践
- **适合路径**:
  - 路径 2: 有编程经验（其他语言）
  - 路径 3: 中级开发者（有 Rust 基础）
- **与本文档对齐**: C07 进程管理、C10 网络编程

---

## 🔄 学习路径调整

### 根据目标调整

- **Web 开发**: 重点学习 C06、C10、C12
- **系统编程**: 重点学习 C05、C07、C10
- **算法开发**: 重点学习 C08、C04
- **嵌入式**: 重点学习 C01、C02、C11

### 根据时间调整

- **时间紧张**: 选择核心模块（C01-C03, C05-C06）
- **时间充足**: 完整学习所有模块
- **持续学习**: 按需深入学习特定模块

---

## 📈 学习效果评估

### 自我评估

- 能够独立编写 Rust 代码
- 理解常见错误并能解决
- 能够阅读和理解他人代码
- 能够设计和实现项目

### 项目评估

- 完成基础项目（CLI 工具）
- 完成中级项目（网络应用）
- 完成高级项目（分布式系统）
- 贡献开源项目

---

## 👤 四类学习者详细学习路径

### 路径 A: 初学者（零编程基础）

**目标**: 从零开始掌握 Rust 基础，建立编程思维

**时间**: 8-10 周

**学习路径**:

```text
第 1-2 周: 编程基础概念
├── 计算机基础与算法思维
├── 变量、数据类型、运算符
└── 实践: 编写简单的计算器程序

第 3-4 周: Rust 基础语法
├── C01: 所有权与借用（重点理解）
├── C02: 类型系统基础
└── 实践: 实现基础数据结构（栈、队列）

第 5-6 周: 控制流与函数
├── C03: 控制流与函数
├── 模式匹配基础
└── 实践: 文本处理工具

第 7-8 周: 项目实战
├── 综合练习项目
├── 代码阅读与理解
└── 实践: 命令行待办事项应用

第 9-10 周: 进阶准备
├── 复习巩固
├── 错误处理基础
└── 准备进入中级学习
```

**推荐资源**:

- [Rust Book 中文版](https://kaisery.github.io/trpl-zh-cn/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
- [所有权速查卡](../02_reference/quick_reference/ownership_cheatsheet.md)

---

### 路径 B: 有经验的开发者（其他语言背景）

**目标**: 快速迁移到 Rust，掌握所有权和类型系统

**时间**: 4-6 周

**学习路径**:

```text
第 1 周: Rust 与其他语言对比
├── 内存管理对比（vs C++/Go/Python）
├── 类型系统对比
└── 实践: 将熟悉的数据结构用 Rust 实现

第 2 周: 所有权系统深度理解
├── C01: 所有权与借用（核心）
├── 生命周期基础
└── 实践: 实现链表（理解所有权转移）

第 3 周: 类型系统与泛型
├── C02: 类型系统
├── C04: 泛型编程
└── 实践: 实现通用容器

第 4 周: 并发编程
├── C05: 线程与并发
├── C06: 异步编程
└── 实践: 并发文件处理器

第 5-6 周: 系统编程实战
├── C07: 进程管理
├── C10: 网络编程
└── 实践: 构建 HTTP 服务器
```

**代码示例 - 从 Python 迁移到 Rust**:

```rust
// Python: def process_data(data): return [x * 2 for x in data if x > 0]
// Rust 等价实现:
fn process_data(data: &[i32]) -> Vec<i32> {
    data.iter()
        .filter(|&&x| x > 0)
        .map(|&x| x * 2)
        .collect()
}
```

**推荐资源**:

- [跨语言对比文档](../02_reference/CROSS_LANGUAGE_COMPARISON.md)
- [线程并发使用指南](../05_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md)
- [异步编程使用指南](../05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md)

---

### 路径 C: 研究者（形式化方法方向）

**目标**: 深入理解 Rust 的形式化基础，掌握证明技术

**时间**: 持续学习（建议 12-16 周入门）

**学习路径**:

```text
第 1-4 周: 形式化基础
├── 分离逻辑基础
├── 线性类型理论
├── RustBelt 论文研读
└── 阅读: [形式化方法研究](../research_notes/formal_methods/README.md)

第 5-8 周: 所有权与借用形式化
├── [所有权模型形式化](../research_notes/formal_methods/ownership_model.md)
├── [借用检查器证明](../research_notes/formal_methods/borrow_checker_proof.md)
├── [生命周期形式化](../research_notes/formal_methods/lifetime_formalization.md)
└── 实践: Prusti/Kani 验证或数学风格证明（见 [CORE_THEOREMS_FULL_PROOFS](../research_notes/CORE_THEOREMS_FULL_PROOFS.md)）

第 9-12 周: 并发与异步形式化
├── [Send/Sync 形式化](../research_notes/formal_methods/send_sync_formalization.md)
├── [异步状态机形式化](../research_notes/formal_methods/async_state_machine.md)
├── [Pin 和自引用类型形式化](../research_notes/formal_methods/pin_self_referential.md)
└── 实践: 分析并发算法的安全性证明

第 13-16 周: 前沿研究
├── [形式化证明系统指南](../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md)
├── [核心定理完整证明](../research_notes/CORE_THEOREMS_FULL_PROOFS.md)
├── [国际对标索引](../research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)
└── 研究项目: 选择一个开放问题深入研究
```

**关键形式化文档索引**:

| 主题 | 文档 | 核心定理 |
| :--- | :--- | :--- |
| 所有权 | [ownership_model](../research_notes/formal_methods/ownership_model.md) | T2 唯一性, T3 内存安全 |
| 借用 | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md) | T1 数据竞争自由 |
| 生命周期 | [lifetime_formalization](../research_notes/formal_methods/lifetime_formalization.md) | LF-T2 引用有效性 |
| 异步 | [async_state_machine](../research_notes/formal_methods/async_state_machine.md) | T6.1-T6.3 状态/安全/进度 |
| Pin | [pin_self_referential](../research_notes/formal_methods/pin_self_referential.md) | T1-T3 Pin 保证 |
| Send/Sync | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md) | SEND-T1, SYNC-T1 |

---

### 路径 D: 维护者/贡献者（Rust 生态方向）

**目标**: 参与 Rust 开源项目，理解编译器和标准库

**时间**: 持续学习

**学习路径**:

```text
阶段 1: 代码贡献基础 (4-6 周)
├── Rust 编译器架构概览
├── Cargo 工作空间管理
├── 测试与文档规范
└── 实践: 提交文档修复和小功能

阶段 2: 深入理解 (8-12 周)
├── rustc  borrowck 模块
├── 宏系统与代码生成
├── unsafe 代码审查
└── 实践: 修复中级 issue

阶段 3: 专业领域 (持续)
├── 特定领域库开发
├── 性能优化技术
├── FFI 与系统接口
└── 实践: 维护 crate 或贡献标准库
```

**推荐资源**:

- [Rust 编译器开发指南](https://rustc-dev-guide.rust-lang.org/)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/) (unsafe 代码指南)
- [形式化工程系统](../rust-formal-engineering-system/README.md)
- [项目架构指南](../07_project/PROJECT_ARCHITECTURE_GUIDE.md)

---

## 📚 相关文档

### 学习支持

- [项目架构指南](../07_project/PROJECT_ARCHITECTURE_GUIDE.md)
- [最佳实践指南](../05_guides/BEST_PRACTICES.md)
- [故障排查指南](../05_guides/TROUBLESHOOTING_GUIDE.md)
- [快速参考卡片](../02_reference/quick_reference/README.md)

### 形式化研究（研究者路径）

- [形式化方法研究](../research_notes/formal_methods/README.md)
- [形式化证明系统指南](../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md)
- [证明索引](../research_notes/PROOF_INDEX.md)
- [国际对标索引](../research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 持续更新
**最后更新**: 2026-05-08 (本轮新增: c01 pin, c02 frontier, c08 decision_trees, 1.95 exercises, emerging, ecosystem)

---

## Rust 1.95+ 学习路径

> **适用版本**: Rust 1.95.0+

### 1.95+ 新特性学习要点

| 特性 | 学习难度 | 推荐顺序 |
|------|---------|---------|
| rray_windows | ⭐ | 第1周 |
| ControlFlow | ⭐⭐ | 第2周 |
| LazyCell/LazyLock 新方法 | ⭐⭐ | 第3周 |
| Peekable::next_if_map | ⭐ | 第4周 |
| `if let` guards | ⭐⭐ | 第5周 |
| `cfg_select!` | ⭐⭐ | 第6周 |
| `Atomic::update` | ⭐⭐ | 第7周 |
| `use<..>` precise capturing | ⭐⭐⭐ | 第8周 |

### 本轮新增模块学习路径

| 模块 | 定位 | 前置要求 | 推荐路径 | 文档位置 |
|------|------|----------|----------|----------|
| **c01 `pin_and_self_referential.rs`** | 高级所有权 | 掌握基础所有权与生命周期 | 路径 2+ 第 9 周起 | [`crates/c01_ownership_borrow_scope/src/pin_and_self_referential.rs`](../../crates/c01_ownership_borrow_scope/src/pin_and_self_referential.rs) |
| **c02 `type_system_frontier.rs`** | 类型系统前沿 | 掌握泛型与 Trait | 路径 3+ 第 7 周起 | [`crates/c02_type_system/src/type_system_frontier.rs`](../../crates/c02_type_system/src/type_system_frontier.rs) |
| **c08 `algorithm_decision_trees.rs`** | 算法选择 | 掌握基础算法 | 路径 2+ 第 7 周起 | [`crates/c08_algorithms/src/algorithm_decision_trees.rs`](../../crates/c08_algorithms/src/algorithm_decision_trees.rs) |
| **exercises `rust_195_feature_exercises.rs`** | 1.95 特性练习 | 完成基础学习 | 所有路径巩固阶段 | [`exercises/src/rust_195_feature_exercises.rs`](../../exercises/src/rust_195_feature_exercises.rs) |
| **content/emerging/** | 前沿特性跟踪 | 中级以上 | 路径 3+ 持续学习 | [`content/emerging/README.md`](../../content/emerging/README.md) |
| **content/ecosystem/** | 生态深度 | 中级以上 | 路径 3+ 持续学习 | [`content/ecosystem/README.md`](../../content/ecosystem/README.md) |

#### 学习路径递进关系

```text
初级 ──────────────────────────────────────────────────────────> 高级

基础阶段 (C01-C03)
  └── 所有权基础 ──> 生命周期基础 ──> 借用规则
       └── 进阶: Pin 与自引用结构 (c01 pin_and_self_referential.rs)

类型阶段 (C02/C04)
  └── 基础类型 ──> 泛型与 Trait ──> 生命周期标注
       └── 进阶: 类型系统前沿 (c02 type_system_frontier.rs: Never type, TAIT, RPITIT)

算法阶段 (C08)
  └── 基础算法 ──> 数据结构
       └── 进阶: 算法决策树 (c08 algorithm_decision_trees.rs: 根据场景选型)

新特性巩固
  └── Rust 1.95 特性练习 (exercises rust_195_feature_exercises.rs)
       ├── if let guards ──> cfg_select! ──> Atomic::update
       └── use<..> precise capturing

前沿与生态
  └── 前沿特性跟踪 (content/emerging/)
       ├── Async Closures
       ├── Generic Const Expressions
       └── TAIT / RPITIT 演进
  └── 生态深度 (content/ecosystem/)
       ├── Tokio 运行时原理
       ├── Axum 服务抽象
       └── SQLx 编译时检查
```

### 学习资源

- [Rust 1.95+ 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 发布说明](../archive/2026_05_historical_docs/16_rust_1.94_release_notes.md)

**最后更新**: 2026-05-08 (添加 Rust 1.95+ 学习路径)

---

## Rust 1.95+ 持续更新更新

> **适用版本**: Rust 1.95.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.95+更新要点

本文档已针对 **Rust 1.95+** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.95+语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.95+ 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查（已归档）](../archive/2026_05_historical_docs/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08 (Rust 1.95+ 持续更新)
