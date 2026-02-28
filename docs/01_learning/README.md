# 学习路径与导航

> **创建日期**: 2025-12-11
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 学习规划与官方资源映射；解决「如何规划学习、与官方资源如何映射」
> **判定目标**: 学习路径可执行、官方资源可追溯
> **完整结构**: [DOCS_STRUCTURE_OVERVIEW](../DOCS_STRUCTURE_OVERVIEW.md) § 2.1
> **概念说明**: Rust 学习路径提供从入门到精通的系统化学习路线，涵盖语言基础、所有权系统、类型系统、异步编程、Unsafe 等核心主题，并与 The Rust Book、Rust Reference 等官方资源映射对应。

---

## 快速开始示例

```rust
// 第一个 Rust 程序（C01 基础）
fn main() {
    println!("Hello, Rust!");

    let name = "Rustacean";
    let age = 5;
    println!("I'm a {} who is {} years old", name, age);
}

// 所有权基础（C02）
fn ownership_example() {
    let s1 = String::from("hello");
    let len = calculate_length(&s1);  // 借用
    println!("'{}' length: {}", s1, len);
}

fn calculate_length(s: &String) -> usize {
    s.len()
}

// 模式匹配（C03）
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
}

fn handle_message(msg: Message) {
    match msg {
        Message::Quit => println!("Quit"),
        Message::Move { x, y } => println!("Move to ({}, {})", x, y),
        Message::Write(text) => println!("Write: {}", text),
    }
}
```

---

## 文档列表

- [LEARNING_PATH_PLANNING.md](./LEARNING_PATH_PLANNING.md) - 学习路径规划（四类路径、进度检查清单）
- [OFFICIAL_RESOURCES_MAPPING.md](./OFFICIAL_RESOURCES_MAPPING.md) - 本项目 ↔ The Rust Book / Reference / RBE

---

## 学习路径概览

| 阶段 | 主题 | 核心内容 | 预计时间 |
| :--- | :--- | :--- | :--- |
| **C01** | 基础 | 变量、类型、函数、控制流 | 1-2 周 |
| **C02** | 所有权 | 所有权、借用、生命周期 | 2-3 周 |
| **C03** | 类型系统 | 枚举、结构体、泛型、trait | 2-3 周 |
| **C04** | 集合与错误 | Vec、HashMap、Result、Option | 1-2 周 |
| **C05** | 模块与测试 | 模块系统、单元测试、文档 | 1-2 周 |
| **C06** | 宏与元编程 | 声明宏、过程宏 | 1-2 周 |
| **C07** | 异步编程 | async/await、Future、Tokio | 2-3 周 |
| **C08** | 并发 | 线程、同步原语、Send/Sync | 2-3 周 |
| **C09** | Unsafe | 原始指针、FFI、unsafe 块 | 2-3 周 |
| **C10** | 标准库深入 | Iterator、AsRef/Deref、类型转换 | 1-2 周 |
| **C11** | 项目实战 | 完整项目开发 | 2-4 周 |

---

## 研究者路径

形式化理论与证明体系：

| 主题 | 文档 | 描述 |
| :--- | :--- | :--- |
| 形式化分析 | [FORMAL_PROOF_SYSTEM_GUIDE.md](../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md) | 形式化证明系统指南 |
| 核心定理证明 | [CORE_THEOREMS_FULL_PROOFS.md](../research_notes/CORE_THEOREMS_FULL_PROOFS.md) | 完整形式化证明 |
| 证明索引 | [PROOF_INDEX](../research_notes/PROOF_INDEX.md) | 形式化证明集合 |

```rust
// 形式化研究示例：所有权形式化
// 定理：如果一个值有且只有一个所有者，则在所有者离开作用域时
// 可以安全地释放该值

fn ownership_theorem() {
    {
        let s = String::from("data");  // s 获得所有权
        // s 是唯一的所有者
    }  // s 离开作用域，内存被安全释放
}
```

---

## 在线学习资源

### Coursera

#### Rust Programming Specialization (Duke University)

- **链接**: <https://www.coursera.org/specializations/rust-programming>
- **内容**:
  - Rust基础语法
  - 数据结构
  - 并发编程
- **与本文档对齐**:

  | Coursera内容 | 本文档对应 |
| :--- | :--- |
  | Rust Basics | 01_learning/ |
  | Data Structures | 02_reference/quick_reference/collections_iterators_cheatsheet.md |
  | Concurrency | 05_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md |

#### Programming in Rust (University of Colorado Boulder)

- **链接**: <https://www.coursera.org/learn/programming-in-rust>
- **内容**: Rust编程基础
- **与本文档对齐**: 01_learning/目录

---

## 相关资源

### 官方资源

| 资源 | 链接 | 描述 |
| :--- | :--- | :--- |
| The Rust Book | <https://doc.rust-lang.org/book/> | 官方入门教程 |
| Rust Reference | <https://doc.rust-lang.org/reference/> | 语言参考 |
| Rust By Example | <https://doc.rust-lang.org/rust-by-example/> | 实例学习 |
| Rustlings | <https://github.com/rust-lang/rustlings> | 练习题 |

### 项目资源

| 资源 | 路径 | 描述 |
| :--- | :--- | :--- |
| 速查卡 | [../02_reference/quick_reference/](../02_reference/quick_reference/README.md) | 20个主题速查 |
| 专题指南 | [../05_guides/](../05_guides/README.md) | 异步、线程、Unsafe 等 |
| 工具链 | [../06_toolchain/](../06_toolchain/README.md) | 编译器、Cargo |
| 形式化理论 | [../research_notes/](../research_notes/README.md) | 类型理论、证明 |

### 在线学习资源1

#### edX

| 课程 | 机构 | 链接 | 内容 | 与本文档对齐 |
| :--- | :--- | :--- | :--- | :--- |
| Introduction to Rust Programming | Microsoft | <https://www.edx.org/learn/rust/microsoft-introduction-to-rust-programming> | Rust编程入门 | 01_learning/基础内容 |
| Rust for Developers | Linux Foundation | <https://www.edx.org/learn/rust/the-linux-foundation-rust-for-developers> | 开发者Rust教程 | 05_guides/开发指南 |
| Programming with Rust | W3C | <https://www.edx.org/learn/rust/w3cx-programming-with-rust> | Rust编程 | 02_reference/速查卡 |

#### Udacity

##### C++ for Programmers

- **平台**: Udacity
- **用途**: 与Rust系统编程概念对比学习
- **对比内容**:

  | C++概念 | Rust对应 | 本文档 |
| :--- | :--- | :--- |
  | 手动内存管理 | 所有权系统 | [formal_methods/ownership_model.md](../research_notes/formal_methods/ownership_model.md) |
  | 智能指针 | Box/Rc/Arc | [02_reference/quick_reference/smart_pointers_cheatsheet.md](../02_reference/quick_reference/smart_pointers_cheatsheet.md) |
  | 模板 | 泛型 | [02_reference/quick_reference/generics_cheatsheet.md](../02_reference/quick_reference/generics_cheatsheet.md) |

##### Memory Management

- **平台**: Udacity
- **用途**: 理解内存管理与Rust所有权的关系
- **与本文档对齐**: [formal_methods/ownership_model.md](../research_notes/formal_methods/ownership_model.md) §内存安全

---

## 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 形式化方法概述 | 形式化验证基础理论 | [../research_notes/formal_methods/README.md](../research_notes/formal_methods/README.md) |
| 所有权模型形式化 | 所有权系统数学定义 | [../research_notes/formal_methods/ownership_model.md](../research_notes/formal_methods/ownership_model.md) |
| 类型系统形式化 | 类型理论数学定义 | [../research_notes/type_theory/type_system_foundations.md](../research_notes/type_theory/type_system_foundations.md) |
| 证明索引 | 形式化证明集合 | [../research_notes/PROOF_INDEX.md](../research_notes/PROOF_INDEX.md) |

---

## 主索引

[00_MASTER_INDEX.md](../00_MASTER_INDEX.md)

---

[返回文档中心](../README.md)
