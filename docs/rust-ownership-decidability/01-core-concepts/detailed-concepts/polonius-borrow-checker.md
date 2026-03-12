# Polonius: 下一代 Rust 借用检查器

> **项目状态**: 活跃开发中 (2024-2025)
> **目标**: Rust 2024 Edition / 2025
> **负责人**: lqd, Amanda Stjerna, Niko Matsakis
> **团队**: Rust Types Team

---

## 目录

- [Polonius: 下一代 Rust 借用检查器](#polonius-下一代-rust-借用检查器)
  - [目录](#目录)
  - [1. 项目概述](#1-项目概述)
    - [1.1 什么是 Polonius](#11-什么是-polonius)
    - [1.2 为什么需要 Polonius](#12-为什么需要-polonius)
    - [1.3 与当前借用检查器的区别](#13-与当前借用检查器的区别)
  - [2. 核心改进](#2-核心改进)
    - [2.1 Case 3: 条件返回引用](#21-case-3-条件返回引用)
    - [2.2 两阶段借用完善](#22-两阶段借用完善)
    - [2.3 Lending Iterators](#23-lending-iterators)
    - [2.4 自引用类型](#24-自引用类型)
  - [3. 理论基础](#3-理论基础)
    - [3.1 基于集合的生命周期](#31-基于集合的生命周期)
    - [3.2 数据流分析](#32-数据流分析)
    - [3.3 位置敏感分析](#33-位置敏感分析)
  - [4. 实现路线图](#4-实现路线图)
    - [4.1 里程碑概览](#41-里程碑概览)
    - [4.2 当前状态 (2024-2025)](#42-当前状态-2024-2025)
  - [5. 实际示例](#5-实际示例)
    - [5.1 当前编译器拒绝的代码](#51-当前编译器拒绝的代码)
    - [5.2 Polonius 接受的代码](#52-polonius-接受的代码)
  - [6. 与验证工具的关系](#6-与验证工具的关系)
    - [6.1 RefinedRust 使用 Polonius](#61-refinedrust-使用-polonius)
    - [6.2 工具集成](#62-工具集成)
  - [7. 未来展望](#7-未来展望)
    - [7.1 自引用类型语法](#71-自引用类型语法)
    - [7.2 移动语义改进](#72-移动语义改进)
  - [8. 如何尝试](#8-如何尝试)
  - [参考文献](#参考文献)
    - [官方资源](#官方资源)
    - [演讲和会议](#演讲和会议)
    - [学术论文](#学术论文)
    - [相关项目](#相关项目)

---

## 1. 项目概述

### 1.1 什么是 Polonius

**Polonius** 是 Rust 下一代借用检查器 (borrow checker) 的代号，以莎士比亚《哈姆雷特》中的角色命名（寓意 "生存还是毁灭" 般的复杂性分析）。

**核心定位**:

- 解决当前 NLL (Non-Lexical Lifetimes) 借用检查器的局限性
- 接受更多被证明是安全的代码模式
- 为 "Lending Iterators" 和 "自引用类型" 提供理论基础

### 1.2 为什么需要 Polonius

当前借用检查器 (基于 NLL) 有几个已知的局限性:

| 问题 | 说明 | 影响 |
|------|------|------|
| **Case 3** | 无法处理条件返回引用 | 限制某些 API 设计 |
| **两阶段借用** | 处理不完善 | Vec::push 等需要特殊处理 |
| **自引用** | 完全不支持 | Pin API 复杂性的根源 |
| **分支敏感** | 缺乏流敏感分析 | 误报某些安全代码 |

### 1.3 与当前借用检查器的区别

```
借用检查器演进:
┌─────────────────────────────────────────────────────────────┐
│  Rust 2015 - 词法生命周期                                   │
│  • 基于作用域的简单规则                                     │
│  • 过于保守，拒绝大量安全代码                               │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  Rust 2018 - NLL (Non-Lexical Lifetimes)                    │
│  • 基于数据流分析                                           │
│  • 接受更多代码，但仍有限制                                 │
│  • 放弃 "Case 3" 支持以换取性能                            │
└─────────────────────────────────────────────────────────────┘
                            ↓
┌─────────────────────────────────────────────────────────────┐
│  Rust 2024/2025 - Polonius ⭐ NEW                           │
│  • 声明式分析 (基于逻辑规则)                                │
│  • 完整支持 Case 3                                          │
│  • 为自引用类型铺平道路                                     │
└─────────────────────────────────────────────────────────────┘
```

---

## 2. 核心改进

### 2.1 Case 3: 条件返回引用

**问题代码** (当前编译器拒绝):

```rust
fn get_or_default<'a>(
    vec: &'a mut Vec<String>,
    idx: usize,
) -> &'a String {
    if idx < vec.len() {
        return &vec[idx];  // 早期返回引用
    }
    vec.push(String::new());  // 修改 vec
    &vec[idx]  // 返回引用
}
```

**当前编译器错误**:

```
error[E0502]: cannot borrow `*vec` as mutable because it is also borrowed as immutable
```

**Polonius 分析**:

- 两个分支**互斥**
- 如果进入 `if` 分支，不会执行 `push`
- 如果跳过 `if` 分支，`vec` 的共享借用已经结束
- 因此代码是安全的

### 2.2 两阶段借用完善

**当前行为**:

```rust
let mut v = vec![1, 2, 3];
v.push(v.len());  // 魔法：被特殊处理
```

**Polonius 改进**:

- 将所有可变引用视为两阶段借用
- 统一的分析模型
- 不需要特殊 case

### 2.3 Lending Iterators

**Lending Iterator** (借出迭代器) 是一个重要的新抽象:

```rust
// 当前 Iterator trait
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

// 理想的 Lending Iterator (需要 Polonius)
trait LendingIterator {
    type Item<'a> where Self: 'a;
    fn next(&mut self) -> Option<Self::Item<'_>>;
}
```

**用途**:

```rust
// 遍历行而不分配
let lines = reader.lines();
while let Some(line) = lines.next() {
    // line 借自 lines
    println!("{}", line);
} // line 在这里结束，不是 'static
```

### 2.4 自引用类型

**当前问题** (Pin API 的复杂性):

```rust
// 现在：使用 Pin<Box<dyn Future>> 实现自引用
async fn foo() {
    let local = 42;
    let ref_to_local = &local;  // 自引用
    bar(ref_to_local).await;    // 跨越 await 点
}
```

**Polonius 未来的可能性**:

```rust
// 可能的未来语法 (EuroRust 2024 提案)
struct Parser<'input> {
    input: &'input str,
    current_pos: &'input str,  // 自引用，指向 input 内部
}

impl<'input> Parser<'input> {
    fn new(input: &'input str) -> Self {
        Self {
            input,
            current_pos: input,  // 显式自引用关系
        }
    }
}
```

---

## 3. 理论基础

### 3.1 基于集合的生命周期

Polonius 的核心创新：**将生命周期表示为 "贷款集合" (set of loans)**

```
传统方法: 生命周期 = 代码区域 (CFG 点集合)
Polonius:   生命周期 = 贷款集合 {loan1, loan2, ...}

贷款 (loan): 一个借用表达式的实例
```

**优势**:

- 更精确的别名分析
- 支持 "outlives" 约束的传递推理
- 更好的错误信息

### 3.2 数据流分析

Polonius 使用 **Datalog** 风格的声明式分析:

```datalog
% 基础事实
loan_live_at(L, P) :-  % 贷款 L 在程序点 P 活跃
origin_contains_loan_at(O, L, P) :-  % 原点 O 在 P 包含贷款 L

% 约束传播
loan_live_at(L, P) :-
    origin_contains_loan_at(O, L, P),
    origin_live_at(O, P).

% 错误检测
error(L, P) :-
    loan_live_at(L, P),
    loan_invalidated_at(L, P).
```

**实现策略演变**:

1. **原型** (2018): 纯 Datalog (Datafrog)
2. **当前** (2024): 原生 rustc 实现，移除 Datalog 依赖
3. **未来**: 完全集成到类型系统

### 3.3 位置敏感分析

**位置不敏感** (当前阶段): 考虑 loan 是否在作用域内
**位置敏感** (最终目标): 考虑 loan 在特定 CFG 点的状态

```rust
fn example(x: &mut i32) {
    let y = &mut *x;  // loan1
    *y = 1;           // loan1 使用

    let z = &mut *x;  // loan2 (当前: 错误，Polonius: OK)
    *z = 2;
}
```

**Polonius 分析**:

- `y` 的 loan 在 `z` 创建前已"死亡"
- 因为之后不再使用 `y`
- 因此可以接受此代码

---

## 4. 实现路线图

### 4.1 里程碑概览

| 里程碑 | 目标日期 | 状态 | 描述 |
|--------|----------|------|------|
| 1. 位置不敏感实现 | 2024 Q4 | ✅ 完成 | 在 nightly 上可用 |
| 2. 测试套件验证 | 2024 Q4 | ✅ 完成 | 通过 15,000+ 测试 |
| 3. Crater 运行 | 2025 Q1 | ⏳ 进行中 | 检查生态兼容性 |
| 4. 位置敏感原型 | 2025 Q1-Q2 | 🚧 开发中 | 接受更多代码模式 |
| 5. a-mir-formality | 2025 | 🚧 进行中 | 形式化模型 |
| 6. 稳定版发布 | 2025+ | 📋 计划中 | 默认启用 |

### 4.2 当前状态 (2024-2025)

**2024 年进展**:

- ✅ 位置不敏感 Polonius 已合并到 nightly
- ✅ 通过完整测试套件
- ✅ 性能优化达到可接受水平

**2025 年目标**:

- 完成位置敏感分析
- 集成到 Rust 2024 Edition
- 形式化验证 (a-mir-formality)

**已知挑战**:

- 某些代码模式导致指数级复杂度
- 需要大量诊断质量工作
- 与 trait 求解器的交互

---

## 5. 实际示例

### 5.1 当前编译器拒绝的代码

**示例 1: 条件返回**

```rust
fn find_or_insert<'a>(
    map: &'a mut HashMap<String, String>,
    key: &str,
) -> &'a String {
    if let Some(value) = map.get(key) {
        return value;  // 早期返回
    }
    map.insert(key.to_string(), String::new());  // 修改
    &map[key]
}
```

**当前错误**: `cannot borrow as mutable`

**Polonius**: ✅ 接受 (分支互斥)

---

**示例 2: 部分借用**

```rust
struct Buffer {
    data: Vec<u8>,
    pos: usize,
}

impl Buffer {
    fn read(&mut self) -> Option<u8> {
        let byte = self.data.get(self.pos)?;  // 共享借用 data
        self.pos += 1;  // 修改 pos
        Some(*byte)
    }
}
```

**当前**: 需要变通
**Polonius**: ✅ 直接接受

---

**示例 3: 循环中的借用**

```rust
fn process_queue(queue: &mut VecDeque<Item>) {
    while let Some(item) = queue.front() {
        if item.ready() {
            let item = queue.pop_front().unwrap();
            process(item);
        } else {
            break;
        }
    }
}
```

**当前错误**: `cannot borrow as mutable`
**Polonius**: ✅ 接受

### 5.2 Polonius 接受的代码

```rust
#![feature(polonius)]

fn polonius_example(vec: &mut Vec<i32>) -> &i32 {
    if vec.is_empty() {
        vec.push(0);
        &vec[0]
    } else {
        &vec[0]
    }
}

fn main() {
    let mut v = vec![1, 2, 3];
    let r = polonius_example(&mut v);
    println!("{}", r);
}
```

**编译**:

```bash
rustc +nightly -Zpolonius example.rs
```

---

## 6. 与验证工具的关系

### 6.1 RefinedRust 使用 Polonius

**RefinedRust** 前端利用 Polonius 提取生命周期信息:

```
RefinedRust 前端:
1. rustc 解析生成 MIR
2. Polonius 分析生成生命周期约束
3. 将 "loans" 映射到 RustBelt 生命周期逻辑
4. 生成 Radium 中间表示
```

**关键技术**:

- 对齐 Polonius 的 "loans" 与 RustBelt 的 "lifetimes"
- 利用 Prusti 实现的工具函数
- 提取引用生命周期信息

### 6.2 工具集成

| 工具 | Polonius 集成 | 用途 |
|------|--------------|------|
| **RefinedRust** | ✅ 使用中 | 生命周期提取 |
| **rust-analyzer** | 📋 计划中 | 更好的 IDE 分析 |
| **gccrs** | 🚧 进行中 | GCC Rust 前端 |

**gccrs 项目** (GCC Rust 编译器):

- 使用 Polonius 作为借用检查器
- 2025 年 3 月已提交 GCC 15 补丁
- 用 Rust 编写的 Polonius 实现

---

## 7. 未来展望

### 7.1 自引用类型语法

**EuroRust 2024 提案**:

```rust
// 可能的语法: 'self 生命周期
struct Parser<'input> {
    input: &'input str,
    cursor: &'self str,  // 借自 self.input
}

impl Parser<'_> {
    fn parse(&mut self) -> &str {
        // 返回借自 self 的引用
        &self.input[self.pos..]
    }
}
```

**影响**:

- 简化 Pin API 的使用
- 启用 Lending Iterator
- 更安全的自引用数据结构

### 7.2 移动语义改进

**当前限制**:

```rust
// 现在：移动后指针无法自动更新
let mut data = [1, 2, 3];
let ptr = &mut data[0];
let moved = data;  // data 被移动
// ptr 现在悬空，但编译器无法检测
```

**Polonius 可能启用的未来**:

- 更精确跟踪移动对引用的影响
- 可能的 "Move trait" 来定制移动语义
- 自动更新内部指针

---

## 8. 如何尝试

**nightly Rust**:

```bash
# 安装 nightly
rustup install nightly

# 使用 Polonius 编译
rustc +nightly -Zpolonius your_code.rs

# 或使用 Cargo
RUSTFLAGS="-Zpolonius" cargo +nightly build
```

**限制**:

- 仅适用于 nightly 工具链
- 尚未优化性能 (可能比默认慢)
- 诊断信息仍在改进中

**测试您的代码**:

```bash
# 检查是否受益于 Polonius
cargo +nightly check  # 标准检查

RUSTFLAGS="-Zpolonius" cargo +nightly check  # Polonius 检查
# 如果后者通过而前者失败，您的代码将受益于 Polonius
```

---

## 参考文献

### 官方资源

1. **Rust Project Goals 2024H2**
   - <https://rust-lang.github.io/rust-project-goals/2024h2/Polonius.html>

2. **Inside Rust Blog - Polonius Update** (2023-10)
   - <https://blog.rust-lang.org/inside-rust/2023/10/06/polonius-update.html>
   - 路线图和里程碑详解

3. **Rust Project Goals 2025H1**
   - <https://rust-lang.github.io/rust-project-goals/2025h1/Polonius.html>

### 演讲和会议

1. **EuroRust 2024 - Amanda Stjerna**
   - "The first six years in the development of Polonius"
   - <https://eurorust.eu/2024/talks/the-first-six-years-in-the-development-of-polonius/>

2. **EuroRust 2024 回顾**
   - <https://lukas-prokop.at/articles/2024-10-13-eurorust24-review>

### 学术论文

1. **NLL 原始论文**
   - 非词法生命周期的理论基础

2. **a-mir-formality**
   - Rust MIR 和类型系统的形式化模型
   - 将包含 Polonius 的形式化语义

### 相关项目

1. **gccrs + Polonius**
   - <https://gcc.gnu.org/pipermail/gcc-patches/2025-March/619453.html>
   - GCC Rust 前端集成 Polonius

2. **Datafrog**
   - <https://github.com/rust-lang/datafrog>
   - 早期原型使用的 Datalog 引擎

---

**文档版本**: 1.0.0
**最后更新**: 2026-03-12
**维护者**: Rust 所有权可判定性研究项目
