# 借用检查算法的可判定性

> **权威来源**: Rust NLL RFC 2094, Polonius
> **形式化参考**: COR演算, Oxide, Pearee (2021)

## 目录

- [借用检查算法的可判定性](#借用检查算法的可判定性)
  - [目录](#目录)
  - [1. 借用检查问题](#1-借用检查问题)
    - [1.1 问题定义](#11-问题定义)
    - [1.2 复杂度概述](#12-复杂度概述)
  - [2. 词法借用检查](#2-词法借用检查)
    - [2.1 基于作用域的算法](#21-基于作用域的算法)
    - [2.2 限制](#22-限制)
  - [3. NLL 借用检查算法](#3-nll-借用检查算法)
    - [3.1 算法概述](#31-算法概述)
    - [3.2 详细步骤](#32-详细步骤)
  - [4. Polonius: Datalog 方法](#4-polonius-datalog-方法)
    - [4.1 核心思想](#41-核心思想)
    - [4.2 Datalog 规则](#42-datalog-规则)
    - [4.3 与 NLL 的关系](#43-与-nll-的关系)
  - [5. 可判定性证明](#5-可判定性证明)
    - [5.1 NLL 的可判定性](#51-nll-的可判定性)
    - [5.2 Polonius 的可判定性](#52-polonius-的可判定性)
  - [6. 边界情况与限制](#6-边界情况与限制)
    - [6.1 不可判定边界](#61-不可判定边界)
    - [6.2 实践中的保证](#62-实践中的保证)
  - [7. 算法优化](#7-算法优化)
    - [7.1 增量借用检查](#71-增量借用检查)
    - [7.2 并行化](#72-并行化)
  - [8. 与其他分析的交互](#8-与其他分析的交互)
    - [8.1 类型推断与借用检查](#81-类型推断与借用检查)
    - [8.2 MIR优化与借用检查](#82-mir优化与借用检查)
  - [参考文献](#参考文献)

## 1. 借用检查问题

### 1.1 问题定义

借用检查需要回答：给定一个Rust程序，它是否满足所有权和借用规则？

```text
形式化问题:

输入: Rust函数 f，其MIR表示
输出: 接受 (满足借用规则) 或 拒绝 (违反借用规则)

判定要求:
- 健全性 (Soundness): 如果接受，则程序运行时内存安全
- 完备性 (Completeness): 如果程序内存安全，则接受
  (实际中Rust追求"接受尽可能多的安全程序")
```

### 1.2 复杂度概述

| 借用检查方面 | 可判定性 | 算法 | 复杂度 |
|-------------|---------|------|--------|
| 词法生命周期 | ✅ | 作用域分析 | O(n) |
| NLL (MIR-based) | ✅ | 数据流分析 | O(n³) |
| 包含泛型 | ⚠️ | 约束求解 | 可能不终止 |
| 常量求值 | ❌ | 解释器 | 停机问题 |

## 2. 词法借用检查

### 2.1 基于作用域的算法

```text
词法借用检查算法 (Rust 1.0):

输入: AST
输出: 错误列表

对于每个借用表达式 &x 或 &mut x:
    1. 确定借用的生命周期:
       lifetime = scope_of_reference

    2. 检查在整个lifetime内:
       - 如果是 &mut x: 没有其他活跃借用
       - 如果是 &x: 没有其他活跃 &mut x

    3. 检查被借用值活得比借用长:
       lifetime(x) ⊇ lifetime(borrow)

复杂度: O(n²) - 需要检查每对借用
```

### 2.2 限制

```rust
// 词法借用检查过于保守
fn lexical_too_restrictive() {
    let mut data = vec![1, 2, 3];
    let x = &data[0];  // 借用开始

    println!("{}", x);  // 使用 x

    // x 在这里不再使用，但借用仍"活着"
    // data.push(4);  // 词法检查: 错误!
}
```

## 3. NLL 借用检查算法

### 3.1 算法概述

```text
NLL (Non-Lexical Lifetimes) 借用检查:

阶段1: 约束生成
  - 创建区域变量
  - 生成活度约束
  - 生成子类型约束
  - 生成重新借用约束

阶段2: 区域推断
  - 使用数据流分析
  - 计算每个区域的最小集合
  - 求解约束系统

阶段3: 借用检查
  - 计算每点的活跃借用
  - 检查每次访问的合法性
  - 报告冲突
```

### 3.2 详细步骤

```text
步骤1: 区域变量创建

对于 MIR 中的每个引用类型，创建区域变量:
- 显式生命周期参数 → 区域变量
- 省略生命周期 → 隐式区域变量
- 每个借用表达式 → 新区域变量

示例:
let r: &'a i32 = &'b x;
// 创建 'a 和 'b 两个区域变量
```

```text
步骤2: 活度约束

数据流分析计算每个变量的活跃性:

LiveIn(b)  = (LiveOut(b) - Kill(b)) ∪ Gen(b)
LiveOut(b) = ⋃ LiveIn(s) for s ∈ succ(b)

其中:
- Gen(b): 在b块中使用的变量
- Kill(b): 在b块中定义的变量

对于引用变量r，其生命周期包含所有它活跃的点。
```

```text
步骤3: 子类型约束

从类型检查生成约束:

赋值: x = y
  如果 x: &'a T, y: &'b T，则 'b: 'a (y的生命周期包含x的)

函数调用: f(arg)
  形参: &'p T, 实参: &'a T
  约束: 'a: 'p

返回值: return x
  返回类型: &'r T, x: &'a T
  约束: 'a: 'r
```

```text
步骤4: 约束求解

使用不动点迭代求解区域:

初始化: 每个区域 = 空集

迭代直到不动点:
  对于每个约束 'a: 'b:
    Region('a) = Region('a) ∪ Region('b)

  对于每个活度约束:
    如果变量在点p使用，则 p ∈ Region(变量类型)

结果: 每个区域是其最小集合
```

```text
步骤5: 借用检查

对于每个程序点p:
  计算活跃借用集: ActiveLoans(p)

  对于在p的每个访问:
    如果访问路径与 loan 冲突:
      检查 loan ∈ ActiveLoans(p)
      如果是 → 错误!

冲突类型:
- 读-写冲突: 读取与 &mut 借用冲突
- 写-写冲突: 写入与任何借用冲突
- 写-移动冲突: 移动与借用冲突
```

## 4. Polonius: Datalog 方法

### 4.1 核心思想

```text
Polonius 将借用检查编码为 Datalog 程序:

优势:
- 声明式: 规则直接表达语义
- 可扩展: 容易添加新规则
- 优化: 利用Datalog引擎的优化

输入关系 (facts):
- loan_issued_at(point, loan)
- loan_killed_at(point, loan)
- loan_invalidated_at(point, loan)
- cfg_edge(point1, point2)
- outlives(origin1, origin2)
```

### 4.2 Datalog 规则

```prolog
% 基础规则

% 借用在其创建点存活
loan_live_at(P, L) :- loan_issued_at(O, L, P).

% 借用通过 CFG 边传播
loan_live_at(P2, L) :-
    loan_live_at(P1, L),
    cfg_edge(P1, P2),
    not loan_killed_at(L, P1).

% 通过 outlives 关系传播
% 如果 'a: 'b 且借用 'a 存活，则借用 'b 也存活
loan_live_at(P, L) :-
    loan_live_at(P, L1),
    loan_issued_at(O1, L1, _),
    loan_issued_at(O2, L2, _),
    outlives(O1, O2).

% 错误检测
error(P, L) :-
    loan_live_at(P, L),
    loan_invalidated_at(L, P).

% 更精确的错误: 三点多错误
error(origin, use_point, loan) :-
    loan_issued_at(origin, loan),
    loan_live_at(use_point, loan),
    loan_invalidated_at(loan, use_point).
```

### 4.3 与 NLL 的关系

```text
NLL vs Polonius:

NLL:
- 命令式算法
- 显式数据流分析
- 已稳定 (Rust 2018+)

Polonius:
- 声明式 (Datalog)
- 更精确的分析
- 接受更多安全程序
- 仍在开发中

Polonius 可以处理 "问题案例 #3" 等复杂情况
```

## 5. 可判定性证明

### 5.1 NLL 的可判定性

```text
定理: NLL 借用检查是可判定的。

证明概要:

1. 有限性:
   - 程序点数量: 有限 (CFG节点)
   - 借用数量: 有限 (程序中的借用表达式)
   - 区域变量: 有限

2. 约束求解终止:
   - 区域是有限点集的子集
   - 约束求解是单调的 (集合只增不减)
   - 达到不动点时终止

3. 借用检查终止:
   - 检查每点的活跃借用
   - 点数量有限
   - 借用数量有限

复杂度: O(n³) 最坏情况
- n 个程序点
- 每个区域最多 n 个点
- 约束求解可能需要 O(n) 次迭代
```

### 5.2 Polonius 的可判定性

```text
定理: Polonius 借用检查是可判定的。

证明:

Datalog 程序在有限域上求值总是终止的。

Stratified Datalog (分层Datalog):
- 无递归否定
- 可以分层求值
- 每层求值终止

Polonius 规则是 stratified 的:
- 事实层: 输入关系
- 推导层: loan_live_at
- 错误层: error

每层在有限域上求值，必然终止。
```

## 6. 边界情况与限制

### 6.1 不可判定边界

```rust
// 以下情况可能导致借用检查不终止或不可判定:

// 1. 常量求值中的借用检查
const fn bad() -> &'static i32 {
    // 如果常量求值涉及递归...
    loop {}  // 编译时无限循环
}

// 2. 复杂泛型约束
trait Foo<T> {
    type Output;
}
impl<T> Foo<T> for () where (): Foo<T>, (): Foo<<() as Foo<T>>::Output> {
    type Output = ();
}
// 无限递归的 trait 约束求解

// 编译器处理:
// - 设置递归深度限制
// - 超时机制
```

### 6.2 实践中的保证

```text
Rust编译器的实际保证:

1. 终止性保证:
   - 借用检查本身总是终止
   - 但总编译时间可能因其他阶段而不终止

2. 健全性保证:
   - 如果编译通过，程序内存安全
   - 不保证接受所有安全程序 (保守性)

3. 保守性:
   - 可能拒绝某些安全程序
   - 需要代码重构
   - 持续改进 (NLL → Polonius)
```

## 7. 算法优化

### 7.1 增量借用检查

```text
增量分析 (IDE使用):

当用户修改代码时:
1. 只重新分析受影响的函数
2. 重用之前的约束求解结果
3. 只更新变化的部分

优势:
- 快速反馈
- 更好的IDE体验
```

### 7.2 并行化

```text
并行借用检查:

函数级别并行:
- 不同函数独立检查
- 结果合并

数据并行:
- 大型函数内的基本块并行分析
- 最后合并结果
```

## 8. 与其他分析的交互

### 8.1 类型推断与借用检查

```text
相互依赖:

type_inference <-> borrow_check

类型推断提供:
- 变量类型 (包含生命周期)
- 子类型约束

借用检查提供:
- 生命周期约束
- 影响类型推断的借用关系

实际实现:
- 交替进行
- 直到不动点
```

### 8.2 MIR优化与借用检查

```text
优化对借用检查的影响:

某些优化必须在借用检查后进行:
- 内联: 可能改变借用关系
- 循环优化: 影响活度分析

某些优化必须在借用检查前:
- 常量传播: 帮助确定分支
```

---

## 参考文献

1. Rust RFC 2094: Non-Lexical Lifetimes (2017).
2. Pearee, D.J. (2021). A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust. *TOPLAS*.
3. Matsushita, Y., et al. (2021). RustHorn: CHC-based Verification for Rust Programs. *TOPLAS*.
4. Abiteboul, S., Hull, R., & Vianu, V. (1995). *Foundations of Databases*. Addison-Wesley.
