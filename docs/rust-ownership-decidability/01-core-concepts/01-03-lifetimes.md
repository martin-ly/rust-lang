# Rust生命周期：理论与实践

> **权威来源**: Rust RFC 2094 (NLL), Rust Reference
> **形式化参考**: RustBelt Lifetime Logic, Oxide

## 目录

- [Rust生命周期：理论与实践](#rust生命周期理论与实践)
  - [目录](#目录)
  - [1. 生命周期的本质](#1-生命周期的本质)
    - [1.1 什么是生命周期？](#11-什么是生命周期)
    - [1.2 生命周期的形式化定义](#12-生命周期的形式化定义)
  - [2. 生命周期标注](#2-生命周期标注)
    - [2.1 显式生命周期](#21-显式生命周期)
    - [2.2 生命周期省略规则 (Elision)](#22-生命周期省略规则-elision)
    - [2.3 'static 生命周期](#23-static-生命周期)
  - [3. 生命周期推断](#3-生命周期推断)
    - [3.1 基于约束的推断](#31-基于约束的推断)
    - [3.2 约束示例](#32-约束示例)
  - [4. 生命周期与数据结构](#4-生命周期与数据结构)
    - [4.1 结构体中的生命周期](#41-结构体中的生命周期)
    - [4.2 生命周期省略在结构体中的限制](#42-生命周期省略在结构体中的限制)
  - [5. 高级生命周期模式](#5-高级生命周期模式)
    - [5.1 高阶 trait bound (HRTB)](#51-高阶-trait-bound-hrtb)
    - [5.2 生命周期子类型](#52-生命周期子类型)
  - [6. NLL (Non-Lexical Lifetimes)](#6-nll-non-lexical-lifetimes)
    - [6.1 从词法到非词法](#61-从词法到非词法)
    - [6.2 NLL 的形式化](#62-nll-的形式化)
  - [7. 生命周期与编译器实现](#7-生命周期与编译器实现)
    - [7.1 MIR 中的生命周期](#71-mir-中的生命周期)
    - [7.2 Polonius: 基于 Datalog 的借用检查](#72-polonius-基于-datalog-的借用检查)
  - [8. 生命周期常见错误与解决](#8-生命周期常见错误与解决)
    - [8.1 悬垂引用](#81-悬垂引用)
    - [8.2 生命周期不够长](#82-生命周期不够长)
  - [9. 生命周期与形式化验证](#9-生命周期与形式化验证)
    - [9.1 在验证工具中的编码](#91-在验证工具中的编码)
    - [9.2 RustBelt 的生命周期逻辑](#92-rustbelt-的生命周期逻辑)
  - [参考文献](#参考文献)

## 1. 生命周期的本质

### 1.1 什么是生命周期？

生命周期（Lifetime）是Rust借用检查器的核心概念，它跟踪引用的有效范围。

```rust
// 直观理解：生命周期是引用有效的代码区域
fn main() {
    let x = 5;              // 'a 开始 ─┐
    let r = &x;             // 'b 开始  │ 'a 包含 'b
                            //          │
    println!("{}", r);      //          │
                            // 'b 结束 ─┤
}                           // 'a 结束 ─┘
```

### 1.2 生命周期的形式化定义

```text
基于区域的解释 (Tofte & Talpin, 1994):

生命周期 'a 是控制流图(CFG)中的点集:
'a ⊆ Points(CFG)

性质:
1. 如果点 p ∈ 'a，则从入口到p的路径上的所有点也应在'a中
2. 生命周期形成一个格结构 (偏序 ⊆)

生命周期约束:
'a : 'b  (读作 "'a 包含 'b")
含义: 'b ⊆ 'a
      'a 至少和'b一样长
```

## 2. 生命周期标注

### 2.1 显式生命周期

```rust
// 函数签名中的生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 含义:
// - 'a 是一个生命周期参数
// - x, y, 和返回值都必须在 'a 期间有效
// - 'a 至少与x和y的生命周期一样长
```

### 2.2 生命周期省略规则 (Elision)

```rust
// 规则1: 单个输入引用
fn first_word(s: &str) -> &str  // 隐式: fn first_word<'a>(s: &'a str) -> &'a str

// 规则2: 多个输入引用 (方法)
impl<'a> MyStruct<'a> {
    fn get_ref(&self) -> &str    // 返回self的生命周期
}

// 规则3: 多个输入引用 (函数) - 必须显式标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str

// 规则4: 'static 生命周期
fn get_static() -> &'static str  // 整个程序期间有效
```

### 2.3 'static 生命周期

```rust
// 'static 是 Rust 中最长的生命周期
// 表示数据在程序的整个执行期间都有效

// 字符串字面量是 'static
let s: &'static str = "I live forever!";

// 常量也是 'static
static CONFIG: &str = "config";

// 拥有 'static 约束的类型
fn require_static<T: 'static>(t: T) {}

// 常见 'static 约束的使用场景
thread::spawn(|| { ... })  // 闭包必须 'static
Box::leak(Box::new(5))     // 泄漏的内存是 'static
```

## 3. 生命周期推断

### 3.1 基于约束的推断

```text
生命周期推断算法:

输入: 带有生命周期变量的程序
输出: 满足所有约束的最小生命周期

步骤:

1. 生命周期变量创建
   为每个引用创建生命周期变量: 'a, 'b, 'c, ...

2. 约束收集
   从代码结构生成约束:
   - let r = &x;  =>  'r : 'x  (r的生命周期包含于x)
   - 函数调用: 参数生命周期 <: 形参生命周期
   - 返回值: 返回值生命周期 <: 实际返回的生命周期

3. 约束求解
   寻找最小满足所有约束的赋值
   使用不动点迭代算法

4. 验证
   确保求解结果满足借用规则
```

### 3.2 约束示例

```rust
fn example<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32 {
    x
}

// 调用:
let result = {
    let a = 1;           // 'a
    let b = 2;           // 'b
    example(&a, &b)      // 约束: 'a : 'x, 'b : 'y
};                       // 返回值 'a 在 b 被drop后仍有效

// 编译器验证:
// - 'a 必须包含 'b (否则返回值可能指向已释放内存)
// - 此例中满足，编译通过
```

## 4. 生命周期与数据结构

### 4.1 结构体中的生命周期

```rust
// 包含引用的结构体必须标注生命周期
struct Book<'a> {
    title: &'a str,
    author: &'a str,
}

// 含义: Book 实例不能比它的 title 和 author 引用活得长

impl<'a> Book<'a> {
    // 方法可以使用结构体的生命周期
    fn get_title(&self) -> &'a str {
        self.title
    }

    // 也可以引入新的生命周期
    fn compare_with<'b>(&self, other: &'b Book) -> bool
    where
        'a: 'b,  // self 必须比 other 活得长
    {
        self.title == other.title
    }
}
```

### 4.2 生命周期省略在结构体中的限制

```rust
// 错误：结构体不能省略生命周期
struct Wrapper {  // 编译错误!
    data: &str,
}

// 正确：必须显式标注
struct Wrapper<'a> {
    data: &'a str,
}
```

## 5. 高级生命周期模式

### 5.1 高阶 trait bound (HRTB)

```rust
// 对于所有生命周期 'a
fn call_with_ref<F>(f: F)
where
    F: for<'a> Fn(&'a i32) -> &'a i32,
{
    let x = 1;
    f(&x);
}

// HRTB 形式化:
// ∀'a. F: Fn(&'a i32) -> &'a i32
// 表示闭包 F 对任意生命周期 'a 都满足该约束
```

### 5.2 生命周期子类型

```rust
// 'static 是 'static : 'a 对所有 'a 成立
fn as_str<'a>(s: &'a str) -> &'a str { s }

fn takes_static(s: &'static str) {}

fn main() {
    let s: &'static str = "literal";
    as_str(s);  // OK: 'static <: 'a
}
```

## 6. NLL (Non-Lexical Lifetimes)

### 6.1 从词法到非词法

```rust
// 词法生命周期 (Rust 1.0-2015)
fn lexical() {
    let mut data = vec![1, 2, 3];
    let slice = &data[0];

    // slice 不使用，但在词法作用域中仍"活着"
    // data.push(4);  // 错误! slice 仍然存在

    println!("{}", slice);
}

// 非词法生命周期 (Rust 2018+)
fn non_lexical() {
    let mut data = vec![1, 2, 3];
    let slice = &data[0];

    println!("{}", slice);  // slice 最后使用

    // slice 在这里结束！
    data.push(4);  // OK!
}
```

### 6.2 NLL 的形式化

```text
NLL 的核心变化:

传统 (词法):
lifetime(x) = scope(x)  // 生命周期等于作用域

NLL (非词法):
lifetime(x) = { p | x 在点 p 是 live }  // 生命周期等于活跃点集

活跃性 (Liveness):
变量 x 在点 p 是 live 的，如果:
1. x 在 p 被使用，或
2. 存在从 p 到 x 的使用的路径，且 x 在该路径上未被重新定义

这对应于数据流分析中的"到达定义"。
```

## 7. 生命周期与编译器实现

### 7.1 MIR 中的生命周期

```text
MIR (Mid-level IR) 中的生命周期表示:

基本块结构:
bb0: {
    _1 = Vec::new();        // _1: Vec<i32>
    _2 = &_1;               // _2: &Vec<i32>, '2 开始
    _3 = (*_2).len();       // 使用 _2
    drop(_2);               // '2 结束
    _4 = Vec::push(move _1, const 1);  // OK, _2 已死
}

生命周期区域:
'a = {bb0[1], bb0[2], bb0[3]}  // 从创建到drop的点集
```

### 7.2 Polonius: 基于 Datalog 的借用检查

```prolog
% Polonius 使用 Datalog 规则

% 基本关系
loan_issued_at(Origin, Loan, Point).
loan_killed_at(Loan, Point).
loan_invalidated_at(Loan, Point).
cfg_edge(Point1, Point2).

% 推导规则
loan_live_at(P, L) :- loan_issued_at(O, L, P).
loan_live_at(P2, L) :- loan_live_at(P1, L), cfg_edge(P1, P2),
                       not loan_killed_at(L, P1).

% 错误检测
error(P, L) :- loan_live_at(P, L), loan_invalidated_at(L, P).
```

## 8. 生命周期常见错误与解决

### 8.1 悬垂引用

```rust
// 错误示例
fn dangling() -> &i32 {
    let x = 5;
    &x  // x 在函数结束时被释放
}

// 错误: missing lifetime specifier
// 解决: 返回拥有所有权的值
fn not_dangling() -> i32 {
    let x = 5;
    x  // 转移所有权
}

// 或使用 'static
fn get_static_str() -> &'static str {
    "always valid"
}
```

### 8.2 生命周期不够长

```rust
// 错误示例
fn main() {
    let r;
    {
        let x = 5;
        r = &x;  // x 在这里被释放
    }
    println!("{}", r);  // 错误: r 引用已释放内存
}

// 解决
fn main() {
    let x = 5;
    let r = &x;
    println!("{}", r);  // OK
}
```

## 9. 生命周期与形式化验证

### 9.1 在验证工具中的编码

```text
Creusot/Why3 中的生命周期:

使用预言变量 (Prophecy Variables) 编码:

fn swap<'a>(x: &'a mut i32, y: &'a mut i32)
    ensures *x == old(*y) && *y == old(*x)

编码:
- 'a 作为逻辑变量
- 借用对应预言观察
- 确保在 'a 结束前操作合法
```

### 9.2 RustBelt 的生命周期逻辑

```text
RustBelt 的生命周期逻辑:

借用命题: &^α P
- α: 生命周期
- P: 借用的资源

规则:
1. 创建: 从所有权创建借用
   own(x) ⇒ &^α own(x) * frozen(x, α)

2. 使用: 在借用期间可以访问
   &^α P * α alive ⇒ 临时访问 P

3. 结束: 当 α 结束，所有权返回
   &^α P * α ended ⇒ P
```

---

## 参考文献

1. Tofte, M., & Talpin, J.-P. (1994). Implementation of the Typed Call-by-Value λ-Calculus using a Stack of Regions. *POPL*.
2. Rust RFC 2094: Non-Lexical Lifetimes.
3. Vytiniotis, D., Peyton Jones, S., & Schrijvers, T. (2010). Let should not be generalized. *TLDI*.
