# 程序设计语义框架

## 目录

- [程序设计语义框架](#程序设计语义框架)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 什么是程序设计语义](#11-什么是程序设计语义)
    - [1.2 为什么需要语义分析框架](#12-为什么需要语义分析框架)
    - [1.3 Rust 语义特性的独特性](#13-rust-语义特性的独特性)
  - [2. 语义分析维度](#2-语义分析维度)
    - [2.1 静态语义 vs 动态语义](#21-静态语义-vs-动态语义)
      - [2.1.1 编译时保证 vs 运行时行为](#211-编译时保证-vs-运行时行为)
      - [2.1.2 类型系统语义](#212-类型系统语义)
      - [2.1.3 所有权系统语义](#213-所有权系统语义)
    - [2.2 控制流语义](#22-控制流语义)
      - [2.2.1 顺序执行语义](#221-顺序执行语义)
      - [2.2.2 条件执行语义](#222-条件执行语义)
      - [2.2.3 循环执行语义](#223-循环执行语义)
      - [2.2.4 跳转语义](#224-跳转语义)
    - [2.3 数据流语义](#23-数据流语义)
      - [2.3.1 值传递语义](#231-值传递语义)
      - [2.3.2 生命周期数据流](#232-生命周期数据流)
      - [2.3.3 共享 vs 独占数据流](#233-共享-vs-独占数据流)
    - [2.4 执行模型语义](#24-执行模型语义)
      - [2.4.1 同步执行模型](#241-同步执行模型)
      - [2.4.2 异步执行模型](#242-异步执行模型)
      - [2.4.3 并发执行模型](#243-并发执行模型)
      - [2.4.4 并行执行模型](#244-并行执行模型)
  - [3. 设计模式语义分类](#3-设计模式语义分类)
    - [3.1 创建型模式语义](#31-创建型模式语义)
      - [3.1.1 所有权转移语义](#311-所有权转移语义)
      - [3.1.2 借用检查语义](#312-借用检查语义)
      - [3.1.3 智能指针语义](#313-智能指针语义)
    - [3.2 结构型模式语义](#32-结构型模式语义)
      - [3.2.1 组合模式语义](#321-组合模式语义)
      - [3.2.2 适配器模式语义](#322-适配器模式语义)
      - [3.2.3 类型状态模式语义](#323-类型状态模式语义)
    - [3.3 行为型模式语义](#33-行为型模式语义)
      - [3.3.1 迭代器模式语义](#331-迭代器模式语义)
      - [3.3.2 观察者模式语义](#332-观察者模式语义)
      - [3.3.3 访问者模式语义](#333-访问者模式语义)
  - [4. 并发语义模型](#4-并发语义模型)
    - [4.1 线程模型语义](#41-线程模型语义)
      - [4.1.1 OS 线程语义](#411-os-线程语义)
      - [4.1.2 绿色线程/协程语义](#412-绿色线程协程语义)
      - [4.1.3 线程间通信语义](#413-线程间通信语义)
    - [4.2 同步原语语义](#42-同步原语语义)
      - [4.2.1 互斥锁语义](#421-互斥锁语义)
      - [4.2.2 读写锁语义](#422-读写锁语义)
      - [4.2.3 条件变量语义](#423-条件变量语义)
      - [4.2.4 屏障语义](#424-屏障语义)
    - [4.3 无锁语义](#43-无锁语义)
      - [4.3.1 原子操作语义（内存序）](#431-原子操作语义内存序)
      - [4.3.2 CAS 循环语义](#432-cas-循环语义)
      - [4.3.3 内存模型语义](#433-内存模型语义)
  - [5. 异步语义模型](#5-异步语义模型)
    - [5.1 Future 语义](#51-future-语义)
      - [5.1.1 Future 状态机语义](#511-future-状态机语义)
      - [5.1.2 Poll 模型语义](#512-poll-模型语义)
      - [5.1.3 Waker 机制语义](#513-waker-机制语义)
    - [5.2 async/await 语义](#52-asyncawait-语义)
      - [5.2.1 状态机转换语义](#521-状态机转换语义)
      - [5.2.2 Pin 语义（自引用）](#522-pin-语义自引用)
      - [5.2.3 取消安全语义](#523-取消安全语义)
    - [5.3 执行器语义](#53-执行器语义)
      - [5.3.1 任务调度语义](#531-任务调度语义)
      - [5.3.2 工作窃取语义](#532-工作窃取语义)
      - [5.3.3 协作式调度语义](#533-协作式调度语义)
  - [6. Actor 模型语义](#6-actor-模型语义)
    - [6.1 Actor 基本语义](#61-actor-基本语义)
      - [6.1.1 消息传递语义](#611-消息传递语义)
      - [6.1.2 Actor 生命周期语义](#612-actor-生命周期语义)
      - [6.1.3 监督树语义](#613-监督树语义)
    - [6.2 分布式 Actor 语义](#62-分布式-actor-语义)
      - [6.2.1 位置透明语义](#621-位置透明语义)
      - [6.2.2 故障隔离语义](#622-故障隔离语义)
      - [6.2.3 一致性与可用性语义](#623-一致性与可用性语义)
  - [7. 运行时行为语义](#7-运行时行为语义)
    - [7.1 内存模型语义](#71-内存模型语义)
      - [7.1.1 栈分配语义](#711-栈分配语义)
      - [7.1.2 堆分配语义](#712-堆分配语义)
      - [7.1.3 内存回收语义（RAII/Drop）](#713-内存回收语义raiidrop)
    - [7.2 调度语义](#72-调度语义)
      - [7.2.1 任务调度语义](#721-任务调度语义)
      - [7.2.2 抢占式调度语义](#722-抢占式调度语义)
      - [7.2.3 协作式调度语义](#723-协作式调度语义)
    - [7.3 I/O 语义](#73-io-语义)
      - [7.3.1 阻塞 I/O 语义](#731-阻塞-io-语义)
      - [7.3.2 非阻塞 I/O 语义](#732-非阻塞-io-语义)
      - [7.3.3 异步 I/O 语义](#733-异步-io-语义)
  - [8. 形式化语义表示](#8-形式化语义表示)
    - [8.1 操作语义](#81-操作语义)
      - [8.1.1 大步语义规则](#811-大步语义规则)
      - [8.1.2 小步语义规则](#812-小步语义规则)
      - [8.1.3 求值上下文](#813-求值上下文)
    - [8.2 类型与效果系统](#82-类型与效果系统)
      - [8.2.1 类型判断语义](#821-类型判断语义)
      - [8.2.2 效果追踪语义](#822-效果追踪语义)
      - [8.2.3 能力系统语义](#823-能力系统语义)
  - [9. 语义分析工具](#9-语义分析工具)
    - [9.1 静态分析语义](#91-静态分析语义)
      - [9.1.1 借用检查器语义](#911-借用检查器语义)
      - [9.1.2 模式匹配穷尽性语义](#912-模式匹配穷尽性语义)
      - [9.1.3 常量求值语义](#913-常量求值语义)
    - [9.2 动态分析语义](#92-动态分析语义)
      - [9.2.1 Miri 语义解释器](#921-miri-语义解释器)
      - [9.2.2 数据竞争检测语义](#922-数据竞争检测语义)
      - [9.2.3 内存泄漏检测语义](#923-内存泄漏检测语义)
  - [10. 总结与展望](#10-总结与展望)
    - [10.1 语义框架回顾](#101-语义框架回顾)
    - [10.2 统一语义形式](#102-统一语义形式)
    - [10.3 未来发展方向](#103-未来发展方向)
    - [10.4 文档组织](#104-文档组织)
  - [附录：符号说明](#附录符号说明)
  - [参考文献](#参考文献)

---

## 1. 引言

### 1.1 什么是程序设计语义

**程序设计语义（Programming Language Semantics）** 是研究程序设计语言含义和行为的数学理论。
它为程序的执行提供严格的数学解释，使得我们能够形式化地分析和验证程序的正确性。

形式化地说，语义定义了从语法到语义的映射函数：

$$
\llbracket \cdot \rrbracket : \text{Syntax} \to \text{Meaning}
$$

其中，语法（Syntax）指程序的文本表示，语义（Meaning）指程序执行时的数学对象（如状态转换、计算过程等）。

程序设计语义通常分为三个主要流派：

| 语义流派 | 核心思想 | 适用场景 | 数学基础 |
|---------|---------|---------|---------|
| **操作语义** | 定义程序执行的步骤 | 实现验证、调试 | 抽象机、转移系统 |
| **指称语义** | 将程序映射到数学函数 | 程序等价性证明 | 域论、λ演算 |
| **公理语义** | 使用逻辑断言描述行为 | 程序验证 | 霍尔逻辑、分离逻辑 |

### 1.2 为什么需要语义分析框架

Rust 作为一门系统级编程语言，其独特的所有权、借用和生命周期系统使得传统的语义分析方法面临挑战：

1. **内存安全保证**：Rust 在编译时保证内存安全，这需要形式化的语义来描述这些保证
2. **零成本抽象**：高级抽象必须映射到底层语义而不引入运行时开销
3. **并发安全**：数据竞争自由需要精确的并发语义模型
4. **异步编程**：`async/await` 引入了复杂的控制流转换

建立一个统一的语义分析框架，能够：

$$
\text{Framework} : \text{Rust Constructs} \times \text{Properties} \to \{ \text{Valid}, \text{Invalid}, \text{Unknown} \}
$$

### 1.3 Rust 语义特性的独特性

Rust 的语义特性可以从以下维度进行分类：

```rust
// 所有权转移语义
let s1 = String::from("hello");
let s2 = s1;           // s1 的所有权移动到 s2
// println!("{}", s1);  // 编译错误：s1 已失效

// 借用语义
let r1 = &s2;          // 不可变借用
let r2 = &s2;          // 多个不可变借用允许
// let r3 = &mut s2;    // 编译错误：不能与不可变借用共存

// 生命周期语义
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

Rust 语义的核心独特性是**资源管理即类型系统**：

$$
\text{Type}(\tau) \implies \text{Ownership}(\tau) \times \text{Lifetime}(\tau) \times \text{Mutability}(\tau)
$$

---

## 2. 语义分析维度

### 2.1 静态语义 vs 动态语义

#### 2.1.1 编译时保证 vs 运行时行为

静态语义在编译时检查程序属性，动态语义描述程序运行时的行为。

**形式化定义：**

静态语义可表示为类型判断：

$$
\Gamma \vdash e : \tau \quad \text{(在环境 } \Gamma \text{ 下，表达式 } e \text{ 具有类型 } \tau \text{)}
$$

动态语义可表示为状态转换：

$$
\langle e, \sigma \rangle \to \langle e', \sigma' \rangle \quad \text{(表达式 } e \text{ 在状态 } \sigma \text{ 下转换到 } e' \text{ 和 } \sigma' \text{)}
$$

**Rust 示例：**

```rust
// 静态语义检查
fn static_semantics() {
    let x: i32 = 42;
    // let y: String = x;  // 编译错误：类型不匹配

    let s = String::from("hello");
    let r = &s;
    // drop(s);  // 编译错误：s 被借用，不能移动
}

// 动态语义行为
fn dynamic_semantics() {
    let v = vec![1, 2, 3];
    let first = v[0];  // 运行时数组索引
    panic!("runtime error");  // 运行时 panic
}
```

#### 2.1.2 类型系统语义

Rust 的类型系统语义包含以下层次：

$$
\begin{aligned}
\text{Base Types} &\ni \texttt{i32}, \texttt{bool}, \texttt{char}, \texttt{()} \\
\text{Reference Types} &\ni \&T, \&\text{mut } T \\
\text{Compound Types} &\ni (T_1, T_2), [T; n], \text{struct } S, \text{enum } E \\
\text{Function Types} &\ni T_1 \to T_2 \\
\text{Lifetime Types} &\ni \&'\!a\, T \\
\text{Trait Types} &\ni \text{dyn } Trait, \text{impl } Trait
\end{aligned}
$$

**类型规则示例（借用规则）：**

$$
\frac{\Gamma \vdash x : T \quad \text{mutable}(x)}{\Gamma \vdash \&\text{mut } x : \&\text{mut } T} \text{ (MUT-BORROW)}
$$

$$
\frac{\Gamma \vdash x : T}{\Gamma \vdash \&x : \&T} \text{ (IMM-BORROW)}
$$

$$
\frac{\Gamma \vdash r : \&T \cup \&\text{mut } T}{\Gamma \vdash *r : T} \text{ (DEREF)}
$$

#### 2.1.3 所有权系统语义

所有权系统的核心规则可以用分离逻辑（Separation Logic）表示：

$$
\text{Own}(x, T) * \text{Own}(y, T) \implies x \neq y \quad \text{(唯一性)}
$$

$$
\text{Own}(x, T) \vdash \exists v. x \mapsto v * T(v) \quad \text{(资源包含)}
$$

```rust
// 所有权语义示例
fn ownership_semantics() {
    // 所有权获取
    let s = String::from("data");  // Own(s, String)

    // 所有权转移
    let t = s;                      // Own(s, String) --move--> Own(t, String)
    // s 不再有效

    // 借用（非所有权）
    let r = &t;                     // Borrow(r, &String) while Own(t, String)

    // 可变借用
    let m = &mut t;                 // MutBorrow(m, &mut String)
    // 此时不能有任何其他借用
}
```

### 2.2 控制流语义

#### 2.2.1 顺序执行语义

顺序执行是最基本的控制流，形式化为：

$$
\frac{\langle e_1, \sigma \rangle \to^* \langle v_1, \sigma_1 \rangle \quad \langle e_2, \sigma_1 \rangle \to^* \langle v_2, \sigma_2 \rangle}{\langle e_1; e_2, \sigma \rangle \to^* \langle v_2, \sigma_2 \rangle}
$$

```rust
fn sequential_semantics() {
    let x = 1;          // σ₀ → σ₁, x ↦ 1
    let y = x + 1;      // σ₁ → σ₂, y ↦ 2
    let z = y * 2;      // σ₂ → σ₃, z ↦ 4
    // 最终状态: σ₃ = {x ↦ 1, y ↦ 2, z ↦ 4}
}
```

#### 2.2.2 条件执行语义

条件执行的形式化语义：

$$
\frac{\langle b, \sigma \rangle \to^* \langle \text{true}, \sigma' \rangle \quad \langle e_1, \sigma' \rangle \to^* \langle v, \sigma'' \rangle}{\langle \text{if } b \{ e_1 \} \text{ else } \{ e_2 \}, \sigma \rangle \to^* \langle v, \sigma'' \rangle}
$$

$$
\frac{\langle b, \sigma \rangle \to^* \langle \text{false}, \sigma' \rangle \quad \langle e_2, \sigma' \rangle \to^* \langle v, \sigma'' \rangle}{\langle \text{if } b \{ e_1 \} \text{ else } \{ e_2 \}, \sigma \rangle \to^* \langle v, \sigma'' \rangle}
$$

```rust
fn conditional_semantics(x: i32) -> i32 {
    let result = if x > 0 {
        x * 2
    } else if x < 0 {
        -x
    } else {
        0
    };
    result
}
```

#### 2.2.3 循环执行语义

循环语义可以使用不动点或递归规则定义：

$$
\text{while } b \{ e \} \equiv \mu W. \text{if } b \{ e; W \} \text{ else } \{ () \}
$$

```rust
fn loop_semantics() {
    // while 循环
    let mut i = 0;
    while i < 10 {
        i += 1;
    }

    // for 循环（迭代器语义）
    for j in 0..10 {
        println!("{}", j);
    }

    // loop 循环（无限循环）
    let result = loop {
        if i > 20 {
            break i * 2;  // 带值 break
        }
        i += 1;
    };
}
```

#### 2.2.4 跳转语义

Rust 支持以下跳转结构：

| 跳转类型 | 语义 | 形式化表示 |
|---------|------|-----------|
| `break` | 退出最内层循环 | $\langle \text{break}, \sigma \rangle \to \top$ |
| `break 'label` | 退出标记循环 | $\langle \text{break } \ell, \sigma \rangle \to \langle \ell : \top, \sigma \rangle$ |
| `continue` | 继续下一次迭代 | $\langle \text{continue}, \sigma \rangle \to \text{next}$ |
| `return` | 从函数返回 | $\langle \text{return } v, \sigma \rangle \to \langle v, \sigma \rangle_{\text{ret}}$ |

```rust
fn jump_semantics() -> i32 {
    'outer: for i in 0..10 {
        for j in 0..10 {
            if i * j > 50 {
                break 'outer;  // 跳出外层循环
            }
            if j % 2 == 0 {
                continue;  // 跳过偶数 j
            }
        }
    }

    let result = loop {
        let x = compute();
        if x.is_ready() {
            break x.value();  // 带值返回
        }
    };

    return result;  // 函数返回
}

fn compute() -> Ready { Ready { value: 42 } }
struct Ready { value: i32 }
impl Ready {
    fn is_ready(&self) -> bool { true }
    fn value(self) -> i32 { self.value }
}
```

### 2.3 数据流语义

#### 2.3.1 值传递语义

Rust 的值传递有三种形式，每种都有精确的语义：

**Copy 语义：**

$$
\frac{x : T \quad \text{Copy}(T)}{\langle y = x, \sigma \rangle \to \langle (), \sigma[y \mapsto \sigma(x)] \rangle}
$$

```rust
#[derive(Copy, Clone)]
struct Point { x: i32, y: i32 }

fn copy_semantics() {
    let p1 = Point { x: 1, y: 2 };
    let p2 = p1;  // 按位复制，p1 仍然有效
    println!("{:?} {:?}", p1.x, p2.x);  // 两者都可用
}
```

**Move 语义：**

$$
\frac{x : T \quad \neg \text{Copy}(T)}{\langle y = x, \sigma \rangle \to \langle (), \sigma[y \mapsto \sigma(x)][x \mapsto \bot] \rangle}
$$

```rust
fn move_semantics() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权转移，s1 失效
    // println!("{}", s1);  // 编译错误！
    println!("{}", s2);
}
```

**Borrow 语义：**

$$
\frac{x : T}{\langle r = \&x, \sigma \rangle \to \langle (), \sigma[r \mapsto \text{ref}(x)] \rangle}
$$

```rust
fn borrow_semantics() {
    let s = String::from("hello");

    // 不可变借用
    let r1 = &s;
    let r2 = &s;  // 允许多个不可变借用
    println!("{} {}", r1, r2);

    // 可变借用
    let r3 = &mut s;  // 此时不能有任何其他借用
    r3.push_str(" world");
}
```

#### 2.3.2 生命周期数据流

生命周期描述了引用的有效范围：

$$
\text{Lifetime} : \text{Variable} \to \mathcal{P}(\text{ProgramPoint})
$$

生命周期约束：

$$
\forall r : \&'\!a\, T. \text{live}(r) \subseteq 'a
$$

```rust
fn lifetime_dataflow<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32
where
    'a: 'b,  // 'a 包含 'b
{
    x  // 返回的生命周期必须不超过输入
}

fn lifetime_example() {
    let r;
    {
        let x = 5;
        r = &x;  // 错误：x 的生命周期不够长
    }  // x 在此处失效
    // println!("{}", r);  // r 指向已释放内存
}
```

#### 2.3.3 共享 vs 独占数据流

Rust 的借用检查器强制执行以下规则：

$$
\begin{aligned}
&\text{共享-独占规则：} \\
&\forall t. \neg(\text{active}(\&\text{mut } x, t) \land \text{active}(\&x, t)) \\
&\text{多个共享允许：} \\
&\forall t. \text{count}(\&x, t) \geq 0 \implies \text{valid}
\end{aligned}
$$

```rust
fn sharing_vs_exclusive() {
    let mut data = vec![1, 2, 3];

    // 共享借用（读取）
    let r1 = &data;
    let r2 = &data;
    println!("{:?} {:?}", r1, r2);  // OK

    // 独占借用（写入）
    let r3 = &mut data;
    r3.push(4);

    // 不能混合
    // let r4 = &data;  // 错误：与 r3 冲突
}
```

### 2.4 执行模型语义

#### 2.4.1 同步执行模型

同步执行模型是最简单的执行模型：

$$
\text{SyncExec} : \text{Program} \to \text{State} \to \text{State}
$$

```rust
fn synchronous_model() {
    // 代码从上到下顺序执行
    let a = compute_a();
    let b = compute_b();  // 等待 a 完成
    let c = compute_c();  // 等待 b 完成

    // 最终结果
    let result = a + b + c;
}

fn compute_a() -> i32 { 1 }
fn compute_b() -> i32 { 2 }
fn compute_c() -> i32 { 3 }
```

#### 2.4.2 异步执行模型

异步执行模型引入了 Future 和任务调度：

$$
\text{AsyncExec} : \text{Future} \to \text{Task} \to \text{State} \to \text{Poll}\langle T \rangle
$$

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future 状态机语义
async fn async_model() -> i32 {
    // .await 是挂起点
    let a = async_compute_a().await;
    let b = async_compute_b().await;
    a + b
}

async fn async_compute_a() -> i32 { 1 }
async fn async_compute_b() -> i32 { 2 }

// Future trait 语义
struct MyFuture {
    state: State,
}

enum State {
    Start,
    Waiting,
    Done,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.state {
            State::Done => Poll::Ready(42),
            _ => {
                // 注册 waker 并返回 Pending
                cx.waker().wake_by_ref();
                Poll::Pending
            }
        }
    }
}
```

#### 2.4.3 并发执行模型

并发模型涉及多个执行流的交错：

$$
\text{ConcurrentExec} : \text{Thread}_1 \times \cdots \times \text{Thread}_n \to \text{Interleaving} \to \text{Result}
$$

```rust
use std::thread;
use std::sync::mpsc;

fn concurrent_model() {
    // 线程创建语义
    let (tx, rx) = mpsc::channel();

    let handle = thread::spawn(move || {
        // 新线程执行
        tx.send(42).unwrap();
        "thread result"
    });

    // 主线程继续执行
    let value = rx.recv().unwrap();
    println!("Received: {}", value);

    // 等待线程完成
    let result = handle.join().unwrap();
}
```

#### 2.4.4 并行执行模型

并行执行模型利用数据并行性：

```rust
// 使用 Rayon 进行数据并行
use rayon::prelude::*;

fn parallel_model() {
    let data: Vec<i32> = (0..10000).collect();

    // 并行 map
    let sum: i32 = data.par_iter()
        .map(|x| x * x)
        .sum();

    // 并行 reduce
    let max = data.par_iter()
        .reduce(|| &0, |a, b| if a > b { a } else { b });
}

// SIMD 并行
use std::simd::*;

fn simd_semantics() {
    let a = f32x4::from_array([1.0, 2.0, 3.0, 4.0]);
    let b = f32x4::from_array([5.0, 6.0, 7.0, 8.0]);
    let c = a + b;  // 向量加法，单指令多数据
}
```

---

## 3. 设计模式语义分类

### 3.1 创建型模式语义

#### 3.1.1 所有权转移语义

所有权转移是 Rust 中资源管理的基础：

$$
\text{Move} : T \to T' \quad \text{where } \text{Own}(T) \land \neg \text{Own}(T')
$$

```rust
// 工厂模式 + 所有权转移
struct ResourceFactory;

impl ResourceFactory {
    fn create() -> Resource {
        Resource { data: vec![1, 2, 3] }
    }
}

struct Resource {
    data: Vec<i32>,
}

impl Resource {
    // 消耗自身的方法
    fn transform(self) -> TransformedResource {
        TransformedResource {
            sum: self.data.iter().sum()
        }
    }
}

struct TransformedResource {
    sum: i32,
}

fn ownership_transfer_pattern() {
    let resource = ResourceFactory::create();  // 获取所有权
    let transformed = resource.transform();    // 所有权转移
    // resource 不再可用
    println!("Sum: {}", transformed.sum);
}
```

#### 3.1.2 借用检查语义

借用检查是编译时验证的核心：

$$
\frac{\Gamma \vdash x : T \quad \text{region}(r) \subseteq \text{lifetime}(x)}{\Gamma \vdash \&r\, x : \&r\, T}
$$

```rust
// 构建器模式 + 借用检查
struct Builder<'a> {
    name: &'a str,
    value: i32,
}

impl<'a> Builder<'a> {
    fn new() -> Self {
        Builder { name: "", value: 0 }
    }

    fn name(&mut self, name: &'a str) -> &mut Self {
        self.name = name;
        self
    }

    fn value(&mut self, value: i32) -> &mut Self {
        self.value = value;
        self
    }

    fn build(&self) -> Product<'a> {
        Product {
            name: self.name,
            value: self.value,
        }
    }
}

struct Product<'a> {
    name: &'a str,
    value: i32,
}

fn builder_pattern() {
    let name = String::from("product");
    let product = Builder::new()
        .name(&name)
        .value(42)
        .build();
    println!("{} = {}", product.name, product.value);
}
```

#### 3.1.3 智能指针语义

智能指针扩展了所有权的表达能力：

| 智能指针 | 所有权模型 | 语义 |
|---------|-----------|------|
| `Box<T>` | 唯一所有权 | $\text{Own}(\text{Box}(x)) \iff \text{Own}(x)$ |
| `Rc<T>` | 共享所有权（单线程） | $\text{Count}(\text{Rc}(x)) = n \implies \text{Shared}_n(x)$ |
| `Arc<T>` | 共享所有权（多线程） | $\text{AtomicCount}(\text{Arc}(x)) = n$ |
| `RefCell<T>` | 运行时借用检查 | $\text{DynamicBorrow}(\text{RefCell}(x))$ |
| `Mutex<T>` | 互斥所有权 | $\text{MutualExclusion}(\text{Mutex}(x))$ |

```rust
use std::rc::Rc;
use std::sync::Arc;
use std::cell::RefCell;
use std::sync::Mutex;

fn smart_pointer_semantics() {
    // Box<T>：堆分配 + 唯一所有权
    let boxed = Box::new(vec![1, 2, 3]);

    // Rc<T>：引用计数（单线程）
    let shared1 = Rc::new(String::from("shared"));
    let shared2 = Rc::clone(&shared1);
    let shared3 = Rc::clone(&shared1);
    println!("Reference count: {}", Rc::strong_count(&shared1));  // 3

    // Arc<T>：原子引用计数（多线程）
    let arc_data = Arc::new(vec![1, 2, 3]);
    let arc_clone = Arc::clone(&arc_data);

    // RefCell<T>：运行时借用检查
    let cell = RefCell::new(vec![1, 2, 3]);
    {
        let mut borrowed = cell.borrow_mut();
        borrowed.push(4);
    }  // 借用在此处结束
    println!("{:?}", cell.borrow());

    // Mutex<T>：互斥锁
    let mutex_data = Mutex::new(0);
    {
        let mut locked = mutex_data.lock().unwrap();
        *locked += 1;
    }  // 锁在此处释放
}
```

### 3.2 结构型模式语义

#### 3.2.1 组合模式语义

组合模式允许统一处理个体和组合对象：

```rust
// 组合模式语义
trait Component {
    fn operation(&self) -> String;
    fn size(&self) -> usize;
}

// 叶子节点
struct Leaf {
    name: String,
    value: i32,
}

impl Component for Leaf {
    fn operation(&self) -> String {
        format!("{}: {}", self.name, self.value)
    }

    fn size(&self) -> usize {
        1
    }
}

// 组合节点
struct Composite {
    name: String,
    children: Vec<Box<dyn Component>>,
}

impl Component for Composite {
    fn operation(&self) -> String {
        let child_ops: Vec<String> = self.children
            .iter()
            .map(|c| c.operation())
            .collect();
        format!("{} [{}]", self.name, child_ops.join(", "))
    }

    fn size(&self) -> usize {
        1 + self.children.iter().map(|c| c.size()).sum::<usize>()
    }
}

impl Composite {
    fn new(name: &str) -> Self {
        Composite {
            name: name.to_string(),
            children: vec![],
        }
    }

    fn add(&mut self, component: Box<dyn Component>) {
        self.children.push(component);
    }
}

fn composite_pattern() {
    let mut root = Composite::new("root");
    root.add(Box::new(Leaf { name: "A".to_string(), value: 1 }));

    let mut subtree = Composite::new("subtree");
    subtree.add(Box::new(Leaf { name: "B".to_string(), value: 2 }));
    subtree.add(Box::new(Leaf { name: "C".to_string(), value: 3 }));

    root.add(Box::new(subtree));

    println!("{}", root.operation());
}
```

#### 3.2.2 适配器模式语义

适配器模式转换接口而不改变实现：

```rust
// 目标接口
trait Target {
    fn request(&self) -> String;
}

// 被适配者
struct Adaptee {
    specific_request_data: String,
}

impl Adaptee {
    fn specific_request(&self) -> String {
        format!("Specific: {}", self.specific_request_data)
    }
}

// 对象适配器
struct Adapter {
    adaptee: Adaptee,
}

impl Target for Adapter {
    fn request(&self) -> String {
        self.adaptee.specific_request()
    }
}

// 泛型适配器（更灵活）
struct GenericAdapter<T> {
    adaptee: T,
    converter: fn(&T) -> String,
}

impl<T> Target for GenericAdapter<T> {
    fn request(&self) -> String {
        (self.converter)(&self.adaptee)
    }
}

fn adapter_pattern() {
    let adaptee = Adaptee {
        specific_request_data: "data".to_string(),
    };

    let adapter = Adapter { adaptee };
    println!("{}", adapter.request());
}
```

#### 3.2.3 类型状态模式语义

类型状态模式在类型系统中编码状态机：

$$
\text{StateMachine} : S \times E \to S' \quad \text{where } S, S' \subseteq \text{Type}
$$

```rust
// 类型状态模式：确保正确的操作序列
struct Connection<State> {
    address: String,
    _state: std::marker::PhantomData<State>,
}

// 状态类型
struct Disconnected;
struct Connected;
struct Authenticated;

// 未连接状态的操作
impl Connection<Disconnected> {
    fn new(address: &str) -> Self {
        Connection {
            address: address.to_string(),
            _state: std::marker::PhantomData,
        }
    }

    fn connect(self) -> Connection<Connected> {
        println!("Connecting to {}", self.address);
        Connection {
            address: self.address,
            _state: std::marker::PhantomData,
        }
    }
}

// 已连接状态的操作
impl Connection<Connected> {
    fn authenticate(self, token: &str) -> Connection<Authenticated> {
        println!("Authenticating with {}", token);
        Connection {
            address: self.address,
            _state: std::marker::PhantomData,
        }
    }

    fn disconnect(self) -> Connection<Disconnected> {
        println!("Disconnecting");
        Connection {
            address: self.address,
            _state: std::marker::PhantomData,
        }
    }
}

// 已认证状态的操作
impl Connection<Authenticated> {
    fn query(&self, sql: &str) -> Vec<String> {
        println!("Executing: {}", sql);
        vec!["result".to_string()]
    }

    fn disconnect(self) -> Connection<Disconnected> {
        println!("Disconnecting");
        Connection {
            address: self.address,
            _state: std::marker::PhantomData,
        }
    }
}

fn typestate_pattern() {
    let conn = Connection::new("localhost:5432")
        .connect()
        .authenticate("secret_token");

    let results = conn.query("SELECT * FROM users");
    println!("{:?}", results);

    // 必须显式断开连接
    let _disconnected = conn.disconnect();

    // 编译错误：不能在未连接状态下查询
    // let conn2 = Connection::new("localhost");
    // conn2.query("SELECT *");  // 编译错误！
}
```

### 3.3 行为型模式语义

#### 3.3.1 迭代器模式语义

迭代器抽象了序列遍历：

$$
\text{Iterator} : \text{State} \to \text{Option}\langle (T, \text{State}) \rangle
$$

```rust
// 自定义迭代器语义
struct Fibonacci {
    curr: u64,
    next: u64,
}

impl Fibonacci {
    fn new() -> Self {
        Fibonacci { curr: 0, next: 1 }
    }
}

impl Iterator for Fibonacci {
    type Item = u64;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.curr;
        self.curr = self.next;
        self.next = current + self.next;
        Some(current)
    }
}

fn iterator_pattern() {
    // 基础迭代
    let fib = Fibonacci::new();
    for i in fib.take(10) {
        println!("{}", i);
    }

    // 迭代器适配器语义
    let sum: u64 = Fibonacci::new()
        .take(10)
        .filter(|x| x % 2 == 0)
        .map(|x| x * 2)
        .sum();

    println!("Sum: {}", sum);

    // 惰性求值语义
    let lazy = Fibonacci::new()
        .skip(5)
        .take(5)
        .collect::<Vec<_>>();
    println!("{:?}", lazy);
}
```

#### 3.3.2 观察者模式语义

观察者模式实现了发布-订阅机制：

```rust
use std::cell::RefCell;
use std::rc::{Rc, Weak};

// 主题接口
trait Subject {
    fn attach(&mut self, observer: Weak<dyn Observer>);
    fn detach(&mut self, observer_id: usize);
    fn notify(&self, event: &Event);
}

// 观察者接口
trait Observer {
    fn update(&self, event: &Event);
    fn id(&self) -> usize;
}

// 事件类型
#[derive(Clone, Debug)]
struct Event {
    event_type: String,
    data: String,
}

// 具体主题
struct ConcreteSubject {
    observers: Vec<Weak<dyn Observer>>,
    state: String,
}

impl ConcreteSubject {
    fn new() -> Self {
        ConcreteSubject {
            observers: vec![],
            state: String::new(),
        }
    }

    fn set_state(&mut self, state: &str) {
        self.state = state.to_string();
        self.notify(&Event {
            event_type: "state_changed".to_string(),
            data: state.to_string(),
        });
    }
}

impl Subject for ConcreteSubject {
    fn attach(&mut self, observer: Weak<dyn Observer>) {
        self.observers.push(observer);
    }

    fn detach(&mut self, observer_id: usize) {
        self.observers.retain(|o| {
            o.upgrade().map(|o| o.id() != observer_id).unwrap_or(false)
        });
    }

    fn notify(&self, event: &Event) {
        for weak_observer in &self.observers {
            if let Some(observer) = weak_observer.upgrade() {
                observer.update(event);
            }
        }
    }
}

// 具体观察者
struct ConcreteObserver {
    id: usize,
    name: String,
}

impl Observer for ConcreteObserver {
    fn update(&self, event: &Event) {
        println!("Observer {} received: {:?}", self.name, event);
    }

    fn id(&self) -> usize {
        self.id
    }
}

fn observer_pattern() {
    let subject = Rc::new(RefCell::new(ConcreteSubject::new()));

    let observer1 = Rc::new(ConcreteObserver {
        id: 1,
        name: "Observer1".to_string(),
    }) as Rc<dyn Observer>;

    let observer2 = Rc::new(ConcreteObserver {
        id: 2,
        name: "Observer2".to_string(),
    }) as Rc<dyn Observer>;

    // 注册观察者
    subject.borrow_mut().attach(Rc::downgrade(&observer1));
    subject.borrow_mut().attach(Rc::downgrade(&observer2));

    // 改变状态，触发通知
    subject.borrow_mut().set_state("new state");
}
```

#### 3.3.3 访问者模式语义

访问者模式允许在不修改类的情况下添加新操作：

```rust
// 元素接口
trait Element {
    fn accept(&self, visitor: &dyn Visitor);
}

// 访问者接口
trait Visitor {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA);
    fn visit_concrete_element_b(&self, element: &ConcreteElementB);
}

// 具体元素 A
struct ConcreteElementA {
    name: String,
}

impl Element for ConcreteElementA {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_concrete_element_a(self);
    }
}

impl ConcreteElementA {
    fn operation_a(&self) -> String {
        format!("A: {}", self.name)
    }
}

// 具体元素 B
struct ConcreteElementB {
    value: i32,
}

impl Element for ConcreteElementB {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_concrete_element_b(self);
    }
}

impl ConcreteElementB {
    fn operation_b(&self) -> i32 {
        self.value * 2
    }
}

// 具体访问者
struct ConcreteVisitor;

impl Visitor for ConcreteVisitor {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA) {
        println!("Visiting A: {}", element.operation_a());
    }

    fn visit_concrete_element_b(&self, element: &ConcreteElementB) {
        println!("Visiting B: {}", element.operation_b());
    }
}

// 双分派访问者（扩展性更强）
struct PrintVisitor;

impl Visitor for PrintVisitor {
    fn visit_concrete_element_a(&self, element: &ConcreteElementA) {
        println!("Print: Element A = {}", element.name);
    }

    fn visit_concrete_element_b(&self, element: &ConcreteElementB) {
        println!("Print: Element B = {}", element.value);
    }
}

fn visitor_pattern() {
    let elements: Vec<Box<dyn Element>> = vec![
        Box::new(ConcreteElementA { name: "Alice".to_string() }),
        Box::new(ConcreteElementB { value: 42 }),
    ];

    let visitor = ConcreteVisitor;
    for element in &elements {
        element.accept(&visitor);
    }

    let print_visitor = PrintVisitor;
    for element in &elements {
        element.accept(&print_visitor);
    }
}
```

---

## 4. 并发语义模型

### 4.1 线程模型语义

#### 4.1.1 OS 线程语义

操作系统线程是最基础的并发单元：

$$
\text{OSThread} : \text{Code} \times \text{Stack} \times \text{RegisterState} \to \text{Execution}
$$

```rust
use std::thread;
use std::time::Duration;

fn os_thread_semantics() {
    // 线程创建语义
    let handle1 = thread::spawn(|| {
        println!("Thread 1 running");
        thread::sleep(Duration::from_millis(100));
        42
    });

    // 带参数的线程
    let data = vec![1, 2, 3];
    let handle2 = thread::spawn(move || {
        println!("Thread 2 with data: {:?}", data);
        data.iter().sum::<i32>()
    });

    // 线程同步语义
    let result1 = handle1.join().unwrap();
    let result2 = handle2.join().unwrap();

    println!("Results: {}, {}", result1, result2);

    // 线程作用域（Rust 1.63+）
    let mut result = 0;
    thread::scope(|s| {
        s.spawn(|| {
            println!("Scoped thread");
        });
    });
}
```

#### 4.1.2 绿色线程/协程语义

协程提供了用户级线程抽象：

```rust
// Rust 标准库不直接提供绿色线程
// 但可以使用 async/await 实现类似语义
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 协程状态机
enum CoroutineState {
    Start,
    Yielded,
    Complete,
}

struct SimpleCoroutine {
    state: CoroutineState,
    counter: i32,
}

impl SimpleCoroutine {
    fn new() -> Self {
        SimpleCoroutine {
            state: CoroutineState::Start,
            counter: 0,
        }
    }
}

impl Future for SimpleCoroutine {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.state {
            CoroutineState::Start => {
                println!("Coroutine starting");
                self.state = CoroutineState::Yielded;
                self.counter = 1;
                Poll::Pending
            }
            CoroutineState::Yielded => {
                println!("Coroutine resumed, counter = {}", self.counter);
                if self.counter < 3 {
                    self.counter += 1;
                    Poll::Pending
                } else {
                    self.state = CoroutineState::Complete;
                    Poll::Ready(self.counter)
                }
            }
            CoroutineState::Complete => {
                Poll::Ready(self.counter)
            }
        }
    }
}
```

#### 4.1.3 线程间通信语义

线程间通信遵循所有权和通道语义：

$$
\text{Channel} : T \to \text{Send} \times \text{Recv} \quad \text{where } \text{Own}(T) \to \text{Channel}(T)
$$

```rust
use std::sync::mpsc;
use std::thread;

fn inter_thread_communication() {
    // 多生产者单消费者通道
    let (tx, rx) = mpsc::channel::<i32>();

    // 生产者线程
    let tx2 = tx.clone();
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(i).unwrap();
            thread::sleep(std::time::Duration::from_millis(10));
        }
    });

    thread::spawn(move || {
        for i in 5..10 {
            tx2.send(i).unwrap();
        }
    });

    // 消费者
    drop(tx);  // 关闭发送端，允许接收端正确结束

    for received in rx {
        println!("Received: {}", received);
    }
    println!("Channel closed");
}
```

### 4.2 同步原语语义

#### 4.2.1 互斥锁语义

互斥锁提供独占访问：

$$
\text{Mutex} : T \times \text{Lock} \times \text{Unlock} \to \text{Guard}\langle T \rangle
$$

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn mutex_semantics() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for i in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            // 获取锁
            let mut num = counter.lock().unwrap();
            *num += 1;
            println!("Thread {} incremented to {}", i, *num);
            // 锁在此处自动释放
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Final count: {}", *counter.lock().unwrap());
}
```

#### 4.2.2 读写锁语义

读写锁允许多读单写：

$$
\text{RwLock} : T \times (\text{Read}_n \cup \text{Write}_1) \to \text{Guard}\langle T \rangle
$$

```rust
use std::sync::{Arc, RwLock};
use std::thread;

fn rwlock_semantics() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];

    // 多个读者
    for i in 0..3 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("Reader {} sees: {:?}", i, *read_guard);
            // 多个读锁可以共存
        }));
    }

    // 一个写者
    {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut write_guard = data.write().unwrap();
            write_guard.push(4);
            println!("Writer added element");
            // 写锁独占
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

#### 4.2.3 条件变量语义

条件变量用于线程间条件通知：

```rust
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

fn condvar_semantics() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);

    // 等待线程
    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        while !*started {
            // 原子释放锁并等待
            started = cvar.wait(started).unwrap();
        }
        println!("Child thread notified!");
    });

    thread::sleep(Duration::from_millis(100));

    // 通知线程
    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    *started = true;
    cvar.notify_one();  // 唤醒一个等待者

    thread::sleep(Duration::from_millis(100));
}
```

#### 4.2.4 屏障语义

屏障用于同步多个线程到达某点：

```rust
use std::sync::{Arc, Barrier};
use std::thread;

fn barrier_semantics() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let barrier = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            println!("Thread {} before barrier", i);

            // 等待所有线程到达
            let result = barrier.wait();

            // 只有一个线程会得到 LeaderResult
            if result.is_leader() {
                println!("Thread {} is the leader", i);
            }

            println!("Thread {} after barrier", i);
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 4.3 无锁语义

#### 4.3.1 原子操作语义（内存序）

原子操作内存序定义了操作之间的可见性：

| 内存序 | 语义 | 用途 |
|-------|------|------|
| `Relaxed` | 仅原子性，无顺序保证 | 计数器 |
| `Acquire` | 获取语义，后续读可见 | 锁获取 |
| `Release` | 释放语义，前面写可见 | 锁释放 |
| `AcqRel` | 获取+释放 | CAS 操作 |
| `SeqCst` | 顺序一致性 | 严格同步 |

```rust
use std::sync::atomic::{AtomicI32, AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

fn atomic_semantics() {
    // Relaxed：最简单的原子操作
    let counter = Arc::new(AtomicI32::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            for _ in 0..100 {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
    println!("Counter: {}", counter.load(Ordering::Relaxed));

    // Acquire-Release 语义
    let flag = Arc::new(AtomicBool::new(false));
    let data = Arc::new(AtomicI32::new(0));

    let flag2 = Arc::clone(&flag);
    let data2 = Arc::clone(&data);

    thread::spawn(move || {
        data2.store(42, Ordering::Relaxed);
        flag2.store(true, Ordering::Release);  // 释放语义
    });

    while !flag.load(Ordering::Acquire) {  // 获取语义
        thread::yield_now();
    }

    // 保证看到 data = 42
    println!("Data: {}", data.load(Ordering::Relaxed));
}
```

#### 4.3.2 CAS 循环语义

比较并交换（CAS）是无锁算法的基础：

$$
\text{CAS}(location, expected, new) = \begin{cases}
\text{true} & \text{if } *location = expected \land *location := new \\
\text{false} & \text{otherwise}
\end{cases}
$$

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

// 无锁栈实现
struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> LockFreeStack<T> {
    fn new() -> Self {
        LockFreeStack {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            unsafe { (*new_node).next = head; }

            // CAS 尝试更新 head
            match self.head.compare_exchange_weak(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(_) => continue,  // 失败重试
            }
        }
    }

    fn pop(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            if head.is_null() {
                return None;
            }

            let next = unsafe { (*head).next };

            match self.head.compare_exchange_weak(
                head,
                next,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => {
                    let node = unsafe { Box::from_raw(head) };
                    return Some(node.data);
                }
                Err(_) => continue,
            }
        }
    }
}
```

#### 4.3.3 内存模型语义

Rust 遵循 C++11 内存模型，提供以下一致性保证：

$$
\text{Happens-Before} : e_1 \prec e_2 \iff \text{visible}(e_1, e_2)
$$

```rust
use std::sync::atomic::{fence, AtomicI32, Ordering};
use std::thread;

fn memory_model_semantics() {
    let x = AtomicI32::new(0);
    let y = AtomicI32::new(0);
    let z = AtomicI32::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            x.store(1, Ordering::Relaxed);
            // 内存屏障，确保前面的写对后面可见
            fence(Ordering::SeqCst);
            y.store(1, Ordering::Relaxed);
        });

        s.spawn(|| {
            while y.load(Ordering::Relaxed) == 0 {}
            fence(Ordering::SeqCst);
            // 保证看到 x = 1
            z.store(x.load(Ordering::Relaxed), Ordering::Relaxed);
        });
    });

    println!("z = {}", z.load(Ordering::Relaxed));
}
```

---

## 5. 异步语义模型

### 5.1 Future 语义

#### 5.1.1 Future 状态机语义

Future 本质上是异步计算的状态机：

$$
\text{Future}\langle T \rangle : \text{State} \times \text{Context} \to \text{Poll}\langle T \rangle
$$

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future 作为状态机
enum MyFutureState {
    Start,
    WaitingForA,
    WaitingForB,
    Done,
}

struct MyFuture {
    state: MyFutureState,
    result_a: Option<i32>,
    result_b: Option<i32>,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        loop {
            match self.state {
                MyFutureState::Start => {
                    println!("State: Start -> WaitingForA");
                    self.state = MyFutureState::WaitingForA;
                    // 启动操作 A，注册 waker
                }
                MyFutureState::WaitingForA => {
                    // 检查操作 A 是否完成
                    if let Some(a) = self.result_a {
                        println!("State: Got A = {}", a);
                        self.state = MyFutureState::WaitingForB;
                    } else {
                        // 返回 Pending，等待唤醒
                        return Poll::Pending;
                    }
                }
                MyFutureState::WaitingForB => {
                    // 检查操作 B 是否完成
                    if let Some(b) = self.result_b {
                        println!("State: Got B = {}", b);
                        self.state = MyFutureState::Done;
                    } else {
                        return Poll::Pending;
                    }
                }
                MyFutureState::Done => {
                    let result = self.result_a.unwrap() + self.result_b.unwrap();
                    println!("State: Done = {}", result);
                    return Poll::Ready(result);
                }
            }
        }
    }
}
```

#### 5.1.2 Poll 模型语义

Poll 模型定义了异步计算的协作式调度：

$$
\text{Poll} = \text{Ready}(T) \mid \text{Pending}
$$

```rust
// Poll 模型语义示例
async fn poll_model_example() {
    // 每个 .await 是一个潜在的挂起点
    let a = async_operation_a().await;  // Poll::Pending / Poll::Ready
    let b = async_operation_b().await;  // Poll::Pending / Poll::Ready
    a + b
}

async fn async_operation_a() -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    42
}

async fn async_operation_b() -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    8
}
```

#### 5.1.3 Waker 机制语义

Waker 用于在异步操作完成时唤醒任务：

$$
\text{Waker} : \text{Task} \to \text{Action} \quad \text{where } \text{Action} \in \{ \text{wake}, \text{wake_by_ref}, \text{clone}, \text{drop} \}
$$

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Wake, Waker};
use std::thread;

// 自定义 Waker
struct MyWaker {
    task_id: usize,
}

impl Wake for MyWaker {
    fn wake(self: Arc<Self>) {
        println!("Task {} woken!", self.task_id);
    }

    fn wake_by_ref(self: &Arc<Self>) {
        println!("Task {} woken by ref!", self.task_id);
    }
}

// 使用 waker 的 Future
struct TimerFuture {
    duration: std::time::Duration,
    waker: Arc<Mutex<Option<Waker>>>,
}

impl Future for TimerFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut waker = self.waker.lock().unwrap();

        if waker.is_none() {
            // 第一次 poll，设置定时器
            let waker = cx.waker().clone();
            let duration = self.duration;
            *self.waker.lock().unwrap() = Some(waker.clone());

            thread::spawn(move || {
                thread::sleep(duration);
                waker.wake();  // 唤醒任务
            });

            Poll::Pending
        } else {
            // 已经被唤醒
            Poll::Ready(())
        }
    }
}
```

### 5.2 async/await 语义

#### 5.2.1 状态机转换语义

`async/await` 被编译器转换为状态机：

```rust
// 源代码
async fn example() -> i32 {
    let x = async_op1().await;
    let y = async_op2().await;
    x + y
}

// 概念上等价于（简化）
enum ExampleStateMachine {
    Start,
    Waiting1(/* 保存的局部变量 */),
    Waiting2(/* 保存的局部变量 */),
    Done,
}

impl Future for ExampleStateMachine {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        loop {
            match *self {
                ExampleStateMachine::Start => {
                    // 开始第一个异步操作
                    *self = ExampleStateMachine::Waiting1(/* ... */);
                }
                ExampleStateMachine::Waiting1(/* ... */) => {
                    // 检查 async_op1 是否完成
                    // 如果完成，保存结果，转换到 Waiting2
                }
                ExampleStateMachine::Waiting2(/* ... */) => {
                    // 检查 async_op2 是否完成
                    // 如果完成，计算结果
                }
                ExampleStateMachine::Done => {
                    return Poll::Ready(/* 结果 */);
                }
            }
        }
    }
}
```

#### 5.2.2 Pin 语义（自引用）

Pin 用于安全地处理自引用结构：

$$
\text{Pin}\langle P\langle T \rangle \rangle \land \text{!Unpin}(T) \implies \text{Immovable}(T)
$$

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

// 自引用结构
struct SelfReferential {
    data: String,
    // 指向 data 的指针
    ptr_to_data: *const String,
    _pin: PhantomPinned,  // 标记为 !Unpin
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        });

        let ptr = &boxed.data as *const String;
        unsafe {
            let mut_ref = boxed.as_mut().get_unchecked_mut();
            mut_ref.ptr_to_data = ptr;
        }

        boxed
    }

    fn get_data(&self) -> &str {
        &self.data
    }

    fn get_data_via_ptr(&self) -> &str {
        unsafe { &*self.ptr_to_data }
    }
}

fn pin_semantics() {
    let data = SelfReferential::new(String::from("hello"));

    // 通过 Pin 安全访问
    assert_eq!(data.get_data(), data.get_data_via_ptr());

    // 不能移动，因为 Pin<Box<_>>
    // let moved = *data;  // 编译错误！
}
```

#### 5.2.3 取消安全语义

取消安全是指当 Future 被丢弃时的正确性：

```rust
// 取消安全的异步操作
use tokio::select;

async fn cancellation_safe() {
    let task1 = async {
        // 取消安全的操作
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        println!("Task 1 completed");
    };

    let task2 = async {
        tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
        println!("Task 2 completed");
    };

    // 当其中一个完成时，另一个会被取消
    tokio::select! {
        _ = task1 => println!("Task 1 won"),
        _ = task2 => println!("Task 2 won"),
    }
}

// 非取消安全的示例（需要额外处理）
struct DatabaseConnection;

impl DatabaseConnection {
    async fn transaction(&mut self) -> Result<(), ()> {
        // 如果在此处被取消，可能导致资源泄漏
        // 需要使用 Drop guard 或作用限定的清理
        tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        Ok(())
    }
}
```

### 5.3 执行器语义

#### 5.3.1 任务调度语义

执行器负责任务的调度执行：

$$
\text{Executor} : \text{Queue}\langle \text{Task} \rangle \times \text{Strategy} \to \text{Execution}
$$

```rust
// 简化的执行器实现
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Wake, Waker};

struct SimpleExecutor {
    task_queue: Arc<Mutex<VecDeque<Task>>>,
}

struct Task {
    future: Mutex<Pin<Box<dyn Future<Output = ()> + Send>>>,
}

impl SimpleExecutor {
    fn new() -> Self {
        SimpleExecutor {
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    fn spawn(&self, future: impl Future<Output = ()> + Send + 'static) {
        let task = Task {
            future: Mutex::new(Box::pin(future)),
        };
        self.task_queue.lock().unwrap().push_back(task);
    }

    fn run(&self) {
        while let Some(task) = self.task_queue.lock().unwrap().pop_front() {
            let mut future = task.future.lock().unwrap();

            // 创建 waker
            let waker = create_waker(self.task_queue.clone());
            let mut context = Context::from_waker(&waker);

            // 轮询 Future
            match future.as_mut().poll(&mut context) {
                Poll::Ready(()) => {}  // 任务完成
                Poll::Pending => {
                    // 任务挂起，稍后重新调度
                    drop(future);
                    self.task_queue.lock().unwrap().push_back(task);
                }
            }
        }
    }
}

fn create_waker(queue: Arc<Mutex<VecDeque<Task>>>) -> Waker {
    // 简化实现
    todo!()
}
```

#### 5.3.2 工作窃取语义

工作窃取是一种负载均衡策略：

```rust
// 工作窃取队列的概念模型
use crossbeam::deque::{Injector, Stealer, Worker};

struct WorkStealingExecutor {
    global_queue: Injector<Task>,
    workers: Vec<Worker<Task>>,
    stealers: Vec<Stealer<Task>>,
}

impl WorkStealingExecutor {
    fn spawn(&self, task: Task) {
        self.global_queue.push(task);
    }

    fn worker_loop(&self, worker_id: usize) {
        let local_queue = &self.workers[worker_id];

        loop {
            // 1. 尝试从本地队列获取任务
            if let Some(task) = local_queue.pop() {
                execute(task);
                continue;
            }

            // 2. 尝试从全局队列获取
            if let Some(task) = self.global_queue.steal().success() {
                execute(task);
                continue;
            }

            // 3. 尝试从其他工作线程窃取
            for stealer in &self.stealers {
                if let Some(task) = stealer.steal().success() {
                    execute(task);
                    break;
                }
            }

            // 4. 如果没有任务，休眠等待
            std::thread::park();
        }
    }
}

fn execute(_task: Task) {
    // 执行任务
}

struct Task;
```

#### 5.3.3 协作式调度语义

协作式调度依赖任务主动让出控制权：

```rust
// 协作式调度的 yield 语义
async fn cooperative_scheduling() {
    for i in 0..10 {
        // 执行一些工作
        do_work(i);

        // 协作式让出，允许其他任务运行
        tokio::task::yield_now().await;
    }
}

fn do_work(i: i32) {
    println!("Working on {}", i);
}

// 长时间运行的任务应该定期让出
async fn long_running_task() {
    for batch in 0..100 {
        for item in 0..1000 {
            process_item(batch * 1000 + item);
        }

        // 每处理一批后让出
        tokio::task::yield_now().await;
    }
}

fn process_item(_item: i32) {
    // 处理单个项目
}
```

---

## 6. Actor 模型语义

### 6.1 Actor 基本语义

#### 6.1.1 消息传递语义

Actor 模型基于异步消息传递：

$$
\text{Actor} : \text{State} \times \text{Inbox}\langle \text{Message} \rangle \times \text{Behavior} \to \text{State}' \times \text{Outbox}\langle \text{Message} \rangle
$$

```rust
use std::sync::mpsc;
use std::thread;

// Actor 消息类型
trait Message: Send + 'static {}

// Actor trait
trait Actor {
    type Msg: Message;
    fn handle_message(&mut self, msg: Self::Msg);
}

// 简单 Actor 实现
struct SimpleActor<M> {
    receiver: mpsc::Receiver<M>,
}

impl<M: Message> SimpleActor<M> {
    fn run<F>(&mut self, mut handler: F)
    where
        F: FnMut(M),
    {
        while let Ok(msg) = self.receiver.recv() {
            handler(msg);
        }
    }
}

// Actor 引用（用于发送消息）
struct ActorRef<M> {
    sender: mpsc::Sender<M>,
}

impl<M: Message> ActorRef<M> {
    fn send(&self, msg: M) {
        let _ = self.sender.send(msg);
    }
}

fn spawn_actor<M: Message, F>(handler: F) -> ActorRef<M>
where
    F: FnMut(M) + Send + 'static,
{
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let mut actor = SimpleActor { receiver: rx };
        actor.run(handler);
    });

    ActorRef { sender: tx }
}

// 示例：计数器 Actor
enum CounterMsg {
    Increment(i32),
    GetValue,
}

impl Message for CounterMsg {}

fn counter_actor_example() {
    let mut value = 0;

    let actor = spawn_actor(move |msg| {
        match msg {
            CounterMsg::Increment(n) => {
                value += n;
                println!("Counter: {}", value);
            }
            CounterMsg::GetValue => {
                println!("Current value: {}", value);
            }
        }
    });

    actor.send(CounterMsg::Increment(5));
    actor.send(CounterMsg::Increment(3));
    actor.send(CounterMsg::GetValue);
}
```

#### 6.1.2 Actor 生命周期语义

Actor 有其明确的生命周期：

```rust
// Actor 生命周期管理
enum ActorLifecycle {
    Starting,
    Running,
    Restarting,
    Stopping,
    Terminated,
}

struct ManagedActor<S, M> {
    state: ActorLifecycle,
    mailbox: mpsc::Receiver<M>,
    context: ActorContext,
    behavior: Behavior<S, M>,
}

struct ActorContext {
    self_ref: ActorRef<ControlMsg>,
    parent: Option<ActorRef<ControlMsg>>,
    children: Vec<ActorRef<ControlMsg>>,
}

enum ControlMsg {
    Stop,
    Restart,
    ChildTerminated,
}

struct Behavior<S, M> {
    on_start: Box<dyn Fn(&mut S)>,
    on_message: Box<dyn Fn(&mut S, M)>,
    on_stop: Box<dyn Fn(&mut S)>,
}

impl<S, M: Message> ManagedActor<S, M> {
    fn new(
        initial_state: S,
        behavior: Behavior<S, M>,
        mailbox: mpsc::Receiver<M>,
    ) -> Self {
        ManagedActor {
            state: ActorLifecycle::Starting,
            mailbox,
            context: ActorContext {
                self_ref: todo!(),
                parent: None,
                children: vec![],
            },
            behavior,
        }
    }

    fn start(&mut self, state: &mut S) {
        self.state = ActorLifecycle::Running;
        (self.behavior.on_start)(state);
    }

    fn stop(&mut self, state: &mut S) {
        self.state = ActorLifecycle::Stopping;
        (self.behavior.on_stop)(state);
        self.state = ActorLifecycle::Terminated;
    }
}
```

#### 6.1.3 监督树语义

监督树提供了故障恢复机制：

```rust
// 监督策略
enum SupervisionStrategy {
    OneForOne,   // 一个子 Actor 失败，只重启它
    OneForAll,   // 一个子 Actor 失败，重启所有子 Actor
    RestForOne,  // 一个子 Actor 失败，重启它及其后启动的子 Actor
}

// 重启策略
enum RestartPolicy {
    Permanent,   // 总是重启
    Transient,   // 只在异常退出时重启
    Temporary,   // 永不重启
}

struct Supervisor {
    strategy: SupervisionStrategy,
    children: Vec<ChildSpec>,
}

struct ChildSpec {
    id: String,
    restart_policy: RestartPolicy,
    max_restarts: u32,
    restart_window: std::time::Duration,
}

impl Supervisor {
    fn handle_child_failure(&mut self, child_id: &str) {
        match self.strategy {
            SupervisionStrategy::OneForOne => {
                self.restart_child(child_id);
            }
            SupervisionStrategy::OneForAll => {
                self.stop_all_children();
                self.start_all_children();
            }
            SupervisionStrategy::RestForOne => {
                self.restart_child_and_following(child_id);
            }
        }
    }

    fn restart_child(&mut self, _child_id: &str) {
        // 重启特定子 Actor
    }

    fn stop_all_children(&mut self) {
        // 停止所有子 Actor
    }

    fn start_all_children(&mut self) {
        // 启动所有子 Actor
    }

    fn restart_child_and_following(&mut self, _child_id: &str) {
        // 重启指定子 Actor 及其后面的所有子 Actor
    }
}
```

### 6.2 分布式 Actor 语义

#### 6.2.1 位置透明语义

位置透明允许 Actor 不感知本地或远程：

```rust
// Actor 路径（位置无关的标识）
struct ActorPath {
    protocol: String,  // "akka", "actix", 等
    system: String,    // Actor 系统名称
    path: Vec<String>, // Actor 层级路径
}

impl ActorPath {
    fn local(name: &str) -> Self {
        ActorPath {
            protocol: "local".to_string(),
            system: "default".to_string(),
            path: vec![name.to_string()],
        }
    }

    fn remote(system: &str, host: &str, port: u16, name: &str) -> Self {
        ActorPath {
            protocol: format!("akka.tcp://{}@{}:{}", system, host, port),
            system: system.to_string(),
            path: vec!["user".to_string(), name.to_string()],
        }
    }
}

// 位置透明的 ActorRef
trait ActorRefTrait<M>: Send + Sync {
    fn tell(&self, message: M);
    fn path(&self) -> ActorPath;
    fn is_local(&self) -> bool;
}

struct LocalActorRef<M> {
    sender: mpsc::Sender<M>,
    path: ActorPath,
}

struct RemoteActorRef<M> {
    connection: RemoteConnection,
    path: ActorPath,
    _phantom: std::marker::PhantomData<M>,
}

impl<M: Message> ActorRefTrait<M> for LocalActorRef<M> {
    fn tell(&self, message: M) {
        let _ = self.sender.send(message);
    }

    fn path(&self) -> ActorPath {
        self.path.clone()
    }

    fn is_local(&self) -> bool {
        true
    }
}

struct RemoteConnection;
```

#### 6.2.2 故障隔离语义

分布式系统中的故障隔离：

```rust
// 网络分区处理
enum PartitionStrategy {
    AutoDown,        // 自动标记节点为 down
    KeepQuorum,      // 保持多数分区存活
    StaticQuorum,    // 静态法定人数
    KeepMajority,    // 保持多数分区
    KeepOldest,      // 保持最老节点
    Custom(Box<dyn Fn(&ClusterState) -> Vec<NodeId>>),
}

struct ClusterState {
    nodes: Vec<NodeState>,
    partitions: Vec<Vec<NodeId>>,
}

struct NodeState {
    id: NodeId,
    reachable: bool,
    last_seen: std::time::Instant,
}

struct NodeId(String);

struct FailureDetector {
    heartbeat_interval: std::time::Duration,
    failure_threshold: u32,
}

impl FailureDetector {
    fn phi(&self, node: &NodeState) -> f64 {
        // Phi 累积分布函数，用于判断节点是否故障
        let elapsed = node.last_seen.elapsed();
        // 简化计算
        elapsed.as_secs_f64() / self.heartbeat_interval.as_secs_f64()
    }

    fn is_suspected(&self, node: &NodeState) -> bool {
        self.phi(node) > 8.0  // 经验阈值
    }
}
```

#### 6.2.3 一致性与可用性语义

分布式系统中的一致性与可用性权衡：

```rust
// CAP 定理的语义表达
enum ConsistencyLevel {
    Strong,       // 线性一致性
    Sequential,   // 顺序一致性
    Causal,       // 因果一致性
    Eventual,     // 最终一致性
    ReadYourWrites,
    MonotonicReads,
    MonotonicWrites,
}

struct DistributedActorSystem {
    consistency: ConsistencyLevel,
    replication_factor: u32,
    nodes: Vec<NodeId>,
}

// CRDT（无冲突复制数据类型）语义
trait Crdt {
    type Operation;
    type Value;

    // 合并操作，必须满足交换律、结合律、幂等律
    fn merge(&mut self, other: &Self);

    // 应用本地操作
    fn apply(&mut self, op: Self::Operation);

    // 获取当前值
    fn value(&self) -> Self::Value;
}

// G-Counter（增长计数器）CRDT
struct GCounter {
    // 每个节点的计数器
    counters: std::collections::HashMap<NodeId, u64>,
}

impl Crdt for GCounter {
    type Operation = u64;  // 增量
    type Value = u64;      // 总计数

    fn merge(&mut self, other: &Self) {
        for (node, count) in &other.counters {
            let entry = self.counters.entry(node.clone()).or_insert(0);
            *entry = (*entry).max(*count);
        }
    }

    fn apply(&mut self, op: Self::Operation) {
        // 在本地节点上增加
        let node = NodeId("local".to_string());
        *self.counters.entry(node).or_insert(0) += op;
    }

    fn value(&self) -> Self::Value {
        self.counters.values().sum()
    }
}
```

---

## 7. 运行时行为语义

### 7.1 内存模型语义

#### 7.1.1 栈分配语义

栈分配是最快的内存分配方式：

$$
\text{StackAlloc}(T) : \text{Size}(T) \to \text{Address} \quad \text{where } \text{AutoFree}(T)
$$

```rust
fn stack_allocation_semantics() {
    // 基本类型：栈分配
    let x: i32 = 42;           // 4 字节栈空间
    let y: f64 = 3.14;         // 8 字节栈空间
    let arr: [i32; 5] = [1, 2, 3, 4, 5];  // 20 字节栈空间

    // 结构体：栈分配（如果所有字段都是 Sized）
    struct Point {
        x: f64,
        y: f64,
    }
    let p = Point { x: 1.0, y: 2.0 };  // 16 字节栈空间

    // 固定大小数组：栈分配
    let fixed: [u8; 1024] = [0; 1024];  // 1KB 栈空间

    // 作用域结束，自动释放
}  // 所有栈变量在此处自动清理

// 注意：大数组可能导致栈溢出
fn stack_overflow_risk() {
    // let big_array: [u8; 10_000_000] = [0; 10_000_000];  // 可能导致栈溢出
    let big_array = Box::new([0u8; 10_000_000]);  // 使用堆分配
}
```

#### 7.1.2 堆分配语义

堆分配用于动态大小的数据：

$$
\text{HeapAlloc}(T) : \text{Size}(T) \to \text{Address} \times \text{Handle} \quad \text{where } \text{ManualFree}(T) \lor \text{RAII}(T)
$$

```rust
fn heap_allocation_semantics() {
    // Box：独占堆所有权
    let boxed = Box::new(vec![1, 2, 3, 4, 5]);

    // Vec：动态数组，堆分配
    let mut vec = Vec::with_capacity(100);
    for i in 0..100 {
        vec.push(i);
    }

    // String：堆分配的 UTF-8 字符串
    let mut s = String::with_capacity(1024);
    s.push_str("Hello, World!");

    // Rc/Arc：引用计数的堆分配
    let shared = std::rc::Rc::new(String::from("shared"));

    // 自定义分配器（nightly）
    // #![feature(allocator_api)]
    // use std::alloc::System;
    // let boxed = Box::new_in(42, System);
}
```

#### 7.1.3 内存回收语义（RAII/Drop）

RAII（资源获取即初始化）是 Rust 的核心内存管理策略：

$$
\text{RAII} : \text{Acquire}(resource) \to \text{Scope}(resource) \to \text{AutomaticRelease}(resource)
$$

```rust
// RAII 语义示例
struct DatabaseConnection {
    id: u64,
}

impl DatabaseConnection {
    fn new(id: u64) -> Self {
        println!("Opening connection {}", id);
        DatabaseConnection { id }
    }
}

impl Drop for DatabaseConnection {
    fn drop(&mut self) {
        println!("Closing connection {}", self.id);
    }
}

fn raii_semantics() {
    {
        let conn = DatabaseConnection::new(1);
        // 使用连接
        println!("Using connection {}", conn.id);
    }  // conn 在此处自动 drop

    println!("Connection closed");

    // 提前释放
    let conn2 = DatabaseConnection::new(2);
    drop(conn2);  // 显式调用 drop
    println!("Connection 2 manually dropped");

    // 转移所有权时不会调用 drop
    let conn3 = DatabaseConnection::new(3);
    let _moved = conn3;  // conn3 被移动，不会 drop
    // _moved 在作用域结束时 drop
}

// 作用域守卫模式
struct LockGuard<'a> {
    data: &'a mut Vec<i32>,
}

impl<'a> LockGuard<'a> {
    fn lock(data: &'a mut Vec<i32>) -> Self {
        println!("Lock acquired");
        LockGuard { data }
    }
}

impl<'a> Drop for LockGuard<'a> {
    fn drop(&mut self) {
        println!("Lock released");
    }
}

impl<'a> std::ops::Deref for LockGuard<'a> {
    type Target = Vec<i32>;
    fn deref(&self) -> &Self::Target {
        self.data
    }
}

impl<'a> std::ops::DerefMut for LockGuard<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.data
    }
}
```

### 7.2 调度语义

#### 7.2.1 任务调度语义

任务调度决定了代码何时执行：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 任务优先级
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum TaskPriority {
    High = 0,
    Normal = 1,
    Low = 2,
}

struct Task {
    priority: TaskPriority,
    future: Pin<Box<dyn Future<Output = ()> + Send>>,
}

// 优先级队列调度
struct PriorityScheduler {
    high_priority: Vec<Task>,
    normal_priority: Vec<Task>,
    low_priority: Vec<Task>,
}

impl PriorityScheduler {
    fn schedule(&mut self) {
        // 高优先级任务优先执行
        while let Some(task) = self.high_priority.pop() {
            self.execute(task);
        }

        // 然后执行普通优先级
        while let Some(task) = self.normal_priority.pop() {
            self.execute(task);
        }

        // 最后执行低优先级
        while let Some(task) = self.low_priority.pop() {
            self.execute(task);
        }
    }

    fn execute(&self, mut _task: Task) {
        // 执行任务的逻辑
    }
}
```

#### 7.2.2 抢占式调度语义

抢占式调度允许操作系统中断任务：

```rust
// 使用线程模拟抢占式调度
use std::thread;
use std::time::Duration;

fn preemptive_scheduling() {
    // 创建两个线程，操作系统会抢占式调度
    let handle1 = thread::spawn(|| {
        for i in 0..5 {
            println!("Thread 1: iteration {}", i);
            // 模拟工作
            thread::sleep(Duration::from_millis(10));
        }
    });

    let handle2 = thread::spawn(|| {
        for i in 0..5 {
            println!("Thread 2: iteration {}", i);
            thread::sleep(Duration::from_millis(10));
        }
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}

// 设置线程优先级（平台相关）
#[cfg(unix)]
fn set_thread_priority_high() {
    // 使用 pthread 设置优先级
}

#[cfg(windows)]
fn set_thread_priority_high() {
    // 使用 Windows API 设置优先级
}
```

#### 7.2.3 协作式调度语义

协作式调度依赖任务主动让出：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 协作式调度器
struct CooperativeScheduler {
    tasks: Vec<Pin<Box<dyn Future<Output = ()>>>>,
    current_task: usize,
}

impl CooperativeScheduler {
    fn new() -> Self {
        CooperativeScheduler {
            tasks: vec![],
            current_task: 0,
        }
    }

    fn spawn(&mut self, task: impl Future<Output = ()> + 'static) {
        self.tasks.push(Box::pin(task));
    }

    fn run(&mut self) {
        let waker = dummy_waker();
        let mut context = Context::from_waker(&waker);

        while !self.tasks.is_empty() {
            let i = self.current_task % self.tasks.len();

            match self.tasks[i].as_mut().poll(&mut context) {
                Poll::Ready(()) => {
                    self.tasks.remove(i);
                }
                Poll::Pending => {
                    self.current_task += 1;
                }
            }
        }
    }
}

fn dummy_waker() -> std::task::Waker {
    use std::sync::Arc;
    use std::task::{RawWaker, RawWakerVTable, Wake};

    struct DummyWaker;
    impl Wake for DummyWaker {
        fn wake(self: Arc<Self>) {}
    }

    Arc::new(DummyWaker).into()
}

// yield_now 实现协作式让出
struct YieldNow {
    yielded: bool,
}

impl Future for YieldNow {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.yielded {
            Poll::Ready(())
        } else {
            self.yielded = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

fn yield_now() -> YieldNow {
    YieldNow { yielded: false }
}
```

### 7.3 I/O 语义

#### 7.3.1 阻塞 I/O 语义

阻塞 I/O 会使线程等待操作完成：

$$
\text{BlockingIO} : \text{Request} \to \text{ThreadSleep} \to \text{Response}
$$

```rust
use std::fs::File;
use std::io::{Read, Write};

fn blocking_io_semantics() {
    // 文件 I/O（阻塞）
    let mut file = File::open("data.txt").unwrap();
    let mut contents = String::new();
    file.read_to_string(&mut contents).unwrap();  // 阻塞直到读取完成

    // 网络 I/O（阻塞）
    use std::net::TcpStream;
    let mut stream = TcpStream::connect("example.com:80").unwrap();
    stream.write_all(b"GET / HTTP/1.0\r\n\r\n").unwrap();  // 可能阻塞

    let mut response = vec![];
    stream.read_to_end(&mut response).unwrap();  // 阻塞直到数据到达
}

// 每个连接一个线程模型
fn thread_per_connection() {
    use std::net::{TcpListener, TcpStream};
    use std::thread;

    let listener = TcpListener::bind("127.0.0.1:8080").unwrap();

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                thread::spawn(|| {
                    handle_connection(stream);
                });
            }
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}

fn handle_connection(_stream: TcpStream) {
    // 处理连接
}
```

#### 7.3.2 非阻塞 I/O 语义

非阻塞 I/O 立即返回，不会阻塞线程：

```rust
// 使用 mio 库实现非阻塞 I/O
use mio::{Events, Interest, Poll, Token};
use mio::net::TcpStream;
use std::io::{self, Read, Write};

fn non_blocking_io_semantics() {
    // 创建一个 Poll 实例
    let mut poll = Poll::new().unwrap();
    let mut events = Events::with_capacity(1024);

    // 连接到服务器
    let addr = "127.0.0.1:8080".parse().unwrap();
    let mut stream = TcpStream::connect(addr).unwrap();

    // 注册到 poll，监听可读和可写事件
    poll.registry()
        .register(&mut stream, Token(0), Interest::READABLE | Interest::WRITABLE)
        .unwrap();

    let mut buffer = [0; 1024];

    loop {
        // 等待 I/O 事件
        poll.poll(&mut events, None).unwrap();

        for event in events.iter() {
            match event.token() {
                Token(0) => {
                    if event.is_writable() {
                        // 可以写入数据
                        match stream.write(b"Hello") {
                            Ok(n) => println!("Wrote {} bytes", n),
                            Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
                                // 暂时无法写入，稍后再试
                            }
                            Err(e) => eprintln!("Write error: {}", e),
                        }
                    }

                    if event.is_readable() {
                        // 有数据可读
                        match stream.read(&mut buffer) {
                            Ok(0) => {
                                // 连接关闭
                                return;
                            }
                            Ok(n) => {
                                println!("Read {} bytes: {:?}", n, &buffer[..n]);
                            }
                            Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
                                // 暂时无数据可读
                            }
                            Err(e) => eprintln!("Read error: {}", e),
                        }
                    }
                }
                _ => {}
            }
        }
    }
}
```

#### 7.3.3 异步 I/O 语义

异步 I/O 结合了非阻塞和事件驱动：

$$
\text{AsyncIO} : \text{Request} \to \text{Future}\langle \text{Response} \rangle \to \text{Callback}
$$

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

// 异步 I/O 语义
async fn async_io_semantics() {
    // 异步连接
    let mut stream = TcpStream::connect("127.0.0.1:8080").await.unwrap();

    // 异步写入
    stream.write_all(b"Hello, World!").await.unwrap();

    // 异步读取
    let mut buffer = [0; 1024];
    let n = stream.read(&mut buffer).await.unwrap();
    println!("Read: {:?}", &buffer[..n]);
}

// 并发处理多个连接
async fn handle_connections() {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await.unwrap();

    loop {
        let (stream, addr) = listener.accept().await.unwrap();
        println!("New connection from {}", addr);

        // 为每个连接生成一个任务
        tokio::spawn(async move {
            handle_async_connection(stream).await;
        });
    }
}

async fn handle_async_connection(mut stream: TcpStream) {
    let mut buffer = [0; 1024];

    loop {
        match stream.read(&mut buffer).await {
            Ok(0) => break,  // 连接关闭
            Ok(n) => {
                if stream.write_all(&buffer[..n]).await.is_err() {
                    break;
                }
            }
            Err(_) => break,
        }
    }
}

// 批量异步 I/O
async fn batch_async_io(urls: Vec<&str>) -> Vec<Result<String, reqwest::Error>> {
    use futures::future::join_all;

    let client = reqwest::Client::new();

    let futures = urls.into_iter().map(|url| {
        let client = client.clone();
        async move {
            client.get(url).send().await?.text().await
        }
    });

    join_all(futures).await
}
```

---

## 8. 形式化语义表示

### 8.1 操作语义

#### 8.1.1 大步语义规则

大步语义（自然语义）描述表达式的完整求值：

$$
\frac{e_1 \Downarrow v_1 \quad e_2[v_1/x] \Downarrow v_2}{\text{let } x = e_1 \text{ in } e_2 \Downarrow v_2} \text{ (LET)}
$$

```rust
// 大步语义示例：let 绑定
fn big_step_let() -> i32 {
    // let x = 5 in let y = x + 3 in x + y
    // 语义：
    // 1. 5 ↓ 5
    // 2. (let y = x + 3 in x + y)[5/x]
    //    = let y = 5 + 3 in 5 + y
    //    → 5 + 3 ↓ 8
    //    → 5 + 8 ↓ 13

    let x = 5;
    let y = x + 3;
    x + y  // 结果：13
}

// 函数应用语义
fn big_step_apply() -> i32 {
    // (fn x => x + 1) 5
    // 语义：(x + 1)[5/x] = 5 + 1 ↓ 6

    let add_one = |x: i32| x + 1;
    add_one(5)  // 结果：6
}
```

#### 8.1.2 小步语义规则

小步语义（结构化操作语义）描述单步转换：

$$
\frac{e_1 \to e_1'}{e_1 + e_2 \to e_1' + e_2} \text{ (ADD-L)}
$$

$$
\frac{e_2 \to e_2'}{v_1 + e_2 \to v_1 + e_2'} \text{ (ADD-R)}
$$

$$
\frac{n = n_1 + n_2}{n_1 + n_2 \to n} \text{ (ADD)}
$$

```rust
// 小步语义示例：表达式求值
fn small_step_evaluation() {
    // (1 + 2) + (3 + 4)
    // 步骤：
    // 1. (1 + 2) + (3 + 4) → 3 + (3 + 4)    [ADD-L, ADD]
    // 2. 3 + (3 + 4) → 3 + 7                [ADD-R, ADD]
    // 3. 3 + 7 → 10                         [ADD]

    let result = (1 + 2) + (3 + 4);  // 10
    println!("{}", result);
}

// 所有权转移的小步语义
fn small_step_ownership() {
    // let s = "hello" in let t = s in t
    // 步骤：
    // 1. σ₀, let s = "hello" in ... → σ₁[s ↦ "hello"], ...
    // 2. σ₁, let t = s in t → σ₂[s ↦ ⊥, t ↦ "hello"], t
    // 3. σ₂, t → σ₂, "hello"

    let s = String::from("hello");
    let t = s;  // s 失效
    println!("{}", t);
}
```

#### 8.1.3 求值上下文

求值上下文（Evaluation Contexts）定义了规约可以进行的位置：

$$
E ::= [\cdot] \mid E + e \mid v + E \mid \text{let } x = E \text{ in } e
$$

```rust
// 求值上下文示例
fn evaluation_contexts() {
    // 表达式：let x = (1 + 2) + 3 in x * 4
    // 上下文分解：
    // E = let x = [·] + 3 in x * 4
    // e = 1 + 2
    //
    // 第一步：在 E 中求值 e
    // 1 + 2 → 3
    //
    // 第二步：E[3] = let x = 3 + 3 in x * 4
    // E' = let x = [·] in x * 4
    // e' = 3 + 3
    //
    // 3 + 3 → 6
    //
    // 第三步：E'[6] = let x = 6 in x * 4
    // → (x * 4)[6/x] = 6 * 4 = 24

    let result = {
        let x = (1 + 2) + 3;
        x * 4
    };
    println!("{}", result);
}
```

### 8.2 类型与效果系统

#### 8.2.1 类型判断语义

类型判断规则定义了程序的类型正确性：

$$
\Gamma \vdash n : \text{Int} \quad \text{如果 } n \in \mathbb{Z}
$$

$$
\frac{\Gamma(x) = \tau}{\Gamma \vdash x : \tau} \text{ (VAR)}
$$

$$
\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x. e : \tau_1 \to \tau_2} \text{ (ABS)}
$$

```rust
// 类型判断语义示例
fn type_judgment_semantics() {
    // Γ ⊢ 42 : Int
    let x: i32 = 42;

    // Γ, x: Int ⊢ x + 1 : Int
    // ------------------------ (ABS)
    // Γ ⊢ λx. x + 1 : Int → Int
    let add_one = |x: i32| -> i32 { x + 1 };

    // Γ ⊢ add_one : Int → Int    Γ ⊢ 5 : Int
    // ---------------------------------------- (APP)
    // Γ ⊢ add_one 5 : Int
    let result = add_one(5);  // : Int

    println!("{}", result);
}

// 生命周期参数的类型判断
fn lifetime_type_judgment<'a>(x: &'a i32) -> &'a i32 {
    // Γ, 'a lifetime, x: &'a i32 ⊢ x : &'a i32
    x
}
```

#### 8.2.2 效果追踪语义

效果系统追踪程序可能产生的效果：

$$
\Gamma \vdash e : \tau \mathbin{!} \epsilon
$$

其中 $\epsilon$ 是效果集合，可能包含 `io`、`read`、`write`、`divergence` 等。

```rust
// 效果系统语义（概念性）
// pure : 纯函数，无副作用
// io : 有 I/O 效果
// mut : 有可变状态效果
// panic : 可能 panic

// pure 函数
#[effect(pure)]
fn pure_add(x: i32, y: i32) -> i32 {
    x + y  // 无副作用
}

// io 效果
#[effect(io)]
fn print_message(msg: &str) {
    println!("{}", msg);  // I/O 效果
}

// mut 效果
#[effect(mut)]
fn increment(counter: &mut i32) {
    *counter += 1;  // 可变状态效果
}

// panic 效果
#[effect(panic)]
fn divide(a: i32, b: i32) -> i32 {
    a / b  // 可能 panic (除以零)
}

// 组合效果
#[effect(io, mut, panic)]
fn complex_operation(data: &mut Vec<i32>) {
    println!("Starting operation");  // io
    data.push(42);  // mut
    let last = data.last().unwrap();  // panic 可能
    println!("Last element: {}", last);  // io
}
```

#### 8.2.3 能力系统语义

能力系统（Capability System）控制对资源的访问：

```rust
// 能力系统语义（概念性）

// 定义能力
trait Capability {}

// 文件系统能力
struct FileSystemCapability;
impl Capability for FileSystemCapability {}

// 网络能力
struct NetworkCapability;
impl Capability for NetworkCapability {}

// 需要特定能力的函数
fn read_file_with_capability(
    _cap: &FileSystemCapability,
    path: &str,
) -> Result<String, std::io::Error> {
    std::fs::read_to_string(path)
}

fn fetch_url_with_capability(
    _cap: &NetworkCapability,
    _url: &str,
) -> Result<String, reqwest::Error> {
    // 需要网络能力
    todo!()
}

// 主程序拥有所有能力
struct MainCapabilities {
    fs: FileSystemCapability,
    net: NetworkCapability,
}

fn main_with_capabilities(caps: &MainCapabilities) {
    let content = read_file_with_capability(&caps.fs, "config.txt");
    // let data = fetch_url_with_capability(&caps.net, "https://example.com");
}

// Rust 中的类型状态实现能力
struct Unprivileged;
struct Privileged;

struct Session<Capability> {
    _cap: std::marker::PhantomData<Capability>,
}

impl Session<Unprivileged> {
    fn login(self, password: &str) -> Option<Session<Privileged>> {
        if password == "secret" {
            Some(Session { _cap: std::marker::PhantomData })
        } else {
            None
        }
    }
}

impl Session<Privileged> {
    fn access_admin_panel(&self) {
        println!("Admin access granted");
    }
}
```

---

## 9. 语义分析工具

### 9.1 静态分析语义

#### 9.1.1 借用检查器语义

借用检查器是 Rust 的核心创新，在编译时验证内存安全：

$$
\text{BorrowCheck} : \text{Program} \to \{ \text{OK}, \text{Error}\langle \text{Message} \rangle \}
$$

```rust
// 借用检查器验证的语义
fn borrow_checker_semantics() {
    let mut x = 5;

    // 规则 1：多个不可变借用允许
    let r1 = &x;
    let r2 = &x;
    println!("{} {}", r1, r2);  // OK

    // 规则 2：不可变和可变借用不能共存
    // let r3 = &mut x;  // 错误：r1 和 r2 仍然活跃

    // r1 和 r2 最后一次使用后，可变借用允许
    let r3 = &mut x;  // OK
    *r3 += 1;

    // 规则 3：同一时间只能有一个可变借用
    // let r4 = &mut x;  // 错误：r3 仍然活跃

    println!("{}", r3);  // r3 最后一次使用

    // 现在可以创建新的借用
    let r4 = &x;  // OK
    println!("{}", r4);
}

// 非词法生命周期（NLL）
fn non_lexical_lifetimes() {
    let mut data = vec![1, 2, 3];

    // 借用只持续到最后一次使用，而非作用域结束
    let x = &data[0];
    println!("{}", x);  // x 最后一次使用

    // 现在可以可变借用
    data.push(4);  // OK，因为 x 不再活跃
}
```

#### 9.1.2 模式匹配穷尽性语义

Rust 编译器检查模式匹配是否穷尽：

```rust
// 穷尽性检查
enum Option<T> {
    Some(T),
    None,
}

fn exhaustive_match(x: Option<i32>) -> i32 {
    match x {
        Some(n) => n,
        None => 0,
    }  // 穷尽，覆盖所有变体
}

// 非穷尽匹配（编译错误）
// fn non_exhaustive_match(x: Option<i32>) -> i32 {
//     match x {
//         Some(n) => n,
//         // 缺少 None 处理
//     }
// }

// 穷尽性检查与守卫
fn match_with_guard(x: Option<i32>) -> i32 {
    match x {
        Some(n) if n > 0 => n,
        Some(n) if n < 0 => -n,
        Some(0) => 0,
        None => 0,
    }
}

// 对于非穷尽守卫，编译器会警告
fn non_exhaustive_guard(x: Option<i32>) -> i32 {
    match x {
        Some(n) if n > 0 => n,
        Some(n) if n <= 0 => -n,
        // 编译器可能无法证明守卫覆盖所有情况
        None => 0,
    }
}

// _ 通配符确保穷尽性
fn wildcard_match(x: Result<i32, String>) -> i32 {
    match x {
        Ok(n) => n,
        _ => 0,  // 通配符匹配所有剩余情况
    }
}
```

#### 9.1.3 常量求值语义

常量求值在编译时执行代码：

```rust
// 常量上下文
const CONST_VALUE: i32 = 42;

// 常量函数
const fn add_const(a: i32, b: i32) -> i32 {
    a + b
}

const SUM: i32 = add_const(10, 20);  // 编译时求值

// 更复杂的常量求值
const fn factorial(n: u64) -> u64 {
    let mut result = 1;
    let mut i = 1;
    while i <= n {
        result *= i;
        i += 1;
    }
    result
}

const FACT_5: u64 = factorial(5);  // 120，编译时计算

// 常量泛型
struct Array<T, const N: usize> {
    data: [T; N],
}

impl<T, const N: usize> Array<T, N> {
    const fn len(&self) -> usize {
        N  // 编译时常量
    }
}

// 静态断言
const _: () = assert!(size_of::<usize>() >= size_of::<u32>(), "usize too small");

use std::mem::size_of;
```

### 9.2 动态分析语义

#### 9.2.1 Miri 语义解释器

Miri 是 Rust 的未定义行为检测工具：

```bash
# 使用 Miri 运行测试
cargo +nightly miri test

# 检查特定文件
cargo +nightly miri run
```

```rust
// Miri 可以检测的未定义行为示例

// 1. 使用已释放内存
// fn use_after_free() {
//     let ptr;
//     {
//         let x = Box::new(42);
//         ptr = &*x as *const i32;
//     }  // x 在此处释放
//     unsafe {
//         println!("{}", *ptr);  // Miri 会报错：使用已释放内存
//     }
// }

// 2. 数据竞争
// fn data_race() {
//     use std::thread;
//     let mut x = 0;
//     let ptr = &mut x as *mut i32;
//
//     thread::spawn(move || unsafe {
//         *ptr = 1;  // Miri 会报错：数据竞争
//     });
//
//     unsafe {
//         *ptr = 2;
//     }
// }

// 3. 无效引用
// fn invalid_reference() {
//     let r;
//     {
//         let x = 5;
//         r = &x;
//     }  // x 在此处失效
//     println!("{}", r);  // Miri 会报错：悬空引用
// }

// 4. 未对齐访问
fn unaligned_access() {
    let mut x = [0u8; 8];
    let ptr = x.as_mut_ptr();
    unsafe {
        // 未对齐的 u64 写入
        // *(ptr.add(1) as *mut u64) = 42;  // Miri 会报错：未对齐访问
    }
}

// Miri 安全代码示例
fn miri_safe_example() {
    let mut v = vec![1, 2, 3];
    let r = &mut v[0];
    *r += 1;
    drop(v);  // OK
}
```

#### 9.2.2 数据竞争检测语义

数据竞争检测确保并发安全：

```rust
// ThreadSanitizer 支持
// RUSTFLAGS="-Z sanitizer=thread" cargo +nightly run

use std::sync::{Arc, Mutex};
use std::thread;

// 正确的并发访问（无数据竞争）
fn no_data_race() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    println!("Count: {}", *counter.lock().unwrap());
}

// 使用原子操作（无数据竞争）
use std::sync::atomic::{AtomicUsize, Ordering};

fn atomic_no_race() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            counter.fetch_add(1, Ordering::Relaxed);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    println!("Count: {}", counter.load(Ordering::Relaxed));
}

// Send 和 Sync trait 确保线程安全
fn thread_safety_traits() {
    // T: Send 表示可以跨线程转移所有权
    // T: Sync 表示可以跨线程共享引用 (&T: Send)

    // Rc 不是 Send 也不是 Sync
    // let rc = std::rc::Rc::new(5);
    // thread::spawn(move || println!("{}", rc));  // 编译错误

    // Arc 是 Send + Sync
    let arc = Arc::new(5);
    let arc2 = Arc::clone(&arc);
    thread::spawn(move || println!("{}", arc2));
}
```

#### 9.2.3 内存泄漏检测语义

内存泄漏检测帮助发现资源管理问题：

```rust
use std::sync::{Arc, Weak};
use std::cell::RefCell;

// 引用循环导致的内存泄漏
#[derive(Debug)]
struct Node {
    value: i32,
    next: Option<Arc<RefCell<Node>>>,
}

fn potential_memory_leak() {
    // 循环引用导致内存无法释放
    let first = Arc::new(RefCell::new(Node { value: 1, next: None }));
    let second = Arc::new(RefCell::new(Node { value: 2, next: None }));

    // 创建循环引用
    first.borrow_mut().next = Some(Arc::clone(&second));
    // second.borrow_mut().next = Some(Arc::clone(&first));  // 循环引用！

    // 此时 first 和 second 的引用计数都是 2
    println!("First refcount: {}", Arc::strong_count(&first));
    println!("Second refcount: {}", Arc::strong_count(&second));

    // 使用 Weak 打破循环
}

// 使用 Weak 避免循环引用
#[derive(Debug)]
struct NodeFixed {
    value: i32,
    parent: Option<Weak<RefCell<NodeFixed>>>,
    children: Vec<Arc<RefCell<NodeFixed>>>,
}

fn no_memory_leak() {
    let root = Arc::new(RefCell::new(NodeFixed {
        value: 0,
        parent: None,
        children: vec![],
    }));

    let child = Arc::new(RefCell::new(NodeFixed {
        value: 1,
        parent: Some(Arc::downgrade(&root)),
        children: vec![],
    }));

    root.borrow_mut().children.push(Arc::clone(&child));

    // 可以访问父节点
    if let Some(parent) = child.borrow().parent.as_ref().and_then(|p| p.upgrade()) {
        println!("Parent value: {}", parent.borrow().value);
    }

    // root 和 child 可以正常释放
}

// Valgrind/Heaptrack 内存分析
// valgrind --tool=memcheck --leak-check=full ./program
// heaptrack ./program
```

---

## 10. 总结与展望

### 10.1 语义框架回顾

本文档建立了一个全面的 Rust 程序设计语义框架，涵盖了以下核心维度：

| 维度 | 核心概念 | 形式化工具 |
|------|---------|-----------|
| **静态 vs 动态** | 类型系统、所有权、生命周期 | 类型判断、分离逻辑 |
| **控制流** | 顺序、条件、循环、跳转 | 操作语义、求值上下文 |
| **数据流** | Copy/Move/Borrow、生命周期 | 分离逻辑、区域演算 |
| **执行模型** | 同步、异步、并发、并行 | 过程演算、π演算 |
| **设计模式** | 创建型、结构型、行为型 | 类型状态、高阶类型 |
| **并发** | 线程、锁、无锁、内存序 | 内存模型、线性逻辑 |
| **异步** | Future、Pin、Waker、执行器 | 效果处理器、延续语义 |
| **Actor** | 消息传递、监督、分布式 | Actor 演算、会话类型 |

### 10.2 统一语义形式

Rust 的核心语义可以用以下统一框架表示：

$$
\text{RustSem} : \text{Program} \times \text{Context} \times \text{Constraints} \to \text{Behavior} \times \text{Guarantees}
$$

其中：

- **Context** 包含类型环境 $\Gamma$ 和生命周期环境 $\Lambda$
- **Constraints** 包含借用约束、生命周期约束、trait 约束
- **Behavior** 描述程序的运行时行为
- **Guarantees** 包括内存安全、类型安全、数据竞争自由

### 10.3 未来发展方向

1. **形式化验证集成**：将 Rust 语义与 Coq/Isabelle 等证明助手集成
2. **异步语义完善**：完整的 async/await 效果系统形式化
3. **unsafe 语义**：unsafe Rust 的严格形式化边界
4. **常量求值**：完整的常量求值语义和编译时计算模型
5. **泛型编程**：高阶类型和关联类型的完整语义

### 10.4 文档组织

本语义框架文档为后续专题文档提供基础：

```
docs/rust-ownership-decidability/
├── 16-program-semantics/
│   ├── 00-semantic-framework.md      # 本框架文档
│   ├── 01-static-semantics.md        # 静态语义深入
│   ├── 02-dynamic-semantics.md       # 动态语义深入
│   ├── 03-concurrent-semantics.md    # 并发语义专题
│   ├── 04-async-semantics.md         # 异步语义专题
│   └── 05-formal-methods.md          # 形式化方法
```

---

## 附录：符号说明

| 符号 | 含义 |
|------|------|
| $\Gamma$ | 类型环境 |
| $\vdash$ | 推导/判断 |
| $\to$ | 小步转换 |
| $\Downarrow$ | 大步求值 |
| $\llbracket \cdot \rrbracket$ | 语义解释函数 |
| $\langle \cdot, \cdot \rangle$ | 配置对 |
| $\sigma$ | 存储/状态 |
| $*$ | 分离合取（分离逻辑） |
| $\mapsto$ | 指向关系 |
| $\forall$ | 全称量词 |
| $\exists$ | 存在量词 |
| $\to^*$ | 多步转换（自反传递闭包） |
| $\mu$ | 最小不动点 |
| $\bot$ | 未定义/无效值 |

---

## 参考文献

1. Harper, R. (2016). *Practical Foundations for Programming Languages*. Cambridge University Press.
2. Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press.
3. O'Hearn, P. W. (2019). *Separation Logic*. Communications of the ACM.
4. Jung, R., et al. (2018). *RustBelt: Securing the Foundations of the Rust Programming Language*. POPL.
5. Dreyer, D., et al. (2010). *Reconciling Scala's Static and Dynamic Type Systems*. PLDI.
6. Boudol, G. (1997). *Typing the Use of Resources in a Concurrent Calculus*. AMAST.
7. Acar, U. A., et al. (2002). *The Failure of theSubject-Observer Pattern*. PPPJ.
