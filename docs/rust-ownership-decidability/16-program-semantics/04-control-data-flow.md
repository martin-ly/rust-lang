# 数据流与控制流分析

## 目录

- [数据流与控制流分析](#数据流与控制流分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 控制流与数据流的关系](#11-控制流与数据流的关系)
    - [1.2 Rust 的所有权对数据流的影响](#12-rust-的所有权对数据流的影响)
    - [1.3 静态分析与动态行为](#13-静态分析与动态行为)
  - [2. 控制流语义](#2-控制流语义)
    - [2.1 顺序控制流](#21-顺序控制流)
      - [2.1.1 语句顺序语义](#211-语句顺序语义)
      - [2.1.2 表达式求值顺序](#212-表达式求值顺序)
      - [2.1.3 副作用排序](#213-副作用排序)
    - [2.2 条件控制流](#22-条件控制流)
      - [2.2.1 if/else 语义](#221-ifelse-语义)
      - [2.2.2 match 语义](#222-match-语义)
      - [2.2.3 穷尽性检查语义](#223-穷尽性检查语义)
    - [2.3 循环控制流](#23-循环控制流)
      - [2.3.1 loop 语义](#231-loop-语义)
      - [2.3.2 while 语义](#232-while-语义)
      - [2.3.3 for 语义（迭代器驱动）](#233-for-语义迭代器驱动)
      - [2.3.4 控制转移（break/continue）](#234-控制转移breakcontinue)
    - [2.4 函数控制流](#24-函数控制流)
      - [2.4.1 函数调用语义](#241-函数调用语义)
      - [2.4.2 返回语义](#242-返回语义)
      - [2.4.3 尾调用优化语义](#243-尾调用优化语义)
    - [2.5 异常控制流（Panic）](#25-异常控制流panic)
      - [2.5.1 panic! 语义](#251-panic-语义)
      - [2.5.2 展开语义](#252-展开语义)
      - [2.5.3 中止语义](#253-中止语义)
      - [2.5.4 恢复语义（catch\_unwind）](#254-恢复语义catch_unwind)
  - [3. 数据流语义](#3-数据流语义)
    - [3.1 值的数据流](#31-值的数据流)
      - [3.1.1 创建-使用-销毁流程](#311-创建-使用-销毁流程)
      - [3.1.2 所有权转移数据流](#312-所有权转移数据流)
      - [3.1.3 借用数据流](#313-借用数据流)
    - [3.2 变量数据流](#32-变量数据流)
      - [3.2.1 定义-使用链](#321-定义-使用链)
      - [3.2.2 活跃变量分析](#322-活跃变量分析)
      - [3.2.3 Reaching Definitions](#323-reaching-definitions)
    - [3.3 类型数据流](#33-类型数据流)
      - [3.3.1 类型推断数据流](#331-类型推断数据流)
      - [3.3.2 泛型单态化数据流](#332-泛型单态化数据流)
      - [3.3.3 Trait 解析数据流](#333-trait-解析数据流)
  - [4. 所有权数据流](#4-所有权数据流)
    - [4.1 所有权转移数据流](#41-所有权转移数据流)
      - [4.1.1 Move 语义数据流](#411-move-语义数据流)
      - [4.1.2 复制数据流（Copy 类型）](#412-复制数据流copy-类型)
      - [4.1.3 线性类型数据流](#413-线性类型数据流)
    - [4.2 借用数据流](#42-借用数据流)
      - [4.2.1 不可变借用流](#421-不可变借用流)
      - [4.2.2 可变借用流](#422-可变借用流)
      - [4.2.3 借用生命周期数据流](#423-借用生命周期数据流)
    - [4.3 生命周期数据流](#43-生命周期数据流)
      - [4.3.1 生命周期参数流](#431-生命周期参数流)
      - [4.3.2 生命周期约束传播](#432-生命周期约束传播)
      - [4.3.3 生命周期推导数据流](#433-生命周期推导数据流)
  - [5. 控制流分析](#5-控制流分析)
    - [5.1 控制流图 (CFG)](#51-控制流图-cfg)
      - [5.1.1 基本块语义](#511-基本块语义)
      - [5.1.2 边和分支语义](#512-边和分支语义)
      - [5.1.3 循环结构识别](#513-循环结构识别)
    - [5.2 到达定义分析](#52-到达定义分析)
      - [5.2.1 定义点追踪](#521-定义点追踪)
      - [5.2.2 使用点识别](#522-使用点识别)
      - [5.2.3 未初始化变量检测](#523-未初始化变量检测)
    - [5.3 活跃性分析](#53-活跃性分析)
      - [5.3.1 变量活跃区间](#531-变量活跃区间)
      - [5.3.2 借用活跃性（NLL）](#532-借用活跃性nll)
      - [5.3.3 资源活跃性](#533-资源活跃性)
  - [6. 数据流分析](#6-数据流分析)
    - [6.1 借用检查数据流](#61-借用检查数据流)
      - [6.1.1 借用创建点](#611-借用创建点)
      - [6.1.2 借用使用点](#612-借用使用点)
      - [6.1.3 借用结束点（NLL）](#613-借用结束点nll)
    - [6.2 初始化分析](#62-初始化分析)
      - [6.2.1 部分初始化](#621-部分初始化)
      - [6.2.2 结构体字段初始化](#622-结构体字段初始化)
      - [6.2.3 数组初始化](#623-数组初始化)
    - [6.3 常量传播](#63-常量传播)
      - [6.3.1 编译时常量求值](#631-编译时常量求值)
      - [6.3.2 常量泛型传播](#632-常量泛型传播)
      - [6.3.3 常量折叠](#633-常量折叠)
  - [7. 并发数据流](#7-并发数据流)
    - [7.1 线程间数据流](#71-线程间数据流)
      - [7.1.1 Send 数据流边界](#711-send-数据流边界)
      - [7.1.2 Sync 数据流边界](#712-sync-数据流边界)
      - [7.1.3 共享状态数据流](#713-共享状态数据流)
    - [7.2 消息传递数据流](#72-消息传递数据流)
      - [7.2.1 通道数据流](#721-通道数据流)
      - [7.2.2 所有权传递](#722-所有权传递)
      - [7.2.3 消息顺序保证](#723-消息顺序保证)
    - [7.3 原子数据流](#73-原子数据流)
      - [7.3.1 原子变量数据流](#731-原子变量数据流)
      - [7.3.2 内存序约束](#732-内存序约束)
      - [7.3.3 happens-before 图](#733-happens-before-图)
  - [8. 异步数据流](#8-异步数据流)
    - [8.1 Future 数据流](#81-future-数据流)
      - [8.1.1 Future 状态数据流](#811-future-状态数据流)
      - [8.1.2 Waker 传播数据流](#812-waker-传播数据流)
      - [8.1.3 执行器数据流](#813-执行器数据流)
    - [8.2 Stream 数据流](#82-stream-数据流)
      - [8.2.1 元素数据流](#821-元素数据流)
      - [8.2.2 背压数据流](#822-背压数据流)
      - [8.2.3 缓冲数据流](#823-缓冲数据流)
    - [8.3 异步状态数据流](#83-异步状态数据流)
      - [8.3.1 状态机状态转换](#831-状态机状态转换)
      - [8.3.2 挂起-恢复数据流](#832-挂起-恢复数据流)
      - [8.3.3 取消数据流](#833-取消数据流)
  - [9. 静态分析技术](#9-静态分析技术)
    - [9.1 借用检查器分析](#91-借用检查器分析)
      - [9.1.1 区域推断](#911-区域推断)
      - [9.1.2 约束生成](#912-约束生成)
      - [9.1.3 约束求解](#913-约束求解)
    - [9.2 类型系统分析](#92-类型系统分析)
      - [9.2.1 类型推断算法](#921-类型推断算法)
      - [9.2.2 Trait 解析](#922-trait-解析)
      - [9.2.3 关联类型求解](#923-关联类型求解)
    - [9.3 lint 分析](#93-lint-分析)
      - [9.3.1 未使用变量检测](#931-未使用变量检测)
      - [9.3.2 未使用导入检测](#932-未使用导入检测)
      - [9.3.3 模式匹配穷尽性](#933-模式匹配穷尽性)
  - [10. 形式化表示](#10-形式化表示)
    - [10.1 控制流形式化](#101-控制流形式化)
      - [10.1.1 操作语义规则](#1011-操作语义规则)
      - [10.1.2 求值上下文](#1012-求值上下文)
      - [10.1.3 规约关系](#1013-规约关系)
    - [10.2 数据流形式化](#102-数据流形式化)
      - [10.2.1 数据流方程](#1021-数据流方程)
      - [10.2.2 不动点求解](#1022-不动点求解)
      - [10.2.3 单调框架](#1023-单调框架)
    - [10.3 类型与效果](#103-类型与效果)
      - [10.3.1 类型判断](#1031-类型判断)
      - [10.3.2 效果系统](#1032-效果系统)
      - [10.3.3 区域类型](#1033-区域类型)
  - [11. 工具与实践](#11-工具与实践)
    - [11.1 编译器分析](#111-编译器分析)
      - [11.1.1 MIR 数据流分析](#1111-mir-数据流分析)
      - [11.1.2 LLVM IR 生成](#1112-llvm-ir-生成)
      - [11.1.3 优化 passes](#1113-优化-passes)
    - [11.2 静态分析工具](#112-静态分析工具)
      - [11.2.1 Clippy 检查](#1121-clippy-检查)
      - [11.2.2 Miri 解释执行](#1122-miri-解释执行)
      - [11.2.3 自定义 lint](#1123-自定义-lint)
    - [11.3 性能分析](#113-性能分析)
      - [11.3.1 火焰图语义](#1131-火焰图语义)
      - [11.3.2 分配追踪](#1132-分配追踪)
      - [11.3.3 缓存分析](#1133-缓存分析)
  - [12. 总结](#12-总结)
    - [12.1 核心概念回顾](#121-核心概念回顾)
    - [12.2 静态分析要点](#122-静态分析要点)
    - [12.3 实践指导](#123-实践指导)
    - [12.4 延伸阅读](#124-延伸阅读)

---

## 1. 引言

### 1.1 控制流与数据流的关系

在程序分析中，**控制流（Control Flow）** 描述程序执行的顺序，而 **数据流（Data Flow）** 描述数据在程序中的传播和变换。
两者相互交织，共同决定了程序的行为。

形式化地，控制流和数据流可以表示为：

$$
\text{Program} = \langle \text{ControlFlow}, \text{DataFlow} \rangle
$$

其中：

- **控制流图（CFG）**：$G = \langle N, E, n_0, n_f \rangle$，节点 $N$ 表示基本块，边 $E$ 表示执行路径
- **数据流图（DFG）**：$D = \langle V, D_e \rangle$，顶点 $V$ 表示值，边 $D_e$ 表示数据依赖

```rust
// 控制流与数据流的交织示例
fn control_data_flow_example(x: i32, y: i32) -> i32 {
    // 数据流：x, y 流入
    let mut sum = 0;                    // 定义点

    // 控制流：条件分支
    if x > 0 {
        // 控制流决定数据流路径
        sum = x + y;                    // 使用点，数据依赖
    } else {
        sum = x - y;                    // 另一条数据流路径
    }

    // 数据流汇聚
    sum *= 2;                           // 使用 sum
    sum                                 // 数据流出
}
```

### 1.2 Rust 的所有权对数据流的影响

Rust 的所有权系统从根本上改变了数据流的语义：

$$
\text{RustDataFlow} = \text{TraditionalDataFlow} \times \text{OwnershipConstraints}
$$

**所有权对数据流的核心影响：**

| 特性 | 传统语言数据流 | Rust 数据流 |
|------|---------------|------------|
| 值传递 | 复制或引用 | Move/Copy/Borrow |
| 别名分析 | 复杂且不确定 | 编译时确定 |
| 资源释放 | 垃圾回收或手动 | RAII + 所有权转移 |
| 并发安全 | 运行时检查 | 编译时静态验证 |

```rust
fn ownership_affects_dataflow() {
    // 所有权转移数据流
    let s1 = String::from("hello");     // s1 获得所有权
    let s2 = s1;                         // 所有权从 s1 转移到 s2
    // println!("{}", s1);              // 错误：s1 已失效，数据流被切断

    // 借用数据流
    let r1 = &s2;                        // 不可变借用创建数据流
    let r2 = &s2;                        // 多个读取数据流允许
    println!("{} {}", r1, r2);

    // 独占借用数据流
    let r3 = &mut s2;                    // 可变借用创建独占数据流
    r3.push_str(" world");
    // println!("{}", r2);              // 错误：与可变数据流冲突
}
```

### 1.3 静态分析与动态行为

Rust 采用**静动分离**的设计哲学：

$$
\text{ProgramAnalysis} = \underbrace{\text{StaticAnalysis}}_{\text{编译时}} + \underbrace{\text{DynamicBehavior}}_{\text{运行时}}
$$

**静态分析保证：**

- 内存安全（无悬垂指针、无数据竞争）
- 类型安全
- 所有权正确性
- 生命周期有效性

**动态行为：**

- 实际的控制流路径
- 内存分配与释放
- 线程调度
- I/O 操作

```rust
// 静态分析 vs 动态行为示例
fn static_vs_dynamic(arr: &[i32]) -> Option<i32> {
    // 静态分析：验证 arr 的引用有效，索引边界检查
    if arr.is_empty() {
        return None;                    // 控制流路径 1
    }

    // 动态行为：实际运行时执行的分支
    let first = arr[0];                  // 数据流：arr[0] -> first
    Some(first * 2)                      // 控制流路径 2
}
```

---

## 2. 控制流语义

### 2.1 顺序控制流

#### 2.1.1 语句顺序语义

顺序执行是最基本的控制流形式，语句按文本顺序执行：

$$
\frac{\langle s_1, \sigma \rangle \to \langle (), \sigma_1 \rangle \quad \langle s_2, \sigma_1 \rangle \to \langle (), \sigma_2 \rangle}{\langle s_1; s_2, \sigma \rangle \to \langle (), \sigma_2 \rangle} \text{ (SEQ)}
$$

```rust
fn sequential_statements() {
    // 语句按顺序执行，状态逐步变换
    let x = 1;              // σ₀ → σ₁, x ↦ 1
    let y = x + 1;          // σ₁ → σ₂, y ↦ 2, 数据依赖 x
    let z = y * 2;          // σ₂ → σ₃, z ↦ 4, 数据依赖 y

    // 副作用按顺序发生
    println!("{}", x);      // 观察 σ₁ 中的 x
    println!("{}", y);      // 观察 σ₂ 中的 y
    println!("{}", z);      // 观察 σ₃ 中的 z
}                           // 最终状态 σ₃
```

#### 2.1.2 表达式求值顺序

Rust 的表达式求值遵循**严格求值**（eager evaluation）策略：

$$
\text{Eval}(e_1 \odot e_2) = \text{let } v_1 = \text{Eval}(e_1) \text{ in } \text{let } v_2 = \text{Eval}(e_2) \text{ in } v_1 \odot v_2
$$

**求值顺序规则：**

| 表达式类型 | 求值顺序 | 示例 |
|-----------|---------|------|
| 函数调用 | 参数从左到右 | `f(a, b, c)` |
| 元组 | 元素从左到右 | `(a, b, c)` |
| 数组 | 元素从左到右 | `[a, b, c]` |
| 结构体 | 字段声明顺序 | `S { a, b }` |
| 赋值 | 先右后左 | `x = y` |

```rust
fn evaluation_order() {
    let mut i = 0;

    // 函数参数从左到右求值
    fn f() -> i32 {
        let mut n = 0;
        std::mem::replace(&mut n, 1)
    }

    // 元组构造
    let t = ({
        let x = f();
        println!("First: {}", x);
        x
    }, {
        let y = f();
        println!("Second: {}", y);
        y
    });
    println!("Tuple: {:?}", t);

    // 赋值表达式：先求值右边
    let mut x = 5;
    x = {
        println!("Right side evaluated");
        10
    };
    println!("x = {}", x);
}
```

#### 2.1.3 副作用排序

Rust 保证副作用的顺序性，这对理解数据流至关重要：

```rust
fn side_effect_ordering() {
    let mut v = vec![];

    // 副作用按顺序发生
    v.push({
        println!("Push 1");
        1
    });
    v.push({
        println!("Push 2");
        2
    });
    v.push({
        println!("Push 3");
        3
    });

    // 借用检查器保证无副作用交错
    let r = &v[0];
    // v.push(4);              // 错误：不能在有引用时修改
    println!("r = {}", r);
    v.push(4);                   // OK: 引用已结束
}
```

### 2.2 条件控制流

#### 2.2.1 if/else 语义

条件分支的形式化语义：

$$
\frac{\langle b, \sigma \rangle \Downarrow \text{true} \quad \langle e_1, \sigma \rangle \Downarrow v}{\langle \text{if } b \{ e_1 \} \text{ else } \{ e_2 \}, \sigma \rangle \Downarrow v}
$$

$$
\frac{\langle b, \sigma \rangle \Downarrow \text{false} \quad \langle e_2, \sigma \rangle \Downarrow v}{\langle \text{if } b \{ e_1 \} \text{ else } \{ e_2 \}, \sigma \rangle \Downarrow v}
$$

```rust
fn if_else_semantics(x: i32) -> i32 {
    // 单一 if
    if x > 0 {
        println!("Positive");
    }

    // if-else
    let sign = if x > 0 {
        1
    } else if x < 0 {
        -1
    } else {
        0
    };

    // if let（模式匹配的条件形式）
    let opt = Some(42);
    let value = if let Some(v) = opt {
        v * 2
    } else {
        0
    };

    sign + value
}
```

#### 2.2.2 match 语义

`match` 是 Rust 最强大的控制流结构，具有穷尽性检查：

$$
\text{match } e \{ p_1 \Rightarrow e_1, \ldots, p_n \Rightarrow e_n \} \equiv
\text{let } v = e \text{ in } \bigcup_{i=1}^{n} \text{if } v \in p_i \text{ then } e_i
$$

```rust
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn match_semantics(msg: Message) {
    match msg {
        // 匹配具体变体
        Message::Quit => {
            println!("Quit");
        }

        // 解构结构体变体
        Message::Move { x, y } => {
            println!("Move to ({}, {})", x, y);
        }

        // 绑定值
        Message::Write(text) => {
            println!("Write: {}", text);
        }

        // 忽略具体值
        Message::ChangeColor(r, g, b) => {
            println!("Color: RGB({}, {}, {})", r, g, b);
        }
    }

    // 使用守卫的条件匹配
    let x = 5;
    match x {
        0 => println!("zero"),
        1..=4 => println!("small"),
        n if n % 2 == 0 => println!("even: {}", n),
        _ => println!("odd: {}", x),
    }
}
```

#### 2.2.3 穷尽性检查语义

Rust 编译器强制要求 `match` 必须穷尽所有可能：

$$
\forall v : T. \exists i. v \in p_i \quad \text{（穷尽性条件）}
$$

```rust
// 穷尽性检查示例
fn exhaustive_checking(opt: Option<i32>) -> i32 {
    // 编译错误：没有处理 None
    // match opt {
    //     Some(v) => v,
    // }

    // 正确：处理所有变体
    match opt {
        Some(v) => v,
        None => 0,
    }
}

// 布尔类型的穷尽性
fn bool_exhaustive(b: bool) -> &'static str {
    match b {
        true => "yes",
        false => "no",
    }
}

// 使用 _ 通配符
fn wildcard_pattern(x: i32) -> &'static str {
    match x {
        0 => "zero",
        1 => "one",
        _ => "other",           // 捕获所有其他情况
    }
}
```

### 2.3 循环控制流

#### 2.3.1 loop 语义

`loop` 创建无限循环，必须通过 `break` 退出：

$$
\text{loop } \{ e \} \equiv \mu L. e; L \quad \text{（不动点语义）}
$$

```rust
fn loop_semantics() -> i32 {
    let mut counter = 0;

    // 无限循环
    loop {
        counter += 1;

        if counter >= 10 {
            break;              // 退出循环
        }
    }

    // 带值的 loop（Rust 特有）
    let result = loop {
        counter += 1;

        if counter > 20 {
            break counter * 2;  // 返回值
        }
    };

    result
}
```

#### 2.3.2 while 语义

`while` 循环的条件在每次迭代前求值：

$$
\text{while } b \{ e \} \equiv \mu W. \text{if } b \{ e; W \} \text{ else } \{ () \}
$$

```rust
fn while_semantics(items: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    while i < items.len() {
        sum += items[i];
        i += 1;
    }

    // while let：模式匹配的条件循环
    let mut iter = items.iter();
    let mut product = 1;
    while let Some(&x) = iter.next() {
        product *= x;
    }

    sum + product
}
```

#### 2.3.3 for 语义（迭代器驱动）

Rust 的 `for` 循环基于迭代器协议：

$$
\text{for } x \text{ in } iter \{ e \} \equiv
\text{let mut } it = iter.into\_iterator(); \\
\text{while let Some}(x) = it.next() \{ e \}
$$

```rust
fn for_semantics() {
    // 范围迭代
    for i in 0..5 {
        println!("{}", i);
    }

    // 包含边界
    for i in 0..=5 {
        println!("{}", i);
    }

    // 迭代集合
    let v = vec![1, 2, 3, 4, 5];
    for item in &v {
        println!("{}", item);
    }

    // 带索引的迭代
    for (index, value) in v.iter().enumerate() {
        println!("{}: {}", index, value);
    }

    // 迭代器适配器（惰性求值）
    let sum: i32 = v.iter()
        .filter(|&&x| x % 2 == 0)
        .map(|x| x * 2)
        .sum();
    println!("Sum: {}", sum);
}
```

#### 2.3.4 控制转移（break/continue）

控制转移语句改变循环的正常执行流：

| 语句 | 语义 | 形式化 |
|------|------|--------|
| `break` | 退出最内层循环 | $\langle \text{break}, \sigma \rangle \to \top$ |
| `break 'label` | 退出标记循环 | $\langle \text{break } \ell, \sigma \rangle \to \langle \ell : \top, \sigma \rangle$ |
| `continue` | 跳过当前迭代 | $\langle \text{continue}, \sigma \rangle \to \text{next}$ |
| `continue 'label` | 继续标记循环 | $\langle \text{continue } \ell, \sigma \rangle \to \langle \ell : \text{next}, \sigma \rangle$ |

```rust
fn control_transfer() {
    // 带标签的循环
    'outer: for i in 0..10 {
        for j in 0..10 {
            if i * j > 50 {
                break 'outer;           // 跳出外层循环
            }
            if j % 2 == 0 {
                continue;               // 跳过偶数 j
            }
            println!("({}, {})", i, j);
        }
    }

    // 带值的 break
    let found = 'search: loop {
        for i in 0..100 {
            if is_target(i) {
                break 'search i;        // 返回找到的值
            }
        }
        break 'search -1;               // 未找到
    };
    println!("Found: {}", found);
}

fn is_target(n: i32) -> bool {
    n == 42
}
```

### 2.4 函数控制流

#### 2.4.1 函数调用语义

函数调用创建新的执行环境：

$$
\frac{\langle e_1, \sigma \rangle \Downarrow v_1 \quad \cdots \quad \langle e_n, \sigma \rangle \Downarrow v_n \quad \langle f(v_1, \ldots, v_n), \sigma \rangle \Downarrow v}{\langle f(e_1, \ldots, e_n), \sigma \rangle \Downarrow v}
$$

```rust
fn function_call_semantics() {
    // 值传递
    let x = 5;
    let result = by_value(x);            // x 被复制（i32 是 Copy）
    println!("x still valid: {}", x);

    // 所有权转移
    let s = String::from("hello");
    takes_ownership(s);                  // s 的所有权转移
    // println!("{}", s);                // 错误：s 已失效

    // 借用传递
    let t = String::from("world");
    borrow(&t);                          // 借用传递
    println!("t still valid: {}", t);    // OK
}

fn by_value(x: i32) -> i32 {
    x * 2
}

fn takes_ownership(s: String) {
    println!("{}", s);
} // s 在此处 drop

fn borrow(s: &String) {
    println!("{}", s);
} // 借用结束，不 drop
```

#### 2.4.2 返回语义

函数返回可能涉及所有权转移或复制：

```rust
fn return_semantics() -> String {
    let s = String::from("created");
    s                                    // 所有权返回给调用者
}

// 多重返回路径
fn multiple_return_paths(x: i32) -> Result<i32, &'static str> {
    if x < 0 {
        return Err("negative");          // 早期返回
    }
    if x == 0 {
        return Ok(0);
    }
    Ok(x * 2)                            // 默认返回
}

// 返回引用（需要显式生命周期）
fn return_reference<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

#### 2.4.3 尾调用优化语义

Rust 目前**不保证**尾调用优化（TCO），但从语义角度可以理解其含义：

$$
\text{tail}(f) \Rightarrow \text{reuse\_frame}(f) \quad \text{（理想语义）}
$$

```rust
// 尾递归形式（Rust 不会优化为循环）
fn tail_recursive_sum(n: i32, acc: i32) -> i32 {
    if n <= 0 {
        acc
    } else {
        tail_recursive_sum(n - 1, acc + n)  // 尾调用位置
    }
}

// 推荐使用循环替代
fn iterative_sum(n: i32) -> i32 {
    let mut sum = 0;
    for i in 1..=n {
        sum += i;
    }
    sum
}

// 尾调用优化的未来（become 关键字提案）
// fn tco_sum(n: i32, acc: i32) -> i32 {
//     if n <= 0 {
//         acc
//     } else {
//         become tco_sum(n - 1, acc + n)  // 显式尾调用
//     }
// }
```

### 2.5 异常控制流（Panic）

#### 2.5.1 panic! 语义

`panic!` 触发不可恢复的错误：

$$
\langle \text{panic!}(msg), \sigma \rangle \to \text{unwind}(\sigma, msg)
$$

```rust
fn panic_semantics(x: i32) -> i32 {
    if x < 0 {
        panic!("Negative value: {}", x);   // 触发 panic
    }
    x * 2
}

// 条件 panic
fn expect_semantics(opt: Option<i32>) -> i32 {
    opt.expect("Value must be present")    // 等价于 match opt { ... }
}

// 断言 panic
fn assert_semantics(x: i32) {
    assert!(x > 0, "x must be positive");
    assert_eq!(x % 2, 0, "x must be even");
}
```

#### 2.5.2 展开语义

Panic 可以展开栈，调用析构函数：

```rust
struct Resource {
    id: i32,
}

impl Drop for Resource {
    fn drop(&mut self) {
        println!("Dropping resource {}", self.id);
    }
}

fn unwinding_semantics() {
    let r1 = Resource { id: 1 };

    {
        let r2 = Resource { id: 2 };

        if true {
            // panic!("Error!");  // r2 先 drop，然后 r1 drop
        }

        // r2 在此处 drop
    }

    // r1 在此处 drop
}
```

#### 2.5.3 中止语义

Panic 可以配置为立即中止（abort），不展开栈：

```toml
# Cargo.toml
[profile.release]
panic = "abort"
```

```rust
// 中止语义：不调用 drop，直接终止进程
// 适用于嵌入式或对二进制大小敏感的场景
```

#### 2.5.4 恢复语义（catch_unwind）

`catch_unwind` 允许捕获 panic：

```rust
use std::panic;

fn catch_unwind_semantics() {
    let result = panic::catch_unwind(|| {
        println!("In closure");
        if true {
            panic!("Caught panic!");
        }
        42
    });

    match result {
        Ok(value) => println!("Success: {}", value),
        Err(_) => println!("Panic caught!"),
    }
}

// 边界安全：跨 FFI 边界
catch_unwind_semantics();
```

---

## 3. 数据流语义

### 3.1 值的数据流

#### 3.1.1 创建-使用-销毁流程

值在 Rust 中经历完整的数据流生命周期：

$$
\text{ValueLifecycle} : \text{Create} \to \text{Use}^* \to \text{Drop}
$$

```rust
fn value_lifecycle() {
    // 1. 创建（Create）
    let s = String::from("hello");

    // 2. 使用（Use）
    println!("{}", s);
    let len = s.len();
    println!("Length: {}", len);

    // 3. 销毁（Drop）- 隐式调用
} // s 在此处 drop

// 显式控制生命周期
fn explicit_lifecycle() {
    let s = String::from("data");

    {
        let r = &s;              // 借用开始
        println!("{}", r);       // 使用借用
    }                            // 借用结束

    drop(s);                     // 显式销毁
    // println!("{}", s);        // 错误：s 已销毁
}
```

#### 3.1.2 所有权转移数据流

所有权转移创建单向数据流：

$$
\text{Own}(x, T) \xrightarrow{\text{move}} \text{Own}(y, T) \land \neg \text{Own}(x, T)
$$

```rust
fn ownership_transfer_flow() {
    // 创建
    let a = vec![1, 2, 3];

    // 转移 1: a → b
    let b = a;
    // a 已失效，数据流单向

    // 转移 2: b → c
    let c = b;

    // 转移 3: c → 函数
    consume(c);
    // c 已失效
}

fn consume(v: Vec<i32>) {
    println!("{:?}", v);
} // v 在此处 drop
```

#### 3.1.3 借用数据流

借用创建临时数据流，不改变所有权：

$$
\text{Own}(x, T) \Rightarrow \text{Borrow}(r, \&T) \land \text{Own}(x, T) \text{ （temporarily restricted）}
$$

```rust
fn borrow_flow() {
    let data = vec![1, 2, 3, 4, 5];

    // 不可变借用：允许多个
    let r1 = &data;              // 借用 1
    let r2 = &data;              // 借用 2
    println!("{} {}", r1[0], r2[0]);

    // 借用生命周期结束

    // 可变借用：独占
    let r3 = &mut data;          // 独占借用
    r3.push(6);

    // 借用结束

    // 所有权可以继续使用
    println!("{:?}", data);
}
```

### 3.2 变量数据流

#### 3.2.1 定义-使用链

**定义-使用链（Definition-Use Chain）** 追踪变量的定义和使用点：

$$
\text{DU-Chain}(v) = \{ (d, u) \mid d \text{ 定义 } v, u \text{ 使用 } v \}
$$

```rust
fn du_chain_example() {
    let x = 5;                   // D1: 定义 x
    let y = x + 1;               // U1: 使用 x, D2: 定义 y
    let z = x * y;               // U2: 使用 x, U3: 使用 y, D3: 定义 z
    println!("{}", z);           // U4: 使用 z

    // 控制流敏感的分析
    let mut w = 0;               // D4: 定义 w
    if y > 5 {                   // U5: 使用 y
        w = 10;                  // D5: 重新定义 w
    } else {
        w = 20;                  // D6: 重新定义 w
    }
    println!("{}", w);           // U6: 使用 w（来自 D5 或 D6）
}
```

#### 3.2.2 活跃变量分析

**活跃变量分析（Live Variable Analysis）** 确定变量在哪些程序点是活跃的：

$$
\text{Live}(v, p) \iff \exists \text{ 路径 } p \leadsto p' \text{ 使得 } v \text{ 在 } p' \text{ 被使用}
$$

```rust
fn live_variable_analysis() {
    let a = 1;                   // a 活跃
    let b = 2;                   // a, b 活跃

    let c = a + b;               // c 活跃（a, b 在此后死亡）

    {
        let d = c * 2;           // d 活跃
        println!("{}", d);       // d 使用后死亡
    }

    // c 仍活跃
    let e = c + 1;               // e 活跃
    println!("{}", e);           // e 使用后死亡
}
```

#### 3.2.3 Reaching Definitions

**到达定义分析（Reaching Definitions）** 确定哪些定义可能到达每个使用点：

$$
\text{RD}(p) = \{ d \mid d \text{ 定义变量 } v \text{ 且存在路径 } d \leadsto p \text{ 上无其他 } v \text{ 的定义} \}
$$

```rust
fn reaching_definitions() {
    let mut x = 1;               // RD1

    if condition() {
        x = 2;                   // RD2
    } else {
        x = 3;                   // RD3
    }

    // 此处 x 的到达定义是 {RD2, RD3}
    use_value(x);

    x = 4;                       // RD4
    // 此处 x 的到达定义是 {RD4}
    use_value(x);
}

fn condition() -> bool {
    true
}

fn use_value(_x: i32) {}
```

### 3.3 类型数据流

#### 3.3.1 类型推断数据流

Rust 的类型推断是双向的，信息从表达式和期望类型双向流动：

$$
\Gamma \vdash e : \tau \quad \text{（类型从环境流向表达式）} \\
e \uparrow \tau \dashv \Gamma \quad \text{（类型从期望流向表达式）}
$$

```rust
fn type_inference_flow() {
    // 自下而上推断
    let x = 5;                   // 推断为 i32
    let y = "hello";             // 推断为 &'static str
    let z = vec![1, 2, 3];       // 推断为 Vec<i32>

    // 上下文敏感推断
    let a: i64 = 5;              // 显式类型约束
    let b = a + 1;               // 推断为 i64

    // 泛型类型推断
    let iter = [1, 2, 3].iter(); // 推断为 Iter<i32>
    let sum: i32 = iter.sum();   // 上下文影响推断
}

// 通用类型推断
fn generic_inference<T>(x: T) -> T {
    x
}

fn use_generic() {
    let result = generic_inference(42);        // T = i32
    let result2 = generic_inference("hello");  // T = &'static str
}
```

#### 3.3.2 泛型单态化数据流

泛型代码在编译时单态化，为每种类型生成专用代码：

$$
\text{Monomorphize}(f\langle T \rangle, \tau) \to f_{\tau}
$$

```rust
// 泛型定义
fn generic_id<T>(x: T) -> T {
    x
}

// 编译器生成：
// fn generic_id_i32(x: i32) -> i32 { x }
// fn generic_id_f64(x: f64) -> f64 { x }
// fn generic_id_string(x: String) -> String { x }

fn monomorphization_flow() {
    let a = generic_id(42i32);       // 使用 generic_id_i32
    let b = generic_id(3.14f64);     // 使用 generic_id_f64
    let c = generic_id(String::new()); // 使用 generic_id_string
}

// 结构体泛型单态化
struct Container<T> {
    value: T,
}

// Container<i32>, Container<String> 等是不同类型
```

#### 3.3.3 Trait 解析数据流

Trait 解析确定调用哪个实现：

$$
\Gamma \vdash \text{impl } Trait \text{ for } T \land e : T \Rightarrow e.\text{method}() \to \text{impl}(T)
$$

```rust
trait Compute {
    fn compute(&self) -> i32;
}

struct A;
struct B;

impl Compute for A {
    fn compute(&self) -> i32 { 1 }
}

impl Compute for B {
    fn compute(&self) -> i32 { 2 }
}

// 静态分发
fn static_dispatch<T: Compute>(x: T) -> i32 {
    x.compute()                  // 编译时确定调用哪个实现
}

// 动态分发
fn dynamic_dispatch(x: &dyn Compute) -> i32 {
    x.compute()                  // 运行时通过 vtable 调用
}

fn trait_resolution_flow() {
    let a = A;
    let b = B;

    let r1 = static_dispatch(a);  // 解析为 A::compute
    let r2 = static_dispatch(b);  // 解析为 B::compute

    let r3 = dynamic_dispatch(&A); // 运行时解析
    let r4 = dynamic_dispatch(&B);
}
```

---

## 4. 所有权数据流

### 4.1 所有权转移数据流

#### 4.1.1 Move 语义数据流

Move 语义是 Rust 所有权系统的核心：

$$
\frac{x : T \quad \neg \text{Copy}(T)}{\langle \text{let } y = x, \sigma \rangle \to \langle (), \sigma[y \mapsto \sigma(x)][x \mapsto \bot] \rangle}
$$

```rust
fn move_semantics_flow() {
    // 堆分配类型的所有权转移
    let s1 = String::from("hello");
    let s2 = s1;                      // s1 移动到 s2
    // println!("{}", s1);            // 错误：s1 已失效

    // 函数参数转移
    let v = vec![1, 2, 3];
    let v = take_and_return(v);       // v 移动进函数，再移出

    // 返回值转移
    let s = create_string();          // 所有权从函数转移到 s
    consume(s);                       // 所有权转移到 consume
}                                     // 无需 drop s

fn take_and_return(v: Vec<i32>) -> Vec<i32> {
    v                                   // 所有权返回
}

fn create_string() -> String {
    String::from("created")
}

fn consume(s: String) {
    println!("{}", s);
} // s 在此处 drop
```

#### 4.1.2 复制数据流（Copy 类型）

Copy 类型按位复制，不转移所有权：

$$
\frac{x : T \quad \text{Copy}(T)}{\langle \text{let } y = x, \sigma \rangle \to \langle (), \sigma[y \mapsto \sigma(x)] \rangle}
$$

```rust
fn copy_semantics_flow() {
    // 标量类型是 Copy
    let x = 5;
    let y = x;                        // x 被复制到 y
    println!("{} {}", x, y);          // 两者都可用

    // 自定义 Copy 类型
    #[derive(Copy, Clone)]
    struct Point {
        x: f64,
        y: f64,
    }

    let p1 = Point { x: 1.0, y: 2.0 };
    let p2 = p1;                      // p1 被复制
    let p3 = p1;                      // p1 仍可用

    println!("{:?} {:?} {:?}", p1.x, p2.x, p3.x);
}

// 包含引用的类型不能是 Copy
// #[derive(Copy, Clone)]          // 错误
struct Wrapper<'a> {
    data: &'a str,
}
```

#### 4.1.3 线性类型数据流

Rust 的所有权系统实现了线性类型（Linear Types），要求值必须被使用且只能使用一次：

$$
\forall x : T. \text{UseCount}(x) = 1 \quad \text{（线性约束）}
$$

```rust
// 线性类型语义
fn linear_type_semantics() {
    let resource = acquire_resource();

    use_resource(resource);           // 必须使用

    // 不能使用两次
    // use_resource(resource);        // 错误：resource 已移动
}

struct Resource {
    id: u32,
}

fn acquire_resource() -> Resource {
    Resource { id: 1 }
}

fn use_resource(r: Resource) -> Resource {
    println!("Using resource {}", r.id);
    r                                    // 返回以继续线性链
}

// 必须使用返回值
fn must_use_result() {
    let r = acquire_resource();
    let r = use_resource(r);          // 使用返回值
    release_resource(r);
}

fn release_resource(_r: Resource) {
    println!("Resource released");
}
```

### 4.2 借用数据流

#### 4.2.1 不可变借用流

不可变借用创建读取数据流：

$$
\frac{\Gamma \vdash x : T}{\Gamma \vdash \&x : \&T} \text{ (IMM-BORROW)}
$$

```rust
fn immutable_borrow_flow() {
    let data = vec![1, 2, 3, 4, 5];

    // 创建多个不可变借用
    let r1 = &data;                   // 借用 1
    let r2 = &data;                   // 借用 2
    let r3 = &data;                   // 借用 3

    // 所有借用同时有效
    println!("{} {} {}", r1.len(), r2[0], r3.is_empty());

    // 借用生命周期结束

    // 原始值仍然可用
    println!("{:?}", data);
}

// 函数中的借用
fn borrow_in_function(v: &[i32]) -> i32 {
    v.iter().sum()                    // 借用数据流通过参数传递
}

// 返回借用
fn return_borrow<'a>(v: &'a [i32]) -> &'a i32 {
    &v[0]                             // 借用数据流通过返回值延续
}
```

#### 4.2.2 可变借用流

可变借用创建独占写入数据流：

$$
\frac{\Gamma \vdash x : T \quad \text{mutable}(x)}{\Gamma \vdash \&\text{mut } x : \&\text{mut } T} \text{ (MUT-BORROW)}
$$

```rust
fn mutable_borrow_flow() {
    let mut data = vec![1, 2, 3];

    // 创建可变借用
    let r1 = &mut data;
    r1.push(4);                       // 通过借用修改

    // 不能创建其他借用
    // let r2 = &data;                // 错误：与可变借用冲突

    // 第一个借用生命周期结束

    // 现在可以创建新的借用
    let r3 = &mut data;
    r3.push(5);

    // r3 结束后

    // 所有权恢复
    println!("{:?}", data);
}

// 可变借用链
fn mutable_borrow_chain(v: &mut Vec<i32>) {
    v.push(1);                        // 第一次修改

    let r = &mut *v;                  // 重新借用
    r.push(2);                        // 通过新借用修改

    // r 结束后

    v.push(3);                        // 继续使用原始借用
}
```

#### 4.2.3 借用生命周期数据流

借用生命周期决定了数据流的活跃区间：

```rust
fn borrow_lifetime_flow() {
    let x = String::from("outer");
    let result;

    {
        let y = String::from("inner");

        // result 借用 y
        result = &y;                  // 错误：y 生命周期不够长
        // result = &x;               // OK: x 生命周期足够

        println!("{}", result);
    }                                 // y 在此处失效

    // println!("{}", result);        // result 可能指向失效内存
}

// 显式生命周期标注
fn explicit_lifetime_flow<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 不同生命周期
fn different_lifetimes<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where
    'b: 'a,                           // 'b 包含 'a
{
    x
}
```

### 4.3 生命周期数据流

#### 4.3.1 生命周期参数流

生命周期参数在泛型代码中传播：

$$
\forall 'a, 'b. \frac{'a \subseteq 'b}{\&'a T \text{ 可以转换为 } \&'b T}
$$

```rust
// 生命周期参数在 trait 中传播
trait Parser<'a> {
    type Output;
    fn parse(&self, input: &'a str) -> Option<Self::Output>;
}

struct StrParser;

impl<'a> Parser<'a> for StrParser {
    type Output = &'a str;

    fn parse(&self, input: &'a str) -> Option<&'a str> {
        Some(input)
    }
}

// 生命周期在结构体中传播
struct Context<'a> {
    data: &'a str,
}

impl<'a> Context<'a> {
    fn new(data: &'a str) -> Self {
        Context { data }
    }

    fn get_data(&self) -> &'a str {
        self.data
    }
}

fn lifetime_propagation() {
    let data = String::from("hello");
    let ctx = Context::new(&data);
    let result = ctx.get_data();
    println!("{}", result);
}                                     // data 在 ctx 和 result 之后失效
```

#### 4.3.2 生命周期约束传播

生命周期约束通过 trait bound 传播：

```rust
// 生命周期约束
fn lifetime_constraint<'a, T>(x: &'a T) -> &'a T
where
    T: 'a,                            // T 至少存活 'a
{
    x
}

// 复杂的生命周期关系
fn complex_lifetimes<'a, 'b, T>(
    x: &'a T,
    y: &'b T,
) -> &'a T
where
    T: 'a + 'b,
    'b: 'a,                           // 'b 包含 'a
{
    if true { x } else { y }
}

// 生命周期在泛型结构体中
struct Container<'a, T: 'a> {
    data: &'a T,
}

// 自引用结构体的生命周期
struct SelfReferential<'a> {
    data: String,
    // ptr: &'a str,                  // 无法安全地指向 data
}
```

#### 4.3.3 生命周期推导数据流

编译器通过生命周期省略规则自动推导：

```rust
// 省略规则 1：每个引用参数获得独立生命周期
fn first_rule(s: &str) -> &str {     // 等价于：fn first_rule<'a>(s: &'a str) -> &'a str
    s
}

// 省略规则 2：只有一个输入生命周期时，所有输出使用它
fn second_rule(x: &str, y: &str) -> &str {  // 错误：无法推导
    x
}

// 正确写法
fn second_rule_explicit<'a>(x: &'a str, _y: &str) -> &'a str {
    x
}

// 省略规则 3：&self 或 &mut self 时，输出生命周期与 self 相同
struct MyStruct;

impl MyStruct {
    fn method(&self) -> &str {        // 等价于：fn method<'a>(&'a self) -> &'a str
        "result"
    }
}

// 复杂推导示例
fn complex_elision(x: &(u32, u32)) -> &u32 {  // 推导为：fn complex_elision<'a>(x: &'a (u32, u32)) -> &'a u32
    &x.0
}
```

---

## 5. 控制流分析

### 5.1 控制流图 (CFG)

#### 5.1.1 基本块语义

**基本块（Basic Block）** 是最大连续语句序列，只有一个入口和一个出口：

$$
\text{BasicBlock} = \langle \text{instructions} : [\text{Instr}], \text{terminator} : \text{Term} \rangle
$$

```rust
// 源代码
fn basic_block_example(x: i32, y: i32) -> i32 {
    let a = x + y;                    // BB0: 开始
    let b = a * 2;

    if b > 10 {                       // BB0: 终止（条件分支）
        let c = b - 10;               // BB1: then
        c * 2                         // BB1: 终止（返回）
    } else {
        let d = b + 10;               // BB2: else
        d * 3                         // BB2: 终止（返回）
    }
}                                     // BB3: 汇合点

// 对应的控制流图结构：
//     BB0
//    /   \
//  BB1   BB2
//    \   /
//     BB3
```

#### 5.1.2 边和分支语义

CFG 的边表示可能的执行路径：

```rust
fn branch_edges(x: i32) {
    // 无条件边
    let a = 1;                        // BB0
    let b = 2;                        // BB0
                                      // BB0 → BB1 (无条件)

    // 条件边
    if x > 0 {                        // BB1
        // BB1 → BB2 (条件: true)
        println!("positive");
    } else {
        // BB1 → BB3 (条件: false)
        println!("non-positive");
    }
                                      // BB2 → BB4, BB3 → BB4

    // 汇合
    println!("end");                  // BB4
}

// 循环边
fn loop_edges() {
    let mut i = 0;                    // BB0
                                      // BB0 → BB1
    while i < 10 {                    // BB1 (条件)
        // BB1 → BB2 (条件: true)
        println!("{}", i);
        i += 1;
                                      // BB2 → BB1 (回边)
    }
    // BB1 → BB3 (条件: false)
    println!("done");                 // BB3
}
```

#### 5.1.3 循环结构识别

识别循环结构对分析至关重要：

| 循环类型 | 结构特征 | 示例 |
|---------|---------|------|
| 简单循环 | 单入口，回边到入口 | `loop {}` |
| while 循环 | 条件在入口 | `while cond {}` |
| for 循环 | 迭代器驱动 | `for x in iter {}` |
| 嵌套循环 | 循环内的循环 | 外层 + 内层 |

```rust
fn loop_structure_analysis() {
    // 简单循环
    'outer: loop {
        // 内层循环
        for i in 0..10 {
            if i == 5 {
                continue 'outer;     // 跳转到外层循环
            }
        }
        break;
    }

    // 嵌套循环分析
    for i in 0..3 {                   // 外层循环头
        for j in 0..3 {               // 内层循环头
            println!("{}, {}", i, j);
        }                             // 内层循环回边
    }                                 // 外层循环回边
}
```

### 5.2 到达定义分析

#### 5.2.1 定义点追踪

到达定义分析追踪变量定义的流动：

```rust
fn reaching_definitions_analysis() {
    let mut x = 1;                    // D1: x = 1

    if condition() {
        x = 2;                        // D2: x = 2
    } else {
        x = 3;                        // D3: x = 3
    }

    // 此处 x 的到达定义是 {D2, D3}
    println!("{}", x);

    x = 4;                            // D4: x = 4

    // 此处 x 的到达定义是 {D4}
    println!("{}", x);
}

fn condition() -> bool {
    true
}
```

#### 5.2.2 使用点识别

识别变量在何处被使用：

```rust
fn use_point_identification() {
    let x = 5;                        // D1
    let y = x + 1;                    // U1: 使用 x
    let z = x * y;                    // U2: 使用 x, U3: 使用 y

    println!("{} {} {}", x, y, z);    // U4, U5, U6

    // 借用也是使用
    let r = &x;                       // U7: 使用 x
    println!("{}", r);                // 通过借用使用
}
```

#### 5.2.3 未初始化变量检测

编译器使用到达定义分析检测未初始化变量：

```rust
fn uninitialized_variable_detection() {
    let x: i32;

    if condition() {
        x = 5;
    }

    // 错误：x 可能未初始化
    // println!("{}", x);

    // 必须覆盖所有路径
    let y: i32;
    if condition() {
        y = 1;
    } else {
        y = 2;
    }
    println!("{}", y);                // OK: y 总是已初始化
}

// 部分初始化
fn partial_initialization() {
    let mut p: Point;
    p.x = 1.0;                        // 部分初始化
    // println!("{}", p.y);           // 错误：y 未初始化
    p.y = 2.0;                        // 完成初始化
    println!("{}, {}", p.x, p.y);     // OK
}

struct Point {
    x: f64,
    y: f64,
}
```

### 5.3 活跃性分析

#### 5.3.1 变量活跃区间

活跃性分析确定变量的活跃区间：

$$
\text{Live}(v, p) \iff \exists \text{ 路径 } p \leadsto \text{exit} \text{ 使得 } v \text{ 被使用而不被重新定义}
$$

```rust
fn variable_liveness() {
    let a = 1;                        // a 活跃开始
    let b = a + 1;                    // b 活跃开始，a 活跃结束
    let c = b + 1;                    // c 活跃开始，b 活跃结束
    println!("{}", c);                // c 活跃结束
}                                     // 无活跃变量

fn conditional_liveness(x: i32) {
    let a = 1;                        // a 活跃
    let mut b = 2;                    // a, b 活跃

    if x > 0 {
        b = a;                        // a 活跃，b 活跃（重新定义）
    }

    println!("{}", b);                // b 活跃
}                                     // 无活跃变量
```

#### 5.3.2 借用活跃性（NLL）

非词法生命周期（NLL）使借用活跃性更精确：

```rust
fn nll_liveness() {
    let mut s = String::from("hello");

    // 借用 s
    let r = &s;
    println!("{}", r);                // 最后一次使用 r

    // NLL: r 在此处死亡，即使仍在作用域内

    // 现在可以可变借用
    let r_mut = &mut s;
    r_mut.push_str(" world");

    // r_mut 死亡

    // 可以继续使用 s
    println!("{}", s);
}

// 传统词法生命周期会失败
fn lexical_vs_nll() {
    let mut v = vec![1, 2, 3];

    let first = &v[0];                // 借用开始
    println!("{}", first);            // 最后一次使用

    // NLL 允许此处修改
    v.push(4);

    // 如果再次使用 first，会导致错误
    // println!("{}", first);          // 错误：借用已失效
}
```

#### 5.3.3 资源活跃性

资源的活跃性影响 Drop 调用时机：

```rust
fn resource_liveness() {
    let file = File::open("data.txt"); // 资源活跃开始

    // 使用 file
    process_file(&file);

    // 资源活跃结束，drop 被调用
} // file 在此处 drop

fn early_drop() {
    let file = File::open("data.txt");
    process_file(&file);
    drop(file);                        // 显式提前 drop

    // file 已不活跃
    other_work();
}

fn conditional_drop() {
    let maybe_file: Option<File>;

    if condition() {
        maybe_file = Some(File::open("a.txt"));
    } else {
        maybe_file = None;
    }

    // maybe_file 活跃
    if let Some(ref f) = maybe_file {
        process_file(f);
    }

} // maybe_file 在此处 drop（如果是 Some）

struct File;
impl Drop for File {
    fn drop(&mut self) {
        println!("File closed");
    }
}
fn process_file(_: &File) {}
fn other_work() {}
fn condition() -> bool { true }
```

---

## 6. 数据流分析

### 6.1 借用检查数据流

#### 6.1.1 借用创建点

追踪借用的创建和使用：

```rust
fn borrow_creation_points() {
    let data = vec![1, 2, 3];

    // 借用创建点 1
    let r1 = &data;                   // 不可变借用创建

    // 借用创建点 2
    let r2 = &data[..2];              // 切片借用创建

    // 使用借用
    println!("{} {}", r1[0], r2.len());

    // 借用生命周期结束

    // 新的借用创建点
    let r3 = &mut data;               // 可变借用创建
    r3.push(4);
}
```

#### 6.1.2 借用使用点

```rust
fn borrow_use_points() {
    let mut data = String::from("hello");

    let r1 = &data;                   // 借用创建

    // 使用点 1：直接解引用
    let len = r1.len();               // 隐式解引用

    // 使用点 2：显式解引用
    let first = (*r1).chars().next();

    // 使用点 3：模式匹配
    match r1 {
        s if s.len() > 0 => println!("Non-empty"),
        _ => println!("Empty"),
    }

    // 使用点 4：作为参数传递
    print_string(r1);

    // 使用点 5：重新借用
    let r2: &str = &r1[..];
    println!("{}", r2);
}

fn print_string(s: &str) {
    println!("{}", s);
}
```

#### 6.1.3 借用结束点（NLL）

非词法生命周期确定借用的精确结束点：

```rust
fn borrow_end_points() {
    let mut data = vec![1, 2, 3];

    // 借用开始
    let r = &data[0];
    let x = *r;                       // 使用 r
    // r 在此处结束（NLL）

    // 可以修改 data
    data.push(4);

    // 传统词法生命周期下，r 会在作用域结束时才失效
}

// 复杂 NLL 示例
fn complex_nll() {
    let mut s = String::from("hello");

    let r1 = &s;
    let r2 = &s;
    let len = r1.len();               // 最后一次使用 r1
    let cap = r2.capacity();          // 最后一次使用 r2
    // r1 和 r2 都结束于 NLL

    // 现在可以可变借用
    let r3 = &mut s;
    r3.push_str(" world");
}
```

### 6.2 初始化分析

#### 6.2.1 部分初始化

Rust 支持变量的部分初始化：

```rust
fn partial_initialization() {
    let mut x: (i32, i32);

    x.0 = 1;                          // 部分初始化 x.0
    // println!("{:?}", x);           // 错误：x.1 未初始化

    x.1 = 2;                          // 部分初始化 x.1
    println!("{:?}", x);              // OK: x 完全初始化
}

// 部分移动
fn partial_move() {
    let t = (String::from("hello"), String::from("world"));

    let s1 = t.0;                     // 移动 t.0
    // println!("{}", t.0);           // 错误：t.0 已移动
    println!("{}", t.1);              // OK: t.1 仍有效

    // t 部分失效，不能再整体使用
    // let t2 = t;                    // 错误：t 已部分移动
}
```

#### 6.2.2 结构体字段初始化

```rust
struct Point3D {
    x: f64,
    y: f64,
    z: f64,
}

fn struct_field_initialization() {
    let mut p: Point3D;

    // 顺序初始化
    p.x = 1.0;
    p.y = 2.0;
    p.z = 3.0;

    println!("{:?}", p.x);

    // 函数式更新语法
    let p2 = Point3D { x: 0.0, ..p }; // 使用 p 的 y, z
}

// 通过函数初始化
fn init_struct() -> Point3D {
    Point3D {
        x: 1.0,
        y: 2.0,
        z: 3.0,
    }
}

// 部分初始化后使用
fn partial_struct_use() {
    let mut p: Point3D;

    p.x = 1.0;
    p.y = 2.0;

    // 可以访问已初始化字段
    println!("x: {}, y: {}", p.x, p.y);

    p.z = 3.0;                        // 完成初始化
}
```

#### 6.2.3 数组初始化

```rust
fn array_initialization() {
    // 完全初始化
    let arr1 = [1, 2, 3, 4, 5];

    // 重复值初始化
    let arr2 = [0; 100];              // 100 个 0

    // 部分初始化（不稳定特性）
    // let mut arr: [i32; 5];
    // arr[0] = 1;
    // arr[1] = 2;
    // 需要完整初始化后才能使用

    // 使用 MaybeUninit 进行部分初始化
    use std::mem::MaybeUninit;

    let mut arr: [MaybeUninit<i32>; 5] = unsafe {
        MaybeUninit::uninit().assume_init()
    };

    arr[0] = MaybeUninit::new(1);
    arr[1] = MaybeUninit::new(2);

    // 安全地提取初始化的值
    let val0 = unsafe { arr[0].assume_init_read() };
    println!("{}", val0);
}
```

### 6.3 常量传播

#### 6.3.1 编译时常量求值

Rust 的常量求值器在编译时执行计算：

```rust
// const 求值
const ARRAY_SIZE: usize = 10;
const DOUBLE_SIZE: usize = ARRAY_SIZE * 2;

// 常量函数
const fn factorial(n: u64) -> u64 {
    let mut result = 1;
    let mut i = 2;
    while i <= n {
        result *= i;
        i += 1;
    }
    result
}

const FACT_5: u64 = factorial(5);     // 编译时计算

fn const_evaluation() {
    let arr = [0; ARRAY_SIZE];
    println!("Array size: {}", arr.len());
    println!("5! = {}", FACT_5);
}

// 复杂常量计算
const fn fibonacci(n: u64) -> u64 {
    if n <= 1 {
        n
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}

const FIB_10: u64 = fibonacci(10);
```

#### 6.3.2 常量泛型传播

常量泛型允许类型参数化为常量：

```rust
// 常量泛型结构体
struct Array<T, const N: usize> {
    data: [T; N],
}

impl<T, const N: usize> Array<T, N> {
    fn new() -> Self
    where
        T: Default + Copy,
    {
        Array {
            data: [T::default(); N],
        }
    }

    const fn len(&self) -> usize {
        N
    }
}

fn const_generics_propagation() {
    let arr1: Array<i32, 10> = Array::new();
    let arr2: Array<i32, 20> = Array::new();

    println!("arr1 len: {}", arr1.len());
    println!("arr2 len: {}", arr2.len());

    // 不同 N 是不同的类型
    // arr1 = arr2;                     // 错误：类型不匹配
}

// 常量表达式
fn const_expression<const N: usize>() -> [u8; N * 2] {
    [0; N * 2]
}

// 条件常量泛型（不稳定）
// impl<T, const N: usize> Array<T, N> where N > 0 {
//     fn first(&self) -> Option<&T> {
//         Some(&self.data[0])
//     }
// }
```

#### 6.3.3 常量折叠

编译器自动进行常量表达式折叠：

```rust
fn constant_folding() {
    // 编译时折叠
    let x = 2 + 3;                    // 折叠为 5
    let y = 10 * 5 + 3;               // 折叠为 53

    // 条件折叠
    if 1 + 1 == 2 {                   // 编译时确定为 true
        println!("Math works!");
    }

    // 数组长度折叠
    let arr = [0; 5 * 2];             // 折叠为 [0; 10]

    // 位操作折叠
    let flags = 0b1010 & 0b1100;      // 折叠为 0b1000 (8)
}

// 优化后的代码等价于：
fn constant_folding_optimized() {
    let x = 5;
    let y = 53;

    println!("Math works!");

    let arr = [0; 10];
    let flags = 8;
}
```

---

## 7. 并发数据流

### 7.1 线程间数据流

#### 7.1.1 Send 数据流边界

`Send` trait 标记可以安全跨线程传递所有权的类型：

$$
\text{Send}(T) \iff \forall t_1, t_2. \text{transfer}(T, t_1 \to t_2) \text{ 是安全的}
$$

```rust
fn send_data_flow() {
    // Send 类型可以跨线程移动
    let s = String::from("hello");

    std::thread::spawn(move || {
        // s 的所有权移动到新线程
        println!("{}", s);
    }).join().unwrap();

    // !Send 类型不能跨线程
    // let rc = std::rc::Rc::new(5);
    // std::thread::spawn(move || {
    //     println!("{}", rc);          // 错误：Rc 不是 Send
    // });
}

// 自定义 Send 类型
struct MySendType {
    data: Vec<i32>,
}

unsafe impl Send for MySendType {}
```

#### 7.1.2 Sync 数据流边界

`Sync` trait 标记可以安全跨线程共享引用的类型：

$$
\text{Sync}(T) \iff \&T : \text{Send}
$$

```rust
fn sync_data_flow() {
    // Sync 类型可以跨线程共享
    let data = vec![1, 2, 3];

    std::thread::scope(|s| {
        s.spawn(|| {
            println!("{:?}", &data);  // 共享引用
        });
        s.spawn(|| {
            println!("{:?}", &data);  // 同时共享引用
        });
    });

    // !Sync 类型不能跨线程共享
    // let cell = std::cell::RefCell::new(5);
    // std::thread::scope(|s| {
    //     s.spawn(|| {
    //         *cell.borrow_mut() = 10; // 错误：RefCell 不是 Sync
    //     });
    // });
}

// Sync 与 Send 的关系
fn sync_send_relationship<T: Sync>()
where
    T: Send,
{
    // T: Sync 意味着 &T: Send
}
```

#### 7.1.3 共享状态数据流

共享状态需要同步原语保护：

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn shared_state_data_flow() {
    // Arc 提供共享所有权
    // Mutex 提供互斥访问
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            // 数据流：counter -> 线程
            let mut num = counter.lock().unwrap();
            *num += 1;
            // 锁释放，数据流回到共享状态
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Result: {}", *counter.lock().unwrap());
}
```

### 7.2 消息传递数据流

#### 7.2.1 通道数据流

通道提供线程间的有向数据流：

$$
\text{Channel}(T) : \text{Sender}\langle T \rangle \times \text{Receiver}\langle T \rangle \to \text{Thread}_1 \times \text{Thread}_2
$$

```rust
use std::sync::mpsc;
use std::thread;

fn channel_data_flow() {
    // 创建通道
    let (tx, rx) = mpsc::channel::<String>();

    // 发送者线程
    let tx2 = tx.clone();
    thread::spawn(move || {
        let data = String::from("from thread 1");
        // 所有权通过通道转移
        tx.send(data).unwrap();
        // data 已移动，不能再使用
    });

    thread::spawn(move || {
        let data = String::from("from thread 2");
        tx2.send(data).unwrap();
    });

    // 主线程接收
    for _ in 0..2 {
        // 所有权从通道转移到 received
        let received = rx.recv().unwrap();
        println!("Got: {}", received);
    }
}
```

#### 7.2.2 所有权传递

消息传递实现了线程间的所有权转移：

```rust
fn ownership_transfer_between_threads() {
    let (tx, rx) = std::sync::mpsc::channel();

    // 转移 Vec 的所有权
    let data = vec![1, 2, 3, 4, 5];
    tx.send(data).unwrap();
    // data 已移动

    // 在另一个线程接收
    let handle = std::thread::spawn(move || {
        let received = rx.recv().unwrap();
        println!("Received: {:?}", received);
        // received 在这个线程中 drop
    });

    handle.join().unwrap();
}

// 双向通信
fn bidirectional_communication() {
    let (tx1, rx1) = std::sync::mpsc::channel::<String>();
    let (tx2, rx2) = std::sync::mpsc::channel::<String>();

    std::thread::spawn(move || {
        let msg = rx1.recv().unwrap();
        tx2.send(format!("Reply to: {}", msg)).unwrap();
    });

    tx1.send(String::from("Hello")).unwrap();
    let reply = rx2.recv().unwrap();
    println!("{}", reply);
}
```

#### 7.2.3 消息顺序保证

通道保证消息的顺序性：

```rust
fn message_order_guarantees() {
    let (tx, rx) = std::sync::mpsc::channel();

    // 发送有序消息
    for i in 0..5 {
        tx.send(i).unwrap();
    }

    // 接收顺序与发送相同
    for expected in 0..5 {
        let received = rx.recv().unwrap();
        assert_eq!(received, expected);
    }
}

// 异步通道（无界）
fn unbounded_channel() {
    let (tx, rx) = std::sync::mpsc::channel();

    // 发送是非阻塞的
    for i in 0..1000 {
        tx.send(i).unwrap();
    }

    // 稍后接收
    std::thread::spawn(move || {
        while let Ok(msg) = rx.recv() {
            println!("{}", msg);
        }
    });
}

// 同步通道（有界）
fn bounded_channel() {
    let (tx, rx) = std::sync::mpsc::sync_channel(10); // 缓冲区大小 10

    std::thread::spawn(move || {
        for i in 0..20 {
            tx.send(i).unwrap();  // 缓冲区满时会阻塞
            println!("Sent: {}", i);
        }
    });

    // 缓慢接收
    while let Ok(msg) = rx.recv() {
        std::thread::sleep(std::time::Duration::from_millis(100));
        println!("Received: {}", msg);
    }
}
```

### 7.3 原子数据流

#### 7.3.1 原子变量数据流

原子变量提供无锁的线程间数据流：

```rust
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::Arc;
use std::thread;

fn atomic_data_flow() {
    let counter = Arc::new(AtomicI32::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..100 {
                // 原子递增
                counter.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Counter: {}", counter.load(Ordering::SeqCst));
}
```

#### 7.3.2 内存序约束

内存序定义了原子操作的可见性顺序：

| 内存序 | 保证 | 代价 | 用例 |
|--------|------|------|------|
| `Relaxed` | 无顺序保证 | 最低 | 计数器 |
| `Acquire` | 获取语义 | 中等 | 锁获取 |
| `Release` | 释放语义 | 中等 | 锁释放 |
| `AcqRel` | 获取+释放 | 高 | CAS |
| `SeqCst` | 顺序一致性 | 最高 | 严格同步 |

```rust
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::thread;

fn memory_ordering_example() {
    // Relaxed：只有原子性
    let counter = AtomicI32::new(0);
    counter.fetch_add(1, Ordering::Relaxed);

    // Release-Acquire：建立 happens-before 关系
    let ready = AtomicBool::new(false);
    let data = AtomicI32::new(0);

    let ready2 = AtomicBool::new(false);
    let data2 = AtomicI32::new(0);

    thread::scope(|s| {
        // 写线程
        s.spawn(|| {
            data2.store(42, Ordering::Relaxed);
            ready2.store(true, Ordering::Release);  // 释放
        });

        // 读线程
        s.spawn(|| {
            while !ready2.load(Ordering::Acquire) {}  // 获取
            assert_eq!(data2.load(Ordering::Relaxed), 42);  // 保证可见
        });
    });

    // SeqCst：全局顺序
    let seq1 = AtomicI32::new(0);
    let seq2 = AtomicI32::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            seq1.store(1, Ordering::SeqCst);
            let _ = seq2.load(Ordering::SeqCst);
        });

        s.spawn(|| {
            seq2.store(1, Ordering::SeqCst);
            let _ = seq1.load(Ordering::SeqCst);
        });
    });
}
```

#### 7.3.3 happens-before 图

happens-before 关系建立了事件的偏序：

```rust
use std::sync::atomic::{fence, AtomicI32, Ordering};
use std::thread;

fn happens_before_graph() {
    let x = AtomicI32::new(0);
    let y = AtomicI32::new(0);
    let z = AtomicI32::new(0);

    thread::scope(|s| {
        // 线程 A
        s.spawn(|| {
            x.store(1, Ordering::Relaxed);
            // 内存屏障，建立 happens-before
            fence(Ordering::SeqCst);
            y.store(1, Ordering::Relaxed);
        });

        // 线程 B
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

## 8. 异步数据流

### 8.1 Future 数据流

#### 8.1.1 Future 状态数据流

Future 内部状态随执行进展而变化：

$$
\text{Future}\langle T \rangle : \text{State} \times \text{Context} \to \text{Poll}\langle T \rangle
$$

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future 状态机
enum MyFutureState {
    Start,
    WaitingForStep1,
    WaitingForStep2,
    Complete(i32),
}

struct MyFuture {
    state: MyFutureState,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        match &mut self.state {
            MyFutureState::Start => {
                println!("State: Start -> WaitingForStep1");
                self.state = MyFutureState::WaitingForStep1;
                Poll::Pending
            }
            MyFutureState::WaitingForStep1 => {
                println!("State: Step1 complete");
                self.state = MyFutureState::WaitingForStep2;
                Poll::Pending
            }
            MyFutureState::WaitingForStep2 => {
                println!("State: Step2 complete");
                self.state = MyFutureState::Complete(42);
                Poll::Pending
            }
            MyFutureState::Complete(result) => {
                println!("State: Complete");
                Poll::Ready(*result)
            }
        }
    }
}
```

#### 8.1.2 Waker 传播数据流

Waker 用于通知执行器任务可以继续执行：

```rust
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};
use std::thread;
use std::time::Duration;

// 自定义 Future 使用 Waker
struct TimerFuture {
    shared_state: Arc<Mutex<SharedState>>,
}

struct SharedState {
    completed: bool,
    waker: Option<Waker>,
}

impl TimerFuture {
    fn new(duration: Duration) -> Self {
        let shared_state = Arc::new(Mutex::new(SharedState {
            completed: false,
            waker: None,
        }));

        let thread_state = Arc::clone(&shared_state);
        thread::spawn(move || {
            thread::sleep(duration);
            let mut state = thread_state.lock().unwrap();
            state.completed = true;
            // 唤醒执行器
            if let Some(waker) = state.waker.take() {
                waker.wake();
            }
        });

        TimerFuture { shared_state }
    }
}

impl Future for TimerFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut state = self.shared_state.lock().unwrap();

        if state.completed {
            Poll::Ready(())
        } else {
            // 保存 waker，稍后唤醒
            state.waker = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}
```

#### 8.1.3 执行器数据流

执行器管理 Future 的调度执行：

```rust
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Wake};

// 简化执行器
type Task = Pin<Box<dyn Future<Output = ()> + Send>>;

struct Executor {
    task_queue: Arc<Mutex<VecDeque<Task>>>,
}

impl Executor {
    fn new() -> Self {
        Executor {
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    fn spawn(&self, future: impl Future<Output = ()> + Send + 'static) {
        let task = Box::pin(future);
        self.task_queue.lock().unwrap().push_back(task);
    }

    fn run(&self) {
        while let Some(mut task) = self.task_queue.lock().unwrap().pop_front() {
            let waker = create_waker(Arc::clone(&self.task_queue));
            let mut context = Context::from_waker(&waker);

            match task.as_mut().poll(&mut context) {
                Poll::Ready(()) => {}
                Poll::Pending => {
                    // 重新入队
                    self.task_queue.lock().unwrap().push_back(task);
                }
            }
        }
    }
}

fn create_waker(queue: Arc<Mutex<VecDeque<Task>>>) -> std::task::Waker {
    struct TaskWaker {
        queue: Arc<Mutex<VecDeque<Task>>>,
    }

    impl Wake for TaskWaker {
        fn wake(self: Arc<Self>) {
            // 唤醒时将任务重新调度
        }
    }

    Arc::new(TaskWaker { queue }).into()
}
```

### 8.2 Stream 数据流

#### 8.2.1 元素数据流

Stream 是异步的迭代器：

```rust
use futures::stream::Stream;
use std::pin::Pin;
use std::task::{Context, Poll};

// 自定义 Stream
struct Counter {
    count: u32,
    max: u32,
}

impl Stream for Counter {
    type Item = u32;

    fn poll_next(
        mut self: Pin<&mut Self>,
        _cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>> {
        if self.count < self.max {
            let current = self.count;
            self.count += 1;
            Poll::Ready(Some(current))
        } else {
            Poll::Ready(None)
        }
    }
}

// 使用 Stream
async fn stream_data_flow() {
    use futures::stream::StreamExt;

    let mut counter = Counter { count: 0, max: 5 };

    while let Some(value) = counter.next().await {
        println!("{}", value);
    }
}
```

#### 8.2.2 背压数据流

背压防止生产者过快淹没消费者：

```rust
use futures::channel::mpsc;
use futures::sink::SinkExt;
use futures::stream::StreamExt;

async fn backpressure_data_flow() {
    // 有界通道实现背压
    let (mut tx, mut rx) = mpsc::channel::<i32>(10); // 缓冲区大小 10

    // 生产者
    let producer = async move {
        for i in 0..100 {
            // 当缓冲区满时，send 会等待
            tx.send(i).await.unwrap();
            println!("Sent: {}", i);
        }
    };

    // 消费者（慢速）
    let consumer = async move {
        while let Some(value) = rx.next().await {
            println!("Received: {}", value);
            // 模拟慢速处理
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }
    };

    // 并发执行
    futures::future::join(producer, consumer).await;
}
```

#### 8.2.3 缓冲数据流

缓冲优化批量处理：

```rust
use futures::stream::{self, StreamExt};

async fn buffered_data_flow() {
    // 创建数据流
    let stream = stream::iter(0..100);

    // 缓冲处理：每 10 个一组
    let buffered = stream.buffered(10);

    // 或者使用 chunks
    let chunked = stream::iter(0..100)
        .chunks(10);

    // 处理每组
    // while let Some(batch) = chunked.next().await {
    //     println!("Processing batch: {:?}", batch);
    // }
}
```

### 8.3 异步状态数据流

#### 8.3.1 状态机状态转换

`async/await` 编译为状态机：

```rust
// 源代码
async fn async_state_machine(x: i32) -> i32 {
    let a = async_step1(x).await;       // 状态 0 -> 1
    let b = async_step2(a).await;       // 状态 1 -> 2
    a + b                               // 状态 2 -> 完成
}

async fn async_step1(x: i32) -> i32 {
    x * 2
}

async fn async_step2(x: i32) -> i32 {
    x + 1
}

// 概念上等价于：
// enum AsyncStateMachine {
//     Start(i32),                       // 初始状态，保存参数 x
//     Waiting1(/* x, future */),        // 等待 step1
//     Waiting2(/* a, future */),        // 等待 step2
//     Complete,
// }
```

#### 8.3.2 挂起-恢复数据流

```rust
use std::future::poll_fn;
use std::task::Poll;

async fn suspend_resume_flow() {
    // 第一次挂起
    println!("Before first await");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    println!("After first await");

    // 第二次挂起
    let result = some_async_operation().await;
    println!("Result: {}", result);

    // 手动控制挂起
    let mut count = 0;
    poll_fn(|_cx| {
        if count < 3 {
            count += 1;
            println!("Polling: {}", count);
            Poll::Pending  // 挂起
        } else {
            Poll::Ready(())  // 完成
        }
    }).await;
}

async fn some_async_operation() -> i32 {
    42
}
```

#### 8.3.3 取消数据流

异步任务的取消需要正确处理：

```rust
use tokio::select;

async fn cancellation_data_flow() {
    // select! 取消未完成的任务
    select! {
        result = long_operation() => {
            println!("Operation completed: {:?}", result);
        }
        _ = tokio::time::sleep(tokio::time::Duration::from_secs(1)) => {
            println!("Timeout! Operation cancelled");
        }
    }

    // 取消安全的模式
    let result = async {
        let guard = DropGuard;
        some_work().await;
        drop(guard);
        "completed"
    };

    // 如果被取消，DropGuard 的 drop 会被调用
}

struct DropGuard;

impl Drop for DropGuard {
    fn drop(&mut self) {
        println!("Cleanup on cancellation");
    }
}

async fn long_operation() -> &'static str {
    tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
    "done"
}

async fn some_work() {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
```

---

## 9. 静态分析技术

### 9.1 借用检查器分析

#### 9.1.1 区域推断

编译器推断生命周期约束：

```rust
// 编译器自动推断 'a 和 'b 的关系
fn auto_infer<'a, 'b>(x: &'a str, y: &'b str) -> &'a str {
    // 推断：返回的生命周期 'a 必须不超过输入
    if x.len() > y.len() { x } else { x }
}

// 显式约束
fn explicit_constraint<'a, 'b: 'a>(x: &'a str, y: &'b str) -> &'a str {
    // 'b: 'a 表示 'b 至少和 'a 一样长
    x
}

// 复杂推断
fn complex_inference<'a>(items: &'a [String]) -> impl Iterator<Item = &'a str> {
    // 编译器推断返回的迭代器生命周期与输入相关
    items.iter().map(|s| s.as_str())
}
```

#### 9.1.2 约束生成

借用检查器生成约束并求解：

```rust
fn constraint_generation() {
    let x = String::from("hello");
    let r = &x;                      // 约束：r 的生命周期 ⊆ x 的生命周期

    println!("{}", r);               // 使用后 r 可以结束

    // x 可以继续使用
    drop(x);

    // 更复杂的约束
    let a = String::from("a");
    let b = String::from("b");

    let result = longest(&a, &b);    // 约束：result 的生命周期 ⊆ a 和 b 的交集
    println!("{}", result);
    // result 结束

    drop(a);
    drop(b);
}

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

#### 9.1.3 约束求解

```rust
// 约束求解示例：检查生命周期是否满足
fn constraint_solving() {
    let r;
    {
        let x = String::from("inner");
        // r = &x;                      // 错误：约束不满足
        println!("{}", x);
    }

    let y = String::from("outer");
    r = &y;                          // OK: 约束满足
    println!("{}", r);
}

// 方法中的约束
struct Wrapper<'a> {
    data: &'a str,
}

impl<'a> Wrapper<'a> {
    fn get(&self) -> &'a str {
        self.data
    }

    fn process<'b>(&'b self) -> &'b str {
        // 'b 可能与 'a 不同
        self.data
    }
}
```

### 9.2 类型系统分析

#### 9.2.1 类型推断算法

Hindley-Milner 风格类型推断：

```rust
fn type_inference_algorithm() {
    // 变量类型推断
    let x = 5;                       // i32

    // 函数返回类型推断
    let y = double(x);               // 从上下文推断

    // 泛型类型推断
    let v = vec![1, 2, 3];           // Vec<i32>
    let first = first_element(&v);   // 推断 T = i32

    // 闭包类型推断
    let f = |x| x + 1;               // 从使用推断类型
    let result = f(5);
}

fn double(x: i32) -> i32 {
    x * 2
}

fn first_element<T>(v: &[T]) -> Option<&T> {
    v.first()
}
```

#### 9.2.2 Trait 解析

```rust
trait Display {
    fn display(&self) -> String;
}

trait Debug {
    fn debug(&self) -> String;
}

struct MyType;

impl Display for MyType {
    fn display(&self) -> String {
        "Display".to_string()
    }
}

impl Debug for MyType {
    fn debug(&self) -> String {
        "Debug".to_string()
    }
}

fn trait_resolution() {
    let obj = MyType;

    // 静态分发：编译时确定
    show_display(&obj);
    show_debug(&obj);

    // 动态分发：运行时确定
    show_dyn(&obj as &dyn Display);
}

fn show_display<T: Display>(x: T) {
    println!("{}", x.display());
}

fn show_debug<T: Debug>(x: T) {
    println!("{}", x.debug());
}

fn show_dyn(x: &dyn Display) {
    println!("{}", x.display());
}
```

#### 9.2.3 关联类型求解

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

struct Counter {
    count: u32,
}

impl Iterator for Counter {
    type Item = u32;                 // 关联类型

    fn next(&mut self) -> Option<Self::Item> {
        if self.count < 5 {
            self.count += 1;
            Some(self.count)
        } else {
            None
        }
    }
}

// 关联类型的约束
trait Container {
    type Item;
    fn get(&self) -> &Self::Item;
}

// 使用关联类型
fn use_container<C: Container>(c: C) -> C::Item
where
    C::Item: Clone,
{
    c.get().clone()
}
```

### 9.3 lint 分析

#### 9.3.1 未使用变量检测

```rust
fn unused_detection() {
    let x = 5;                       // 警告：未使用

    let _y = 10;                     // OK: 下划线前缀忽略

    let z = 20;
    println!("{}", z);               // OK: 已使用

    // 故意不使用
    #[allow(unused_variables)]
    let unused = 100;
}
```

#### 9.3.2 未使用导入检测

```rust
// 警告：未使用的导入
// use std::collections::HashMap;

// OK: 使用的导入
use std::vec::Vec;

fn used_import() {
    let v = Vec::new();
    println!("{:?}", v);
}
```

#### 9.3.3 模式匹配穷尽性

```rust
fn pattern_exhaustiveness_checking(x: Option<i32>) {
    // 警告：未穷尽（启用#![deny(non_exhaustive)]时）
    // match x {
    //     Some(v) => println!("{}", v),
    // }

    // OK: 穷尽
    match x {
        Some(v) => println!("{}", v),
        None => println!("None"),
    }

    // 或使用 if let
    if let Some(v) = x {
        println!("{}", v);
    }
}

enum Color {
    Red,
    Green,
    Blue,
}

// 穷尽性检查包含所有变体
fn color_exhaustive(c: Color) {
    match c {
        Color::Red => "red",
        Color::Green => "green",
        Color::Blue => "blue",
    };
}
```

---

## 10. 形式化表示

### 10.1 控制流形式化

#### 10.1.1 操作语义规则

**小步操作语义（Small-step Operational Semantics）：**

$$
\langle e, \sigma \rangle \to \langle e', \sigma' \rangle
$$

```rust
// 变量查找
\frac{x \in \text{dom}(\sigma)}{\langle x, \sigma \rangle \to \langle \sigma(x), \sigma \rangle}

// 赋值
\langle x = v, \sigma \rangle \to \langle (), \sigma[x \mapsto v] \rangle

// 顺序
\frac{\langle e_1, \sigma \rangle \to \langle e_1', \sigma' \rangle}{\langle e_1; e_2, \sigma \rangle \to \langle e_1'; e_2, \sigma' \rangle}

// 条件
\frac{}{\langle \text{if true } \{e_1\} \text{ else } \{e_2\}, \sigma \rangle \to \langle e_1, \sigma \rangle}

\frac{}{\langle \text{if false } \{e_1\} \text{ else } \{e_2\}, \sigma \rangle \to \langle e_2, \sigma \rangle}
```

#### 10.1.2 求值上下文

求值上下文 $E$ 表示可以规约的位置：

$$
E ::= [] \mid E; e \mid \text{if } E \{e_1\} \text{ else } \{e_2\} \mid \ldots
$$

```rust
// 上下文示例
// 在 [] + 2 中，[] 是求值上下文
// 1 + 2 可以先规约 1

// 复杂上下文
// if [] { e1 } else { e2 }
// 先求值条件

// E[e] 表示在上下文 E 中放入 e
```

#### 10.1.3 规约关系

```rust
// 规约关系示例
// (\x -> e) v  ~>  e[x/v]           // beta 规约

// let x = v in e  ~>  e[x/v]        // let 规约

// match C(v) { C(x) => e }  ~>  e[x/v]  // match 规约

// &*r  ~>  r                        // 借用解引用

// *&x  ~>  x                        // 解引用借用
```

### 10.2 数据流形式化

#### 10.2.1 数据流方程

**前向数据流分析：**

$$
\text{OUT}[b] = f_b(\text{IN}[b])
$$

$$
\text{IN}[b] = \bigcup_{p \in \text{pred}(b)} \text{OUT}[p]
$$

```rust
// 到达定义分析的方程
// Gen[b]: 基本块 b 中生成的定义
// Kill[b]: 基本块 b 杀死的定义

// OUT[b] = Gen[b] ∪ (IN[b] - Kill[b])
// IN[b] = ∪ OUT[p] for p ∈ pred(b)

fn dataflow_equations_example() {
    let mut x = 1;                    // Gen: D1
    x = 2;                            // Gen: D2, Kill: D1

    if condition() {
        x = 3;                        // Gen: D3, Kill: D2
    } else {
        x = 4;                        // Gen: D4, Kill: D2
    }

    // IN = {D3, D4}
    println!("{}", x);
}

fn condition() -> bool { true }
```

#### 10.2.2 不动点求解

```rust
// 迭代求解直到不动点
// 初始：OUT[b] = ∅ for all b
// 重复：
//   for each b:
//     IN[b] = ∪ OUT[p]
//     OUT[b] = Gen[b] ∪ (IN[b] - Kill[b])
// 直到没有变化

// 示例：活跃变量分析
fn fixed_point_example() {
    let a = 1;                        // Gen: a 活跃
    let b = a + 1;                    // Gen: b 活跃, Kill: a 活跃
    let c = b + 1;                    // Gen: c 活跃, Kill: b 活跃
    println!("{}", c);                // Use: c
}
```

#### 10.2.3 单调框架

数据流分析基于单调框架：

$$
(D, \sqsubseteq, \bot, \top, \sqcup, f)
$$

其中：

- $D$：值域（如变量集合）
- $\sqsubseteq$：偏序关系
- $\bot, \top$：最小、最大元
- $\sqcup$：合并操作（join）
- $f$：转移函数（单调）

```rust
// 单调性：x ⊑ y ⟹ f(x) ⊑ f(y)

// 到达定义：
// D = P(Definitions)  // 定义的幂集
// ⊑ = ⊆               // 包含关系
// ⊥ = ∅               // 空集
// ⊤ = AllDefinitions  // 所有定义
// ⊔ = ∪               // 并集

// 活跃变量：
// D = P(Variables)
// ⊑ = ⊇               // 反向包含
// ⊥ = AllVariables
// ⊤ = ∅
// ⊔ = ∩               // 交集
```

### 10.3 类型与效果

#### 10.3.1 类型判断

$$
\Gamma \vdash e : \tau \quad \text{（在环境 } \Gamma \text{ 下，} e \text{ 具有类型 } \tau \text{）}
$$

```rust
// 类型判断规则
// (T-Var)  Γ(x) = τ
//          ---------
//          Γ ⊢ x : τ

// (T-Abs)  Γ, x:τ₁ ⊢ e : τ₂
//          -----------------
//          Γ ⊢ λx.e : τ₁ → τ₂

// (T-App)  Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
//          --------------------------------
//          Γ ⊢ e₁ e₂ : τ₂

// (T-Borrow)  Γ ⊢ x : T
//             -----------
//             Γ ⊢ &x : &T

// (T-MutBorrow)  Γ ⊢ x : mut T
//                --------------
//                Γ ⊢ &mut x : &mut T
```

#### 10.3.2 效果系统

效果系统追踪计算可能产生的效果：

```rust
// 效果标记：读、写、异常、IO、非终止等

// 纯函数：无副作用
fn pure_function(x: i32) -> i32 {
    x + 1
}

// 有副作用的函数
fn impure_function() {
    println!("IO effect");            // IO 效果
}

// 可能 panic
fn panicking_function() -> i32 {
    panic!("exception effect");
}

// Rust 没有显式效果系统，但可以通过类型表示
// io::Result<T> 表示可能失败的 IO
// Option<T> 表示可能缺失
// Result<T, E> 表示可能错误
```

#### 10.3.3 区域类型

区域类型追踪资源的生命周期：

```rust
// 区域类型语法
// &^ρ T  表示区域 ρ 中的引用

// 区域包含
// ρ₁ ⊆ ρ₂  表示 ρ₁ 的生命周期包含于 ρ₂

// 子类型
// &^ρ₁ T <: &^ρ₂ T  if ρ₂ ⊆ ρ₁  （协变）

// 实际 Rust 语法
fn region_types<'a, 'b>(x: &'a str, y: &'b str) -> &'a str
where
    'b: 'a,  // 'b 包含 'a
{
    x
}

// 区域在类型中
struct Ref<'a, T> {
    data: &'a T,
}

// 区域约束传播
fn region_propagation<'a, 'b, T>(x: &'a T, y: &'b T) -> (&'a T, &'b T)
where
    T: 'a + 'b,
{
    (x, y)
}
```

---

## 11. 工具与实践

### 11.1 编译器分析

#### 11.1.1 MIR 数据流分析

Rust 编译器使用 MIR（Mid-level IR）进行分析：

```rust
// 查看 MIR
// rustc --emit=mir example.rs

// MIR 结构：
// - 基本块（BasicBlock）
// - 语句（Statement）
// - 终止符（Terminator）

// 示例 Rust 代码
fn mir_example(x: i32) -> i32 {
    let mut sum = 0;
    for i in 0..x {
        sum += i;
    }
    sum
}

// 对应的 MIR 概念结构：
// fn mir_example(_1: i32) -> i32 {
//     let mut _0: i32;
//     let mut _2: i32;
//     let mut _3: std::ops::Range<i32>;
//     let mut _4: std::ops::Range<i32>;
//     let mut _5: i32;
//
//     bb0: {
//         _2 = const 0_i32;
//         _4 = std::ops::Range { start: const 0_i32, end: _1 };
//         _3 = <std::ops::Range<i32> as IntoIterator>::into_iter(move _4);
//         goto -> bb1;
//     }
//
//     bb1: {
//         _5 = <std::ops::Range<i32> as Iterator>::next(&mut _3);
//         // ...
//     }
// }
```

#### 11.1.2 LLVM IR 生成

Rust 编译器生成 LLVM IR 进行优化：

```bash
# 生成 LLVM IR
rustc --emit=llvm-ir example.rs

# 优化级别
rustc -C opt-level=3 example.rs  # 最高优化
```

```rust
// LLVM IR 示例（概念）
// define i32 @example(i32 %x) {
// entry:
//   %sum = alloca i32
//   store i32 0, i32* %sum
//   ; 循环...
//   %result = load i32, i32* %sum
//   ret i32 %result
// }
```

#### 11.1.3 优化 passes

```rust
// 常见优化
// 1. 常量传播
fn const_prop(x: i32) -> i32 {
    let a = 2 + 3;                    // 优化为 5
    x + a
}

// 2. 死代码消除
fn dead_code_elimination(x: i32) -> i32 {
    let unused = x * 2;               // 被消除
    x + 1
}

// 3. 内联
fn inline_example(x: i32) -> i32 {
    add_one(x)                        // 内联为 x + 1
}

#[inline]
fn add_one(x: i32) -> i32 {
    x + 1
}

// 4. 循环优化
fn loop_optimization() -> i32 {
        let mut sum = 0;
    for i in 0..100 {
        sum += i;
    }
    sum                                 // 可能优化为 4950
}
```

### 11.2 静态分析工具

#### 11.2.1 Clippy 检查

```bash
# 运行 Clippy
cargo clippy

# 所有检查
cargo clippy -- -W clippy::all
```

```rust
// Clippy 检测的常见问题

// 不必要的 clone
fn unnecessary_clone(s: &str) -> String {
    s.to_string()                     // 优于 s.clone()
}

// 不必要的引用解引用
fn needless_deref(x: &&i32) -> i32 {
    **x                               // Clippy 提示：可以简化
}

// 可能的 panic
fn potential_panic(v: &[i32]) -> i32 {
    v[0]                              // Clippy 建议使用 get()
}

// 改进版
fn improved(v: &[i32]) -> Option<i32> {
    v.first().copied()
}
```

#### 11.2.2 Miri 解释执行

```bash
# 安装 Miri
rustup component add miri

# 运行测试
cargo miri test

# 运行程序
cargo miri run
```

```rust
// Miri 检测的问题

// 未定义行为检测
fn undefined_behavior() {
    let ptr = 0x12345678 as *const i32;
    // unsafe { *ptr };                  // Miri 报错：无效内存访问
}

// 悬垂指针
fn dangling_pointer() {
    let r;
    {
        let x = 5;
        r = &x;
    }
    // println!("{}", r);                  // Miri 报错：使用已释放内存
}

// 数据竞争
fn data_race() {
    use std::thread;

    let mut x = 0;
    let r = &mut x;
    let r2 = r as *mut i32;

    thread::spawn(move || {
        unsafe { *r2 = 1; }
    });

    // unsafe { *r2 = 2; }                  // Miri 报错：数据竞争
}
```

#### 11.2.3 自定义 lint

```rust
// 使用 clippy API 创建自定义 lint（需要 clippy_utils）
// 在 .cargo/config.toml 中配置

// 或条件编译 lint
#![allow(dead_code)]              // 允许死代码
#![deny(unsafe_code)]             // 禁止 unsafe
#![warn(missing_docs)]            // 警告缺少文档

// 自定义属性
#[deprecated(since = "1.0.0", note = "Use new_function instead")]
fn old_function() {}

#[must_use]
fn important_result() -> i32 {
    42
}
```

### 11.3 性能分析

#### 11.3.1 火焰图语义

```bash
# 使用 cargo-flamegraph
cargo install flamegraph
cargo flamegraph

# 使用 perf（Linux）
perf record --call-graph dwarf ./target/release/myapp
perf script | inferno-collapse-perf | inferno-flamegraph > flamegraph.svg
```

```rust
// 示例代码用于火焰图分析
fn cpu_intensive_work() {
    let mut sum = 0u64;
    for i in 0..10_000_000 {
        sum += fibonacci(i % 30);
    }
    println!("Sum: {}", sum);
}

fn fibonacci(n: u64) -> u64 {
    if n <= 1 {
        n
    } else {
        fibonacci(n - 1) + fibonacci(n - 2)
    }
}
```

#### 11.3.2 分配追踪

```rust
// 使用 dhat 进行堆分析
// cargo add dhat

#[cfg(feature = "dhat")]
#[global_allocator]
static ALLOC: dhat::Alloc = dhat::Alloc;

fn allocation_profiling() {
    #[cfg(feature = "dhat")]
    let _profiler = dhat::Profiler::new_heap();

    // 分配密集型操作
    let mut v = vec![];
    for i in 0..1000 {
        v.push(vec![i; 1000]);
    }

    // 在 dhat-heap.json 中查看结果
}
```

#### 11.3.3 缓存分析

```rust
// 缓存友好的数据访问模式
fn cache_friendly() {
    let n = 1000;
    let mut matrix = vec![vec![0.0f64; n]; n];

    // 行优先访问（缓存友好）
    for i in 0..n {
        for j in 0..n {
            matrix[i][j] += 1.0;      // 连续内存访问
        }
    }
}

fn cache_unfriendly() {
    let n = 1000;
    let mut matrix = vec![vec![0.0f64; n]; n];

    // 列优先访问（缓存不友好）
    for j in 0..n {
        for i in 0..n {
            matrix[i][j] += 1.0;      // 跳跃式内存访问
        }
    }
}

// 使用 cachegrind 分析
cargo build --release
valgrind --tool=cachegrind ./target/release/myapp
```

---

## 12. 总结

### 12.1 核心概念回顾

本文档深入分析了 Rust 的数据流和控制流语义：

| 概念 | 核心语义 | 形式化表示 |
|------|---------|-----------|
| 所有权 | 唯一所有权，Move/Copy/Borrow | $\text{Own}(x, T) \xrightarrow{\text{move}} \text{Own}(y, T)$ |
| 借用 | 不可变/可变引用，生命周期约束 | $\Gamma \vdash \&x : \&T$ |
| 生命周期 | 引用的有效范围 | $\text{live}(r) \subseteq 'a$ |
| 控制流 | 顺序、条件、循环、跳转 | $\langle e, \sigma \rangle \to \langle e', \sigma' \rangle$ |
| 数据流 | 值的创建-使用-销毁 | $\text{Create} \to \text{Use}^* \to \text{Drop}$ |
| 并发 | Send/Sync，消息传递 | $\text{Own}(T) \to \text{Channel}(T)$ |
| 异步 | Future/Stream，状态机 | $\text{Future} : \text{State} \to \text{Poll}\langle T \rangle$ |

### 12.2 静态分析要点

1. **借用检查器**：通过区域推断和约束求解确保内存安全
2. **数据流分析**：到达定义、活跃性分析优化代码生成
3. **类型推断**：Hindley-Milner 风格，支持双向推断
4. **常量求值**：编译时执行，支持复杂计算

### 12.3 实践指导

- 使用 `rustc --emit=mir` 查看中间表示
- 使用 `cargo clippy` 进行静态检查
- 使用 `cargo miri` 检测未定义行为
- 使用 `cargo flamegraph` 进行性能分析
- 理解 NLL（非词法生命周期）使借用更灵活

### 12.4 延伸阅读

- [Rust 参考手册](https://doc.rust-lang.org/reference/)
- [Rustc 开发者指南](https://rustc-dev-guide.rust-lang.org/)
- [Rust 形式化语义研究（RustBelt）](https://plv.mpi-sws.org/rustbelt/)
- [Stacked Borrows](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md)
- [Tree Borrows](https://perso.crans.org/vanille/treebor/)

---

*本文档是 Rust 所有权可判定性研究系列的一部分，与 `00-semantic-framework.md` 保持一致的语义框架。*
