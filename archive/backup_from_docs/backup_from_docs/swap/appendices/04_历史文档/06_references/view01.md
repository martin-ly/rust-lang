# Rust 控制流特性分析 (修订版)

## 目录

- [Rust 控制流特性分析 (修订版)](#rust-控制流特性分析-修订版)
  - [目录](#目录)
  - [1. 引言：控制流基础](#1-引言控制流基础)
  - [2. 条件控制表达式](#2-条件控制表达式)
    - [2.1 `if` 表达式](#21-if-表达式)
      - [2.1.1 定义与控制流](#211-定义与控制流)
      - [2.1.2 作为表达式](#212-作为表达式)
      - [2.1.3 所有权与借用](#213-所有权与借用)
      - [2.1.4 形式化视角](#214-形式化视角)
      - [2.1.5 代码示例](#215-代码示例)
    - [2.2 `if let` 表达式](#22-if-let-表达式)
    - [2.3 `match` 表达式](#23-match-表达式)
      - [2.3.1 定义与模式匹配](#231-定义与模式匹配)
      - [2.3.2 穷尽性 (Exhaustiveness)](#232-穷尽性-exhaustiveness)
      - [2.3.3 所有权与借用](#233-所有权与借用)
      - [2.3.4 形式化视角](#234-形式化视角)
      - [2.3.5 代码示例](#235-代码示例)
  - [3. 循环控制语句](#3-循环控制语句)
    - [3.1 `loop` 语句](#31-loop-语句)
    - [3.2 `while` 语句](#32-while-语句)
    - [3.3 `while let` 语句](#33-while-let-语句)
    - [3.4 `for` 语句](#34-for-语句)
    - [3.5 循环中的所有权与借用](#35-循环中的所有权与借用)
    - [3.6 `break` 与 `continue` (含标签)](#36-break-与-continue-含标签)
    - [3.7 代码示例 (循环综合)](#37-代码示例-循环综合)
  - [4. 函数与控制流](#4-函数与控制流)
    - [4.1 调用、返回与所有权传递](#41-调用返回与所有权传递)
    - [4.2 递归](#42-递归)
    - [4.3 发散函数 (`!`)](#43-发散函数-)
    - [4.4 代码示例](#44-代码示例)
  - [5. 闭包与控制流](#5-闭包与控制流)
    - [5.1 定义、环境捕获与 Traits (`Fn`/`FnMut`/`FnOnce`)](#51-定义环境捕获与-traits-fnfnmutfnonce)
    - [5.2 作为控制流机制 (高阶函数、回调)](#52-作为控制流机制-高阶函数回调)
    - [5.3 `move` 关键字](#53-move-关键字)
    - [5.4 代码示例](#54-代码示例)
  - [6. 异步函数与非阻塞控制流](#6-异步函数与非阻塞控制流)
    - [6.1 `async fn` 与 `Future`](#61-async-fn-与-future)
    - [6.2 `.await` 与控制流暂停/恢复](#62-await-与控制流暂停恢复)
    - [6.3 状态机转换](#63-状态机转换)
    - [6.4 异步中的所有权与生命周期](#64-异步中的所有权与生命周期)
    - [6.5 代码示例](#65-代码示例)
  - [7. 形式化视角与类型系统总结](#7-形式化视角与类型系统总结)
  - [8. 思维导图 (文本)](#8-思维导图-文本)

---

## 1. 引言：控制流基础

控制流（Control Flow）是程序指令执行顺序的规则集合。
它决定了程序如何根据条件、循环、函数调用及并发操作来导航其执行路径。
Rust 提供了丰富、类型安全且富有表现力的控制流机制。
这些机制与 Rust 独特的所有权（Ownership）、借用（Borrowing）和生命周期（Lifetimes）系统深度集成，
共同保证了内存安全和线程安全，使得开发者能够在编译时捕获大量潜在错误。
本分析将深入探讨 Rust 的各项控制流特性，并结合其类型系统和形式化概念进行阐释。

## 2. 条件控制表达式

Rust 中的条件控制结构通常是表达式（Expressions），意味着它们会计算并返回一个值。

### 2.1 `if` 表达式

#### 2.1.1 定义与控制流

`if` 基于布尔条件选择性地执行代码块。
基本形式为 `if condition { block_true }`，也可带有 `else { block_false }` 或 `else if condition2 { ... }`。

#### 2.1.2 作为表达式

当 `if` 带有 `else` 块时，它可以作为一个表达式返回值。
此时，`if` 和 `else`（以及所有 `else if`）分支 **必须返回相同类型** 的值。
如果分支不返回值，则它们隐式返回单元类型 `()`。

#### 2.1.3 所有权与借用

所有权和借用规则在 `if` 的各个分支中独立但共同作用：

- 如果一个值的所有权在一个分支中被移出（move），则它在 `if` 表达式之后将不可用（除非所有分支都移出并赋给同一变量）。
- 借用必须在整个 `if` 表达式的范围内有效。在一个分支中创建的借用不能与另一分支中的不兼容借用（例如，同一变量的可变借用与不可变借用）冲突。

#### 2.1.4 形式化视角

可以将 `if` 表达式 \(E_{if}\) 视为一个函数，根据条件选择评估哪个分支：
\[ E_{if}(condition, block_{true}, block_{false}) = \begin{cases} eval(block_{true}) & \text{if } condition = \text{true} \\ eval(block_{false}) & \text{if } condition = \text{false} \end{cases} \]
类型系统强制 \( \text{typeof}(eval(block_{true})) = \text{typeof}(eval(block_{false})) \)。

#### 2.1.5 代码示例

```rust
fn describe_temp(temp: i32) -> &'static str {
    if temp > 30 {
        "Hot"
    } else if temp < 10 {
        "Cold"
    } else {
        "Moderate" // 所有分支返回 &'static str
    }
}

fn process_optional_value(opt_val: Option<i32>) {
    let mut value = 0;
    if opt_val.is_some() {
        // 在分支内借用 opt_val 是允许的
        println!("Has value: {}", opt_val.unwrap());
        // value = opt_val.unwrap(); // 错误: 不能移出 Option<i32>，除非使用 take() 或 match
    } else {
        println!("No value");
    }
    // opt_val 在这里仍然可用 (如果之前未被移出)
}
```

### 2.2 `if let` 表达式

`if let` 是 `match` 表达式的一种语法糖，用于当只关心一种模式匹配成功的情况。它允许在 `if` 条件中进行模式匹配和解构。

```rust
let maybe_num: Option<i32> = Some(5);

if let Some(num) = maybe_num {
    println!("Got number: {}", num); // 只有当 maybe_num 是 Some 时执行
} else {
    println!("No number"); // 可选的 else 分支
}

// 等价于但不那么冗长的 match:
// match maybe_num {
//     Some(num) => println!("Got number: {}", num),
//     None => println!("No number"),
// }
```

`if let` 同样遵循所有权和借用规则。

### 2.3 `match` 表达式

#### 2.3.1 定义与模式匹配

`match` 允许将一个值与一系列模式（Patterns）进行比较，并执行第一个成功匹配的模式对应的代码块。模式可以非常强大，包括字面值、变量绑定、通配符 (`_`)、解构元组/结构体/枚举、范围、匹配守卫（`if` 条件）等。

#### 2.3.2 穷尽性 (Exhaustiveness)

Rust 强制要求 `match` 表达式必须是 **穷尽** 的，即所有可能的值都必须被至少一个模式覆盖。编译器会静态检查这一点。如果类型不是可以轻易列举完所有情况的（如 `i32`），通常需要一个通配符 `_` 分支来确保穷尽性。这防止了未处理情况导致的运行时错误。

#### 2.3.3 所有权与借用

`match` 分支中的所有权和借用规则与 `if` 类似：

- 变量绑定默认是引用绑定（借用），除非使用了 `ref` 或 `ref mut`（较少见，通常自动推断）或模式本身导致移动（如直接绑定非 `Copy` 类型变量）。
- 在一个分支中移动值会影响其在 `match` 后的可用性。
- 所有分支的借用行为必须兼容。

#### 2.3.4 形式化视角

\(E_{match}\) 可以看作是将输入值映射到基于模式匹配的第一个成功分支的求值结果：
\[ E_{match}(value, [(p_1, e_1), (p_2, e_2), \dots]) = eval(e_i) \text{ where } p_i \text{ is the first pattern matching } value \]
类型系统强制所有 \(e_i\) 返回相同类型（如果 `match` 作为表达式）。穷尽性检查保证对于任何可能的 `value`，都存在一个匹配的 \(p_i\)。

#### 2.3.5 代码示例

```rust
enum Message {
    Quit,
    Write(String),
    Move { x: i32, y: i32 },
}

fn process_message(msg: Message) {
    match msg {
        Message::Quit => println!("Quit message"),
        Message::Write(text) => { // text 绑定了 String 的所有权 (move)
            println!("Write message: {}", text);
            // msg 在这里不再可用，因为 Write(String) 被移出
        }
        Message::Move { x, y } if x > 0 && y > 0 => { // x, y 绑定了 i32 (Copy)
            println!("Move to positive quadrant: ({}, {})", x, y);
        }
        Message::Move { x, y } => {
            println!("Move to: ({}, {})", x, y);
        }
        // 不需要 `_` 因为 Message 的所有变体都被覆盖了
    }
}

let owned_message = Message::Write(String::from("hello"));
process_message(owned_message);
// println!("{:?}", owned_message); // 编译错误: value used here after move
```

## 3. 循环控制语句

循环语句用于重复执行代码块。它们通常不返回值（或隐式返回 `()`），除非特殊情况（如 `loop` 的 `break`）。

### 3.1 `loop` 语句

`loop` 创建一个无限循环，需要使用 `break` 来显式退出。一个独特的特性是 `loop` 可以通过 `break value;` 从循环中返回值，使其本身可以成为一个表达式。

```rust
let mut counter = 0;
let result = loop {
    counter += 1;
    if counter == 10 {
        break counter * 2; // 退出并返回 20
    }
};
println!("Result: {}", result); // 输出 20
```

### 3.2 `while` 语句

`while condition { block }` 在每次迭代开始前检查布尔条件 `condition`。如果为 `true`，则执行 `block`，否则循环终止。

```rust
let mut number = 3;
while number != 0 {
    println!("{}!", number);
    number -= 1;
}
```

### 3.3 `while let` 语句

类似于 `if let`，`while let` 是一种方便的语法糖，它将 `while` 循环与模式匹配结合起来。只要模式匹配成功，循环就继续。常用于处理 `Option` 或 `Result`，或消耗迭代器的一部分。

```rust
let mut optional_num = Some(0);
while let Some(i) = optional_num {
    if i > 3 {
        println!("Stopping at {}", i);
        optional_num = None; // 改变条件以停止循环
    } else {
        println!("Current: {}", i);
        optional_num = Some(i + 1);
    }
}

let mut vec = vec![1, 2, 3];
// 处理栈 (LIFO)
while let Some(top) = vec.pop() {
    println!("Popped: {}", top);
}
```

### 3.4 `for` 语句

`for item in iterator { block }` 是 Rust 中最常用、最惯用的循环方式。它通过迭代 `iterator`（任何实现了 `IntoIterator` trait 的类型）来工作。`for` 循环会自动处理迭代器的 `next()` 调用和结束条件 (`None`)。

**安全性**: 它避免了手动管理索引和边界检查（如 C 风格 `for`），从而减少了 off-by-one 等常见错误。

```rust
let names = vec!["Alice", "Bob", "Charlie"];
for name in names.iter() { // .iter() 创建一个不可变引用的迭代器
    println!("Hello, {}!", name);
}
// names 在这里仍然可用

for i in 0..5 { // 范围 (Range) 实现了 IntoIterator
    println!("Number: {}", i); // 输出 0 到 4
}
```

### 3.5 循环中的所有权与借用

- **`for` 循环**:
  - `for item in collection`: 会取得 `collection` 的所有权并消耗它。`collection` 在循环后不可用。
  - `for item in collection.iter()`: 借用 `collection`，每次迭代产生不可变引用 `&T`。`collection` 在循环后可用。
  - `for item in collection.iter_mut()`: 可变借用 `collection`，每次迭代产生可变引用 `&mut T`。`collection` 在循环后可用。
- **`while` / `loop`**: 循环体内部的借用规则与普通代码块相同。需要注意的是，在循环条件或 `break`/`continue` 处，借用必须仍然有效或已结束。借用检查器会确保循环不会导致悬垂引用。

### 3.6 `break` 与 `continue` (含标签)

- `break`: 立即退出当前最内层的循环 (`loop`, `while`, `for`)。
- `continue`: 跳过当前迭代的剩余部分，开始下一次迭代（对于 `while` 和 `for`，会重新评估条件或获取下一个元素）。
- **标签 (`'label:`)**: 可以为循环添加标签，并与 `break` 或 `continue` 结合使用 (`break 'label;`, `continue 'label;`) 来控制嵌套循环中的非局部跳转。

```rust
'outer: for i in 0..3 {
    for j in 0..3 {
        if i == 1 && j == 1 {
            println!("Skipping outer iteration from inner loop");
            continue 'outer; // 跳到 i=2 的迭代
        }
        if i == 2 && j == 1 {
            println!("Breaking outer loop from inner loop");
            break 'outer; // 完全退出外层循环
        }
        println!("({}, {})", i, j);
    }
}
```

### 3.7 代码示例 (循环综合)

```rust
fn process_items(items: &mut Vec<Option<i32>>) {
    let mut i = 0;
    while i < items.len() {
        if let Some(ref mut val) = items[i] { // 模式匹配可变引用
            if *val < 0 {
                println!("Removing negative value at index {}", i);
                items.remove(i);
                // 注意：删除元素后，不需要递增 i，因为下一个元素移到了当前索引
                continue; // 跳过下面的处理，直接开始下一次迭代
            }
            *val *= 2; // 修改值
        }
        i += 1; // 只有在没有删除元素时才递增索引
    }

    for (index, item_opt) in items.iter().enumerate() {
        if let Some(item) = item_opt {
             println!("Final item at index {}: {}", index, item);
        } else {
             println!("Item at index {} is None", index);
        }
    }
}
```

## 4. 函数与控制流

### 4.1 调用、返回与所有权传递

函数调用是基本的控制流转移机制。

- **调用**: 控制权转移到函数入口，参数根据其类型按值传递（对于 `Copy` 类型）或移动所有权（对于非 `Copy` 类型）或传递引用（借用）。调用信息（如返回地址）保存在调用栈（Call Stack）上。
- **返回**: 函数执行完毕（遇到 `return` 或到达函数体末尾的表达式），返回值（如果有）被传递回调用者，控制权返回到调用点之后，栈帧被销毁。
- **所有权**: 函数参数和返回值的所有权转移是 Rust 内存管理的关键部分，由编译器静态检查。

### 4.2 递归

函数调用自身形成递归。必须包含 **基本情况 (Base Case)** 来终止递归，否则会导致无限递归和栈溢出。

### 4.3 发散函数 (`!`)

返回类型为 `!` (Never 类型) 的函数称为发散函数。它们保证 **永不返回** 控制权给调用者（例如通过 `panic!`, `std::process::exit` 或无限 `loop`)。编译器利用这个信息进行控制流分析，例如，`match` 分支若调用发散函数，则该分支无需返回值。

### 4.4 代码示例

```rust
// 参数所有权转移
fn consume_string(s: String) {
    println!("Consumed: {}", s);
    // s 在函数结束时被 drop
}

// 参数借用
fn inspect_string(s: &str) {
    println!("Inspecting: {}", s);
}

// 返回所有权
fn create_string() -> String {
    String::from("new string")
}

// 递归计算阶乘
fn factorial(n: u64) -> u64 {
    if n == 0 { // Base case
        1
    } else {
        n * factorial(n - 1) // Recursive call
    }
}

// 发散函数示例
fn always_panic() -> ! {
    panic!("This function always panics");
}

fn main() {
    let my_string = String::from("hello");
    inspect_string(&my_string); // 传递引用
    // consume_string(my_string); // 移动所有权
    // println!("{}", my_string); // 错误: 如果上面 consume_string 被调用

    let new_s = create_string();
    println!("{}", new_s);

    println!("Factorial of 5: {}", factorial(5));

    // let value = match Some(1) {
    //     Some(x) => x,
    //     None => always_panic(), // OK: 此分支不返回值，因为它永不返回
    // };
}
```

## 5. 闭包与控制流

### 5.1 定义、环境捕获与 Traits (`Fn`/`FnMut`/`FnOnce`)

闭包是可捕获其定义环境（作用域内的变量）的匿名函数。语法通常为 `|param1, ...| { body }`。

**环境捕获** 是核心特性，有三种方式，对应三种 `Fn` Trait：

- **`FnOnce`**: 闭包可能**消耗**（获取所有权）捕获的变量。它只能被调用一次。所有闭包都至少实现 `FnOnce`。对应捕获方式：`T` (移动)。
- **`FnMut`**: 闭包可以**可变地借用**捕获的变量。它可以被调用多次。实现 `FnMut` 的闭包也实现了 `FnOnce`。对应捕获方式：`&mut T` (可变借用)。
- **`Fn`**: 闭包只能**不可变地借用**捕获的变量。它可以被调用多次。实现 `Fn` 的闭包也实现了 `FnMut` 和 `FnOnce`。对应捕获方式：`&T` (不可变借用)。

编译器根据闭包如何使用环境中的变量来自动推断实现哪个最具体的 Trait。

### 5.2 作为控制流机制 (高阶函数、回调)

闭包是 Rust 实现函数式编程风格和某些设计模式的关键：

- **高阶函数**: 接受其他函数（通常是闭包）作为参数或返回函数的函数。例如，迭代器适配器 (`map`, `filter`, `fold`) 接受闭包来定义操作，极大地改变了数据处理的控制流。
- **回调**: 将闭包作为参数传递，以便在特定事件发生时（如异步操作完成、UI事件）执行。
- **延迟执行**: 定义一段逻辑（闭包），但不立即执行，而是在稍后某个时间点或条件下调用。

### 5.3 `move` 关键字

在闭包定义前使用 `move` 关键字 (`move || { ... }`) 会强制闭包获取其捕获的所有变量的**所有权**，即使它原本只需要借用。
这在需要将闭包传递到不同线程或确保闭包生命周期超过其捕获的变量时非常有用。
`move` 闭包通常只实现 `FnOnce`（如果它消耗了捕获的变量）或 `Fn` / `FnMut`（如果捕获的是 `Copy` 类型或闭包内部没有消耗它们）。

### 5.4 代码示例

```rust
fn apply_operation<F>(a: i32, b: i32, op: F) -> i32
where
    F: Fn(i32, i32) -> i32, // 要求闭包实现 Fn
{
    op(a, b)
}

fn main() {
    let factor = 10;
    // Fn: 不可变借用 factor
    let multiply = |x, y| (x + y) * factor;
    println!("Result (Fn): {}", apply_operation(3, 4, multiply));

    let mut offset = 5;
    // FnMut: 可变借用 offset
    let mut add_offset = |x| {
        offset += 1; // 修改环境
        x + offset
    };
    println!("Result (FnMut 1): {}", add_offset(10)); // offset 变为 6, 输出 16
    println!("Result (FnMut 2): {}", add_offset(10)); // offset 变为 7, 输出 17

    let data = vec![1, 2, 3];
    // FnOnce (因为使用了 move 且 Vec 不是 Copy)
    let process_data = move || {
        println!("Processing data: {:?}", data);
        // data 的所有权被移入闭包
        data.len()
    };
    println!("Data length: {}", process_data());
    // println!("{:?}", data); // 错误: data 已被移动

    // 迭代器适配器示例
    let numbers = vec![1, 2, 3, 4];
    let doubled_evens: Vec<_> = numbers
        .into_iter() // 获取所有权
        .filter(|x| x % 2 == 0) // filter 接受 FnMut 闭包
        .map(|x| x * 2)        // map 接受 FnMut 闭包
        .collect();
    println!("Doubled evens: {:?}", doubled_evens);
}
```

## 6. 异步函数与非阻塞控制流

### 6.1 `async fn` 与 `Future`

`async fn` 定义一个异步函数。调用它**不会立即执行**函数体，而是返回一个实现了 `Future` trait 的对象。
`Future` 代表一个可能在未来完成的计算（例如，一个 I/O 操作）。

### 6.2 `.await` 与控制流暂停/恢复

在 `async` 上下文（`async fn` 或 `async {}` 块）中，`.await` 操作符用于等待一个 `Future` 完成。关键在于：

- 当 `.await` 等待的 `Future` 尚未就绪时，当前 `async fn` 的执行会 **暂停 (yield)**。
- 暂停时，控制权**交还给异步运行时 (Executor)**，允许运行时执行其他就绪的任务（实现并发）。
- 当前线程**不会被阻塞**。
- 当等待的 `Future` 完成后，运行时会**恢复**该 `async fn` 的执行，从 `.await` 暂停点之后继续。

### 6.3 状态机转换

编译器将 `async fn` 转换成一个**状态机 (State Machine)**。这个状态机实现了 `Future` trait。

- **状态**: 对应 `async fn` 中每个 `.await` 点之间或函数开始/结束的代码段。
- **状态保存**: `async fn` 中的局部变量会成为状态机结构体的字段，以便在 `.await` 的暂停和恢复之间保持它们的状态。
- **`poll` 方法**: 异步运行时通过调用 `Future` 的 `poll` 方法来驱动状态机执行。`poll` 要么推进状态机到下一个暂停点（返回 `Poll::Pending`），要么完成计算（返回 `Poll::Ready(value)`）。

### 6.4 异步中的所有权与生命周期

异步代码给所有权和生命周期带来了额外的复杂性：

- **`Send` 和 `Sync`**: 如果 `Future` 需要在线程间移动（常见于多线程运行时），它及其包含的所有状态（捕获的变量、局部变量）必须是 `Send`。如果状态需要在线程间共享引用，则需要 `Sync`。
- **生命周期跨 `.await`**: 引用（借用）的生命周期不能安全地跨越 `.await` 点，因为暂停期间数据可能被修改或销毁。这通常导致需要使用拥有所有权的数据（如将数据 `move` 进 `async` 块或使用 `Arc`）。

### 6.5 代码示例

```rust
// 需要 tokio 依赖: tokio = { version = "1", features = ["full"] }
use tokio::time::{sleep, Duration};
use std::sync::Arc;

async fn fetch_url(url: String) -> String {
    println!("Fetching {}...", url);
    sleep(Duration::from_millis(100)).await; // 暂停点 1
    println!("Finished fetching {}", url);
    format!("Data from {}", url)
}

async fn process_data(data: Arc<Vec<i32>>) -> usize {
    println!("Processing data (first pass)...");
    sleep(Duration::from_millis(50)).await; // 暂停点 2
    // Arc 允许安全地跨 await 共享数据
    let len = data.len();
    println!("Processing data (second pass)...");
    sleep(Duration::from_millis(50)).await; // 暂停点 3
    len * 2
}

#[tokio::main] // 启动 Tokio 运行时
async fn main() {
    let url1 = String::from("http://example.com");
    let url2 = String::from("http://example.org");
    let shared_data = Arc::new(vec![1, 2, 3]);

    // 使用 tokio::join! 并发执行多个 Future
    let (result1, result2, processed_len) = tokio::join!(
        fetch_url(url1), // fetch_url(url1) 返回 Future
        fetch_url(url2.clone()), // 需要 clone url2 因为所有权会被移入 Future
        process_data(shared_data.clone()) // Arc::clone 是廉价的引用计数增加
    );

    println!("Result 1: {}", result1);
    println!("Result 2: {}", result2);
    println!("Processed data result: {}", processed_len);
}
// 控制流: join! 会同时 poll 所有三个 Future。
// 每个 Future 在其 .await 点暂停，允许其他 Future 运行。
// 直到所有 Future 都完成后，join! 才返回结果。
```

## 7. 形式化视角与类型系统总结

Rust 的控制流设计与其类型系统紧密耦合，提供了强大的静态保证：

1. **表达式为中心**: `if`, `match` 等作为表达式，强制类型统一，减少了特定类型的错误。形式化 \( \Gamma \vdash e : T \) 强调了类型在上下文中的重要性。
2. **模式匹配与穷尽性**: `match` (以及 `if let`, `while let`) 提供了结构化的解构和分支，穷尽性检查保证了所有情况都被考虑，排除了许多逻辑错误。
3. **所有权与生命周期**: 贯穿所有控制流结构。编译器静态跟踪数据的所有权转移和借用范围，确保在任何执行路径上都不会发生数据竞争、悬垂引用或二次释放。循环、函数调用、闭包捕获、跨 `await` 都受此约束。
4. **Trait 系统**: `Iterator`, `Fn*`, `Future` 等 Trait 定义了通用行为接口，使得 `for`, 闭包调用, `.await` 等控制流机制具有统一、可组合且类型安全的基础。
5. **Never 类型 (`!`)**: 形式化地标记永不返回的控制路径，增强了编译器的类型检查和流程分析能力，例如允许 `match` 分支在调用发散函数时不必返回值。

**核心目标**: 通过在编译时利用类型系统对控制流进行严格分析，Rust 旨在消除传统语言中常见的运行时错误，提供高性能的同时保证内存安全和线程安全。

## 8. 思维导图 (文本)

```text
Rust 控制流分析 (修订版)
├── 1. 引言
│   ├── 控制流定义
│   └── 与所有权/借用/生命周期的关系
├── 2. 条件控制表达式 (返回值)
│   ├── 2.1 if 表达式
│   │   ├── 定义 & 控制流
│   │   ├── 作为表达式 (类型一致性)
│   │   ├── 所有权 & 借用规则
│   │   ├── 形式化视角 (E_if)
│   │   └── 代码示例
│   ├── 2.2 if let 表达式 (语法糖)
│   │   ├── 模式匹配 Option/Result/Enum
│   │   └── 代码示例
│   ├── 2.3 match 表达式
│   │   ├── 定义 & 强大模式匹配
│   │   ├── 穷尽性检查 (编译时)
│   │   ├── 所有权 & 借用 (分支绑定)
│   │   ├── 形式化视角 (E_match)
│   │   └── 代码示例
├── 3. 循环控制语句
│   ├── 3.1 loop 语句
│   │   ├── 无限循环 & break 退出
│   │   └── break value 返回值
│   ├── 3.2 while 语句 (条件前置检查)
│   ├── 3.3 while let 语句 (循环 + 模式匹配)
│   ├── 3.4 for 语句 (基于 Iterator)
│   │   └── 安全性 & 惯用法
│   ├── 3.5 循环中的所有权 & 借用 (iter/iter_mut/into_iter)
│   ├── 3.6 break & continue (含标签 'label)
│   └── 3.7 代码示例 (综合)
├── 4. 函数与控制流
│   ├── 4.1 调用/返回 (栈帧, 控制权转移)
│   │   └── 所有权传递 (按值/移动/借用)
│   ├── 4.2 递归 (自调用, Base Case)
│   ├── 4.3 发散函数 (!) (永不返回)
│   └── 4.4 代码示例
├── 5. 闭包与控制流
│   ├── 5.1 定义 & 环境捕获
│   │   └── Fn/FnMut/FnOnce Traits (与借用/所有权关联)
│   ├── 5.2 作为控制流 (高阶函数, 回调, 延迟执行)
│   ├── 5.3 move 关键字 (强制捕获所有权)
│   └── 5.4 代码示例
├── 6. 异步函数与非阻塞控制流
│   ├── 6.1 async fn & Future (延迟计算)
│   ├── 6.2 .await (暂停/恢复, 非阻塞)
│   ├── 6.3 状态机转换 (编译器实现)
│   ├── 6.4 异步中的所有权 & 生命周期 (Send/Sync, 跨 await)
│   └── 6.5 代码示例 (tokio, join!)
├── 7. 形式化视角与类型系统总结
│   ├── 表达式为中心 & 类型安全
│   ├── 模式匹配 & 穷尽性
│   ├── 所有权/借用/生命周期 的静态约束
│   ├── Traits 定义行为接口
│   ├── Never 类型 (!) 的作用
│   └── 核心目标: 编译时安全保证
└── 8. 思维导图 (文本)
```
