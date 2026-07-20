# 控制流：条件与循环

## 目录

- [控制流：条件与循环](#控制流条件与循环)
  - [目录](#目录)
    - [1. 作为表达式的控制流](#1-作为表达式的控制流)
    - [2. 条件表达式](#2-条件表达式)
      - [2.1. `if-else` 表达式](#21-if-else-表达式)
      - [2.2. `if let` 表达式](#22-if-let-表达式)
    - [3. 循环结构](#3-循环结构)
      - [3.1. `loop`：无限循环与返回值](#31-loop无限循环与返回值)
      - [3.2. `while`：条件循环](#32-while条件循环)
      - [3.3. `while let`：条件模式匹配循环](#33-while-let条件模式匹配循环)
      - [3.4. `for`：迭代循环](#34-for迭代循环)
      - [3.5. `break` 与 `continue`](#35-break-与-continue)
    - [4. 循环中的所有权与借用](#4-循环中的所有权与借用)
    - [5. 哲学批判性分析](#5-哲学批判性分析)

---

### 1. 作为表达式的控制流

Rust 的一个核心设计哲学是 **表达式优先 (Expression-Oriented)**。
与许多将 `if`、`switch` 等作为语句 (Statement) 的语言不同，
Rust 中的大多数控制流结构都是表达式 (Expression)，这意味着它们可以计算并返回一个值。

这个设计有几个重要优势：

- **简洁性**: 允许将条件逻辑直接用在 `let` 绑定中，避免了冗余的临时变量声明。
- **安全性**: 编译器强制要求 `if-else` 或 `match` 的所有分支必须返回相同的类型，这消除了因分支类型不匹配而导致的潜在错误。
- **函数式风格**: 鼓励开发者编写更具声明性和组合性的代码。

### 2. 条件表达式

#### 2.1. `if-else` 表达式

`if` 基于布尔条件选择性地执行代码块。
当 `if` 带有 `else` 块时，它就构成了一个完整的表达式。

```rust
let temperature = 25;
let weather = if temperature > 30 {
    "Hot" // 此分支返回 &str
} else if temperature < 10 {
    "Cold" // 此分支返回 &str
} else {
    "Moderate" // 此分支也必须返回 &str
};
// `weather` 被绑定为 "Moderate"
```

**所有权**: 如果 `if-else` 的某个分支移动了值的所有权，那么在表达式之后，该值将不可用（除非所有分支都移动了该值并赋给同一变量）。

#### 2.2. `if let` 表达式

`if let` 是 `match` 的一种语法糖，用于当你只关心一种模式匹配成功的情况时，可以写出更简洁的代码。

```rust
let favorite_color: Option<&str> = None;
let is_tuesday = false;

if let Some(color) = favorite_color {
    println!("Using your favorite color, {}, as the background", color);
} else if is_tuesday {
    println!("Tuesday is green day!");
} else {
    println!("Using blue as the background color");
}
```

`if let` 同样可以与 `else` 和 `else if` 组合，形成复杂的条件逻辑链。

### 3. 循环结构

循环用于重复执行代码块，直到满足某个终止条件。

#### 3.1. `loop`：无限循环与返回值

`loop` 关键字创建一个无限循环，必须使用 `break` 关键字显式退出。
`loop` 一个独特的特性是，它可以作为表达式从 `break` 中返回值。

```rust
let mut counter = 0;

let result = loop {
    counter += 1;
    if counter == 10 {
        // 使用 break 退出循环并返回值
        break counter * 2; 
    }
};
// `result` 被绑定为 20
assert_eq!(result, 20);
```

#### 3.2. `while`：条件循环

`while` 循环在每次迭代开始前检查一个布尔条件。
如果条件为 `true`，则执行循环体；否则，循环终止。

```rust
let mut number = 3;

while number != 0 {
    println!("{}!", number);
    number -= 1;
}
println!("LIFTOFF!!!");
```

#### 3.3. `while let`：条件模式匹配循环

类似于 `if let`，`while let` 只要模式匹配成功，循环就会一直持续。
它在处理如 `Option` 或消耗迭代器等场景时非常有用。

```rust
let mut stack = vec![1, 2, 3];

// .pop() 返回 Option<i32>
// 只要 pop() 返回 Some(value)，循环就继续
while let Some(top) = stack.pop() {
    println!("{}", top);
}
// 循环结束后，stack 为空
```

#### 3.4. `for`：迭代循环

`for` 循环是 Rust 中最常用、最安全、最惯用的循环方式。
它通过迭代任何实现了 `IntoIterator` Trait 的类型来工作。

```rust
let a = [10, 20, 30, 40, 50];

// item 是数组中的每个元素的拷贝（因为 i32 是 Copy）
for item in a.iter() {
    println!("the value is: {}", item);
}

// .rev() 创建一个反向迭代器
for number in (1..4).rev() {
    println!("{}!", number);
}
```

`for` 循环会自动处理迭代器的所有权和结束条件，使其比手写 `while` 循环更安全，不易出错。

#### 3.5. `break` 与 `continue`

- `break`: 立即终止并退出当前循环。
- `continue`: 跳过本次循环的剩余部分，立即开始下一次迭代。

Rust 还支持 **循环标签 (loop labels)**，允许 `break` 和 `continue` 指定它们作用于哪个嵌套循环。

```rust
'outer: loop {
    println!("Entered the outer loop");
    'inner: loop {
        println!("Entered the inner loop");
        // 这只会退出内部循环
        // break;

        // 这会退出外部循环
        break 'outer;
    }
    println!("This point will not be reached");
}
println!("Exited the outer loop");
```

### 4. 循环中的所有权与借用

`for` 循环会获得迭代器表达式的所有权。
在循环内部，迭代产生的每个元素的所有权如何处理，取决于调用的是 `into_iter()`、`iter()` 还是 `iter_mut()`：

- `into_iter()`: 迭代 `T`。循环体获得每个元素的所有权。
- `iter()`: 迭代 `&T`。循环体获得对每个元素的不可变引用。
- `iter_mut()`: 迭代 `&mut T`。循环体获得对每个元素的可变引用。

```rust
let names = vec![String::from("Alice"), String::from("Bob")];

// .iter() 创建 &String 的迭代器，name 的类型是 &String
for name in names.iter() {
    println!("Name: {}", name);
}
// `names` 在这里仍然可用

let mut mut_names = vec![String::from("Alice"), String::from("Bob")];
// .iter_mut() 创建 &mut String 的迭代器
for name in mut_names.iter_mut() {
    name.push_str(" Smith");
}

// .into_iter() 创建 String 的迭代器
// 循环结束后，`names` 的所有权被移出，不再可用
for name in names.into_iter() {
    // name 的类型是 String
    println!("Consumed name: {}", name);
}
// println!("{:?}", names); // 编译错误：value borrowed here after move
```

### 5. 哲学批判性分析

Rust 对基础控制流的设计体现了其对安全和表现力的双重追求。

- **表达式驱动**: 将 `if` 和 `loop` 设计为表达式，简化了代码，并利用类型系统强制分支返回类型一致，这是一种编译时的安全保证。
- **迭代器抽象 (`for`)**: `for` 循环与 `Iterator` Trait 的深度集成，
是 Rust "零成本抽象"的典范。它将复杂的迭代逻辑（状态管理、结束条件、所有权）封装在安全的、可组合的接口背后，
使得手写循环（尤其是索引循环）成为反模式。
- **所有权集成**: 所有权和借用规则无缝地应用于所有控制流路径。
编译器静态地验证所有分支和所有循环迭代的资源使用情况，这在系统语言中是独一无二的，它从根本上消除了因复杂控制流导致的资源泄漏或悬垂指针问题。
