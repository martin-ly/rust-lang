# 代数数据类型 (Algebraic Data Types)

## 1. 核心概念

代数数据类型（Algebraic Data Types, ADTs）是类型论中的一个核心概念，它允许通过组合现有类型来创建新类型。其"代数"性质来源于新类型的可能值集合可以通过对基础类型集合进行代数运算（主要是乘法和加法）来描述。

Rust 的类型系统深度集成了 ADTs，主要通过两种构造来实现：

- **积类型 (Product Types)**：将多个类型组合在一起，新类型的值包含所有组成类型的值。这对应于代数中的 **乘法**。
- **和类型 (Sum Types)**：从多个类型中选择一个，新类型的值是其中一个组成类型的值。这对应于代数中的 **加法**。

## 2. 积类型 (Product Types)

积类型将多个类型 `T1, T2, ..., Tn` 聚合为一个复合类型。一个积类型的值必须同时包含所有这些类型的值。

### 2.1 形式化定义

从集合论的角度看，如果类型 `T` 的值集合为 `S(T)`，那么由类型 `A` 和 `B` 构成的积类型 `P` 的值集合 `S(P)` 是 `S(A)` 和 `S(B)` 的 **笛卡尔积 (Cartesian Product)**：

\[
S(P) = S(A) \times S(B) = \{ (a, b) \mid a \in S(A) \land b \in S(B) \}
\]

一个积类型的值的数量是其组成类型的值的数量的乘积。例如，`bool` 有2个值，`(bool, bool)` 有 `2 * 2 = 4` 个值。

在范畴论中，积类型对应于范畴中的 **积 (Product)** 对象。

### 2.2 在 Rust 中的实现

Rust 主要通过 `struct` 和元组 `tuple` 来实现积类型。

#### 2.2.1 结构体 (Structs)

结构体通过为每个字段命名来定义一个积类型。

```rust
// 定义一个积类型 Point，由两个 f64 类型的字段组成
struct Point {
    x: f64,
    y: f64,
}

// 创建 Point 类型的一个实例
let p = Point { x: 1.0, y: 2.0 };
```

#### 2.2.2 元组 (Tuples)

元组是匿名的积类型，通过位置来访问其元素。

```rust
// 定义一个积类型，由 i32 和 String 组成
let pair: (i32, String) = (1, "hello".to_string());

// 通过位置访问元素
let number = pair.0;
let text = pair.1;
```

#### 2.2.3 单元结构体 (Unit-like Structs)

单元结构体是一种特殊的积类型，它不包含任何字段。其值集合只有一个元素，对应于代数中的 `1`。它在范畴论中对应 **终对象 (Terminal Object)**。

```rust
struct Marker;
let m = Marker;
```

## 3. 和类型 (Sum Types)

和类型，也称为标签联合（Tagged Union）或变体（Variant），表示一个值可以是多种不同类型中的 **一种**。每个可能的值都带有一个标签（tag）来指明它当前是哪种类型。

### 3.1 形式化定义

从集合论的角度看，由类型 `A` 和 `B` 构成的和类型 `S` 的值集合 `S(S)` 是 `S(A)` 和 `S(B)` 的 **不交并 (Disjoint Union)**：

\[
S(S) = S(A) \sqcup S(B) = (\{ \text{tag}_A \} \times S(A)) \cup (\{ \text{tag}_B \} \times S(B))
\]

一个和类型的值的数量是其组成类型的值的数量的和。例如，`Option<bool>` (在概念上是 `bool` 和 `()` 的和) 有 `2 + 1 = 3` 个可能的值 (`Some(true)`, `Some(false)`, `None`)。

在范畴论中，和类型对应于 **余积 (Coproduct)** 对象。

### 3.2 在 Rust 中的实现

Rust 通过 `enum` 关键字实现和类型。`enum` 的每个变体（variant）都是一个独立的构造器，可以包含不同类型的数据。

```rust
// 定义一个和类型 Shape
enum Shape {
    Circle(f64),                  // 包含一个 f64
    Rectangle { width: f64, height: f64 }, // 包含一个积类型
    Point,                        // 单元变体，对应于单元类型
}

// 创建 Shape 类型的实例
let circle = Shape::Circle(10.0);
let rect = Shape::Rectangle { width: 3.0, height: 4.0 };
let point = Shape::Point;
```

Rust 的 `Option<T>` 和 `Result<T, E>` 是和类型的典型应用：

- `Option<T>` 在形式上是 `T + 1`，代表一个值要么是 `T` 类型，要么是单元类型 `()`。
- `Result<T, E>` 在形式上是 `T + E`，代表一个值要么是 `T` 类型，要么是 `E` 类型。

## 4. 模式匹配：和类型的消除规则

代数数据类型的强大之处在于其与模式匹配的深度集成。特别是对于和类型，模式匹配是其核心的 **消除规则 (Elimination Rule)**。它允许安全地解构一个 `enum`，并为每个可能的变体提供一个处理分支。

Rust 的编译器会强制进行 **穷尽性检查 (Exhaustiveness Checking)**，确保 `match` 表达式处理了 `enum` 的所有变体。这消除了传统 C/C++ 联合（union）中忘记检查标签的风险，是类型安全的重要保证。

```rust
fn get_area(shape: Shape) -> f64 {
    match shape {
        Shape::Circle(radius) => std::f64::consts::PI * radius * radius,
        Shape::Rectangle { width, height } => width * height,
        Shape::Point => 0.0,
    }
}
```

在这个例子中，`match` 表达式安全地消费了一个 `Shape` 类型的值，并根据其变体执行相应的逻辑。如果 `Shape` 添加了新的变体，而此 `match` 表达式没有更新，编译器将会报错。这种机制确保了代码的健壮性和可维护性。
