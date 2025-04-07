/*
从范畴论的视角来看，Rust的类型系统确实可以被视为基于原生类型的组合映射。
这种分析提供了一种理解Rust类型系统的深层次视角，以下是一些相关的思考：
1. **类型作为对象**
在范畴论中，类型可以被视为对象，而值则是这些对象的实例。
Rust中的每种类型（如整数、浮点数、结构体、枚举等）都可以被视为一个对象，
这些对象之间可以通过不同的映射（态射）进行组合。
2. **组合映射**
Rust的类型系统支持组合类型（如元组、结构体和枚举），
这些组合类型可以看作是基本类型的组合映射。
例如，结构体可以包含多个字段，每个字段可以是不同的类型，这种组合可以通过`struct`定义。

```rust
struct Point {
    x: f64,
    y: f64,
}
```
在这个例子中，`Point`结构体可以被视为一个组合类型，它将两个原生类型（`f64`）组合在一起。

3. **代数数据类型**
Rust的枚举类型（如`enum`）可以被视为代数数据类型（Algebraic Data Types, ADTs），
它们允许通过组合不同的构造函数来定义复杂的类型。
这种组合可以看作是范畴论中的和（sum）类型。

```rust
enum Shape {
    Circle(f64),
    Rectangle(f64, f64),
}
```

在这个例子中，`Shape`枚举可以表示不同的形状，每种形状都可以看作是一个不同的构造函数。

4. **态射与模式匹配**
在Rust中，`match`语句可以被视为一种态射，
它将输入的复杂数据结构映射到输出的结果。
通过模式匹配，Rust能够在类型安全的前提下处理不同的输入类型并返回相应的结果。
这种映射确保了类型的一致性和安全性。

5. **高阶类型与泛型**
Rust的泛型和高阶类型（如函数类型）允许我们定义接受其他类型作为参数的类型。
这种特性使得Rust的类型系统更加灵活，能够表达更复杂的类型关系。

```rust
fn apply<F, T>(func: F, value: T) -> T
where
    F: Fn(T) -> T,
{
    func(value)
}
```

在这个例子中，`apply`函数接受一个高阶函数作为参数，这种高阶类型的组合可以看作是范畴论中的态射。

总结

从范畴论的视角来看，Rust的类型系统确实可以被理解为基于原生类型的组合映射。
通过将类型视为对象、使用组合类型和代数数据类型、以及通过态射和模式匹配来处理数据，
Rust的类型系统展现了范畴论的深层结构。
这种分析不仅有助于理解Rust的设计哲学，也为编程语言的类型系统提供了更广泛的理论基础。

*/

/*
在 Rust 中，具体类型、数据类型、抽象类型和多态类型（泛型）是构建类型系统的基本概念。
以下是对这些概念的定义和示例：

1. 具体类型（Concrete Types）
具体类型是指在编译时已知的类型，例如基本数据类型、结构体、枚举等。
它们的大小和布局在编译时是固定的。

示例

```rust
struct Point {
    x: i32,
    y: i32,
}

enum Color {
    Red,
    Green,
    Blue,
}

fn main() {
    let p = Point { x: 10, y: 20 };
    let c = Color::Red;
}
```

2. 数据类型（Data Types）

数据类型是指在 Rust 中定义的所有类型，
包括基本类型（如整数、浮点数、布尔值等）、
复合类型（如元组、数组）、结构体、枚举和 trait。

示例

```rust
// 基本数据类型
let integer: i32 = 42;
let float: f64 = 3.14;
let boolean: bool = true;

// 复合数据类型
let tuple: (i32, f64) = (42, 3.14);
let array: [i32; 3] = [1, 2, 3];
```

3. 抽象类型（Abstract Types）

抽象类型通常指 trait，它们定义了一组方法的接口，但不提供具体的实现。
实现了某个 trait 的类型可以被视为该抽象类型。

示例

```rust
trait Shape {
    fn area(&self) -> f64; // 抽象方法
}

struct Circle {
    radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }
}
```

4. 多态类型（泛型）

泛型允许你定义函数、结构体、枚举和 trait，使其能够处理多种类型，而不需要在编写时指定具体类型。
泛型在 Rust 中通过尖括号 `<T>` 来表示。

示例

```rust
// 定义一个泛型函数
fn print_value<T: std::fmt::Display>(value: T) {
    println!("{}", value);
}

// 定义一个泛型结构体
struct Pair<T, U> {
    first: T,
    second: U,
}

fn main() {
    print_value(42); // 整数
    print_value(3.14); // 浮点数

    let pair = Pair { first: 1, second: "hello" }; // 泛型结构体
}
```

总结
- **具体类型**：在编译时已知的类型，如结构体和枚举。
- **数据类型**：Rust 中定义的所有类型，包括基本类型和复合类型。
- **抽象类型**：通过 trait 定义的接口，允许不同类型实现相同的方法。
- **多态类型（泛型）**：允许定义处理多种类型的函数和数据结构，使用尖括号表示。
通过这些概念，Rust 提供了强大的类型系统，支持安全和灵活的编程。

**/

pub mod collection;
pub mod composite;
