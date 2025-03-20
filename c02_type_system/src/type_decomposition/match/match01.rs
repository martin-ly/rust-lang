/*
在 Rust 中，具体类型、数据类型、抽象类型和多态类型（泛型）是构建类型系统的基本概念。以下是对这些概念的定义和示例：

### 1. 具体类型（Concrete Types）

具体类型是指在编译时已知的类型，例如基本数据类型、结构体、枚举等。它们的大小和布局在编译时是固定的。

#### 示例

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

### 2. 数据类型（Data Types）

数据类型是指在 Rust 中定义的所有类型，包括基本类型（如整数、浮点数、布尔值等）、复合类型（如元组、数组）、结构体、枚举和 trait。

#### 示例

```rust
// 基本数据类型
let integer: i32 = 42;
let float: f64 = 3.14;
let boolean: bool = true;

// 复合数据类型
let tuple: (i32, f64) = (42, 3.14);
let array: [i32; 3] = [1, 2, 3];
```

### 3. 抽象类型（Abstract Types）

抽象类型通常指 trait，它们定义了一组方法的接口，但不提供具体的实现。实现了某个 trait 的类型可以被视为该抽象类型。

#### 示例

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

### 4. 多态类型（泛型）

泛型允许你定义函数、结构体、枚举和 trait，使其能够处理多种类型，而不需要在编写时指定具体类型。泛型在 Rust 中通过尖括号 `<T>` 来表示。

#### 示例

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

### 总结

- **具体类型**：在编译时已知的类型，如结构体和枚举。
- **数据类型**：Rust 中定义的所有类型，包括基本类型和复合类型。
- **抽象类型**：通过 trait 定义的接口，允许不同类型实现相同的方法。
- **多态类型（泛型）**：允许定义处理多种类型的函数和数据结构，使用尖括号表示。

通过这些概念，Rust 提供了强大的类型系统，支持安全和灵活的编程。

**/

//match 解构类型

#[allow(unused)]
pub fn base_type01() {
    let x = 10;
    match x {
        1 => println!("x is 1"),
        2 => println!("x is 2"),
        3..=10 => println!("x is 3 to 10"),
        _ => println!("x is other"),
    }
}

#[allow(unused)]
pub fn base_type02() {
    enum Color {
        Red,
        Green,
        Blue,
    }
 
    let color = Color::Green;
    match color {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        Color::Blue => println!("Blue"),
    }
}

#[allow(unused)]
pub fn base_type03() {
    struct Point {
        x: i32,
        y: i32,
    }
 
    let point = Point { x: 10, y: 20 };
    match point {
        Point { x, y: 0 } => println!("On the x-axis at {}", x),
        Point { x: 0, y } => println!("On the y-axis at {}", y),
        Point { x, y } => println!("Point at ({}, {})", x, y),
    }
}


#[allow(unused)]
pub fn base_type04() {
    let tuple = (1, 2);
    match tuple {
        (x, y) => println!("x: {}, y: {}", x, y),
    }
}


#[allow(unused)]
pub fn base_type05() {
    let array = [1, 2, 3];
    match array {
        [x, y, z] => println!("x: {}, y: {}, z: {}", x, y, z),
    }

    match array {
        [1, _, _] => println!("Starts with 1"),
        _ => println!("Other"),
    }
}


#[allow(unused)]
pub fn base_type06() {
    let some_value: Option<i32> = Some(10);
    match some_value {
        Some(value) => println!("Value is: {}", value),
        None => println!("No value"),
    }
}

#[allow(unused)]
pub fn base_type07() {

    #[derive(PartialEq)] // 自动实现 PartialEq
    struct MyStruct {
        value: i32,
    }
    
    // 注意：没有实现 PartialEq trait
    impl MyStruct {
        fn new(value: i32) -> Self {
            MyStruct { value }
        }
    }
    

    let my_instance = MyStruct::new(10);

    // 尝试在 match 中解构 MyStruct
    match my_instance {
        MyStruct { value } => println!("Value is: {}", value), // 这里会报错
    }
    // error[E0277]: the trait bound `MyStruct: PartialEq` is not satisfied
    // 解决方法：实现 PartialEq trait
}

/*
不可以解构的类型
原始类型：
    原始类型（如 i32、f64 等）不能被解构为更复杂的结构。
未实现 match 的类型：
    自定义类型如果没有实现 PartialEq 或 Eq trait，可能无法直接使用 match 进行比较。
动态类型：
    Rust 不支持动态类型（如 JavaScript 中的对象），因此不能直接解构。
总结
    虽然 match 表达式可以解构多种类型
    （如基本类型、枚举、结构体、元组、数组、切片、Option 和 Result），
    但并不是所有类型都可以使用 match 进行解构。
    具体来说，原始类型和未实现必要 trait 的类型不能直接解构。
*/

#[allow(dead_code)]
pub enum Message {
    Hello { id: i32 },
    Goodbye { id: i32 },
}

#[allow(dead_code)]
pub fn process_message(msg: Message) {
    match msg {
        Message::Hello { id: id @ 1..=10 } => {
            println!("Hello message with id: {}", id);
        }
        Message::Goodbye { id } => {
            println!("Goodbye message with id: {}", id);
        }
        _ => {
            println!("Other message");
        }
    }
}


#[allow(dead_code)]
pub fn fizz_buzz(n: u32) -> String {
    match (n % 3, n % 5) {
        (0, 0) => "FizzBuzz".to_string(),
        (0, _) => "Fizz".to_string(),
        (_, 0) => "Buzz".to_string(),
        (_, _) => n.to_string(),
    }
}


#[allow(dead_code)]
pub fn match_guard(x: u32) {
    match x {
        x if x % 2 == 0 => println!("Even"),
        x if x % 2 != 0 => println!("Odd"),
        _ => println!("Other"),
    }
}


