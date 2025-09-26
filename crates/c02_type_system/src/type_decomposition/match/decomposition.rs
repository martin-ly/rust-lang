/*
从范畴论的角度来看，
Rust的`match`语句与类型系统的结合确实可以被视为一种解构的映射，这种分析视角是有意义的。
以下是一些相关的思考：
1. **类型与模式匹配的关系**：
    在Rust中，`match`语句允许你根据不同的类型和模式来解构数据。
    这种解构可以看作是将复杂的数据结构映射到更简单的形式。
    例如，枚举类型可以被视为一个代数数据类型（Algebraic Data Type），
    而`match`则是对这些类型的模式进行解构和处理。

2. **递归应用**：
    Rust的类型系统支持递归数据结构（如链表、树等），
    而`match`语句可以递归地应用于这些结构。
    通过模式匹配，可以逐层解构数据，直到达到基本情况。
    这种递归的解构方式与范畴论中的递归定义有相似之处。

3. **范畴论中的态射**：
    在范畴论中，态射（morphism）是对象之间的映射。
    `match`语句可以被视为一种态射，它将输入的复杂数据结构映射到输出的简单结果。
    通过模式匹配，Rust能够在类型安全的前提下，处理不同的输入类型并返回相应的结果。

4. **类型安全与模式匹配**：
    Rust的类型系统确保了在使用`match`时，所有可能的模式都被考虑到。
    这种类型安全性使得程序员能够在编译时捕获错误，避免运行时的类型错误。
    这与范畴论中的结构保持一致，确保了映射的有效性。

5. **高阶类型与抽象**：
    Rust的类型系统支持高阶类型和泛型，这使得`match`语句可以与这些抽象结合使用。
    通过将模式匹配与高阶函数结合，可以实现更复杂的逻辑，同时保持代码的简洁性和可读性。

总结
    从范畴论的角度分析Rust的`match`与类型系统的结合，确实提供了一种有趣的视角。
    它强调了类型安全、递归解构和模式匹配之间的深层关系。
    这种分析不仅有助于理解Rust的设计哲学，
    也为编程语言的类型系统和控制流结构提供了更广泛的理论基础。
*/

//match 解构类型
/*
match 表达式可以解构多种类型
（如基本类型、枚举、结构体、元组、数组、切片、Option 和 Result），
但并不是所有类型都可以使用 match 进行解构。

不可以解构的类型
原始类型：
    原始类型（如 i32、f64 等）不能被解构为更复杂的结构。只能解构其值。
未实现 match 的类型：
    自定义类型如果没有实现 PartialEq 或 Eq trait，可能无法直接使用 match 进行比较。
动态类型：
    Rust 不支持动态类型（如 dyn trait 对象），因此不能直接解构。
总结
    虽然 match 表达式可以解构多种类型
    （如基本类型、枚举、结构体、元组、数组、切片、Option 和 Result），
    但并不是所有类型都可以使用 match 进行解构。
    具体来说，原始类型和未实现必要 trait 的类型不能直接解构。
    也不是所有的控制流全使用 match 进行解构。
    比如使用let,if,else等。
*/

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
    let (x, y) = tuple;
    println!("x: {}, y: {}", x, y)
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
    let MyStruct { value } = my_instance;
    println!("Value is: {}", value) // 这里会报错
    // error[E0277]: the trait bound `MyStruct: PartialEq` is not satisfied
    // 解决方法：实现 PartialEq trait
}

#[allow(unused)]
pub enum Message {
    Hello { id: i32 },
    Goodbye { id: i32 },
}

#[allow(unused)]
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

#[allow(unused)]
pub fn fizz_buzz(n: u32) -> String {
    match (n % 3, n % 5) {
        (0, 0) => "FizzBuzz".to_string(),
        (0, _) => "Fizz".to_string(),
        (_, 0) => "Buzz".to_string(),
        (_, _) => n.to_string(),
    }
}

#[allow(unused)]
pub fn match_guard(x: u32) {
    match x {
        x if x % 2 == 0 => println!("Even"),
        x if x % 2 != 0 => println!("Odd"),
        _ => println!("Other"),
    }
}

// 定义一个 Trait，表示图形
trait Shape {
    fn area(&self) -> f64; // 计算面积
    fn draw(&self); // 绘制图形
}

// 定义一个圆形结构体
#[allow(unused)]
pub struct Circle {
    pub radius: f64,
}

impl Shape for Circle {
    fn area(&self) -> f64 {
        std::f64::consts::PI * self.radius * self.radius
    }

    fn draw(&self) {
        println!("Drawing a Circle with radius: {}", self.radius);
    }
}

// 定义一个矩形结构体
#[allow(unused)]
pub struct Rectangle {
    pub width: f64,
    pub height: f64,
}

impl Shape for Rectangle {
    fn area(&self) -> f64 {
        self.width * self.height
    }

    fn draw(&self) {
        println!(
            "Drawing a Rectangle with width: {} and height: {}",
            self.width, self.height
        );
    }
}

// 定义一个枚举，用于存储不同类型的图形
#[allow(unused)]
pub enum ShapeEnum {
    Circle(Circle),
    Rectangle(Rectangle),
}

impl ShapeEnum {
    pub fn area(&self) -> f64 {
        match self {
            ShapeEnum::Circle(circle) => circle.area(),
            ShapeEnum::Rectangle(rectangle) => rectangle.area(),
        }
    }

    pub fn draw(&self) {
        match self {
            ShapeEnum::Circle(circle) => circle.draw(),
            ShapeEnum::Rectangle(rectangle) => rectangle.draw(),
        }
    }
}
