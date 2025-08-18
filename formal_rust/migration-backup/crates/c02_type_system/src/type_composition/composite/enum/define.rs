/*
在Rust中，enum（枚举）是一种自定义数据类型，可以表示一组相关的值。
每个值称为一个变体（variant），可以包含不同类型的数据。
枚举在Rust中非常强大，常用于表示状态、选择或多态性。
定义：
    枚举使用enum关键字定义，后面跟着枚举的名称和变体的定义。
    每个变体可以是简单的，也可以包含数据。
解释：
    枚举允许你定义一个类型，该类型可以是多个不同值中的一个。
    它们通常用于表示一组相关的状态或选项，特别是在需要处理不同类型的值时。

枚举（enum）：用于定义一组相关的值，可以是多个不同值中的一个。
变体：枚举的每个值称为变体，可以是简单的或包含数据。
模式匹配：使用match语句可以方便地处理不同的枚举变体。
示例：
    1. 定义枚举
    2. 枚举包含数据
    3. 枚举的综合示例
    4. 枚举的多态性
    5. 枚举的默认实现
*/

pub fn define_enum() {
    println!("1. 定义枚举");

    #[allow(unused)]
    enum Direction {
        Up,
        Down,
        Left,
        Right,
    }

    let move_direction = Direction::Up;

    match move_direction {
        Direction::Up => println!("Moving up!"),
        Direction::Down => println!("Moving down!"),
        Direction::Left => println!("Moving left!"),
        Direction::Right => println!("Moving right!"),
    }
}

pub fn define_enum_2() {
    println!("2. 枚举包含数据");
    #[allow(unused)]
    enum Shape {
        Circle(f64),         // 半径
        Rectangle(f64, f64), // 宽度和高度
    }

    fn area(shape: &Shape) -> f64 {
        match shape {
            Shape::Circle(radius) => std::f64::consts::PI * radius * radius,
            Shape::Rectangle(width, height) => width * height,
        }
    }

    let circle = Shape::Circle(2.0);
    let rectangle = Shape::Rectangle(3.0, 4.0);

    println!("Circle area: {}", area(&circle)); // 输出: Circle area: 12.566370614359172
    println!("Rectangle area: {}", area(&rectangle)); // 输出: Rectangle area: 12
}

pub fn define_enum_3() {
    println!("3. 枚举的综合示例");
    #[allow(unused)]
    enum Operation {
        Add(i32, i32),
        Subtract(i32, i32),
        Multiply(i32, i32),
        Divide(i32, i32),
    }

    fn calculate(operation: Operation) -> f32 {
        match operation {
            Operation::Add(a, b) => (a + b) as f32,
            Operation::Subtract(a, b) => (a - b) as f32,
            Operation::Multiply(a, b) => (a * b) as f32,
            Operation::Divide(a, b) => {
                if b != 0 {
                    (a / b) as f32
                } else {
                    panic!("Cannot divide by zero!");
                }
            }
        }
    }

    let add = Operation::Add(5, 3);
    let subtract = Operation::Subtract(10, 4);
    let multiply = Operation::Multiply(2, 6);
    let divide = Operation::Divide(8, 2);

    println!("5 + 3 = {}", calculate(add)); // 输出: 5 + 3 = 8
    println!("10 - 4 = {}", calculate(subtract)); // 输出: 10 - 4 = 6
    println!("2 * 6 = {}", calculate(multiply)); // 输出: 2 * 6 = 12
    println!("8 / 2 = {}", calculate(divide)); // 输出: 8 / 2 = 4
}

/*
枚举的多态性
    通过实现特征，可以为枚举提供多态性，使得不同变体可以共享相同的接口。
*/

pub fn define_enum_4() {
    println!("4. 枚举的多态性");
    #[allow(unused)]
    trait Shape {
        fn area(&self) -> f64;
    }

    #[allow(unused)]
    #[derive(Debug)]
    enum MyShape {
        Circle(f64),
        Rectangle(f64, f64),
    }

    impl Shape for MyShape {
        fn area(&self) -> f64 {
            match self {
                MyShape::Circle(radius) => std::f64::consts::PI * radius * radius,
                MyShape::Rectangle(width, height) => width * height,
            }
        }
    }

    let shapes: Vec<MyShape> = vec![MyShape::Circle(2.0), MyShape::Rectangle(3.0, 4.0)];

    for shape in shapes {
        println!("Area: {}", shape.area());
    }
}

/*
枚举的默认实现
    可以为枚举实现Default特征，以便为枚举提供默认值。
*/

pub fn define_enum_5() {
    println!("5. 枚举的默认实现");
    #[allow(unused)]
    #[derive(Debug, Default)]
    enum Color {
        Red,
        Green,
        Blue,
        #[default]
        Unknown,
    }

    let color: Color = Default::default();
    println!("Default color: {:?}", color); // 输出: Default color: Unknown
}
