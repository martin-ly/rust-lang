use serde::{Deserialize, Serialize};

/*
在Rust中，枚举的高级应用可以通过多种方式实现，
包括使用模式匹配、特征结合、嵌套枚举、元组枚举和泛型枚举等。

总结
1. 关联函数：为枚举定义关联函数以便更方便地创建和操作实例。
2. 组合与嵌套：枚举可以嵌套其他枚举或结构体，以构建复杂的数据结构。
3. 模式匹配与解构：使用模式匹配解构和访问枚举数据。
4. 可序列化与反序列化：使用serde库轻松处理枚举的序列化和反序列化。
5. 错误处理：枚举常用于表示错误类型，便于处理操作的成功或失败。
6. 泛型：枚举可以使用泛型提高灵活性和重用性。
*/

/*
1. 枚举的关联函数
    可以为枚举定义关联函数，以便更方便地创建和操作枚举实例。
*/
#[allow(unused)]
pub fn advance_enum01() {
    println!("1. 枚举的关联函数");

    #[allow(unused)]
    #[derive(Debug)]
    enum TrafficLight {
        Red,
        Yellow,
        Green,
    }

    impl TrafficLight {
        fn next(&self) -> TrafficLight {
            match self {
                TrafficLight::Red => TrafficLight::Green,
                TrafficLight::Yellow => TrafficLight::Red,
                TrafficLight::Green => TrafficLight::Yellow,
            }
        }
    }

    let light = TrafficLight::Red;
    println!("Current light: {:?}", light);
    let next_light = light.next();
    println!("Next light: {:?}", next_light);
}

/*
2. 枚举的组合与嵌套
    枚举可以嵌套其他枚举或结构体，以构建复杂的数据结构。
*/

#[allow(unused)]
pub fn advance_enum02() {
    println!("2. 枚举的组合与嵌套");
    #[allow(unused)]
    #[derive(Debug)]
    enum Shape {
        Circle(f64),
        Rectangle(f64, f64),
    }

    #[allow(unused)]
    #[derive(Debug)]
    enum ShapeType {
        Basic(Shape),
        Complex(Vec<ShapeType>),
    }

    let circle = ShapeType::Basic(Shape::Circle(2.0));
    let rectangle = ShapeType::Basic(Shape::Rectangle(3.0, 4.0));
    let complex_shape = ShapeType::Complex(vec![circle, rectangle]);

    match complex_shape {
        ShapeType::Basic(shape) => match shape {
            Shape::Circle(radius) => println!("Circle with radius: {}", radius),
            Shape::Rectangle(width, height) => println!("Rectangle {} x {}", width, height),
        },
        ShapeType::Complex(shapes) => {
            println!("Complex shape with {} shapes.", shapes.len());
        }
    }
}

/*
3. 枚举的模式匹配与解构
    Rust的模式匹配功能可以与枚举结合使用，以便更方便地解构和访问数据。
*/

#[allow(unused)]
pub fn advance_enum03() {
    println!("3. 枚举的模式匹配与解构");

    #[allow(unused)]
    #[derive(Debug)]
    enum Message {
        Quit,
        ChangeColor(i32, i32, i32),
        Move { x: i32, y: i32 },
    }

    fn process_message(msg: Message) {
        match msg {
            Message::Quit => println!("Quit message received."),
            Message::ChangeColor(r, g, b) => {
                println!("Change color to RGB({}, {}, {})", r, g, b);
            }
            Message::Move { x, y } => {
                println!("Move to position ({}, {})", x, y);
            }
        }
    }

    let msg1 = Message::Quit;
    let msg2 = Message::ChangeColor(255, 0, 0);
    let msg3 = Message::Move { x: 10, y: 20 };

    process_message(msg1);
    process_message(msg2);
    process_message(msg3);
}

/*
4. 枚举的可序列化与反序列化
    使用第三方库（如serde）可以轻松地将枚举序列化为JSON或其他格式，或从这些格式反序列化。
*/

#[allow(unused)]
pub fn advance_enum04() {
    println!("4. 枚举的可序列化与反序列化");

    #[allow(unused)]
    #[derive(Serialize, Deserialize, Debug)]
    enum Command {
        Start,
        Stop,
        Pause,
    }
    let command = Command::Start;

    // 序列化为JSON
    let json = serde_json::to_string(&command).unwrap();
    println!("Serialized: {:?}", json);

    // 反序列化
    let deserialized_command: Command = serde_json::from_str(&json).unwrap();
    println!("Deserialized: {:?}", deserialized_command);
}

/*
5. 枚举的错误处理
    枚举常用于错误处理，特别是通过Result和Option类型来表示操作的成功或失败。
*/

#[allow(unused)]
pub fn advance_enum05() {
    println!("5. 枚举的错误处理");

    #[allow(unused)]
    #[derive(Debug)]
    enum MyError {
        NotFound,
        PermissionDenied,
    }

    fn find_item(id: i32) -> Result<String, MyError> {
        if id == 1 {
            Ok(String::from("Item found"))
        } else {
            Err(MyError::NotFound)
        }
    }

    match find_item(1) {
        Ok(item) => println!("{}", item),
        Err(MyError::NotFound) => println!("Item not found."),
        Err(MyError::PermissionDenied) => println!("Permission denied."),
    }
}

/*
6. 枚举的泛型
    枚举可以使用泛型来处理不同类型的数据，从而提高代码的灵活性和重用性。
*/

#[allow(unused)]
pub fn advance_enum06() {
    println!("6. 枚举的泛型");

    #[allow(unused)]
    #[derive(Debug)]
    enum Option<T> {
        Some(T),
        None,
    }

    let some_value: Option<i32> = Option::Some(10);
    let no_value: Option<i32> = Option::None;

    match some_value {
        Option::Some(value) => println!("Value: {}", value),
        Option::None => println!("No value"),
    }

    match no_value {
        Option::Some(value) => println!("Value: {}", value),
        Option::None => println!("No value"),
    }
}
