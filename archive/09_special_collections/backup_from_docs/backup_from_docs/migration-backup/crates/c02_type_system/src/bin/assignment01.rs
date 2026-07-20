/*
Rust 中的析构赋值提供了强大的模式匹配功能，允许我们方便地提取和使用数据结构中的值。
通过解构结构体、元组和枚举，结合嵌套解构和部分解构等高级用法，
可以编写出更简洁和可读的代码。
*/

#[allow(dead_code)]
struct Point {
    x: i32,
    y: i32,
}

fn main() {
    //1. 解构结构体
    let point = Point { x: 10, y: 20 };
    // 解构赋值
    let Point { x, y } = point;
    println!("x: {}, y: {}", x, y); // 输出: x: 10, y: 20

    //2. 解构元组
    let tuple = (1, 2, 3);
    let (a, b, c) = tuple;
    println!("a: {}, b: {}, c: {}", a, b, c); // 输出: a: 1, b: 2, c: 3

    //3. 解构枚举
    #[allow(dead_code)]
    enum Message {
        Quit,
        Move { x: i32, y: i32 },
        Write(String),
    }
    let msg = Message::Move { x: 10, y: 20 };
    match msg {
        Message::Quit => println!("Quit"),
        Message::Move { x, y } => println!("Move to ({}, {})", x, y),
        Message::Write(s) => println!("Write: {}", s),
    }

    #[allow(dead_code)]
    enum Shape {
        Circle(f64),
        Rectangle(f64, f64),
    }
    let shape = Shape::Rectangle(10.0, 20.0);
    match shape {
        Shape::Circle(r) => println!("Circle with radius: {}", r),
        Shape::Rectangle(w, h) => println!("Rectangle with width: {}, height: {}", w, h),
    }

    //4. 嵌套解构
    let complex = (1, (2, 3), 4);
    match complex {
        (a, (b, c), d) => println!("a: {}, b: {}, c: {}, d: {}", a, b, c, d),
    }

    struct Rectangle {
        width: u32,
        height: u32,
    }

    struct Shape0 {
        rect: Rectangle,
        color: String,
    }

    let shape = Shape0 {
        rect: Rectangle {
            width: 10,
            height: 20,
        },
        color: "red".to_string(),
    };

    // 嵌套解构
    let Shape0 {
        rect: Rectangle { width, height },
        color,
    } = shape;

    println!("Width: {}, Height: {}, Color: {}", width, height, color);
    // 输出: Width: 10, Height: 20, Color: red

    //5. 部分解构
    let numbers = (1, 2, 3, 4, 5);
    match numbers {
        (first, .., last) => println!("First: {}, Last: {}", first, last),
    }
    // 输出: First: 1, Last: 5

    #[allow(dead_code)]
    struct Person {
        name: String,
        age: u32,
        city: String,
    }

    let person = Person {
        name: String::from("Alice"),
        age: 30,
        city: String::from("Wonderland"),
    };

    // 部分解构
    let Person { name, .. } = person;

    println!("Name: {}", name); // 输出: Name: Alice
    let Person { age: a, .. } = person;
    println!("Age: {}", a); // 输出: Age: 30
    let Person { city: ct, .. } = person;
    println!("City: {}", ct); // 输出: City: Wonderland

    //6. 忽略值
    let (_, _, third, _, _) = numbers;
    println!("Third: {}", third); // 输出: Third: 3

    //7.在函数参数中解构
    struct Point {
        x: i32,
        y: i32,
    }

    fn print_point(Point { x, y }: Point) {
        println!("Point is at ({}, {})", x, y);
    }

    let point = Point { x: 10, y: 20 };
    print_point(point); // 输出: Point is at (10, 20)

    //8. 解构带有默认值的结构体
    // 可以为结构体字段提供默认值，并在解构时使用。
    #[allow(dead_code)]
    #[derive(Debug)]
    struct Config {
        host: String,
        port: u16,
    }

    impl Default for Config {
        fn default() -> Self {
            Config {
                host: String::from("localhost"),
                port: 8080,
            }
        }
    }

    let config = Config::default();
    // 解构赋值
    let Config { host, port } = config;
    println!("Host: {}, Port: {}", host, port); // 输出: Host: localhost, Port: 8080
}
