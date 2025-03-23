/*
Rust 的模式匹配是一种强大的控制流机制，
允许根据数据值的结构进行分支。

模式匹配可以被视为一种自然变换，它将输入数据的不同形态映射到不同的处理逻辑。
*/

/*
match允许根据数据值的结构进行分支。
*/
#[allow(unused)]
pub fn test_pattern_match() {

    //可以使用|符号来匹配多个模式。
    fn describe_number01(num: i32) -> &'static str {
        match num {
            0 => "零",
            1 | 2 | 3 => "小数字",
            _ => "大数字",
        }
    }

    //使用守卫（Guard）：可以在模式匹配中添加条件
    fn describe_number02(num: i32) -> &'static str {
        match num {
            n if n < 0 => "负数",
            n if n == 0 => "零",
            n if n > 0 => "正数",
            _ => "未知",
        }
    }

    let x = 5;

    match x {
        1 => println!("x is 1"),
        2 => println!("x is 2"),
        _ => println!("x is something else"),
    }

    println!("{}", describe_number01(x));
    println!("{}", describe_number02(x));
}

/*
模式匹配（Pattern Matching）与控制结构（Control Structure）：
组合关系：
    模式匹配是一种特殊的控制结构，它允许根据数据的结构和内容进行分支。
    它可以看作是对控制流的扩展，提供更强大的条件判断能力。
形式：
    使用模式匹配：解构泛型具体化，类型inference；具体类型的值，值的判断等。
*/
#[allow(unused)]
pub fn test_pattern_match_2() -> () {
    let value = Some(10);
    match value {
        Some(x) => println!("Value is: {}", x), // 控制结构
        None => println!("No value"), // 控制结构
    }
}


/*
match可以用来解构元组、结构体和枚举等复杂数据类型。
*/
#[allow(unused)]
pub fn test_pattern_match_3() -> () {
    enum Shape {
        Circle(f64),
        Rectangle(f64, f64),
    }
    
    enum Message {
        Shape(Shape),
        Quit,
    }
    
    let msg = Message::Shape(Shape::Circle(3.0));
    fn process_message(msg: Message) {
        match msg {
            Message::Quit => println!("退出"),
            Message::Shape(shape) => {
                match shape {
                    Shape::Circle(radius) => println!("圆的半径: {}", radius),
                    Shape::Rectangle(width, height) => {
                        println!("矩形的宽度: {}, 高度: {}", width, height);
                    }
                }
            }
        }
    }

    process_message(msg);
}

/*
    泛型解构
*/
#[allow(unused)]
pub fn test_pattern_match_4() -> () {
    // 定义一个泛型结构体
    struct Wrapper<T> {
        value: T,
    }

    // 定义一个泛型枚举
    enum Option<T> {
        Some(T),
        None,
    }

    fn describe_wrapper<T: std::fmt::Debug>(wrapper: Wrapper<T>) {
        match wrapper {
            Wrapper { value } => println!("Wrapper contains: {:?}", value),
        }
    }

    fn describe_option<T: std::fmt::Debug>(option: Option<T>) {
        match option {
            Option::Some(value) => println!("Option contains: {:?}", value),
            Option::None => println!("Option is None"),
        }
    }

    let wrapped = Wrapper { value: 42 };
    describe_wrapper(wrapped);

    let some_value = Option::Some("Hello");
    describe_option(some_value);

    let none_value: Option<&str> = Option::None;
    describe_option(none_value);
}

