use serde::{Serialize, Deserialize};


/*
在Rust中，结构体（struct）的高级应用可以通过多种方式实现，
包括使用方法、实现特征、组合和嵌套结构体、以及使用元组结构体和单元结构体等

总结
1. 结构体方法：为结构体定义方法以封装行为。
2. 特征结合：通过实现特征为结构体提供多态性。
3. 组合和嵌套：使用组合和嵌套结构体构建复杂数据结构。
4. 元组和单元结构体：简化数据结构的定义。
5. 可变性和所有权：结构体字段可以是可变的(mut self)，允许在运行时修改。
6. 生命周期：确保引用的有效性，避免悬垂引用。
7. 默认值：通过实现Default特征为结构体提供默认值。
8. 序列化与反序列化：使用serde库轻松处理数据格式转换。
9. 组合模式：通过组合多个结构体实现复杂设计。
10. 可变性与不可变性：灵活管理结构体字段的可变性。
11. 可变借用与不可变借用：利用Rust的借用机制管理结构体的状态。
12. 模式匹配：使用模式匹配解构和访问结构体数据。
13. 字段更新语法：简化结构体实例的创建。
14. 泛型：使用泛型提高结构体的灵活性和重用性。
15. 自定义方法与链式调用：定义自定义方法并支持链式调用。
*/


/*
1. 结构体方法
    可以为结构体定义方法，以便更好地封装行为。
*/
struct Rectangle {
    width: u32,
    height: u32,
}

impl Rectangle {
    // 计算面积的方法
    fn area(&self) -> u32 {
        self.width * self.height
    }

    // 判断是否是正方形的方法
    fn is_square(&self) -> bool {
        self.width == self.height
    }
}

#[allow(unused)]
pub fn advance_struct01() {
    println!("1. 结构体方法");
    let rect = Rectangle { width: 10, height: 5 };
    println!("Area: {}", rect.area()); // 输出: Area: 50
    println!("Is square: {}", rect.is_square()); // 输出: Is square: false
}


/*
2. 结构体与特征结合
    通过实现特征，可以为结构体提供多态性。
*/

#[allow(unused)]
pub fn advance_struct02() {
    println!("2. 结构体与特征结合");
    trait Shape {
        fn area(&self) -> f64;
    }
    
    struct Circle {
        radius: f64,
    }
    
    struct Square {
        side: f64,
    }
    
    impl Shape for Circle {
        fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
    }
    
    impl Shape for Square {
        fn area(&self) -> f64 {
            self.side * self.side
        }
    }
    
    fn print_area<T: Shape>(shape: T) {
        println!("Area: {}", shape.area());
    }

    let circle = Circle { radius: 5.0 };
    let square = Square { side: 4.0 };

    print_area(circle); // 输出: Area: 78.53981633974483
    print_area(square); // 输出: Area: 16
}

/*
3. 组合和嵌套结构体
    通过组合和嵌套结构体，可以构建复杂的数据结构。
*/

#[allow(unused)]
pub fn advance_struct03() {
    println!("3. 组合和嵌套结构体");
    struct Engine {
        horsepower: u32,
    }
    
    struct Car {
        model: String,
        year: u32,
        engine: Engine, // 嵌套结构体
    }

    let engine = Engine { horsepower: 300 };
    let car = Car {
        model: String::from("Mustang"),
        year: 2021,
        engine,
    };

    println!("Car Model: {}, Year: {}, Horsepower: {}", 
             car.model, 
             car.year, 
             car.engine.horsepower);
}


/*
4. 元组结构体和单元结构体
    元组结构体和单元结构体可以用于简化数据结构的定义。
*/

#[allow(unused)]
pub fn advance_struct04() {
    println!("4. 元组结构体和单元结构体");
    // 元组结构体
    struct Point(i32, i32);

    let point = Point(10, 20);
    println!("Point: ({}, {})", point.0, point.1); // 输出: Point: (10, 20)

    struct UnitStruct; // 单元结构体

    let _unit = UnitStruct; // 创建单元结构体的实例
    println!("Unit struct created!");
}

/*
5. 结构体的可变性和所有权
    结构体的字段可以是可变的(mut self)，允许在运行时修改其值。
*/

#[allow(unused)]
pub fn advance_struct05() {
    println!("5. 结构体的可变性和所有权");
    struct Counter {
        count: u32,
    }
    
    impl Counter {
        fn increment(&mut self) {
            self.count += 1;
        }
    }
    
    let mut counter = Counter { count: 0 };
    counter.increment();
    println!("Count: {}", counter.count); // 输出: Count: 1
    
}

/*
6. 结构体的生命周期
    在Rust中，生命周期用于确保引用的有效性。
    结构体可以包含引用类型的字段，这时需要显式地指定生命周期。
*/

#[allow(unused)]
pub fn advance_struct06() {
    println!("6. 结构体的生命周期");
    struct Book<'a> {
        title: &'a str,
        author: &'a str,
    }
    
    
    let title = String::from("1984");
    let author = String::from("George Orwell");

    let book = Book {
        title: &title,
        author: &author,
    };
    
    println!("Book: {}, Author: {}", book.title, book.author);
}

/*
7. 结构体的默认值
    可以为结构体实现Default特征，以便为结构体提供默认值。   
*/

#[allow(unused)]
pub fn advance_struct07() {
    println!("7. 结构体的默认值");
    //#[derive(Default)]
    struct Config {
        host: String,
        port: u32,
    }

    // 手工实现Default特征
    impl Default for Config {
        fn default() -> Self {
            Config {
                host: String::new(),
                port: 0,
            }
        }
    }

    let config: Config = Default::default(); // 使用默认值
    println!("Host: {}, Port: {}", config.host, config.port); // 输出: Host: , Port: 0

}

/*
8. 结构体的序列化与反序列化
   使用第三方库（如serde）可以轻松地将结构体序列化为JSON或其他格式，或从这些格式反序列化。
*/

#[allow(unused)]
pub fn advance_struct08() {
    println!("8. 结构体的序列化与反序列化");
    #[derive(Serialize, Deserialize, Debug)]
    struct User {
        username: String,
        email: String,
    }

    let user = User {
        username: String::from("alice"),
        email: String::from("alice@example.com"),
    };

    // 序列化为JSON
    let json = serde_json::to_string(&user).unwrap();
    println!("Serialized: {}", json);

    // 反序列化
    let deserialized_user: User = serde_json::from_str(&json).unwrap();
    println!("Deserialized: {:?}", deserialized_user);

}

/*
9. 结构体的组合模式
   通过组合多个结构体，可以实现更复杂的设计模式，例如组合模式。
*/

#[allow(unused)]
pub fn advance_struct09() {
    println!("9. 结构体的组合模式");
    struct Engine {
        horsepower: u32,
    }
    
    struct Wheels {
        count: u32,
    }
    
    struct Car {
        engine: Engine,
        wheels: Wheels,
    }
    

    let car = Car {
        engine: Engine { horsepower: 300 },
        wheels: Wheels { count: 4 },
    };

    println!("Car has {} horsepower and {} wheels.", 
                car.engine.horsepower, 
                car.wheels.count);
    
}

/*
10. 结构体的可变性与不可变性
    Rust中的结构体字段可以是可变的或不可变的，使用mut关键字来声明可变性。
*/

#[allow(unused)]
pub fn advance_struct10() {
    println!("10. 结构体的可变性与不可变性");
    struct Point {
        x: i32,
        y: i32,
    }
        
    let mut point = Point { x: 0, y: 0 };
    point.x = 10; // 修改可变字段
    point.y = 20;

    println!("Point: ({}, {})", point.x, point.y); // 输出: Point: (10, 20)
}

/*
11. 结构体的可变借用与不可变借用
    可变借用与不可变借用：利用Rust的借用机制管理结构体的状态。
*/

#[allow(unused)]
pub fn advance_struct11() {
    println!("11. 结构体的可变借用与不可变借用");
    struct Counter {
        count: u32,
    }
    
    impl Counter {
        fn increment(&mut self) {
            self.count += 1;
        }
    
        fn get_count(&self) -> u32 {
            self.count
        }
    }
    
 
    let mut counter = Counter { count: 0 };

    {
        let mut_ref = &mut counter; // 可变借用
        mut_ref.increment();
    } // 可变借用结束

    let immut_ref = &counter; // 不可变借用
    println!("Count: {}", immut_ref.get_count()); // 输出: Count: 1

}


/*
12. 结构体的模式匹配
    Rust的模式匹配功能可以与结构体结合使用，以便更方便地解构和访问数据。
    模式匹配：使用模式匹配解构和访问结构体数据。
*/

#[allow(unused)]
pub fn advance_struct12() {
    println!("12. 结构体的模式匹配");
    struct Point {
        x: i32,
        y: i32,
    }
    
    fn print_point(point: Point) {
        match point {
            Point { x, y } => println!("Point is at ({}, {})", x, y),
        }
    }

    let point = Point { x: 10, y: 20 };
    print_point(point); // 输出: Point is at (10, 20)
    
}

/*
13. 结构体的字段更新语法
    结构体的字段更新语法可以简化结构体实例的创建。
    字段更新语法：简化结构体实例的创建。
*/

#[allow(unused)]
pub fn advance_struct13() {
    println!("13. 结构体的字段更新语法");
    struct User {
        username: String,
        email: String,
    }
    
    let user1 = User {
        username: String::from("alice"),
        email: String::from("alice@example.com"),
    };

    // 使用字段更新语法创建新实例
    let user2 = User {
        email: String::from("bob@example.com"),
        ..user1 // 复制user1的username字段
    };

    println!("User2: {}, {}", user2.username, user2.email); // 输出: User2: alice, bob@example.com
}

/*
14. 结构体的泛型
    结构体可以使用泛型来处理不同类型的数据，从而提高代码的灵活性和重用性。
    泛型：使用泛型提高结构体的灵活性和重用性。
*/

#[allow(unused)]
pub fn advance_struct14() {
    println!("14. 结构体的泛型");
    struct Pair<T, U> {
        first: T,
        second: U,
    }
    
    impl<T, U> Pair<T, U> {
        fn new(first: T, second: U) -> Self {
            Pair { first, second }
        }
    }

    let pair = Pair { first: 1, second: "one" };
    let pair2 = Pair::new(1, "one");
    println!("pair: First: {}, Second: {}", pair.first, pair.second);
    println!("pair2: First: {}, Second: {}", pair2.first, pair2.second);

}

/*
15. 结构体的自定义方法与链式调用
    可以为结构体定义自定义方法，并通过返回self实现链式调用。
    自定义方法与链式调用：定义自定义方法并支持链式调用。
*/

#[allow(unused)]
pub fn advance_struct15() {
    println!("15. 结构体的自定义方法与链式调用");
    #[derive(Debug,Clone)]
    struct Builder {
        value: String,
    }
    
    impl Builder {
        fn new() -> Self {
            Builder {
                value: String::new(),
            }
        }
    
        fn append(&mut self, text: &str) -> &mut Self {
            self.value.push_str(text);
            self // 返回可变引用以支持链式调用
        }
    
        fn build(&mut self) -> &String {
            &self.value
        }
    }
    
    // 使用链式调用
    let mut builder = Builder::new();
    let result = builder
        .append("Hello, ")
        .append("World!")
        .build();

    println!("{}", result); // 输出: Hello, World!
    
}

