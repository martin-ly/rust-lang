//! Rust 1.89 基础语法模块
//!
//! 本模块提供了 Rust 语言的基础语法元素，包括：
//! - 变量声明与绑定
//! - 数据类型与类型推断
//! - 控制流结构
//! - 函数定义与调用
//! - 表达式与语句
//! - 模式匹配
//! - 错误处理
//!
//! 所有示例都遵循 Rust 1.89 的最新语法规范，并包含详细的注释说明。

use std::collections::HashMap;
use std::fmt::{self, Display};

/// 基础语法演示结构体
/// 
/// 这个结构体用于演示 Rust 的基础语法特性，包括：
/// - 结构体定义
/// - 方法实现
/// - 生命周期参数
/// - 泛型参数
#[derive(Debug, Clone, PartialEq)]
pub struct BasicSyntaxDemo<T> 
where 
    T: Clone + PartialEq + Display,
{
    /// 数据字段，使用泛型类型
    pub data: T,
    /// 计数器字段
    pub count: u32,
    /// 可选的元数据
    pub metadata: Option<String>,
}

impl<T> BasicSyntaxDemo<T> 
where 
    T: Clone + PartialEq + Display,
{
    /// 创建新的 BasicSyntaxDemo 实例
    /// 
    /// # 参数
    /// * `data` - 要存储的数据
    /// 
    /// # 返回值
    /// 返回一个新的 BasicSyntaxDemo 实例
    /// 
    /// # 示例
    /// ```rust
    /// use c03_control_fn::basic_syntax::BasicSyntaxDemo;
    /// 
    /// let demo = BasicSyntaxDemo::new(42);
    /// assert_eq!(demo.data, 42);
    /// assert_eq!(demo.count, 0);
    /// ```
    pub fn new(data: T) -> Self {
        Self {
            data,
            count: 0,
            metadata: None,
        }
    }

    /// 更新数据并增加计数器
    /// 
    /// # 参数
    /// * `new_data` - 新的数据值
    /// 
    /// # 示例
    /// ```rust
    /// use c03_control_fn::basic_syntax::BasicSyntaxDemo;
    /// 
    /// let mut demo = BasicSyntaxDemo::new(42);
    /// demo.update_data(100);
    /// assert_eq!(demo.data, 100);
    /// assert_eq!(demo.count, 1);
    /// ```
    pub fn update_data(&mut self, new_data: T) {
        self.data = new_data;
        self.count += 1;
    }

    /// 设置元数据
    /// 
    /// # 参数
    /// * `metadata` - 元数据字符串
    /// 
    /// # 示例
    /// ```rust
    /// use c03_control_fn::basic_syntax::BasicSyntaxDemo;
    /// 
    /// let mut demo = BasicSyntaxDemo::new(42);
    /// demo.set_metadata("示例数据".to_string());
    /// assert_eq!(demo.metadata, Some("示例数据".to_string()));
    /// ```
    pub fn set_metadata(&mut self, metadata: String) {
        self.metadata = Some(metadata);
    }

    /// 获取数据的字符串表示
    /// 
    /// # 返回值
    /// 返回数据的字符串表示
    /// 
    /// # 示例
    /// ```rust
    /// use c03_control_fn::basic_syntax::BasicSyntaxDemo;
    /// 
    /// let demo = BasicSyntaxDemo::new(42);
    /// assert_eq!(demo.to_string(), "42");
    /// ```
    pub fn to_string(&self) -> String {
        format!("{}", self.data)
    }
}

impl<T> Display for BasicSyntaxDemo<T> 
where 
    T: Clone + PartialEq + Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BasicSyntaxDemo(data: {}, count: {})", self.data, self.count)
    }
}

/// 变量声明与绑定演示
/// 
/// 演示 Rust 中变量声明、绑定和可变性的各种用法
pub mod variable_binding {
    use super::*;

    /// 基础变量声明演示
    /// 
    /// 展示 Rust 中变量的基本声明方式：
    /// - 不可变变量（默认）
    /// - 可变变量（mut 关键字）
    /// - 类型注解
    /// - 类型推断
    pub fn basic_variable_declaration() {
        println!("=== 基础变量声明演示 ===");

        // 1. 不可变变量（默认行为）
        let x = 42;
        println!("不可变变量 x = {}", x);

        // 2. 可变变量（使用 mut 关键字）
        let mut y = 10;
        println!("可变变量 y = {}", y);
        y += 5;
        println!("修改后的 y = {}", y);

        // 3. 显式类型注解
        let z: i32 = 100;
        let name: String = "Rust".to_string();
        println!("显式类型注解: z = {}, name = {}", z, name);

        // 4. 类型推断
        let inferred_int = 42;        // 推断为 i32
        let inferred_float = 3.14;    // 推断为 f64
        let inferred_string = "Hello"; // 推断为 &str
        println!("类型推断: int = {}, float = {}, string = {}", 
                inferred_int, inferred_float, inferred_string);

        // 5. 变量遮蔽（shadowing）
        let shadowed = 1;
        println!("第一次声明: {}", shadowed);
        let shadowed = shadowed + 1;
        println!("遮蔽后: {}", shadowed);
        let shadowed = shadowed * 2;
        println!("再次遮蔽: {}", shadowed);
    }

    /// 复杂类型变量声明演示
    /// 
    /// 展示复杂数据类型的变量声明方式
    pub fn complex_type_declaration() {
        println!("\n=== 复杂类型变量声明演示 ===");

        // 1. 数组类型
        let array: [i32; 5] = [1, 2, 3, 4, 5];
        println!("数组: {:?}", array);

        // 2. 切片类型
        let slice: &[i32] = &array[1..4];
        println!("切片: {:?}", slice);

        // 3. 元组类型
        let tuple: (i32, f64, String) = (42, 3.14, "Rust".to_string());
        println!("元组: {:?}", tuple);

        // 4. 结构体类型
        let demo = BasicSyntaxDemo::new(100);
        println!("结构体: {}", demo);

        // 5. 枚举类型
        #[allow(dead_code)]
        #[derive(Debug)]
        enum Color {
            Red,
            Green,
            Blue,
            Rgb(u8, u8, u8),
        }
        let color = Color::Rgb(255, 0, 0);
        println!("枚举: {:?}", color);

        // 6. 向量类型
        let mut vector: Vec<i32> = vec![1, 2, 3];
        vector.push(4);
        println!("向量: {:?}", vector);

        // 7. HashMap 类型
        let mut map: HashMap<String, i32> = HashMap::new();
        map.insert("apple".to_string(), 5);
        map.insert("banana".to_string(), 3);
        println!("HashMap: {:?}", map);
    }

    /// 模式匹配变量绑定演示
    /// 
    /// 展示使用模式匹配进行变量绑定的高级用法
    pub fn pattern_matching_binding() {
        println!("\n=== 模式匹配变量绑定演示 ===");

        // 1. 元组解构
        let tuple = (1, 2.0, "three");
        let (a, b, c) = tuple;
        println!("元组解构: a = {}, b = {}, c = {}", a, b, c);

        // 2. 结构体解构
        let demo = BasicSyntaxDemo::new(42);
        let BasicSyntaxDemo { data, count, metadata } = demo;
        println!("结构体解构: data = {}, count = {}, metadata = {:?}", 
                data, count, metadata);

        // 3. 数组/切片解构
        let array = [1, 2, 3, 4, 5];
        let [first, second, .., last] = array;
        println!("数组解构: first = {}, second = {}, last = {}", 
                first, second, last);

        // 4. 枚举解构
        #[allow(dead_code)]
        #[derive(Debug)]
        enum Message {
            Quit,
            Move { x: i32, y: i32 },
            Write(String),
            ChangeColor(i32, i32, i32),
        }

        let msg = Message::Move { x: 10, y: 20 };
        match msg {
            Message::Quit => println!("退出消息"),
            Message::Move { x, y } => println!("移动消息: x = {}, y = {}", x, y),
            Message::Write(text) => println!("写入消息: {}", text),
            Message::ChangeColor(r, g, b) => println!("颜色消息: RGB({}, {}, {})", r, g, b),
        }
    }
}

/// 数据类型与类型推断演示
/// 
/// 演示 Rust 的类型系统和类型推断机制
pub mod type_system {
    use super::*;

    /// 基础数据类型演示
    /// 
    /// 展示 Rust 的基础数据类型及其特性
    pub fn basic_data_types() {
        println!("\n=== 基础数据类型演示 ===");

        // 1. 整数类型
        let int8: i8 = 127;
        let uint8: u8 = 255;
        let int16: i16 = 32767;
        let uint16: u16 = 65535;
        let int32: i32 = 2147483647;
        let uint32: u32 = 4294967295;
        let int64: i64 = 9223372036854775807;
        let uint64: u64 = 18446744073709551615;
        let int128: i128 = 170141183460469231731687303715884105727;
        let uint128: u128 = 340282366920938463463374607431768211455;
        let isize: isize = 9223372036854775807;
        let usize: usize = 18446744073709551615;

        println!("整数类型:");
        println!("  i8: {}, u8: {}", int8, uint8);
        println!("  i16: {}, u16: {}", int16, uint16);
        println!("  i32: {}, u32: {}", int32, uint32);
        println!("  i64: {}, u64: {}", int64, uint64);
        println!("  i128: {}, u128: {}", int128, uint128);
        println!("  isize: {}, usize: {}", isize, usize);

        // 2. 浮点数类型
        let float32: f32 = 3.14159;
        let float64: f64 = 3.141592653589793;
        println!("浮点数类型:");
        println!("  f32: {}, f64: {}", float32, float64);

        // 3. 布尔类型
        let boolean: bool = true;
        println!("布尔类型: {}", boolean);

        // 4. 字符类型
        let character: char = 'R';
        let emoji: char = '🚀';
        println!("字符类型: {}, emoji: {}", character, emoji);

        // 5. 字符串类型
        let string_slice: &str = "Hello, Rust!";
        let owned_string: String = String::from("Hello, World!");
        println!("字符串类型:");
        println!("  字符串切片: {}", string_slice);
        println!("  拥有所有权的字符串: {}", owned_string);
    }

    /// 复合数据类型演示
    /// 
    /// 展示 Rust 的复合数据类型
    pub fn compound_data_types() {
        println!("\n=== 复合数据类型演示 ===");

        // 1. 元组类型
        let tuple: (i32, f64, char) = (42, 3.14, 'R');
        println!("元组: {:?}", tuple);
        println!("元组访问: 第一个元素 = {}", tuple.0);

        // 2. 数组类型
        let array: [i32; 5] = [1, 2, 3, 4, 5];
        println!("数组: {:?}", array);
        println!("数组长度: {}", array.len());

        // 3. 切片类型
        let slice: &[i32] = &array[1..4];
        println!("切片: {:?}", slice);

        // 4. 向量类型
        let mut vector: Vec<i32> = vec![1, 2, 3];
        vector.push(4);
        vector.push(5);
        println!("向量: {:?}", vector);

        // 5. 字符串向量
        let string_vector: Vec<String> = vec![
            "Hello".to_string(),
            "World".to_string(),
            "Rust".to_string(),
        ];
        println!("字符串向量: {:?}", string_vector);
    }

    /// 类型推断演示
    /// 
    /// 展示 Rust 强大的类型推断能力
    pub fn type_inference() {
        println!("\n=== 类型推断演示 ===");

        // 1. 基础类型推断
        let x = 42;           // 推断为 i32
        let y = 3.14;         // 推断为 f64
        let z = true;         // 推断为 bool
        let s = "Hello";      // 推断为 &str

        println!("推断类型:");
        println!("  x = {} (i32)", x);
        println!("  y = {} (f64)", y);
        println!("  z = {} (bool)", z);
        println!("  s = {} (&str)", s);

        // 2. 函数返回类型推断
        let result = add_numbers(10, 20);
        println!("函数返回类型推断: add_numbers(10, 20) = {}", result);

        // 3. 闭包类型推断
        let closure = |x: i32| x * 2;
        let result = closure(21);
        println!("闭包类型推断: closure(21) = {}", result);

        // 4. 泛型类型推断
        let demo = BasicSyntaxDemo::new(100);
        println!("泛型类型推断: {}", demo);
    }

    /// 辅助函数：两个数字相加
    fn add_numbers(a: i32, b: i32) -> i32 {
        a + b
    }
}

/// 控制流结构演示
/// 
/// 演示 Rust 中的各种控制流结构
pub mod control_flow {
    //use super::*;

    /// 条件语句演示
    /// 
    /// 展示 if、if-else、if-else if-else 语句的用法
    pub fn conditional_statements() {
        println!("\n=== 条件语句演示 ===");

        let number = 42;

        // 1. 简单 if 语句
        if number > 0 {
            println!("数字 {} 是正数", number);
        }

        // 2. if-else 语句
        if number % 2 == 0 {
            println!("数字 {} 是偶数", number);
        } else {
            println!("数字 {} 是奇数", number);
        }

        // 3. if-else if-else 语句
        if number < 0 {
            println!("数字 {} 是负数", number);
        } else if number == 0 {
            println!("数字 {} 是零", number);
        } else if number < 100 {
            println!("数字 {} 是小于100的正数", number);
        } else {
            println!("数字 {} 是大于等于100的正数", number);
        }

        // 4. 条件表达式（三元运算符的替代）
        let message = if number > 50 {
            "大数字"
        } else {
            "小数字"
        };
        println!("条件表达式结果: {}", message);

        // 5. 嵌套条件语句
        let score = 85;
        if score >= 90 {
            println!("成绩: A");
        } else if score >= 80 {
            println!("成绩: B");
        } else if score >= 70 {
            println!("成绩: C");
        } else if score >= 60 {
            println!("成绩: D");
        } else {
            println!("成绩: F");
        }
    }

    /// 循环语句演示
    /// 
    /// 展示 loop、while、for 循环的用法
    pub fn loop_statements() {
        println!("\n=== 循环语句演示 ===");

        // 1. loop 循环（无限循环）
        let mut counter = 0;
        loop {
            counter += 1;
            if counter > 3 {
                break;
            }
            println!("loop 循环: counter = {}", counter);
        }

        // 2. while 循环
        let mut number = 10;
        while number > 0 {
            println!("while 循环: number = {}", number);
            number -= 2;
        }

        // 3. for 循环 - 范围
        println!("for 循环 - 范围:");
        for i in 1..=5 {
            println!("  i = {}", i);
        }

        // 4. for 循环 - 数组/向量
        let numbers = [10, 20, 30, 40, 50];
        println!("for 循环 - 向量:");
        for (index, value) in numbers.iter().enumerate() {
            println!("  [{}] = {}", index, value);
        }

        // 5. for 循环 - 字符串
        let text = "Rust";
        println!("for 循环 - 字符串:");
        for ch in text.chars() {
            println!("  字符: {}", ch);
        }

        // 6. 循环控制 - break 和 continue
        println!("循环控制演示:");
        for i in 1..=10 {
            if i % 3 == 0 {
                continue; // 跳过能被3整除的数
            }
            if i > 7 {
                break; // 当 i > 7 时退出循环
            }
            println!("  有效数字: {}", i);
        }
    }

    /// 模式匹配演示
    /// 
    /// 展示 match 表达式的强大功能
    pub fn pattern_matching() {
        println!("\n=== 模式匹配演示 ===");

        // 1. 基础模式匹配
        let number = 42;
        match number {
            0 => println!("数字是零"),
            1..=10 => println!("数字在1到10之间"),
            11..=50 => println!("数字在11到50之间"),
            51..=100 => println!("数字在51到100之间"),
            _ => println!("数字大于100"),
        }

        // 2. 枚举模式匹配
        #[allow(dead_code)]
        #[derive(Debug)]
        enum Direction {
            North,
            South,
            East,
            West,
        }

        let direction = Direction::North;
        match direction {
            Direction::North => println!("向北"),
            Direction::South => println!("向南"),
            Direction::East => println!("向东"),
            Direction::West => println!("向西"),
        }

        // 3. 带数据的枚举模式匹配
        #[allow(dead_code)]
        #[derive(Debug)]
        enum Message {
            Quit,
            Move { x: i32, y: i32 },
            Write(String),
            ChangeColor(i32, i32, i32),
        }

        let messages = vec![
            Message::Quit,
            Message::Move { x: 10, y: 20 },
            Message::Write("Hello".to_string()),
            Message::ChangeColor(255, 0, 0),
        ];

        for msg in messages {
            match msg {
                Message::Quit => println!("收到退出消息"),
                Message::Move { x, y } => println!("移动到位置: ({}, {})", x, y),
                Message::Write(text) => println!("写入文本: {}", text),
                Message::ChangeColor(r, g, b) => println!("改变颜色为: RGB({}, {}, {})", r, g, b),
            }
        }

        // 4. 守卫条件（guard）
        let pair = (2, 4);
        match pair {
            (x, y) if x == y => println!("两个数相等"),
            (x, y) if x > y => println!("第一个数大于第二个数"),
            (x, y) if x < y => println!("第一个数小于第二个数"),
            _ => println!("其他情况"),
        }

        // 5. 绑定变量
        let value = Some(42);
        match value {
            Some(x) if x > 40 => println!("值 {} 大于40", x),
            Some(x) => println!("值 {} 小于等于40", x),
            None => println!("没有值"),
        }
    }
}

/// 函数定义与调用演示
/// 
/// 演示 Rust 中函数的各种定义和调用方式
pub mod functions {
    use super::*;

    /// 基础函数演示
    /// 
    /// 展示函数的基本定义和调用方式
    pub fn basic_functions() {
        println!("\n=== 基础函数演示 ===");

        // 1. 无参数无返回值函数
        greet();

        // 2. 有参数无返回值函数
        greet_person("Alice");

        // 3. 有参数有返回值函数
        let sum = add(10, 20);
        println!("10 + 20 = {}", sum);

        // 4. 多个参数函数
        let result = calculate(10, 20, 30);
        println!("计算结果: {}", result);

        // 5. 返回元组的函数
        let (min, max) = find_min_max(&[1, 5, 3, 9, 2]);
        println!("最小值: {}, 最大值: {}", min, max);
    }

    /// 高级函数特性演示
    /// 
    /// 展示函数的高级特性
    pub fn advanced_functions() {
        println!("\n=== 高级函数特性演示 ===");

        // 1. 闭包
        let add_one = |x: i32| x + 1;
        println!("闭包 add_one(5) = {}", add_one(5));

        // 2. 高阶函数
        let numbers = vec![1, 2, 3, 4, 5];
        let doubled: Vec<i32> = numbers.iter().map(|x| x * 2).collect();
        println!("原数组: {:?}", numbers);
        println!("翻倍后: {:?}", doubled);

        // 3. 函数作为参数
        let result = apply_operation(10, 20, |a, b| a + b);
        println!("应用加法操作: {}", result);

        let result = apply_operation(10, 20, |a, b| a * b);
        println!("应用乘法操作: {}", result);

        // 4. 返回闭包的函数
        let multiplier = create_multiplier(3);
        println!("乘数器(3) * 5 = {}", multiplier(5));

        // 5. 递归函数
        let factorial_result = factorial(5);
        println!("5! = {}", factorial_result);
    }

    /// 泛型函数演示
    /// 
    /// 展示泛型函数的使用
    pub fn generic_functions() {
        println!("\n=== 泛型函数演示 ===");

        // 1. 基础泛型函数
        let int_result = identity(42);
        let string_result = identity("Hello");
        println!("泛型函数结果: int = {}, string = {}", int_result, string_result);

        // 2. 泛型函数与约束
        let max_int = max_value(10, 20);
        let max_float = max_value(3.14, 2.71);
        println!("最大值: int = {}, float = {}", max_int, max_float);

        // 3. 泛型结构体方法
        let demo_int = BasicSyntaxDemo::new(100);
        let demo_string = BasicSyntaxDemo::new("Rust".to_string());
        println!("泛型结构体: int = {}, string = {}", demo_int, demo_string);
    }

    // 辅助函数定义

    /// 简单的问候函数
    fn greet() {
        println!("Hello, Rust!");
    }

    /// 带参数的问候函数
    fn greet_person(name: &str) {
        println!("Hello, {}!", name);
    }

    /// 加法函数
    fn add(a: i32, b: i32) -> i32 {
        a + b
    }

    /// 复杂计算函数
    fn calculate(a: i32, b: i32, c: i32) -> i32 {
        a * b + c
    }

    /// 查找最小值和最大值
    fn find_min_max(slice: &[i32]) -> (i32, i32) {
        let mut min = slice[0];
        let mut max = slice[0];
        
        for &value in slice {
            if value < min {
                min = value;
            }
            if value > max {
                max = value;
            }
        }
        
        (min, max)
    }

    /// 应用操作的高阶函数
    fn apply_operation<F>(a: i32, b: i32, operation: F) -> i32
    where
        F: Fn(i32, i32) -> i32,
    {
        operation(a, b)
    }

    /// 创建乘数器的函数
    fn create_multiplier(factor: i32) -> impl Fn(i32) -> i32 {
        move |x| x * factor
    }

    /// 递归计算阶乘
    pub fn factorial(n: u32) -> u32 {
        if n <= 1 {
            1
        } else {
            n * factorial(n - 1)
        }
    }

    /// 泛型恒等函数
    fn identity<T>(x: T) -> T {
        x
    }

    /// 泛型最大值函数
    pub fn max_value<T>(a: T, b: T) -> T
    where
        T: PartialOrd,
    {
        if a > b { a } else { b }
    }
}

/// 错误处理演示
/// 
/// 演示 Rust 中的错误处理机制
pub mod error_handling {
    use std::num::ParseIntError;

    /// 基础错误处理演示
    /// 
    /// 展示 Result 和 Option 的基本用法
    pub fn basic_error_handling() {
        println!("\n=== 基础错误处理演示 ===");

        // 1. Option 类型
        let some_value = Some(42);
        let none_value: Option<i32> = None;

        match some_value {
            Some(value) => println!("有值: {}", value),
            None => println!("没有值"),
        }

        match none_value {
            Some(value) => println!("有值: {}", value),
            None => println!("没有值"),
        }

        // 2. Result 类型
        let success_result: Result<i32, &str> = Ok(42);
        let error_result: Result<i32, &str> = Err("出错了");

        match success_result {
            Ok(value) => println!("成功: {}", value),
            Err(error) => println!("错误: {}", error),
        }

        match error_result {
            Ok(value) => println!("成功: {}", value),
            Err(error) => println!("错误: {}", error),
        }

        // 3. 字符串解析错误处理
        let valid_number = "42".parse::<i32>();
        let invalid_number = "abc".parse::<i32>();

        match valid_number {
            Ok(value) => println!("解析成功: {}", value),
            Err(error) => println!("解析失败: {}", error),
        }

        match invalid_number {
            Ok(value) => println!("解析成功: {}", value),
            Err(error) => println!("解析失败: {}", error),
        }
    }

    /// 高级错误处理演示
    /// 
    /// 展示错误处理的高级特性
    pub fn advanced_error_handling() {
        println!("\n=== 高级错误处理演示 ===");

        // 1. 使用 ? 操作符
        let result = parse_and_double("21");
        match result {
            Ok(value) => println!("解析并翻倍成功: {}", value),
            Err(error) => println!("操作失败: {}", error),
        }

        // 2. 链式错误处理
        let result = parse_and_double("abc");
        match result {
            Ok(value) => println!("解析并翻倍成功: {}", value),
            Err(error) => println!("操作失败: {}", error),
        }

        // 3. 自定义错误类型
        #[allow(dead_code)]
        #[derive(Debug)]
        enum CustomError {
            ParseError(ParseIntError),
            DivisionByZero,
            NegativeNumber,
        }

        impl std::fmt::Display for CustomError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    CustomError::ParseError(e) => write!(f, "解析错误: {}", e),
                    CustomError::DivisionByZero => write!(f, "除零错误"),
                    CustomError::NegativeNumber => write!(f, "负数错误"),
                }
            }
        }

        impl std::error::Error for CustomError {}

        // 4. 使用自定义错误
        let result = safe_divide(10, 2);
        match result {
            Ok(value) => println!("安全除法结果: {}", value),
            Err(error) => println!("除法错误: {}", error),
        }

        let result = safe_divide(10, 0);
        match result {
            Ok(value) => println!("安全除法结果: {}", value),
            Err(error) => println!("除法错误: {}", error),
        }
    }

    // 辅助函数

    /// 解析字符串并翻倍
    pub fn parse_and_double(s: &str) -> Result<i32, ParseIntError> {
        let number = s.parse::<i32>()?;
        Ok(number * 2)
    }

    /// 安全除法函数
    fn safe_divide(a: i32, b: i32) -> Result<i32, CustomError> {
        if b == 0 {
            return Err(CustomError::DivisionByZero);
        }
        if a < 0 {
            return Err(CustomError::NegativeNumber);
        }
        Ok(a / b)
    }

    // 自定义错误类型定义
    #[allow(dead_code)]
    #[derive(Debug)]
    enum CustomError {
        ParseError(ParseIntError),
        DivisionByZero,
        NegativeNumber,
    }

    impl std::fmt::Display for CustomError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                CustomError::ParseError(e) => write!(f, "解析错误: {}", e),
                CustomError::DivisionByZero => write!(f, "除零错误"),
                CustomError::NegativeNumber => write!(f, "负数错误"),
            }
        }
    }

    impl std::error::Error for CustomError {}
}

/// 综合演示函数
/// 
/// 运行所有基础语法演示
pub fn run_all_demos() {
    println!("🚀 Rust 1.89 基础语法综合演示");
    println!("=====================================");

    // 运行所有演示模块
    variable_binding::basic_variable_declaration();
    variable_binding::complex_type_declaration();
    variable_binding::pattern_matching_binding();
    
    type_system::basic_data_types();
    type_system::compound_data_types();
    type_system::type_inference();
    
    control_flow::conditional_statements();
    control_flow::loop_statements();
    control_flow::pattern_matching();
    
    functions::basic_functions();
    functions::advanced_functions();
    functions::generic_functions();
    
    error_handling::basic_error_handling();
    error_handling::advanced_error_handling();

    println!("\n✅ 所有基础语法演示完成！");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_syntax_demo_creation() {
        let demo = BasicSyntaxDemo::new(42);
        assert_eq!(demo.data, 42);
        assert_eq!(demo.count, 0);
        assert_eq!(demo.metadata, None);
    }

    #[test]
    fn test_basic_syntax_demo_update() {
        let mut demo = BasicSyntaxDemo::new(42);
        demo.update_data(100);
        assert_eq!(demo.data, 100);
        assert_eq!(demo.count, 1);
    }

    #[test]
    fn test_basic_syntax_demo_metadata() {
        let mut demo = BasicSyntaxDemo::new(42);
        demo.set_metadata("测试数据".to_string());
        assert_eq!(demo.metadata, Some("测试数据".to_string()));
    }

    #[test]
    fn test_basic_syntax_demo_display() {
        let demo = BasicSyntaxDemo::new(42);
        let display_string = demo.to_string();
        assert_eq!(display_string, "42");
    }

    #[test]
    fn test_factorial() {
        assert_eq!(functions::factorial(0), 1);
        assert_eq!(functions::factorial(1), 1);
        assert_eq!(functions::factorial(5), 120);
    }

    #[test]
    fn test_max_value() {
        assert_eq!(functions::max_value(10, 20), 20);
        assert_eq!(functions::max_value(3.14, 2.71), 3.14);
    }

    #[test]
    fn test_parse_and_double() {
        assert_eq!(error_handling::parse_and_double("21").unwrap(), 42);
        assert!(error_handling::parse_and_double("abc").is_err());
    }
}
