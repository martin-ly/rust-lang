//! 类型定义系统示例代码
//! 
//! 本文件包含了类型定义系统的各种示例，包括：
//! - 基本数据类型
//! - 复合类型
//! - 自定义类型
//! - 指针类型
//! - 函数类型
//! - 泛型类型

use std::rc::Rc;
use std::sync::Arc;

/// 基本数据类型示例
pub fn basic_data_types_examples() {
    println!("=== 基本数据类型示例 ===");
    
    // 整数类型
    let i8_val: i8 = -128;
    let u8_val: u8 = 255;
    let i32_val: i32 = -2147483648;
    let u64_val: u64 = 18446744073709551615;
    
    println!("i8: {}, u8: {}, i32: {}, u64: {}", 
             i8_val, u8_val, i32_val, u64_val);
    
    // 浮点类型
    let f32_val: f32 = 3.14;
    let f64_val: f64 = 2.718281828459045;
    
    println!("f32: {}, f64: {}", f32_val, f64_val);
    
    // 布尔类型
    let t = true;
    let f: bool = false;
    
    println!("Boolean: {}, {}", t, f);
    
    // 字符类型
    let c = 'z';
    let z = 'ℤ';
    let heart_eyed_cat = '😻';
    
    println!("Characters: {}, {}, {}", c, z, heart_eyed_cat);
}

/// 复合类型示例
pub fn compound_types_examples() {
    println!("\n=== 复合类型示例 ===");
    
    // 元组类型
    let tup: (i32, f64, u8) = (500, 6.4, 1);
    let (x, y, z) = tup;
    println!("Tuple: ({}, {}, {})", x, y, z);
    println!("Tuple access: {}, {}, {}", tup.0, tup.1, tup.2);
    
    // 数组类型
    let a = [1, 2, 3, 4, 5];
    let b: [i32; 5] = [1, 2, 3, 4, 5];
    let c = [3; 5];  // [3, 3, 3, 3, 3]
    
    println!("Array a: {:?}", a);
    println!("Array b: {:?}", b);
    println!("Array c: {:?}", c);
    
    // 数组访问
    let first = a[0];
    let last = a[4];
    println!("First: {}, Last: {}", first, last);
    
    // 数组迭代
    for (i, &element) in a.iter().enumerate() {
        println!("a[{}] = {}", i, element);
    }
}

/// 自定义类型示例
pub fn custom_types_examples() {
    println!("\n=== 自定义类型示例 ===");
    
    // 结构体类型
    let user = User {
        username: String::from("alice"),
        email: String::from("alice@example.com"),
        sign_in_count: 1,
        active: true,
    };
    
    println!("User: {:?}", user);
    
    // 结构体方法
    let mut user2 = User::new(
        String::from("bob"),
        String::from("bob@example.com"),
    );
    
    user2.sign_in();
    println!("User2 active: {}, Sign in count: {}", 
             user2.is_active(), user2.sign_in_count);
    
    // 元组结构体
    let color = Color(255, 0, 0);
    let point = Point3D(0, 0, 0);
    
    println!("Color: ({}, {}, {})", color.0, color.1, color.2);
    println!("Point: ({}, {}, {})", point.0, point.1, point.2);
    
    // 枚举类型
    let home = IpAddr::V4(String::from("127.0.0.1"));
    let loopback = IpAddr::V6(String::from("::1"));
    
    println!("Home: {:?}, Loopback: {:?}", home, loopback);
    
    // 枚举方法
    let msg = Message::Write(String::from("hello"));
    msg.call();
}

/// 指针类型示例
#[allow(unused_variables)]
pub fn pointer_types_examples() {
    println!("\n=== 指针类型示例 ===");
    
    // 引用类型
    let x = 5;
    let y = &x;
    println!("x: {}, y: {}", x, y);
    
    // 可变引用
    let mut s = String::from("hello");
    change(&mut s);
    println!("Changed string: {}", s);
    
    // 智能指针
    let b = Box::new(5);
    println!("Box value: {}", b);
    
    let rc = Rc::new(5);
    let rc_clone = Rc::clone(&rc);
    println!("Rc count: {}", Rc::strong_count(&rc));
    
    let arc = Arc::new(5);
    let arc_clone = Arc::clone(&arc);
    println!("Arc count: {}", Arc::strong_count(&arc));
    
    // 自定义智能指针
    let my_box = MyBox::new(5);
    println!("MyBox value: {}", *my_box);
}

/// 函数类型示例
pub fn function_types_examples() {
    println!("\n=== 函数类型示例 ===");
    
    // 函数指针
    let f: fn(i32) -> i32 = add_one;
    let result = f(5);
    println!("Function pointer result: {}", result);
    
    // 函数指针作为参数
    let result = do_twice(add_one, 5);
    println!("Do twice result: {}", result);
    
    // 闭包类型
    let add_one_closure = |x| x + 1;
    let result = add_one_closure(5);
    println!("Closure result: {}", result);
    
    // 捕获环境
    let x = 4;
    let equal_to_x = |z| z == x;
    let y = 4;
    println!("Equal to x: {}", equal_to_x(y));
    
    // 移动闭包
    let x = vec![1, 2, 3];
    let equal_to_x = move |z| z == x;
    let y = vec![1, 2, 3];
    println!("Move closure result: {}", equal_to_x(y));
}

/// 泛型类型示例
pub fn generic_types_examples() {
    println!("\n=== 泛型类型示例 ===");
    
    // 泛型结构体
    let integer_point = Point::new(5, 10);
    let float_point = Point::new(1.0, 4.0);
    
    println!("Integer point: {:?}", integer_point);
    println!("Float point: {:?}", float_point);
    
    // 泛型方法
    let point = Point::new(3.0, 4.0);
    println!("Distance from origin: {}", point.distance_from_origin());
    
    // 泛型枚举
    let some_number = MyOption::Some(5);
    let some_string = MyOption::Some("a string");
    let absent_number: MyOption<i32> = MyOption::None;
    
    println!("Some number: {:?}", some_number);
    println!("Some string: {:?}", some_string);
    println!("Absent number: {:?}", absent_number);
    
    // 泛型函数
    let number_list = vec![34, 50, 25, 100, 65];
    let result = largest(&number_list);
    println!("The largest number is {}", result);
    
    let char_list = vec!['y', 'm', 'a', 'q'];
    let result = largest(&char_list);
    println!("The largest char is {}", result);
}

/// 类型转换示例
pub fn type_conversion_examples() {
    println!("\n=== 类型转换示例 ===");
    
    // 显式转换
    let x = 3.14;
    let y = x as i32;
    println!("x: {}, y: {}", x, y);
    
    // 隐式转换
    let s = String::from("hello");
    let slice: &str = &s;
    println!("String: {}, Slice: {}", s, slice);
    
    // From/Into 转换
    let s = String::from("hello");
    let bytes: Vec<u8> = s.into();
    let back_to_string = String::from_utf8(bytes).unwrap();
    println!("Back to string: {}", back_to_string);
}

/// 类型推断示例
pub fn type_inference_examples() {
    println!("\n=== 类型推断示例 ===");
    
    // 字面量推断
    let x = 42;        // i32
    let y = 3.14;      // f64
    let z = true;      // bool
    
    println!("x: {}, y: {}, z: {}", x, y, z);
    
    // 函数调用推断
    let mut vec = Vec::new();
    vec.push(42);      // 推断为 Vec<i32>
    println!("Vec: {:?}", vec);
    
    // 方法调用推断
    let result = vec.iter().sum::<i32>();
    println!("Sum: {}", result);
}

// ============================================================================
// 辅助结构体和函数定义
// ============================================================================

/// 用户结构体
#[allow(dead_code)]
#[derive(Debug)]
struct User {
    username: String,
    email: String,
    sign_in_count: u64,
    active: bool,
}

impl User {
    fn new(username: String, email: String) -> Self {
        User {
            username,
            email,
            sign_in_count: 0,
            active: true,
        }
    }
    
    fn sign_in(&mut self) {
        self.sign_in_count += 1;
    }
    
    fn is_active(&self) -> bool {
        self.active
    }
}

/// 颜色元组结构体
#[allow(dead_code)]
struct Color(i32, i32, i32);

/// 点元组结构体
#[allow(dead_code)]
struct Point3D(i32, i32, i32);

/// IP地址枚举
#[derive(Debug)]
#[allow(dead_code)]
enum IpAddr {
    V4(String),
    V6(String),
}

/// 消息枚举
#[allow(dead_code)]
#[derive(Debug)]
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

impl Message {
    fn call(&self) {
        match self {
            Message::Quit => println!("Quitting"),
            Message::Move { x, y } => println!("Moving to ({}, {})", x, y),
            Message::Write(text) => println!("Writing: {}", text),
            Message::ChangeColor(r, g, b) => println!("Changing color to RGB({}, {}, {})", r, g, b),
        }
    }
}

/// 泛型点结构体
#[derive(Debug)]
struct Point<T> {
    x: T,
    y: T,
}

#[allow(dead_code)]
impl<T> Point<T> {
    fn new(x: T, y: T) -> Self {
        Point { x, y }
    }
    
    fn x(&self) -> &T {
        &self.x
    }
    
    fn y(&self) -> &T {
        &self.y
    }
}

#[allow(dead_code)]
impl Point<f32> {
    fn distance_from_origin(&self) -> f32 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}

/// 泛型选项枚举
#[derive(Debug)]
#[allow(dead_code)]
enum MyOption<T> {
    Some(T),
    None,
}

/// 泛型函数
#[allow(dead_code)]
fn largest<T: PartialOrd + Copy>(list: &[T]) -> T {
    let mut largest = list[0];
    
    for &item in list {
        if item > largest {
            largest = item;
        }
    }
    
    largest
}

/// 添加函数
fn add_one(x: i32) -> i32 {
    x + 1
}

/// 执行两次函数
fn do_twice(f: fn(i32) -> i32, arg: i32) -> i32 {
    f(arg) + f(arg)
}

/// 改变字符串函数
fn change(some_string: &mut String) {
    some_string.push_str(", world");
}

/// 自定义智能指针
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> MyBox<T> {
    fn new(x: T) -> MyBox<T> {
        MyBox(x)
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

fn main() {
    println!("Rust 类型定义系统示例");
    println!("======================");
    
    basic_data_types_examples();
    compound_types_examples();
    custom_types_examples();
    pointer_types_examples();
    function_types_examples();
    generic_types_examples();
    type_conversion_examples();
    type_inference_examples();
    
    println!("\n所有示例运行完成！");
}
