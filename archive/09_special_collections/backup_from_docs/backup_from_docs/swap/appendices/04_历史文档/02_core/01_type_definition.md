# Rust 类型定义系统完整指南

## 📋 目录

- [Rust 类型定义系统完整指南](#rust-类型定义系统完整指南)
  - [📋 目录](#-目录)
  - [1. 类型定义基础](#1-类型定义基础)
    - [1.1 什么是类型](#11-什么是类型)
    - [1.2 类型的作用](#12-类型的作用)
    - [1.3 基本类型](#13-基本类型)
  - [2. 基本数据类型](#2-基本数据类型)
    - [2.1 整数类型](#21-整数类型)
    - [2.2 浮点类型](#22-浮点类型)
    - [2.3 布尔类型](#23-布尔类型)
    - [2.4 字符类型](#24-字符类型)
  - [3. 复合类型](#3-复合类型)
    - [3.1 元组类型](#31-元组类型)
    - [3.2 数组类型](#32-数组类型)
    - [3.3 切片类型](#33-切片类型)
    - [3.4 字符串类型](#34-字符串类型)
  - [4. 自定义类型](#4-自定义类型)
    - [4.1 结构体类型](#41-结构体类型)
    - [4.2 枚举类型](#42-枚举类型)
    - [4.3 联合体类型](#43-联合体类型)
    - [4.4 类型别名](#44-类型别名)
  - [5. 指针类型](#5-指针类型)
    - [5.1 引用类型](#51-引用类型)
    - [5.2 原始指针](#52-原始指针)
    - [5.3 智能指针](#53-智能指针)
  - [6. 函数类型](#6-函数类型)
    - [6.1 函数指针](#61-函数指针)
    - [6.2 闭包类型](#62-闭包类型)
    - [6.3 函数项](#63-函数项)
  - [7. 泛型类型](#7-泛型类型)
    - [7.1 泛型结构体](#71-泛型结构体)
    - [7.2 泛型枚举](#72-泛型枚举)
    - [7.3 泛型函数](#73-泛型函数)
  - [8. 特征对象](#8-特征对象)
    - [8.1 特征对象类型](#81-特征对象类型)
    - [8.2 对象安全](#82-对象安全)
    - [8.3 动态分发](#83-动态分发)
  - [9. 类型转换](#9-类型转换)
    - [9.1 隐式转换](#91-隐式转换)
    - [9.2 显式转换](#92-显式转换)
    - [9.3 类型强制](#93-类型强制)
  - [10. 类型推断](#10-类型推断)
    - [10.1 推断规则](#101-推断规则)
    - [10.2 推断限制](#102-推断限制)
    - [10.3 类型注解](#103-类型注解)
  - [11. 最佳实践](#11-最佳实践)
    - [11.1 类型设计原则](#111-类型设计原则)
    - [11.2 命名约定](#112-命名约定)
    - [11.3 性能考虑](#113-性能考虑)
  - [12. 总结](#12-总结)
    - [关键要点](#关键要点)
    - [进一步学习](#进一步学习)

## 1. 类型定义基础

### 1.1 什么是类型

类型（Type）是 Rust 中值的分类系统，它定义了值可以执行的操作和占用的内存空间。
类型系统是 Rust 内存安全和性能保证的基础。

```rust
// 基本类型示例
fn basic_types() {
    let integer: i32 = 42;           // 32位有符号整数
    let floating: f64 = 3.14;        // 64位浮点数
    let boolean: bool = true;        // 布尔值
    let character: char = 'A';       // Unicode字符
    let string: &str = "hello";      // 字符串切片
}
```

### 1.2 类型的作用

Rust 的类型系统提供以下保证：

1. **内存安全**: 防止内存错误和数据竞争
2. **类型安全**: 编译时检查类型正确性
3. **性能优化**: 零成本抽象和编译时优化
4. **代码清晰**: 明确表达程序意图

```rust
// 类型安全示例
fn type_safety() {
    let x: i32 = 42;
    let y: f64 = 3.14;
    
    // 类型检查：编译时发现错误
    // let sum = x + y;  // 错误：不能将 i32 和 f64 相加
    
    // 正确的类型转换
    let sum = x as f64 + y;
    println!("Sum: {}", sum);
}
```

### 1.3 基本类型

Rust 的基本类型包括：

```rust
// 基本类型分类
fn basic_type_categories() {
    // 标量类型
    let integer: i32 = 42;
    let floating: f64 = 3.14;
    let boolean: bool = true;
    let character: char = 'A';
    
    // 复合类型
    let tuple: (i32, f64, bool) = (42, 3.14, true);
    let array: [i32; 5] = [1, 2, 3, 4, 5];
    let slice: &[i32] = &array[1..4];
    
    // 字符串类型
    let string_literal: &str = "hello";
    let owned_string: String = String::from("world");
}
```

## 2. 基本数据类型

### 2.1 整数类型

Rust 提供了多种整数类型，支持不同的位宽和符号：

```rust
// 有符号整数
fn signed_integers() {
    let i8_val: i8 = -128;
    let i16_val: i16 = -32768;
    let i32_val: i32 = -2147483648;
    let i64_val: i64 = -9223372036854775808;
    let i128_val: i128 = -170141183460469231731687303715884105728;
    let isize_val: isize = -100;  // 架构相关大小
}

// 无符号整数
fn unsigned_integers() {
    let u8_val: u8 = 255;
    let u16_val: u16 = 65535;
    let u32_val: u32 = 4294967295;
    let u64_val: u64 = 18446744073709551615;
    let u128_val: u128 = 340282366920938463463374607431768211455;
    let usize_val: usize = 100;  // 架构相关大小
}

// 整数字面量
fn integer_literals() {
    let decimal = 98_222;        // 十进制
    let hex = 0xff;              // 十六进制
    let octal = 0o77;            // 八进制
    let binary = 0b1111_0000;    // 二进制
    let byte = b'A';             // 字节（仅限 u8）
    
    // 类型后缀
    let i32_literal = 42i32;
    let u64_literal = 42u64;
    let f64_literal = 3.14f64;
}
```

### 2.2 浮点类型

Rust 提供两种浮点类型：

```rust
// 浮点类型
fn floating_point_types() {
    let f32_val: f32 = 3.14;
    let f64_val: f64 = 2.718281828459045;
    
    // 浮点字面量
    let scientific = 1.0e6;      // 科学计数法
    let with_suffix = 3.14f32;   // 类型后缀
    
    // 特殊值
    let infinity = f64::INFINITY;
    let neg_infinity = f64::NEG_INFINITY;
    let nan = f64::NAN;
    
    println!("Infinity: {}", infinity);
    println!("NaN: {}", nan);
}

// 浮点运算
fn floating_point_operations() {
    let x = 3.14;
    let y = 2.0;
    
    let sum = x + y;
    let difference = x - y;
    let product = x * y;
    let quotient = x / y;
    let remainder = x % y;
    
    println!("Sum: {}, Difference: {}, Product: {}, Quotient: {}, Remainder: {}", 
             sum, difference, product, quotient, remainder);
}
```

### 2.3 布尔类型

布尔类型表示真值：

```rust
// 布尔类型
fn boolean_type() {
    let t = true;
    let f: bool = false;
    
    // 布尔运算
    let and_result = t && f;     // false
    let or_result = t || f;      // true
    let not_result = !t;         // false
    
    // 条件表达式
    let result = if t { "true" } else { "false" };
    println!("Result: {}", result);
}

// 布尔转换
fn boolean_conversion() {
    let number = 42;
    let is_positive = number > 0;
    let is_even = number % 2 == 0;
    
    println!("Is positive: {}, Is even: {}", is_positive, is_even);
}
```

### 2.4 字符类型

字符类型表示 Unicode 标量值：

```rust
// 字符类型
fn character_type() {
    let c = 'z';
    let z = 'ℤ';
    let heart_eyed_cat = '😻';
    
    // 字符操作
    let uppercase = c.to_ascii_uppercase();
    let is_alphabetic = c.is_alphabetic();
    let is_digit = c.is_ascii_digit();
    
    println!("Uppercase: {}, Is alphabetic: {}, Is digit: {}", 
             uppercase, is_alphabetic, is_digit);
}

// 字符迭代
fn character_iteration() {
    let s = "hello";
    
    for c in s.chars() {
        println!("Character: {}", c);
    }
    
    // 字符计数
    let char_count = s.chars().count();
    let byte_count = s.len();
    println!("Character count: {}, Byte count: {}", char_count, byte_count);
}
```

## 3. 复合类型

### 3.1 元组类型

元组将多个不同类型的值组合成一个复合类型：

```rust
// 元组类型
fn tuple_types() {
    let tup: (i32, f64, u8) = (500, 6.4, 1);
    
    // 解构元组
    let (x, y, z) = tup;
    println!("x: {}, y: {}, z: {}", x, y, z);
    
    // 通过索引访问
    let first = tup.0;
    let second = tup.1;
    let third = tup.2;
    println!("First: {}, Second: {}, Third: {}", first, second, third);
}

// 元组作为返回值
fn tuple_return() -> (i32, i32) {
    (5, 6)
}

fn use_tuple_return() {
    let (x, y) = tuple_return();
    println!("x: {}, y: {}", x, y);
}

// 空元组（单元类型）
fn unit_type() -> () {
    println!("This function returns unit");
}

// 元组结构体
struct Point(i32, i32, i32);

fn tuple_struct() {
    let origin = Point(0, 0, 0);
    println!("Origin: ({}, {}, {})", origin.0, origin.1, origin.2);
}
```

### 3.2 数组类型

数组是相同类型元素的固定大小集合：

```rust
// 数组类型
fn array_types() {
    let a = [1, 2, 3, 4, 5];           // 类型推断
    let b: [i32; 5] = [1, 2, 3, 4, 5]; // 显式类型
    let c = [3; 5];                    // 重复值：[3, 3, 3, 3, 3]
    
    // 数组访问
    let first = a[0];
    let last = a[4];
    println!("First: {}, Last: {}", first, last);
    
    // 数组长度
    println!("Array length: {}", a.len());
}

// 数组迭代
fn array_iteration() {
    let a = [10, 20, 30, 40, 50];
    
    // 通过索引迭代
    for i in 0..a.len() {
        println!("a[{}] = {}", i, a[i]);
    }
    
    // 直接迭代元素
    for element in a.iter() {
        println!("Element: {}", element);
    }
    
    // 使用 enumerate
    for (index, value) in a.iter().enumerate() {
        println!("a[{}] = {}", index, value);
    }
}

// 数组切片
fn array_slicing() {
    let a = [1, 2, 3, 4, 5];
    
    let slice = &a[1..4];  // [2, 3, 4]
    println!("Slice: {:?}", slice);
    
    let full_slice = &a[..];  // 整个数组
    println!("Full slice: {:?}", full_slice);
}
```

### 3.3 切片类型

切片是对数组或向量的引用：

```rust
// 切片类型
fn slice_types() {
    let s = String::from("hello world");
    
    let hello = &s[0..5];      // "hello"
    let world = &s[6..11];     // "world"
    
    println!("Hello: {}, World: {}", hello, world);
}

// 字符串切片
fn string_slices() {
    let s = String::from("hello world");
    
    // 获取字符串切片
    let slice = &s[..];
    println!("Full string slice: {}", slice);
    
    // 获取部分字符串
    let hello = &s[0..5];
    let world = &s[6..];
    
    println!("Hello: {}, World: {}", hello, world);
}

// 数组切片
fn array_slices() {
    let a = [1, 2, 3, 4, 5];
    
    let slice = &a[1..4];  // [2, 3, 4]
    println!("Array slice: {:?}", slice);
    
    // 切片操作
    let sum: i32 = slice.iter().sum();
    println!("Sum of slice: {}", sum);
}
```

### 3.4 字符串类型

Rust 有多种字符串类型：

```rust
// 字符串类型
fn string_types() {
    // 字符串字面量（&str）
    let s1 = "hello";
    let s2: &str = "world";
    
    // 拥有的字符串（String）
    let s3 = String::from("hello");
    let s4 = "world".to_string();
    
    // 字符串操作
    let mut s5 = String::from("hello");
    s5.push_str(", world");
    s5.push('!');
    
    println!("s5: {}", s5);
}

// 字符串方法
fn string_methods() {
    let s = String::from("Hello, World!");
    
    // 长度和容量
    println!("Length: {}", s.len());
    println!("Capacity: {}", s.capacity());
    
    // 字符操作
    println!("First char: {:?}", s.chars().next());
    println!("Last char: {:?}", s.chars().last());
    
    // 字符串分割
    let words: Vec<&str> = s.split(", ").collect();
    println!("Words: {:?}", words);
    
    // 大小写转换
    println!("Uppercase: {}", s.to_uppercase());
    println!("Lowercase: {}", s.to_lowercase());
}
```

## 4. 自定义类型

### 4.1 结构体类型

结构体允许创建自定义数据类型：

```rust
// 结构体类型
#[derive(Debug)]
struct User {
    username: String,
    email: String,
    sign_in_count: u64,
    active: bool,
}

fn struct_types() {
    let user1 = User {
        email: String::from("someone@example.com"),
        username: String::from("someusername123"),
        active: true,
        sign_in_count: 1,
    };
    
    println!("User: {:?}", user1);
    
    // 修改结构体字段
    let mut user2 = user1;
    user2.email = String::from("anotheremail@example.com");
    println!("Modified user: {:?}", user2);
}

// 结构体方法
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

fn use_struct_methods() {
    let mut user = User::new(
        String::from("alice"),
        String::from("alice@example.com"),
    );
    
    user.sign_in();
    println!("User active: {}, Sign in count: {}", 
             user.is_active(), user.sign_in_count);
}

// 元组结构体
struct Color(i32, i32, i32);
struct Point(i32, i32, i32);

fn tuple_structs() {
    let black = Color(0, 0, 0);
    let origin = Point(0, 0, 0);
    
    println!("Black color: ({}, {}, {})", black.0, black.1, black.2);
    println!("Origin point: ({}, {}, {})", origin.0, origin.1, origin.2);
}

// 单元结构体
struct AlwaysEqual;

fn unit_structs() {
    let subject = AlwaysEqual;
    // 单元结构体不包含任何数据
}
```

### 4.2 枚举类型

枚举允许定义可能值的集合：

```rust
// 枚举类型
#[derive(Debug)]
enum IpAddrKind {
    V4,
    V6,
}

fn enum_types() {
    let four = IpAddrKind::V4;
    let six = IpAddrKind::V6;
    
    println!("IP version: {:?}, {:?}", four, six);
}

// 带数据的枚举
#[derive(Debug)]
enum IpAddr {
    V4(String),
    V6(String),
}

fn enum_with_data() {
    let home = IpAddr::V4(String::from("127.0.0.1"));
    let loopback = IpAddr::V6(String::from("::1"));
    
    println!("Home: {:?}, Loopback: {:?}", home, loopback);
}

// 复杂枚举
#[derive(Debug)]
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn complex_enum() {
    let messages = vec![
        Message::Quit,
        Message::Move { x: 10, y: 20 },
        Message::Write(String::from("hello")),
        Message::ChangeColor(255, 0, 0),
    ];
    
    for msg in messages {
        println!("Message: {:?}", msg);
    }
}

// 枚举方法
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

fn use_enum_methods() {
    let msg = Message::Write(String::from("hello"));
    msg.call();
}
```

### 4.3 联合体类型

联合体允许在同一内存位置存储不同类型的数据：

```rust
// 联合体类型
#[repr(C)]
union MyUnion {
    f1: u32,
    f2: f32,
}

fn union_types() {
    let u = MyUnion { f1: 1 };
    
    unsafe {
        println!("Union f1: {}", u.f1);
        println!("Union f2: {}", u.f2);
    }
}

// 安全的联合体使用
use std::mem;

fn safe_union_usage() {
    let u = MyUnion { f1: 0x3f800000 };  // 1.0f32 的位表示
    
    unsafe {
        let f2_value = u.f2;
        println!("Union as f32: {}", f2_value);
        
        // 使用 mem::transmute 进行类型转换
        let f1_value: u32 = mem::transmute(u.f2);
        println!("Union as u32: {}", f1_value);
    }
}
```

### 4.4 类型别名

类型别名允许为现有类型创建新名称：

```rust
// 类型别名
type Kilometers = i32;
type Meters = i32;

fn type_aliases() {
    let distance: Kilometers = 5;
    let height: Meters = 180;
    
    println!("Distance: {} km, Height: {} m", distance, height);
    
    // 类型别名可以互换使用
    let total: i32 = distance + height;
    println!("Total: {}", total);
}

// 复杂类型别名
type Thunk = Box<dyn Fn() + Send + 'static>;
type Result<T> = std::result::Result<T, std::io::Error>;

fn complex_type_aliases() {
    let f: Thunk = Box::new(|| println!("Hello from thunk"));
    f();
    
    let result: Result<String> = Ok("success".to_string());
    println!("Result: {:?}", result);
}

// 泛型类型别名
type GenericResult<T> = Result<T, Box<dyn std::error::Error>>;

fn generic_type_alias() {
    let success: GenericResult<i32> = Ok(42);
    let error: GenericResult<i32> = Err("Something went wrong".into());
    
    println!("Success: {:?}", success);
    println!("Error: {:?}", error);
}
```

## 5. 指针类型

### 5.1 引用类型

引用是 Rust 中最重要的指针类型：

```rust
// 引用类型
fn reference_types() {
    let x = 5;
    let y = &x;  // y 是 x 的引用
    
    println!("x: {}, y: {}", x, y);
    println!("x: {}, *y: {}", x, *y);
}

// 可变引用
fn mutable_references() {
    let mut s = String::from("hello");
    
    change(&mut s);
    println!("Changed string: {}", s);
}

fn change(some_string: &mut String) {
    some_string.push_str(", world");
}

// 引用规则
fn reference_rules() {
    let mut s = String::from("hello");
    
    let r1 = &s;     // 不可变引用
    let r2 = &s;     // 不可变引用
    println!("{} and {}", r1, r2);
    
    let r3 = &mut s; // 可变引用
    r3.push_str(", world");
    println!("{}", r3);
}
```

### 5.2 原始指针

原始指针提供底层内存访问：

```rust
// 原始指针
fn raw_pointers() {
    let mut num = 5;
    
    let r1 = &num as *const i32;      // 不可变原始指针
    let r2 = &mut num as *mut i32;    // 可变原始指针
    
    unsafe {
        println!("r1 is: {}", *r1);
        println!("r2 is: {}", *r2);
        
        *r2 = 10;
        println!("After mutation: {}", *r1);
    }
}

// 原始指针的算术运算
fn raw_pointer_arithmetic() {
    let arr = [1, 2, 3, 4, 5];
    let ptr = arr.as_ptr();
    
    unsafe {
        for i in 0..arr.len() {
            let value = *ptr.add(i);
            println!("arr[{}] = {}", i, value);
        }
    }
}
```

### 5.3 智能指针

智能指针提供额外的功能：

```rust
// 智能指针
use std::rc::Rc;
use std::sync::Arc;

fn smart_pointers() {
    // Box - 堆分配
    let b = Box::new(5);
    println!("Box value: {}", b);
    
    // Rc - 引用计数
    let rc = Rc::new(5);
    let rc_clone = Rc::clone(&rc);
    println!("Rc count: {}", Rc::strong_count(&rc));
    
    // Arc - 原子引用计数
    let arc = Arc::new(5);
    let arc_clone = Arc::clone(&arc);
    println!("Arc count: {}", Arc::strong_count(&arc));
}

// 自定义智能指针
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

fn custom_smart_pointer() {
    let x = 5;
    let y = MyBox::new(x);
    
    assert_eq!(5, x);
    assert_eq!(5, *y);  // 通过 Deref 自动解引用
}
```

## 6. 函数类型

### 6.1 函数指针

函数指针允许将函数作为值传递：

```rust
// 函数指针
fn add_one(x: i32) -> i32 {
    x + 1
}

fn function_pointers() {
    let f: fn(i32) -> i32 = add_one;
    let result = f(5);
    println!("Result: {}", result);
}

// 函数指针作为参数
fn do_twice(f: fn(i32) -> i32, arg: i32) -> i32 {
    f(arg) + f(arg)
}

fn use_function_pointer() {
    let result = do_twice(add_one, 5);
    println!("Do twice result: {}", result);
}

// 函数指针数组
fn function_pointer_array() {
    let functions: [fn(i32) -> i32; 3] = [add_one, |x| x * 2, |x| x * x];
    
    for (i, func) in functions.iter().enumerate() {
        let result = func(5);
        println!("Function {} result: {}", i, result);
    }
}
```

### 6.2 闭包类型

闭包是可以捕获环境的匿名函数：

```rust
// 闭包类型
fn closure_types() {
    let add_one = |x| x + 1;
    let result = add_one(5);
    println!("Closure result: {}", result);
    
    // 带类型注解的闭包
    let add_one_typed = |x: i32| -> i32 { x + 1 };
    let result2 = add_one_typed(5);
    println!("Typed closure result: {}", result2);
}

// 捕获环境
fn closure_capture() {
    let x = 4;
    
    let equal_to_x = |z| z == x;
    let y = 4;
    
    assert!(equal_to_x(y));
    println!("Closure captured x: {}", x);
}

// 移动闭包
fn move_closure() {
    let x = vec![1, 2, 3];
    
    let equal_to_x = move |z| z == x;
    // println!("{:?}", x);  // 错误：x 已被移动
    
    let y = vec![1, 2, 3];
    assert!(equal_to_x(y));
}

// 闭包特征
fn closure_traits() {
    let mut x = 5;
    
    // FnOnce - 只能调用一次
    let fn_once = || {
        let y = x;
        y
    };
    
    // FnMut - 可变借用
    let mut fn_mut = || {
        x += 1;
        x
    };
    
    // Fn - 不可变借用
    let fn_immut = || x;
    
    println!("FnOnce: {}", fn_once());
    println!("FnMut: {}", fn_mut());
    println!("Fn: {}", fn_immut());
}
```

### 6.3 函数项

函数项是函数的零大小类型：

```rust
// 函数项
fn function_items() {
    // 函数项类型
    let f: fn(i32) -> i32 = add_one;
    let g: fn(i32) -> i32 = |x| x * 2;
    
    println!("Function item f: {}", f(5));
    println!("Function item g: {}", g(5));
}

// 函数项的大小
fn function_item_size() {
    println!("Size of function item: {}", std::mem::size_of::<fn(i32) -> i32>());
    println!("Size of closure: {}", std::mem::size_of_val(&|x: i32| x + 1));
}

// 函数项作为泛型参数
fn use_function_item<T>(f: T, x: i32) -> i32
where
    T: Fn(i32) -> i32,
{
    f(x)
}

fn function_item_generic() {
    let result1 = use_function_item(add_one, 5);
    let result2 = use_function_item(|x| x * 2, 5);
    
    println!("Generic function item results: {}, {}", result1, result2);
}
```

## 7. 泛型类型

### 7.1 泛型结构体

```rust
// 泛型结构体
#[derive(Debug)]
struct Point<T> {
    x: T,
    y: T,
}

fn generic_structs() {
    let integer_point = Point { x: 5, y: 10 };
    let float_point = Point { x: 1.0, y: 4.0 };
    
    println!("Integer point: {:?}", integer_point);
    println!("Float point: {:?}", float_point);
}

// 多个类型参数
#[derive(Debug)]
struct Pair<T, U> {
    first: T,
    second: U,
}

fn multiple_generic_params() {
    let pair = Pair {
        first: 5,
        second: "hello",
    };
    
    println!("Pair: {:?}", pair);
}

// 泛型方法
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

// 为特定类型实现方法
impl Point<f32> {
    fn distance_from_origin(&self) -> f32 {
        (self.x.powi(2) + self.y.powi(2)).sqrt()
    }
}

fn use_generic_methods() {
    let point = Point::new(3.0, 4.0);
    println!("Distance from origin: {}", point.distance_from_origin());
}
```

### 7.2 泛型枚举

```rust
// 泛型枚举
#[derive(Debug)]
enum Option<T> {
    Some(T),
    None,
}

#[derive(Debug)]
enum Result<T, E> {
    Ok(T),
    Err(E),
}

fn generic_enums() {
    let some_number = Option::Some(5);
    let some_string = Option::Some("a string");
    let absent_number: Option<i32> = Option::None;
    
    println!("Some number: {:?}", some_number);
    println!("Some string: {:?}", some_string);
    println!("Absent number: {:?}", absent_number);
    
    let success = Result::Ok(42);
    let failure = Result::Err("Something went wrong");
    
    println!("Success: {:?}", success);
    println!("Failure: {:?}", failure);
}

// 泛型枚举方法
impl<T> Option<T> {
    fn is_some(&self) -> bool {
        match self {
            Option::Some(_) => true,
            Option::None => false,
        }
    }
    
    fn is_none(&self) -> bool {
        !self.is_some()
    }
    
    fn unwrap_or(self, default: T) -> T {
        match self {
            Option::Some(value) => value,
            Option::None => default,
        }
    }
}

fn use_generic_enum_methods() {
    let some_value = Option::Some(42);
    let none_value: Option<i32> = Option::None;
    
    println!("Some is some: {}", some_value.is_some());
    println!("None is none: {}", none_value.is_none());
    
    let value = none_value.unwrap_or(0);
    println!("Unwrapped or default: {}", value);
}
```

### 7.3 泛型函数

```rust
// 泛型函数
fn largest<T: PartialOrd + Copy>(list: &[T]) -> T {
    let mut largest = list[0];
    
    for &item in list {
        if item > largest {
            largest = item;
        }
    }
    
    largest
}

fn generic_functions() {
    let number_list = vec![34, 50, 25, 100, 65];
    let result = largest(&number_list);
    println!("The largest number is {}", result);
    
    let char_list = vec!['y', 'm', 'a', 'q'];
    let result = largest(&char_list);
    println!("The largest char is {}", result);
}

// 泛型函数约束
fn generic_with_constraints<T>(item: T) -> T
where
    T: Clone + std::fmt::Debug,
{
    let cloned = item.clone();
    println!("Cloned item: {:?}", cloned);
    item
}

fn use_generic_constraints() {
    let result = generic_with_constraints("hello");
    println!("Result: {}", result);
}
```

## 8. 特征对象

### 8.1 特征对象类型

```rust
// 特征对象类型
trait Drawable {
    fn draw(&self);
}

struct Circle {
    radius: f64,
}

impl Drawable for Circle {
    fn draw(&self) {
        println!("Drawing a circle with radius {}", self.radius);
    }
}

struct Rectangle {
    width: f64,
    height: f64,
}

impl Drawable for Rectangle {
    fn draw(&self) {
        println!("Drawing a rectangle {}x{}", self.width, self.height);
    }
}

fn trait_objects() {
    let circle = Circle { radius: 5.0 };
    let rectangle = Rectangle { width: 3.0, height: 4.0 };
    
    // 特征对象
    let drawables: Vec<Box<dyn Drawable>> = vec![
        Box::new(circle),
        Box::new(rectangle),
    ];
    
    for drawable in drawables {
        drawable.draw();
    }
}
```

### 8.2 对象安全

```rust
// 对象安全
trait ObjectSafe {
    fn method(&self);
    fn method_with_default(&self) {
        println!("Default implementation");
    }
}

// 不对象安全的特征
trait NotObjectSafe {
    fn method(&self);
    fn generic_method<T>(&self, item: T);  // 泛型方法
    fn returns_self(&self) -> Self;        // 返回 Self
}

// 使特征对象安全
trait SafeNotObjectSafe {
    fn method(&self);
    
    fn generic_method<T>(&self, item: T)
    where
        Self: Sized,
    {
        // 实现
    }
    
    fn returns_self(&self) -> Self
    where
        Self: Sized,
    {
        // 实现
    }
}

fn object_safety_example() {
    let safe_objects: Vec<Box<dyn ObjectSafe>> = vec![
        // 可以创建特征对象
    ];
}
```

### 8.3 动态分发

```rust
// 动态分发
fn dynamic_dispatch() {
    let shapes: Vec<Box<dyn Drawable>> = vec![
        Box::new(Circle { radius: 5.0 }),
        Box::new(Rectangle { width: 3.0, height: 4.0 }),
    ];
    
    // 运行时多态
    for shape in shapes {
        shape.draw();
    }
}

// 静态分发 vs 动态分发
fn static_dispatch<T: Drawable>(shape: T) {
    shape.draw();  // 编译时确定
}

fn dynamic_dispatch_trait(shape: Box<dyn Drawable>) {
    shape.draw();  // 运行时确定
}

fn compare_dispatch() {
    let circle = Circle { radius: 5.0 };
    
    // 静态分发
    static_dispatch(circle);
    
    // 动态分发
    let boxed_circle = Box::new(Circle { radius: 5.0 });
    dynamic_dispatch_trait(boxed_circle);
}
```

## 9. 类型转换

### 9.1 隐式转换

```rust
// 隐式转换
fn implicit_conversions() {
    // 数字类型提升
    let x: i32 = 42;
    let y: i64 = x;  // 隐式转换
    
    // 引用转换
    let s = String::from("hello");
    let slice: &str = &s;  // &String 到 &str
    
    println!("x: {}, y: {}, slice: {}", x, y, slice);
}

// Deref 转换
fn deref_conversion() {
    let s = String::from("hello");
    let slice: &str = &s;  // 通过 Deref 转换
    
    // 函数参数中的 Deref 转换
    fn takes_str(s: &str) {
        println!("String: {}", s);
    }
    
    takes_str(&s);  // &String 自动转换为 &str
}
```

### 9.2 显式转换

```rust
// 显式转换
fn explicit_conversions() {
    let x = 3.14;
    let y = x as i32;  // 显式转换
    println!("x: {}, y: {}", x, y);
    
    // 指针转换
    let ptr = &42 as *const i32;
    let raw_ptr = ptr as *mut i32;
    
    // 地址转换
    let addr = ptr as usize;
    let back_to_ptr = addr as *const i32;
    
    println!("Address: 0x{:x}", addr);
}

// 安全的类型转换
fn safe_conversions() {
    let x = 42u32;
    let y = x as u64;  // 安全的扩展转换
    
    let z = 3.14f64;
    let w = z as i32;  // 截断转换
    
    println!("x: {}, y: {}, z: {}, w: {}", x, y, z, w);
}

// 使用 From/Into 特征
fn from_into_conversions() {
    let s = String::from("hello");
    let bytes: Vec<u8> = s.into();  // String 到 Vec<u8>
    
    let back_to_string = String::from_utf8(bytes).unwrap();
    println!("Back to string: {}", back_to_string);
}
```

### 9.3 类型强制

```rust
// 类型强制
fn type_coercion() {
    // 引用强制
    let s = String::from("hello");
    let slice: &str = &s;  // &String 强制为 &str
    
    // 生命周期强制
    let static_str: &'static str = "hello";
    let s: &str = static_str;  // 生命周期强制
    
    // 不安全的强制
    let x = 42;
    let ptr = &x as *const i32;
    let raw_ptr = ptr as *mut i32;  // 不安全的强制
    
    println!("Slice: {}, Static: {}", slice, s);
}

// 自动解引用
fn auto_deref() {
    let s = String::from("hello");
    
    // 自动解引用
    let len = s.len();  // 等价于 (*s).len()
    let first_char = s.chars().next();  // 自动解引用
    
    println!("Length: {}, First char: {:?}", len, first_char);
}
```

## 10. 类型推断

### 10.1 推断规则

```rust
// 类型推断规则
fn type_inference_rules() {
    // 规则1：字面量推断
    let x = 42;        // 推断为 i32
    let y = 3.14;      // 推断为 f64
    let z = true;      // 推断为 bool
    
    // 规则2：函数调用推断
    let vec = Vec::new();  // 无法推断
    let vec: Vec<i32> = Vec::new();  // 显式类型
    
    // 规则3：方法调用推断
    let mut vec = Vec::new();
    vec.push(42);      // 从 push 推断 Vec<i32>
    
    println!("x: {}, y: {}, z: {}", x, y, z);
}

// 推断失败场景
fn inference_failure() {
    // 错误：无法推断类型
    // let x = Vec::new();
    
    // 解决方案1：显式类型注解
    let x: Vec<i32> = Vec::new();
    
    // 解决方案2：提供上下文
    let x = vec![1, 2, 3];  // 从元素推断
    
    // 解决方案3：使用类型注解
    let x = Vec::<i32>::new();
    
    println!("Vec: {:?}", x);
}
```

### 10.2 推断限制

```rust
// 推断限制
fn inference_limitations() {
    // 限制1：空集合
    let mut vec: Vec<i32> = Vec::new();
    vec.push(42);
    
    // 限制2：函数指针
    let func: fn(i32) -> i32 = |x| x * 2;
    
    // 限制3：特征对象
    let display: Box<dyn std::fmt::Display> = Box::new(42);
    
    // 限制4：复杂泛型
    let map: std::collections::HashMap<String, Vec<i32>> = 
        std::collections::HashMap::new();
    
    println!("Func result: {}", func(5));
    println!("Display: {}", display);
    println!("Map: {:?}", map);
}
```

### 10.3 类型注解

```rust
// 类型注解
fn type_annotations() {
    // 变量类型注解
    let x: i32 = 42;
    let y: f64 = 3.14;
    let z: bool = true;
    
    // 函数类型注解
    let add: fn(i32, i32) -> i32 = |a, b| a + b;
    
    // 结构体类型注解
    let point: Point<i32> = Point { x: 1, y: 2 };
    
    // 枚举类型注解
    let option: Option<String> = Some("hello".to_string());
    
    println!("x: {}, y: {}, z: {}", x, y, z);
    println!("Add result: {}", add(1, 2));
    println!("Point: {:?}", point);
    println!("Option: {:?}", option);
}

// 泛型类型注解
fn generic_type_annotations() {
    let vec: Vec<i32> = vec![1, 2, 3];
    let option: Option<String> = Some("hello".to_string());
    let result: Result<i32, String> = Ok(42);
    
    println!("Vec: {:?}, Option: {:?}, Result: {:?}", vec, option, result);
}
```

## 11. 最佳实践

### 11.1 类型设计原则

```rust
// 类型设计原则
fn type_design_principles() {
    // 原则1：使用有意义的类型
    type UserId = u64;
    type Email = String;
    
    struct User {
        id: UserId,
        email: Email,
    }
    
    // 原则2：使用适当的抽象级别
    struct BankAccount {
        balance: f64,
        account_number: String,
    }
    
    impl BankAccount {
        fn deposit(&mut self, amount: f64) {
            self.balance += amount;
        }
        
        fn withdraw(&mut self, amount: f64) -> Result<f64, String> {
            if amount > self.balance {
                Err("Insufficient funds".to_string())
            } else {
                self.balance -= amount;
                Ok(self.balance)
            }
        }
    }
    
    // 原则3：使用类型系统防止错误
    #[derive(Debug, PartialEq)]
    struct NonEmptyString(String);
    
    impl NonEmptyString {
        fn new(s: String) -> Option<Self> {
            if s.is_empty() {
                None
            } else {
                Some(NonEmptyString(s))
            }
        }
    }
    
    let valid_string = NonEmptyString::new("hello".to_string());
    let invalid_string = NonEmptyString::new("".to_string());
    
    println!("Valid: {:?}, Invalid: {:?}", valid_string, invalid_string);
}
```

### 11.2 命名约定

```rust
// 命名约定
fn naming_conventions() {
    // 类型命名：PascalCase
    struct UserAccount;
    enum AccountStatus;
    type UserId = u64;
    
    // 变量命名：snake_case
    let user_account = UserAccount;
    let account_status = AccountStatus::Active;
    let user_id: UserId = 12345;
    
    // 常量命名：SCREAMING_SNAKE_CASE
    const MAX_USERS: u32 = 1000;
    const DEFAULT_TIMEOUT: u64 = 30;
    
    // 特征命名：PascalCase，通常以 -able 结尾
    trait Drawable {
        fn draw(&self);
    }
    
    trait Readable {
        fn read(&self) -> String;
    }
    
    println!("Max users: {}, Timeout: {}", MAX_USERS, DEFAULT_TIMEOUT);
}

// 枚举变体命名
#[derive(Debug)]
enum HttpStatus {
    Ok,                    // 简单变体
    NotFound,              // 简单变体
    InternalServerError,   // 简单变体
    BadRequest { code: u16, message: String },  // 带数据的变体
}

fn enum_naming() {
    let statuses = vec![
        HttpStatus::Ok,
        HttpStatus::NotFound,
        HttpStatus::InternalServerError,
        HttpStatus::BadRequest { 
            code: 400, 
            message: "Bad Request".to_string() 
        },
    ];
    
    for status in statuses {
        println!("Status: {:?}", status);
    }
}
```

### 11.3 性能考虑

```rust
// 性能考虑
fn performance_considerations() {
    // 1. 使用 Copy 类型避免移动开销
    #[derive(Copy, Clone, Debug)]
    struct Point {
        x: i32,
        y: i32,
    }
    
    let p1 = Point { x: 1, y: 2 };
    let p2 = p1;  // 复制，不是移动
    println!("p1: {:?}, p2: {:?}", p1, p2);
    
    // 2. 使用引用避免克隆
    let s = String::from("hello");
    let slice = &s;  // 借用，不克隆
    println!("Slice: {}", slice);
    
    // 3. 使用适当的容器类型
    let vec = vec![1, 2, 3, 4, 5];  // 连续内存
    let sum: i32 = vec.iter().sum();
    println!("Sum: {}", sum);
    
    // 4. 避免不必要的类型转换
    let x = 42i32;
    let y = 100i32;
    let sum = x + y;  // 直接运算，避免转换
    println!("Sum: {}", sum);
}

// 内存布局优化
#[repr(C)]
struct OptimizedStruct {
    large_field: u64,  // 8 字节
    medium_field: u32, // 4 字节
    small_field: u16,  // 2 字节
    tiny_field: u8,    // 1 字节
}

fn memory_layout_optimization() {
    println!("Optimized struct size: {}", std::mem::size_of::<OptimizedStruct>());
    println!("Optimized struct alignment: {}", std::mem::align_of::<OptimizedStruct>());
}
```

## 12. 总结

Rust 的类型定义系统提供了强大而灵活的类型抽象能力：

1. **类型安全**: 编译时保证类型正确性
2. **内存安全**: 通过类型系统防止内存错误
3. **性能优化**: 零成本抽象和编译时优化
4. **代码清晰**: 明确表达程序意图

### 关键要点

- 类型是值的分类系统，定义了可执行的操作
- 基本类型包括标量类型和复合类型
- 自定义类型通过结构体、枚举、联合体定义
- 指针类型提供内存访问和所有权管理
- 泛型类型支持参数多态
- 特征对象支持运行时多态

### 进一步学习

- 学习更多高级类型特性
- 研究类型系统的理论基础
- 了解类型推断算法
- 实践编写类型安全的代码

---

**示例与测试**: 见 `examples/type_definition_examples.rs` 与 `tests/type_definition_tests.rs`。
