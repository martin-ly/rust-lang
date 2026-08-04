# 05 类型系统实际示例

## 目录

- [05 类型系统实际示例](#05-类型系统实际示例)
  - [目录](#目录)
  - [1. 基本类型示例](#1-基本类型示例)
    - [1.1 整数类型](#11-整数类型)
    - [1.2 浮点类型](#12-浮点类型)
    - [1.3 布尔类型](#13-布尔类型)
    - [1.4 字符类型](#14-字符类型)
    - [1.5 字符串类型](#15-字符串类型)
  - [2. 复合类型示例](#2-复合类型示例)
    - [2.1 元组类型](#21-元组类型)
    - [2.2 数组类型](#22-数组类型)
    - [2.3 向量类型](#23-向量类型)
    - [2.4 切片类型](#24-切片类型)
  - [3. 函数类型示例](#3-函数类型示例)
    - [3.1 基本函数](#31-基本函数)
    - [3.2 闭包](#32-闭包)
    - [3.3 高阶函数](#33-高阶函数)
  - [4. 泛型类型示例](#4-泛型类型示例)
    - [4.1 泛型函数](#41-泛型函数)
    - [4.2 泛型结构体体体体](#42-泛型结构体体体体)
    - [4.3 泛型枚举](#43-泛型枚举)
  - [5. Trait类型示例](#5-trait类型示例)
    - [5.1 基本Trait](#51-基本trait)
    - [5.2 泛型Trait](#52-泛型trait)
    - [5.3 关联类型Trait](#53-关联类型trait)
  - [6. 高级类型示例](#6-高级类型示例)
    - [6.1 智能指针](#61-智能指针)
    - [6.2 类型别名](#62-类型别名)
    - [6.3 高级模式匹配](#63-高级模式匹配)

## 1. 基本类型示例

### 1.1 整数类型

```rust
fn integer_types() {
    // 有符号整数
    let x: i8 = 127;
    let y: i16 = 32767;
    let z: i32 = 2147483647;
    let w: i64 = 9223372036854775807;
    let v: i128 = 170141183460469231731687303715884105727;
    
    // 无符号整数
    let a: u8 = 255;
    let b: u16 = 65535;
    let c: u32 = 4294967295;
    let d: u64 = 18446744073709551615;
    let e: u128 = 340282366920938463463374607431768211455;
    
    // 平台相关整数
    let f: isize = 9223372036854775807;  // 64位平台
    let g: usize = 18446744073709551615; // 64位平台
    
    // 整数运算
    let sum = x + y as i8;
    let product = z * w as i32;
    let remainder = v % 10;
}
```

### 1.2 浮点类型

```rust
fn float_types() {
    // 单精度浮点
    let x: f32 = 3.14;
    let y: f32 = 2.718;
    
    // 双精度浮点
    let z: f64 = 3.14159265359;
    let w: f64 = 2.71828182846;
    
    // 浮点运算
    let sum = x + y;
    let product = z * w;
    let power = x.powf(2.0);
    let sqrt = z.sqrt();
    
    // 特殊值
    let infinity = f64::INFINITY;
    let neg_infinity = f64::NEG_INFINITY;
    let nan = f64::NAN;
}
```

### 1.3 布尔类型

```rust
fn boolean_types() {
    let true_val: bool = true;
    let false_val: bool = false;
    
    // 布尔运算
    let and_result = true_val && false_val;  // false
    let or_result = true_val || false_val;   // true
    let not_result = !true_val;              // false
    
    // 条件表达式
    let conditional = if true_val { 42 } else { 0 };
    
    // 比较运算
    let equal = 5 == 5;      // true
    let not_equal = 5 != 3;  // true
    let less = 3 < 5;        // true
    let greater = 7 > 4;     // true
}
```

### 1.4 字符类型

```rust
fn character_types() {
    // Unicode字符
    let c1: char = 'A';
    let c2: char = '中';
    let c3: char = '😀';
    let c4: char = '\u{1F600}';  // 笑脸emoji
    
    // 转义字符
    let newline = '\n';
    let tab = '\t';
    let backslash = '\\';
    let quote = '\'';
    
    // 字符运算
    let next_char = (c1 as u8 + 1) as char;  // 'B'
    let is_alphabetic = c1.is_alphabetic();
    let is_digit = '5'.is_digit(10);
}
```

### 1.5 字符串类型

```rust
fn string_types() {
    // 字符串切片
    let s1: &str = "Hello, World!";
    let s2: &str = "你好，世界！";
    
    // 拥有字符串
    let s3: String = String::from("Hello");
    let s4: String = "World".to_string();
    
    // 字符串操作
    let concatenated = s3 + " " + &s4;
    let formatted = format!("{} {}", s3, s4);
    
    // 字符串方法
    let length = s1.len();
    let is_empty = s1.is_empty();
    let contains = s1.contains("Hello");
    let starts_with = s1.starts_with("Hello");
    let ends_with = s1.ends_with("!");
}
```

## 2. 复合类型示例

### 2.1 元组类型

```rust
fn tuple_types() {
    // 基本元组
    let tuple1: (i32, f64, &str) = (1, 2.0, "three");
    let tuple2 = (42, "hello", true);
    
    // 元组访问
    let first = tuple1.0;
    let second = tuple1.1;
    let third = tuple1.2;
    
    // 元组解构
    let (x, y, z) = tuple1;
    let (a, _, c) = tuple2;  // 忽略第二个元素
    
    // 嵌套元组
    let nested = ((1, 2), (3, 4));
    let ((a, b), (c, d)) = nested;
    
    // 空元组
    let unit = ();
    let function_return = ();  // 隐式返回类型
}
```

### 2.2 数组类型

```rust
fn array_types() {
    // 固定大小数组
    let arr1: [i32; 5] = [1, 2, 3, 4, 5];
    let arr2 = [0; 10];  // 10个0
    
    // 数组访问
    let first = arr1[0];
    let last = arr1[4];
    
    // 数组迭代
    for element in &arr1 {
        println!("{}", element);
    }
    
    // 数组方法
    let length = arr1.len();
    let is_empty = arr1.is_empty();
    let first_element = arr1.first();
    let last_element = arr1.last();
    
    // 多维数组
    let matrix: [[i32; 3]; 3] = [
        [1, 2, 3],
        [4, 5, 6],
        [7, 8, 9],
    ];
    
    let element = matrix[1][2];  // 6
}
```

### 2.3 向量类型

```rust
fn vector_types() {
    // 创建向量
    let mut vec1: Vec<i32> = Vec::new();
    let vec2 = vec![1, 2, 3, 4, 5];
    let vec3: Vec<i32> = (0..10).collect();
    
    // 向量操作
    vec1.push(42);
    vec1.push(100);
    let popped = vec1.pop();
    
    // 向量访问
    let first = vec2[0];
    let last = vec2.last();
    let slice = &vec2[1..4];
    
    // 向量迭代
    for element in &vec2 {
        println!("{}", element);
    }
    
    for (index, element) in vec2.iter().enumerate() {
        println!("{}: {}", index, element);
    }
    
    // 向量方法
    let length = vec2.len();
    let capacity = vec2.capacity();
    let is_empty = vec2.is_empty();
    
    // 向量转换
    let sorted = vec![3, 1, 4, 1, 5];
    let mut sorted = sorted;
    sorted.sort();
}
```

### 2.4 切片类型

```rust
fn slice_types() {
    let data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    // 切片引用
    let slice1: &[i32] = &data[0..5];    // [1, 2, 3, 4, 5]
    let slice2: &[i32] = &data[5..];     // [6, 7, 8, 9, 10]
    let slice3: &[i32] = &data[..5];     // [1, 2, 3, 4, 5]
    let slice4: &[i32] = &data[..];      // 整个数组
    
    // 切片操作
    let length = slice1.len();
    let is_empty = slice1.is_empty();
    let first = slice1.first();
    let last = slice1.last();
    
    // 切片迭代
    for element in slice1 {
        println!("{}", element);
    }
    
    // 字符串切片
    let text = "Hello, World!";
    let hello: &str = &text[0..5];   // "Hello"
    let world: &str = &text[7..12];  // "World"
}
```

## 3. 函数类型示例

### 3.1 基本函数

```rust
fn basic_functions() {
    // 无参数无返回值
    fn greet() {
        println!("Hello, World!");
    }
    
    // 有参数无返回值
    fn print_number(x: i32) {
        println!("Number: {}", x);
    }
    
    // 有参数有返回值
    fn add(x: i32, y: i32) -> i32 {
        x + y
    }
    
    // 函数调用
    greet();
    print_number(42);
    let result = add(5, 3);
    
    // 函数指针
    let func: fn(i32, i32) -> i32 = add;
    let result2 = func(10, 20);
}
```

### 3.2 闭包

```rust
fn closure_types() {
    // 基本闭包
    let add_one = |x| x + 1;
    let result = add_one(5);  // 6
    
    // 带类型注解的闭包
    let multiply: fn(i32, i32) -> i32 = |x, y| x * y;
    let product = multiply(4, 6);  // 24
    
    // 捕获环境的闭包
    let factor = 10;
    let multiply_by_factor = |x| x * factor;
    let result = multiply_by_factor(5);  // 50
    
    // 可变闭包
    let mut counter = 0;
    let mut increment = || {
        counter += 1;
        counter
    };
    
    let first = increment();  // 1
    let second = increment(); // 2
    
    // 移动语义闭包
    let data = vec![1, 2, 3, 4, 5];
    let print_data = move || {
        for element in data {
            println!("{}", element);
        }
    };
    
    print_data();
    // data在这里已经不可用
}
```

### 3.3 高阶函数

```rust
fn higher_order_functions() {
    // 接受函数作为参数
    fn apply<F>(f: F, x: i32, y: i32) -> i32 
    where F: Fn(i32, i32) -> i32 
    {
        f(x, y)
    }
    
    let add = |x, y| x + y;
    let multiply = |x, y| x * y;
    
    let sum = apply(add, 5, 3);      // 8
    let product = apply(multiply, 4, 6);  // 24
    
    // 返回函数
    fn create_adder(n: i32) -> impl Fn(i32) -> i32 {
        move |x| x + n
    }
    
    let add_five = create_adder(5);
    let result = add_five(10);  // 15
    
    // 函数组合
    fn compose<F, G, T, U, V>(f: F, g: G) -> impl Fn(T) -> V
    where
        F: Fn(U) -> V,
        G: Fn(T) -> U,
    {
        move |x| f(g(x))
    }
    
    let double = |x| x * 2;
    let add_one = |x| x + 1;
    let double_then_add = compose(add_one, double);
    let result = double_then_add(5);  // 11
}
```

## 4. 泛型类型示例

### 4.1 泛型函数

```rust
fn generic_functions() {
    // 基本泛型函数
    fn identity<T>(x: T) -> T {
        x
    }
    
    let int_result: i32 = identity(42);
    let string_result: String = identity(String::from("hello"));
    let bool_result: bool = identity(true);
    
    // 多类型参数
    fn pair<T, U>(x: T, y: U) -> (T, U) {
        (x, y)
    }
    
    let result = pair(42, "hello");
    
    // 泛型比较函数
    fn find_max<T: PartialOrd>(list: &[T]) -> Option<&T> {
        list.iter().max()
    }
    
    let numbers = vec![1, 5, 3, 9, 2];
    let max_number = find_max(&numbers);
    
    let strings = vec!["apple", "banana", "cherry"];
    let max_string = find_max(&strings);
}
```

### 4.2 泛型结构体体体体

```rust
fn generic_structs() {
    // 基本泛型结构体体体体
    struct Container<T> {
        data: T,
    }
    
    let int_container = Container { data: 42 };
    let string_container = Container { data: String::from("hello") };
    
    // 多类型参数结构体体体体
    struct Pair<T, U> {
        first: T,
        second: U,
    }
    
    let pair = Pair {
        first: 42,
        second: "hello",
    };
    
    // 泛型方法
    impl<T> Container<T> {
        fn new(data: T) -> Self {
            Container { data }
        }
        
        fn get_data(&self) -> &T {
            &self.data
        }
        
        fn set_data(&mut self, data: T) {
            self.data = data;
        }
    }
    
    let mut container = Container::new(42);
    let data = container.get_data();
    container.set_data(100);
}
```

### 4.3 泛型枚举

```rust
fn generic_enums() {
    // 基本泛型枚举
    enum Option<T> {
        Some(T),
        None,
    }
    
    let some_int: Option<i32> = Option::Some(42);
    let none_int: Option<i32> = Option::None;
    
    // 多类型参数枚举
    enum Result<T, E> {
        Ok(T),
        Err(E),
    }
    
    let success: Result<i32, String> = Result::Ok(42);
    let failure: Result<i32, String> = Result::Err(String::from("error"));
    
    // 泛型枚举方法
    impl<T> Option<T> {
        fn is_some(&self) -> bool {
            matches!(self, Option::Some(_))
        }
        
        fn is_none(&self) -> bool {
            matches!(self, Option::None)
        }
        
        fn unwrap(self) -> T {
            match self {
                Option::Some(value) => value,
                Option::None => panic!("called `unwrap()` on a `None` value"),
            }
        }
    }
    
    let option = Option::Some(42);
    if option.is_some() {
        let value = option.unwrap();
        println!("Value: {}", value);
    }
}
```

## 5. Trait类型示例

### 5.1 基本Trait

```rust
fn basic_traits() {
    // 定义trait
    trait Printable {
        fn print(&self);
        fn to_string(&self) -> String;
    }
    
    // 为基本类型实现trait
    impl Printable for i32 {
        fn print(&self) {
            println!("Integer: {}", self);
        }
        
        fn to_string(&self) -> String {
            self.to_string()
        }
    }
    
    impl Printable for String {
        fn print(&self) {
            println!("String: {}", self);
        }
        
        fn to_string(&self) -> String {
            self.clone()
        }
    }
    
    // 使用trait
    let number = 42;
    number.print();
    
    let text = String::from("hello");
    text.print();
    
    // Trait约束函数
    fn print_value<T: Printable>(value: T) {
        value.print();
    }
    
    print_value(42);
    print_value(String::from("world"));
}
```

### 5.2 泛型Trait

```rust
fn generic_traits() {
    // 泛型trait
    trait Container<T> {
        fn len(&self) -> usize;
        fn is_empty(&self) -> bool;
        fn contains(&self, item: &T) -> bool;
    }
    
    // 为Vec实现trait
    impl<T: PartialEq> Container<T> for Vec<T> {
        fn len(&self) -> usize {
            self.len()
        }
        
        fn is_empty(&self) -> bool {
            self.is_empty()
        }
        
        fn contains(&self, item: &T) -> bool {
            self.contains(item)
        }
    }
    
    // 使用泛型trait
    let numbers = vec![1, 2, 3, 4, 5];
    println!("Length: {}", numbers.len());
    println!("Contains 3: {}", numbers.contains(&3));
    
    // Trait约束
    fn process_container<T, C>(container: &C, item: &T)
    where
        C: Container<T>,
        T: std::fmt::Display,
    {
        if container.contains(item) {
            println!("Container has {} items and contains {}", container.len(), item);
        }
    }
    
    process_container(&numbers, &3);
}
```

### 5.3 关联类型Trait

```rust
fn associated_type_traits() {
    // 关联类型trait
    trait Iterator {
        type Item;
        fn next(&mut self) -> Option<Self::Item>;
    }
    
    // 实现迭代器
    struct Counter {
        count: u32,
        max: u32,
    }
    
    impl Iterator for Counter {
        type Item = u32;
        
        fn next(&mut self) -> Option<u32> {
            if self.count < self.max {
                self.count += 1;
                Some(self.count)
            } else {
                None
            }
        }
    }
    
    // 使用迭代器
    let mut counter = Counter { count: 0, max: 5 };
    while let Some(num) = counter.next() {
        println!("{}", num);
    }
    
    // 泛型迭代器
    trait Collection {
        type Item;
        type Iterator: Iterator<Item = Self::Item>;
        
        fn iter(&self) -> Self::Iterator;
    }
    
    impl Collection for Vec<i32> {
        type Item = i32;
        type Iterator = std::vec::IntoIter<i32>;
        
        fn iter(&self) -> Self::Iterator {
            self.clone().into_iter()
        }
    }
}
```

## 6. 高级类型示例

### 6.1 智能指针

```rust
fn smart_pointers() {
    // Box智能指针
    let boxed_int = Box::new(42);
    let boxed_string = Box::new(String::from("hello"));
    
    // 递归数据结构体体体
    enum List<T> {
        Cons(T, Box<List<T>>),
        Nil,
    }
    
    let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
    
    // Rc智能指针
    use std::rc::Rc;
    
    let shared_data = Rc::new(vec![1, 2, 3, 4, 5]);
    let reference1 = Rc::clone(&shared_data);
    let reference2 = Rc::clone(&shared_data);
    
    println!("Reference count: {}", Rc::strong_count(&shared_data));
    
    // Arc智能指针
    use std::sync::Arc;
    use std::thread;
    
    let shared_counter = Arc::new(std::sync::Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&shared_counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Final count: {}", *shared_counter.lock().unwrap());
}
```

### 6.2 类型别名

```rust
fn type_aliases() {
    // 基本类型别名
    type Kilometers = i32;
    type Meters = i32;
    
    let distance: Kilometers = 5;
    let height: Meters = 100;
    
    // 泛型类型别名
    type Result<T> = std::result::Result<T, String>;
    type Option<T> = std::option::Option<T>;
    
    let success: Result<i32> = Ok(42);
    let failure: Result<i32> = Err(String::from("error"));
    
    // 函数类型别名
    type MathFn = fn(i32, i32) -> i32;
    
    let add: MathFn = |x, y| x + y;
    let multiply: MathFn = |x, y| x * y;
    
    // 复杂类型别名
    type ComplexResult<T, E> = Result<Option<T>, E>;
    
    let complex: ComplexResult<i32, String> = Ok(Some(42));
}
```

### 6.3 高级模式匹配

```rust
fn advanced_pattern_matching() {
    // 结构体体体体模式匹配
    struct Point {
        x: i32,
        y: i32,
    }
    
    let point = Point { x: 10, y: 20 };
    
    match point {
        Point { x, y } => println!("Point at ({}, {})", x, y),
    }
    
    // 枚举模式匹配
    enum Message {
        Quit,
        Move { x: i32, y: i32 },
        Write(String),
        ChangeColor(i32, i32, i32),
    }
    
    let message = Message::Move { x: 10, y: 20 };
    
    match message {
        Message::Quit => println!("Quit"),
        Message::Move { x, y } => println!("Move to ({}, {})", x, y),
        Message::Write(text) => println!("Write: {}", text),
        Message::ChangeColor(r, g, b) => println!("Color: ({}, {}, {})", r, g, b),
    }
    
    // 守卫条件
    let number = Some(42);
    
    match number {
        Some(x) if x < 10 => println!("Small number: {}", x),
        Some(x) if x < 100 => println!("Medium number: {}", x),
        Some(x) => println!("Large number: {}", x),
        None => println!("No number"),
    }
    
    // 绑定模式
    let value = Some(42);
    
    match value {
        Some(x @ 1..=50) => println!("Small number: {}", x),
        Some(x @ 51..=100) => println!("Medium number: {}", x),
        Some(x) => println!("Large number: {}", x),
        None => println!("No value"),
    }
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-01-27  
**维护者**: Rust语言形式化理论项目组  
**状态**: 完成
