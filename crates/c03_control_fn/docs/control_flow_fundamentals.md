# 控制流基础概念

本文档介绍 Rust 中控制流的核心概念，包括条件语句、循环、模式匹配和函数控制流。

## 目录

- [条件控制流](#条件控制流)
- [循环控制流](#循环控制流)
- [模式匹配](#模式匹配)
- [函数控制流](#函数控制流)
- [错误处理控制流](#错误处理控制流)
- [异步控制流](#异步控制流)

## 条件控制流

### if 表达式

Rust 中的 `if` 是一个表达式，不是语句，这意味着它可以返回值：

```rust
let number = 6;

let result = if number % 4 == 0 {
    "divisible by 4"
} else if number % 3 == 0 {
    "divisible by 3"
} else if number % 2 == 0 {
    "divisible by 2"
} else {
    "not divisible by 4, 3, or 2"
};

println!("{}", result);
```

### match 表达式

`match` 是 Rust 中最强大的控制流构造，它允许你根据模式匹配来执行不同的代码分支：

```rust
let number = 13;

match number {
    1 => println!("One!"),
    2 | 3 | 5 | 7 | 11 => println!("This is a prime"),
    13..=19 => println!("A teen"),
    _ => println!("Ain't special"),
}
```

## 循环控制流

### loop 循环

`loop` 创建一个无限循环，直到遇到 `break`：

```rust
let mut counter = 0;

let result = loop {
    counter += 1;

    if counter == 10 {
        break counter * 2;
    }
};

println!("The result is {}", result);
```

### while 循环

`while` 循环在条件为真时继续执行：

```rust
let mut number = 3;

while number != 0 {
    println!("{}!", number);
    number -= 1;
}

println!("LIFTOFF!!!");
```

### for 循环

`for` 循环用于遍历集合：

```rust
let a = [10, 20, 30, 40, 50];

for element in a.iter() {
    println!("the value is: {}", element);
}

// 使用范围
for number in (1..4).rev() {
    println!("{}!", number);
}
```

## 模式匹配

### 基本模式匹配

```rust
let x = 1;

match x {
    1 => println!("one"),
    2 => println!("two"),
    3 => println!("three"),
    _ => println!("anything"),
}
```

### 解构模式

```rust
struct Point {
    x: i32,
    y: i32,
}

let p = Point { x: 0, y: 7 };

match p {
    Point { x, y: 0 } => println!("On the x axis at {}", x),
    Point { x: 0, y } => println!("On the y axis at {}", y),
    Point { x, y } => println!("On neither axis: ({}, {})", x, y),
}
```

### 守卫条件

```rust
let num = Some(4);

match num {
    Some(x) if x < 5 => println!("less than five: {}", x),
    Some(x) => println!("{}", x),
    None => (),
}
```

## 函数控制流

### 函数定义与调用

```rust
fn five() -> i32 {
    5  // 没有分号，这是一个表达式
}

fn main() {
    let x = five();
    println!("The value of x is: {}", x);
}
```

### 函数参数

```rust
fn another_function(x: i32, y: i32) {
    println!("The value of x is: {}", x);
    println!("The value of y is: {}", y);
}

fn main() {
    another_function(5, 6);
}
```

### 闭包

```rust
let add_one = |x: i32| -> i32 { x + 1 };
let add_one_v2 = |x| x + 1;  // 类型推断

let result = add_one(5);
println!("Result: {}", result);
```

## 错误处理控制流

### Result 类型

```rust
use std::fs::File;
use std::io::ErrorKind;

fn open_file() -> Result<File, std::io::Error> {
    let f = File::open("hello.txt");

    let f = match f {
        Ok(file) => file,
        Err(error) => match error.kind() {
            ErrorKind::NotFound => match File::create("hello.txt") {
                Ok(fc) => fc,
                Err(e) => panic!("Problem creating the file: {:?}", e),
            },
            other_error => {
                panic!("Problem opening the file: {:?}", other_error)
            }
        },
    };
    Ok(f)
}
```

### ? 操作符

```rust
use std::fs::File;
use std::io;
use std::io::Read;

fn read_username_from_file() -> Result<String, io::Error> {
    let mut f = File::open("hello.txt")?;
    let mut s = String::new();
    f.read_to_string(&mut s)?;
    Ok(s)
}
```

### panic! 宏

```rust
fn main() {
    panic!("crash and burn");
}

// 条件性 panic
let v = vec![1, 2, 3];
v[99]; // 这会导致 panic
```

## 异步控制流

### async/await

```rust
use std::future::Future;

async fn hello_world() {
    println!("hello, world!");
}

async fn learn_song() -> String {
    "song".to_string()
}

async fn sing_song(song: String) {
    println!("Singing: {}", song);
}

async fn dance() {
    println!("Dancing!");
}

async fn learn_and_sing() {
    let song = learn_song().await;
    sing_song(song).await;
}

async fn async_main() {
    let f1 = learn_and_sing();
    let f2 = dance();

    futures::join!(f1, f2);
}

fn main() {
    let future = async_main();
    // 需要运行时来执行
}
```

### 异步迭代器

```rust
use futures::stream::{self, StreamExt};

async fn process_stream() {
    let mut stream = stream::iter(1..=3);
    
    while let Some(value) = stream.next().await {
        println!("Got: {}", value);
    }
}
```

## 最佳实践

1. **优先使用 match 而不是 if-else 链**：match 更安全，编译器会检查穷尽性
2. **使用 ? 操作符简化错误处理**：让代码更简洁易读
3. **合理使用闭包**：在需要函数式编程风格时使用
4. **异步编程时注意生命周期**：确保异步函数中的引用有效
5. **使用 guard 条件增强模式匹配**：提供更精确的控制

## 相关主题

- [函数与闭包详解](./functions_closures.md)
- [错误处理最佳实践](./error_handling.md)
- [异步编程指南](./async_programming.md)
- [模式匹配进阶](./pattern_matching_advanced.md)
