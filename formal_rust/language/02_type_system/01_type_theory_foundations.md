# 2. 类型系统理论基础

## 目录

2. [2. 类型系统理论基础](#2-类型系统理论基础)
   1. [2.1 引言](#21-引言)
   2. [2.2 类型系统基础](#22-类型系统基础)
      1. [2.2.1 类型与值](#221-类型与值)
      2. [2.2.2 类型安全](#222-类型安全)
      3. [2.2.3 类型推导](#223-类型推导)
   3. [2.3 Rust类型系统架构](#23-rust类型系统架构)
      1. [2.3.1 基本类型](#231-基本类型)
      2. [2.3.2 复合类型](#232-复合类型)
      3. [2.3.3 引用类型](#233-引用类型)
      4. [2.3.4 智能指针类型](#234-智能指针类型)
   4. [2.4 类型系统形式化](#24-类型系统形式化)
      1. [2.4.1 类型规则](#241-类型规则)
      2. [2.4.2 子类型关系](#242-子类型关系)
      3. [2.4.3 类型等价性](#243-类型等价性)
   5. [2.5 高级类型特性](#25-高级类型特性)
      1. [2.5.1 泛型系统](#251-泛型系统)
      2. [2.5.2 Trait系统](#252-trait系统)
      3. [2.5.3 关联类型](#253-关联类型)
   6. [2.6 类型系统与内存安全](#26-类型系统与内存安全)
   7. [2.7 总结](#27-总结)

## 2.1 引言

Rust的类型系统是其内存安全和并发安全保证的核心机制之一。通过静态类型检查，Rust在编译时就能发现大部分错误，确保程序在运行时的安全性。

### 2.1.1 类型系统的设计目标

```rust
// 类型系统的核心价值
fn type_system_goals() {
    // 1. 内存安全 - 通过类型检查防止内存错误
    let x: i32 = 5;
    // let y: &str = x; // 编译错误：类型不匹配
    
    // 2. 并发安全 - 通过类型系统保证线程安全
    let data = vec![1, 2, 3];
    let ref1 = &data; // 不可变引用
    // let ref2 = &mut data; // 编译错误：违反借用规则
    
    // 3. 零成本抽象 - 类型信息在编译时消除
    let v: Vec<i32> = vec![1, 2, 3];
    // 编译后，类型信息被消除，运行时无开销
}
```

## 2.2 类型系统基础

### 2.2.1 类型与值

**类型定义**：

类型是值的集合，描述了值的形式和可执行的操作。在Rust中，每个值都有明确的类型。

**形式化表示**：

```
T ::= τ | T → T | ∀α.T | T × T | T + T
```

其中：
- `τ` 是基本类型
- `T → T` 是函数类型
- `∀α.T` 是泛型类型
- `T × T` 是乘积类型（元组、结构体）
- `T + T` 是求和类型（枚举）

**实现示例**：

```rust
fn types_and_values() {
    // 基本类型
    let x: i32 = 42;           // 整数类型
    let y: f64 = 3.14;         // 浮点类型
    let z: bool = true;        // 布尔类型
    let s: &str = "hello";     // 字符串切片类型
    
    // 复合类型
    let tuple: (i32, f64) = (1, 2.0);           // 元组类型
    let array: [i32; 3] = [1, 2, 3];            // 数组类型
    let vector: Vec<i32> = vec![1, 2, 3];       // 向量类型
    
    // 引用类型
    let ref_x: &i32 = &x;                       // 不可变引用
    let mut ref_y: &mut f64 = &mut y;           // 可变引用
    
    // 函数类型
    let func: fn(i32) -> i32 = |x| x * 2;       // 函数类型
}
```

### 2.2.2 类型安全

**类型安全定义**：

类型安全确保程序在运行时不会出现类型错误，如访问不存在的字段、调用不存在的方法等。

**类型安全保证**：

```rust
fn type_safety() {
    // 1. 字段访问安全
    struct Point {
        x: i32,
        y: i32,
    }
    
    let p = Point { x: 1, y: 2 };
    println!("x: {}, y: {}", p.x, p.y);
    // println!("z: {}", p.z); // 编译错误：字段不存在
    
    // 2. 方法调用安全
    let v = vec![1, 2, 3];
    println!("长度: {}", v.len());
    // v.non_existent_method(); // 编译错误：方法不存在
    
    // 3. 类型转换安全
    let x: i32 = 5;
    let y: f64 = x as f64; // 显式类型转换
    // let z: &str = x; // 编译错误：无法隐式转换
}
```

### 2.2.3 类型推导

**类型推导算法**：

Rust使用Hindley-Milner类型推导算法，能够自动推导大部分类型。

**推导规则**：

```
Γ ⊢ e : τ    Γ ⊢ e' : τ'
───────────────────────── (Application)
Γ ⊢ e e' : τ'

Γ, x:τ ⊢ e : τ'
──────────────── (Abstraction)
Γ ⊢ λx.e : τ → τ'
```

**实现示例**：

```rust
fn type_inference() {
    // 基本类型推导
    let x = 5;              // 推导为 i32
    let y = 3.14;           // 推导为 f64
    let z = "hello";        // 推导为 &str
    
    // 泛型类型推导
    let v = vec![1, 2, 3];  // 推导为 Vec<i32>
    let m = HashMap::new(); // 推导为 HashMap<K, V>，需要上下文
    
    // 函数类型推导
    let add = |x, y| x + y; // 推导为 fn(i32, i32) -> i32
    let result = add(1, 2);
    
    // 结构体类型推导
    let point = Point { x: 1, y: 2 }; // 推导为 Point
}
```

## 2.3 Rust类型系统架构

### 2.3.1 基本类型

**数值类型**：

```rust
fn numeric_types() {
    // 整数类型
    let i8_val: i8 = 127;           // 8位有符号整数
    let u8_val: u8 = 255;           // 8位无符号整数
    let i32_val: i32 = 2147483647;  // 32位有符号整数
    let u32_val: u32 = 4294967295;  // 32位无符号整数
    let i64_val: i64 = 9223372036854775807; // 64位有符号整数
    let u64_val: u64 = 18446744073709551615; // 64位无符号整数
    
    // 浮点类型
    let f32_val: f32 = 3.14;        // 32位浮点数
    let f64_val: f64 = 3.14159265359; // 64位浮点数
    
    // 平台相关整数
    let isize_val: isize = 42;      // 有符号整数，大小与平台指针相同
    let usize_val: usize = 42;      // 无符号整数，大小与平台指针相同
}
```

**布尔类型**：

```rust
fn boolean_types() {
    let true_val: bool = true;
    let false_val: bool = false;
    
    // 布尔运算
    let and_result = true && false;  // false
    let or_result = true || false;   // true
    let not_result = !true;          // false
}
```

**字符类型**：

```rust
fn character_types() {
    let char_val: char = 'A';
    let unicode_char: char = '中';
    let emoji: char = '😀';
    
    // 字符操作
    let is_alphabetic = char_val.is_alphabetic();
    let is_digit = char_val.is_digit(10);
}
```

### 2.3.2 复合类型

**元组类型**：

```rust
fn tuple_types() {
    // 元组定义
    let tuple: (i32, f64, &str) = (1, 2.0, "hello");
    
    // 元组访问
    let first = tuple.0;
    let second = tuple.1;
    let third = tuple.2;
    
    // 元组解构
    let (x, y, z) = tuple;
    
    // 空元组（单元类型）
    let unit: () = ();
}
```

**数组类型**：

```rust
fn array_types() {
    // 固定大小数组
    let array: [i32; 5] = [1, 2, 3, 4, 5];
    
    // 数组访问
    let first = array[0];
    let last = array[4];
    
    // 数组切片
    let slice: &[i32] = &array[1..4]; // [2, 3, 4]
    
    // 数组初始化
    let zeros: [i32; 10] = [0; 10];
}
```

**结构体类型**：

```rust
fn struct_types() {
    // 命名结构体
    struct Point {
        x: i32,
        y: i32,
    }
    
    let point = Point { x: 1, y: 2 };
    
    // 元组结构体
    struct Color(i32, i32, i32);
    let color = Color(255, 0, 0);
    
    // 单元结构体
    struct Unit;
    let unit = Unit;
    
    // 结构体方法
    impl Point {
        fn new(x: i32, y: i32) -> Self {
            Point { x, y }
        }
        
        fn distance(&self, other: &Point) -> f64 {
            let dx = self.x - other.x;
            let dy = self.y - other.y;
            ((dx * dx + dy * dy) as f64).sqrt()
        }
    }
}
```

**枚举类型**：

```rust
fn enum_types() {
    // 简单枚举
    enum Direction {
        North,
        South,
        East,
        West,
    }
    
    let dir = Direction::North;
    
    // 带数据的枚举
    enum Message {
        Quit,
        Move { x: i32, y: i32 },
        Write(String),
        ChangeColor(i32, i32, i32),
    }
    
    let msg = Message::Write(String::from("hello"));
    
    // 枚举方法
    impl Direction {
        fn opposite(&self) -> Direction {
            match self {
                Direction::North => Direction::South,
                Direction::South => Direction::North,
                Direction::East => Direction::West,
                Direction::West => Direction::East,
            }
        }
    }
}
```

### 2.3.3 引用类型

**不可变引用**：

```rust
fn immutable_references() {
    let x = 5;
    let ref_x: &i32 = &x;
    
    // 通过引用访问值
    println!("值: {}", *ref_x);
    println!("值: {}", ref_x); // 自动解引用
    
    // 多个不可变引用
    let ref1 = &x;
    let ref2 = &x;
    let ref3 = &x;
    
    println!("ref1: {}, ref2: {}, ref3: {}", ref1, ref2, ref3);
}
```

**可变引用**：

```rust
fn mutable_references() {
    let mut x = 5;
    let ref_x: &mut i32 = &mut x;
    
    // 通过可变引用修改值
    *ref_x += 1;
    println!("修改后: {}", x);
    
    // 可变引用的排他性
    // let ref1 = &mut x;
    // let ref2 = &mut x; // 编译错误：多个可变引用
}
```

### 2.3.4 智能指针类型

**Box类型**：

```rust
fn box_types() {
    // 堆分配
    let boxed = Box::new(5);
    println!("boxed值: {}", *boxed);
    
    // 递归数据结构
    enum List {
        Cons(i32, Box<List>),
        Nil,
    }
    
    let list = List::Cons(1, Box::new(List::Cons(2, Box::new(List::Nil))));
}
```

**Rc类型**：

```rust
use std::rc::Rc;

fn rc_types() {
    let data = Rc::new(vec![1, 2, 3]);
    
    // 多个所有者
    let ref1 = Rc::clone(&data);
    let ref2 = Rc::clone(&data);
    
    println!("ref1: {:?}, ref2: {:?}", ref1, ref2);
    println!("引用计数: {}", Rc::strong_count(&data));
}
```

**Arc类型**：

```rust
use std::sync::Arc;
use std::thread;

fn arc_types() {
    let data = Arc::new(vec![1, 2, 3]);
    
    // 线程间共享
    let data_clone = Arc::clone(&data);
    let handle = thread::spawn(move || {
        println!("线程中的数据: {:?}", data_clone);
    });
    
    handle.join().unwrap();
    println!("主线程中的数据: {:?}", data);
}
```

## 2.4 类型系统形式化

### 2.4.1 类型规则

**类型规则定义**：

类型规则描述了如何从子表达式的类型推导出复合表达式的类型。

**基本类型规则**：

```
Γ ⊢ x : τ    (x:τ ∈ Γ)
───────────────────── (Var)
Γ ⊢ x : τ

Γ, x:τ ⊢ e : τ'
──────────────── (Abs)
Γ ⊢ λx.e : τ → τ'

Γ ⊢ e : τ → τ'    Γ ⊢ e' : τ
──────────────────────────── (App)
Γ ⊢ e e' : τ'
```

**Rust特定规则**：

```rust
fn type_rules() {
    // 变量规则
    let x: i32 = 5;
    let y = x; // y的类型推导为i32
    
    // 函数应用规则
    fn add(x: i32, y: i32) -> i32 { x + y }
    let result = add(1, 2); // result的类型推导为i32
    
    // 结构体构造规则
    struct Point { x: i32, y: i32 }
    let point = Point { x: 1, y: 2 }; // point的类型推导为Point
}
```

### 2.4.2 子类型关系

**子类型定义**：

如果类型S是类型T的子类型（记作S <: T），那么S的值可以在需要T的地方使用。

**协变和逆变**：

```rust
fn subtyping() {
    // 协变：如果S <: T，那么Vec<S> <: Vec<T>
    let numbers: Vec<i32> = vec![1, 2, 3];
    let any_numbers: Vec<Box<dyn std::any::Any>> = numbers.into_iter()
        .map(|n| Box::new(n) as Box<dyn std::any::Any>)
        .collect();
    
    // 逆变：函数参数类型是逆变的
    fn process_number(f: fn(i32) -> ()) {
        f(42);
    }
    
    fn process_any(x: Box<dyn std::any::Any>) {
        println!("处理任意类型");
    }
    
    // process_any可以接受更具体的类型
    process_number(|x| process_any(Box::new(x)));
}
```

### 2.4.3 类型等价性

**类型等价定义**：

两个类型T和U是等价的（记作T ≡ U），如果它们可以相互转换而不损失信息。

**结构等价**：

```rust
fn type_equivalence() {
    // 结构等价：具有相同结构的类型
    struct Point1 { x: i32, y: i32 }
    struct Point2 { x: i32, y: i32 }
    
    // 虽然结构相同，但在Rust中是不同的类型
    let p1 = Point1 { x: 1, y: 2 };
    let p2 = Point2 { x: 1, y: 2 };
    
    // 需要显式转换
    // let p3: Point2 = p1; // 编译错误
}
```

## 2.5 高级类型特性

### 2.5.1 泛型系统

**泛型定义**：

泛型允许编写可以处理多种类型的代码，而不需要为每种类型编写重复的代码。

**泛型函数**：

```rust
fn generic_functions() {
    // 泛型函数
    fn identity<T>(x: T) -> T {
        x
    }
    
    let int_result = identity(5);
    let string_result = identity("hello");
    
    // 泛型结构体
    struct Container<T> {
        value: T,
    }
    
    let int_container = Container { value: 5 };
    let string_container = Container { value: "hello" };
    
    // 泛型方法
    impl<T> Container<T> {
        fn new(value: T) -> Self {
            Container { value }
        }
        
        fn get_value(&self) -> &T {
            &self.value
        }
    }
}
```

**类型约束**：

```rust
fn type_constraints() {
    // Trait约束
    fn print_and_return<T: std::fmt::Display>(x: T) -> T {
        println!("值: {}", x);
        x
    }
    
    let result = print_and_return(42);
    
    // 多重约束
    fn process<T>(x: T) -> T 
    where 
        T: std::fmt::Display + std::fmt::Debug + Clone,
    {
        println!("显示: {}", x);
        println!("调试: {:?}", x);
        x.clone()
    }
    
    let result = process("hello");
}
```

### 2.5.2 Trait系统

**Trait定义**：

Trait定义了类型必须实现的功能集合。

**基本Trait**：

```rust
fn trait_system() {
    // Trait定义
    trait Drawable {
        fn draw(&self);
        fn area(&self) -> f64;
    }
    
    // 为类型实现Trait
    struct Circle {
        radius: f64,
    }
    
    impl Drawable for Circle {
        fn draw(&self) {
            println!("绘制圆形，半径: {}", self.radius);
        }
        
        fn area(&self) -> f64 {
            std::f64::consts::PI * self.radius * self.radius
        }
    }
    
    struct Rectangle {
        width: f64,
        height: f64,
    }
    
    impl Drawable for Rectangle {
        fn draw(&self) {
            println!("绘制矩形，宽度: {}, 高度: {}", self.width, self.height);
        }
        
        fn area(&self) -> f64 {
            self.width * self.height
        }
    }
    
    // 使用Trait对象
    fn draw_shape(shape: &dyn Drawable) {
        shape.draw();
        println!("面积: {}", shape.area());
    }
    
    let circle = Circle { radius: 5.0 };
    let rectangle = Rectangle { width: 4.0, height: 6.0 };
    
    draw_shape(&circle);
    draw_shape(&rectangle);
}
```

**默认实现**：

```rust
fn default_implementations() {
    trait Printable {
        fn print(&self) {
            println!("默认打印实现");
        }
        
        fn format(&self) -> String;
    }
    
    struct MyStruct;
    
    impl Printable for MyStruct {
        fn format(&self) -> String {
            "MyStruct".to_string()
        }
        // print方法使用默认实现
    }
    
    let obj = MyStruct;
    obj.print(); // 使用默认实现
    println!("格式化: {}", obj.format());
}
```

### 2.5.3 关联类型

**关联类型定义**：

关联类型允许在Trait中定义与实现类型相关的类型。

**关联类型示例**：

```rust
fn associated_types() {
    // 定义带关联类型的Trait
    trait Iterator {
        type Item;
        
        fn next(&mut self) -> Option<Self::Item>;
    }
    
    // 实现Iterator
    struct Counter {
        count: u32,
        max: u32,
    }
    
    impl Iterator for Counter {
        type Item = u32;
        
        fn next(&mut self) -> Option<Self::Item> {
            if self.count < self.max {
                self.count += 1;
                Some(self.count)
            } else {
                None
            }
        }
    }
    
    // 使用关联类型
    fn process_iterator<I>(mut iter: I) 
    where 
        I: Iterator<Item = u32>,
    {
        while let Some(item) = iter.next() {
            println!("处理项目: {}", item);
        }
    }
    
    let counter = Counter { count: 0, max: 5 };
    process_iterator(counter);
}
```

## 2.6 类型系统与内存安全

**类型系统在内存安全中的作用**：

```rust
fn type_system_memory_safety() {
    // 1. 防止空指针解引用
    let x = 5;
    let ref_x = &x;
    // 类型系统确保ref_x不为空
    
    // 2. 防止类型错误
    let v = vec![1, 2, 3];
    // let element: &str = v[0]; // 编译错误：类型不匹配
    
    // 3. 防止越界访问
    let array = [1, 2, 3];
    // let element = array[10]; // 编译错误：索引越界
    
    // 4. 通过生命周期防止悬垂引用
    fn get_reference() -> &'static str {
        "static string"
    }
    
    let ref_str = get_reference();
    // 类型系统确保ref_str的生命周期有效
}
```

## 2.7 总结

Rust的类型系统通过以下机制提供安全保障：

1. **静态类型检查**：编译时发现类型错误
2. **类型推导**：减少显式类型标注
3. **泛型系统**：提供类型安全的代码复用
4. **Trait系统**：定义类型的行为接口
5. **生命周期系统**：确保引用安全

**核心优势**：

- 编译时错误检测
- 零运行时开销
- 内存安全保证
- 并发安全保证
- 代码可读性和可维护性

**适用场景**：

- 系统编程
- 高性能应用
- 并发编程
- 嵌入式开发
- 安全关键系统

类型系统是Rust语言安全保证的重要组成部分，与所有权系统共同构成了Rust的安全基础。 