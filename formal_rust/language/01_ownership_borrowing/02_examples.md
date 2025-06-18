# Rust所有权与借用系统代码示例

## 目录

1. [基础示例](#1-基础示例)
2. [所有权转移](#2-所有权转移)
3. [借用系统](#3-借用系统)
4. [生命周期](#4-生命周期)
5. [作用域](#5-作用域)
6. [高级模式](#6-高级模式)
7. [错误处理](#7-错误处理)

## 1. 基础示例

### 1.1 所有权基础

```rust
fn ownership_basics() {
    // 1. 基本所有权
    let s1 = String::from("hello");
    println!("s1: {}", s1);
    
    // 2. 所有权转移
    let s2 = s1; // s1的所有权移动到s2
    // println!("s1: {}", s1); // 编译错误：s1已被移动
    println!("s2: {}", s2);
    
    // 3. 作用域结束
    {
        let s3 = String::from("world");
        println!("s3: {}", s3);
    } // s3在这里被drop
    
    // 4. Copy语义
    let x = 5;
    let y = x; // x被复制，不是移动
    println!("x: {}, y: {}", x, y);
}
```

### 1.2 函数与所有权

```rust
fn take_ownership(s: String) {
    println!("函数内部: {}", s);
} // s在这里被drop

fn make_copy(i: i32) {
    println!("函数内部: {}", i);
} // i在这里被drop

fn ownership_and_functions() {
    let s = String::from("hello");
    take_ownership(s); // s的所有权移动到函数
    // println!("{}", s); // 编译错误：s已被移动
    
    let x = 5;
    make_copy(x); // x被复制到函数
    println!("x仍然可用: {}", x); // x仍然可用
}
```

## 2. 所有权转移

### 2.1 移动语义

```rust
fn move_semantics() {
    // 1. 变量赋值
    let v1 = vec![1, 2, 3];
    let v2 = v1; // v1移动到v2
    // println!("{:?}", v1); // 编译错误
    
    // 2. 函数参数
    let s = String::from("hello");
    process_string(s); // s移动到函数
    // println!("{}", s); // 编译错误
    
    // 3. 返回值
    let s = create_string();
    println!("创建字符串: {}", s);
}

fn process_string(s: String) {
    println!("处理: {}", s);
}

fn create_string() -> String {
    String::from("world")
}
```

### 2.2 克隆与复制

```rust
fn clone_and_copy() {
    // 1. 克隆（深拷贝）
    let s1 = String::from("hello");
    let s2 = s1.clone(); // 深拷贝
    println!("s1: {}, s2: {}", s1, s2);
    
    // 2. Copy trait
    let x = 5;
    let y = x; // 复制
    println!("x: {}, y: {}", x, y);
    
    // 3. 自定义Copy类型
    #[derive(Copy, Clone, Debug)]
    struct Point {
        x: i32,
        y: i32,
    }
    
    let p1 = Point { x: 1, y: 2 };
    let p2 = p1; // 复制
    println!("p1: {:?}, p2: {:?}", p1, p2);
}
```

## 3. 借用系统

### 3.1 不可变借用

```rust
fn immutable_borrowing() {
    let s1 = String::from("hello");
    
    // 多个不可变借用
    let len = calculate_length(&s1);
    let first_char = get_first_char(&s1);
    
    println!("字符串: '{}', 长度: {}, 首字符: {}", s1, len, first_char);
}

fn calculate_length(s: &String) -> usize {
    s.len()
}

fn get_first_char(s: &String) -> char {
    s.chars().next().unwrap_or(' ')
}
```

### 3.2 可变借用

```rust
fn mutable_borrowing() {
    let mut s = String::from("hello");
    
    // 可变借用
    change_string(&mut s);
    println!("修改后: {}", s);
    
    // 借用规则示例
    let mut data = vec![1, 2, 3];
    
    // 多个不可变借用
    let first = &data[0];
    let second = &data[1];
    println!("first: {}, second: {}", first, second);
    
    // 不可变借用结束后，可以创建可变借用
    data.push(4);
    println!("添加元素后: {:?}", data);
}

fn change_string(s: &mut String) {
    s.push_str(", world");
}
```

### 3.3 借用检查器

```rust
fn borrowing_checker() {
    let mut data = vec![1, 2, 3];
    
    // 正确的借用模式
    {
        let slice = &data[..2];
        println!("切片: {:?}", slice);
    } // slice在这里结束
    
    // 现在可以可变借用
    data.push(4);
    println!("数据: {:?}", data);
    
    // 错误的借用模式（注释掉）
    /*
    let slice = &data[..2];
    data.push(4); // 编译错误：不能同时有不可变和可变借用
    println!("切片: {:?}", slice);
    */
}
```

## 4. 生命周期

### 4.1 生命周期标注

```rust
fn lifetime_annotations() {
    let string1 = String::from("long string is long");
    let string2 = String::from("xyz");
    
    let result = longest(&string1, &string2);
    println!("最长的字符串是: {}", result);
}

// 生命周期参数
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}
```

### 4.2 结构体中的生命周期

```rust
struct ImportantExcerpt<'a> {
    part: &'a str,
}

fn struct_lifetimes() {
    let novel = String::from("Call me Ishmael. Some years ago...");
    let first_sentence = novel.split('.').next().expect("找不到句号");
    
    let i = ImportantExcerpt {
        part: first_sentence,
    };
    
    println!("摘录: {}", i.part);
}
```

### 4.3 生命周期省略

```rust
fn lifetime_elision() {
    let s = String::from("hello");
    let len = get_length(&s);
    println!("长度: {}", len);
}

// 编译器自动推断生命周期
fn get_length(s: &str) -> usize {
    s.len()
}

// 等价于：
// fn get_length<'a>(s: &'a str) -> usize {
//     s.len()
// }
```

## 5. 作用域

### 5.1 作用域基础

```rust
fn scope_basics() {
    // 外部作用域
    let outer = 1;
    
    {
        // 内部作用域
        let inner = 2;
        println!("内部: outer={}, inner={}", outer, inner);
    } // inner在这里结束
    
    // println!("外部: inner={}", inner); // 编译错误：inner已超出作用域
    println!("外部: outer={}", outer);
}
```

### 5.2 嵌套作用域

```rust
fn nested_scopes() {
    let x = 10;
    
    {
        let y = 5;
        println!("第一层: x={}, y={}", x, y);
        
        {
            let z = 15;
            println!("第二层: x={}, y={}, z={}", x, y, z);
        } // z在这里结束
    } // y在这里结束
    
    println!("最外层: x={}", x);
}
```

### 5.3 作用域与借用

```rust
fn scope_and_borrowing() {
    let mut data = vec![1, 2, 3];
    
    {
        let slice = &data[..2];
        println!("切片: {:?}", slice);
    } // slice在这里结束，借用结束
    
    // 现在可以修改data
    data.push(4);
    println!("修改后: {:?}", data);
}
```

## 6. 高级模式

### 6.1 内部可变性

```rust
use std::cell::RefCell;

fn interior_mutability() {
    let data = RefCell::new(5);
    
    // 在不可变引用中修改数据
    {
        let mut borrowed = data.borrow_mut();
        *borrowed += 10;
    }
    
    println!("修改后: {}", *data.borrow());
}
```

### 6.2 智能指针

```rust
use std::rc::Rc;

fn smart_pointers() {
    let data = Rc::new(String::from("hello"));
    
    // 多个所有者
    let data1 = Rc::clone(&data);
    let data2 = Rc::clone(&data);
    
    println!("data: {}", data);
    println!("data1: {}", data1);
    println!("data2: {}", data2);
    
    // 引用计数
    println!("引用计数: {}", Rc::strong_count(&data));
}
```

### 6.3 模式匹配

```rust
fn pattern_matching() {
    let value = Some(String::from("hello"));
    
    match value {
        Some(s) => {
            println!("有值: {}", s);
            // s在这里被移动
        }
        None => println!("无值"),
    }
    
    // println!("{}", value); // 编译错误：value已被移动
}
```

## 7. 错误处理

### 7.1 常见错误

```rust
fn common_errors() {
    // 错误1：使用已移动的值
    /*
    let s1 = String::from("hello");
    let s2 = s1;
    println!("{}", s1); // 编译错误
    */
    
    // 修复：使用克隆
    let s1 = String::from("hello");
    let s2 = s1.clone();
    println!("s1: {}, s2: {}", s1, s2);
    
    // 错误2：借用规则冲突
    /*
    let mut data = vec![1, 2, 3];
    let r1 = &data;
    let r2 = &mut data; // 编译错误
    println!("{:?} {:?}", r1, r2);
    */
    
    // 修复：分离借用
    let mut data = vec![1, 2, 3];
    {
        let r1 = &data;
        println!("不可变引用: {:?}", r1);
    }
    let r2 = &mut data;
    r2.push(4);
    println!("可变引用: {:?}", r2);
}
```

### 7.2 生命周期错误

```rust
fn lifetime_errors() {
    // 错误：悬垂引用
    /*
    let r;
    {
        let x = 5;
        r = &x; // 编译错误：x的生命周期太短
    }
    println!("{}", r);
    */
    
    // 修复：确保生命周期
    let x = 5;
    let r = &x;
    println!("{}", r);
}
```

### 7.3 调试技巧

```rust
fn debugging_tips() {
    // 1. 使用println!调试
    let mut data = vec![1, 2, 3];
    println!("初始数据: {:?}", data);
    
    let slice = &data[..2];
    println!("切片: {:?}", slice);
    
    data.push(4);
    println!("修改后: {:?}", data);
    
    // 2. 使用dbg!宏
    let x = 5;
    let y = dbg!(x * 2);
    println!("y = {}", y);
    
    // 3. 类型注解
    let s: String = String::from("hello");
    let len: usize = s.len();
    println!("长度: {}", len);
}
```

---

**示例总结**:

这些示例展示了Rust所有权与借用系统的核心概念：

1. **所有权基础**: 移动语义、作用域、Copy trait
2. **借用系统**: 不可变/可变借用、借用规则
3. **生命周期**: 标注、推断、省略规则
4. **作用域**: 嵌套、借用关系
5. **高级模式**: 内部可变性、智能指针、模式匹配
6. **错误处理**: 常见错误、修复方法、调试技巧

这些示例为理解Rust的内存安全模型提供了实践基础。
