# Rust 字符串处理 (String Handling)

> 掌握 Rust 中字符串的所有细节，从 `String` 与 `&str` 的区别到高级格式化技巧。
>
> ⏱️ **预计学习时间**: 45-60 分钟
> 🎯 **难度**: 中级

---

## 🎯 学习目标

完成本章节后，你将能够：

- 清晰理解 `String` 和 `&str` 的区别及使用场景
- 掌握 Rust 中字符串的所有权规则
- 熟练进行字符串的创建、修改、切片和迭代
- 正确处理 UTF-8 编码的字符串
- 使用格式化宏进行复杂的字符串格式化
- 了解 `OsString`/`OsStr` 和 `CString`/`CStr` 的用途

---

## 📋 先决条件

- Rust 基础语法和所有权概念
- 借用和引用的基本规则
- 基本的模式匹配知识

---

## 🧠 核心概念

### String vs &str —— 堆与栈的区分

这是 Rust 字符串中最重要也是最令人困惑的概念。

```rust
fn main() {
    // &str —— 字符串切片（String Slice）
    // 特点：不可变、存储在栈上（或静态内存）、固定大小
    let s1: &str = "Hello";           // 字符串字面量，存储在程序的二进制中
    let s2: &str = &String::from("World")[..]; // 从 String 借用的切片
    
    // String —— 可增长的 UTF-8 编码字符串
    // 特点：可变、存储在堆上、拥有所有权、运行时确定大小
    let mut s3: String = String::from("Hello");
    s3.push_str(", World!");
}
```

**核心区别对比表：**

| 特性 | `&str` | `String` |
|------|--------|----------|
| **存储位置** | 栈/静态内存 | 堆内存 |
| **所有权** | 借用（Borrow） | 拥有（Own） |
| **可变性** | 不可变 | 可变（`mut`） |
| **大小** | 固定（指针+长度） | 动态增长 |
| **生命周期** | 需要显式标注 | 与变量作用域相同 |
| **创建成本** | 低（编译期确定） | 高（堆分配） |

**如何选择？**

- 使用 `&str`：当只需要读取字符串时（函数参数首选）
- 使用 `String`：当需要修改或拥有字符串时

```rust
// 最佳实践：函数参数使用 &str，更灵活
fn greet(name: &str) {  // ✓ 推荐：可以接受 &str 和 &String
    println!("Hello, {}!", name);
}

fn main() {
    let s = String::from("Alice");
    greet(&s);        // ✓ 可以传递引用
    greet("Bob");     // ✓ 也可以传递字面量
}
```

### 字符串创建和操作

```rust
fn main() {
    // 创建字符串
    let s1 = String::from("Hello");
    let s2 = "Hello".to_string();
    let mut s3 = String::new();
    let mut s4 = String::with_capacity(100); // 预分配内存
    
    // 修改字符串
    s3.push_str("Hello");
    s3.push(' ');
    s3.push('W');
    
    // 拼接（注意：+ 运算符会获取左操作数的所有权）
    let s5 = s1 + " " + &s2;  // s1 被移动，之后不可用
    
    // 更好的拼接方式：format! 宏
    let s6 = format!("{} {}", s2, "World");
    
    // 字符串长度
    let s = "你好".to_string();
    println!("字节长度: {}", s.len());         // 6（UTF-8 编码）
    println!("字符数: {}", s.chars().count()); // 2
}
```

### 字符串切片和索引

Rust 不允许直接使用整数索引访问字符串，这是为了防止破坏 UTF-8 编码。

```rust
fn main() {
    let s = "Hello, 世界!";
    
    // s[0];  // ❌ 编译错误：Rust 不支持字符串索引
    
    // ✅ 正确方式：使用切片（必须是有效的 UTF-8 边界）
    let hello = &s[0..5];    // "Hello"
    let world = &s[7..13];   // "世界"（每个汉字占 3 字节）
    
    // 安全的字节边界检查
    if let Some(sub) = s.get(0..5) {
        println!("子串: {}", sub);
    }
    
    // 迭代字符（推荐方式）
    for c in s.chars() {
        println!("字符: {}", c);
    }
}
```

### UTF-8 处理

Rust 字符串始终是有效的 UTF-8。处理非 UTF-8 数据时需要特殊处理。

```rust
use std::str;

fn main() {
    // 从字节创建字符串（必须是有效的 UTF-8）
    let bytes = b"Hello, World!";
    let s = str::from_utf8(bytes).expect("有效的 UTF-8");
    
    // 处理可能无效的 UTF-8
    let invalid = vec![0, 159, 146, 150];
    
    match str::from_utf8(&invalid) {
        Ok(s) => println!("有效: {}", s),
        Err(e) => println!("无效 UTF-8: {}", e),
    }
    
    // 替换无效字符
    let lossy = String::from_utf8_lossy(&invalid);
    println!("替换后: {}", lossy);  // �（替换字符）
}
```

### String 方法概览

```rust
fn main() {
    let s = String::from("  Hello, World!  ");
    
    // 查找和替换
    assert!(s.contains("Hello"));
    assert!(s.starts_with("  "));
    let replaced = s.replace("World", "Rust");
    
    // 大小写转换
    let lower = "Hello".to_lowercase();  // "hello"
    let upper = "Hello".to_uppercase();  // "HELLO"
    
    // 修剪空白
    let trimmed = s.trim();        // "Hello, World!"
    let left_trim = s.trim_start(); // "Hello, World!  "
    
    // 分割字符串
    let csv = "apple,banana,cherry";
    for fruit in csv.split(',') {
        println!("水果: {}", fruit);
    }
    
    // 查找位置
    if let Some(pos) = s.find("World") {
        println!("'World' 在位置 {}", pos);
    }
    
    // 弹出字符
    let mut s_pop = String::from("abc");
    assert_eq!(s_pop.pop(), Some('c'));
    
    // 插入字符/字符串
    s_pop.insert(0, 'X');        // Xab
    s_pop.insert_str(1, "YZ");   // XYZab
}
```

### 格式化宏

```rust
use std::fmt::Write;

fn main() {
    // format! 宏
    let name = "Rust";
    let version = 1.75;
    let formatted = format!("{} 版本 {}", name, version);
    
    // 格式化选项
    println!("二进制: {:b}", 10);      // 1010
    println!("十六进制: {:x}", 255);    // ff
    println!("宽度 10: [{:10}]", "hi"); // [        hi]
    println!("左对齐: [{:<10}]", "hi"); // [hi        ]
    println!("填充 0: {:04}", 42);      // 0042
    println!("精度: {:.2}", 3.14159);   // 3.14
    
    // 调试格式
    let v = vec![1, 2, 3];
    println!("{:?}", v);    // [1, 2, 3]
    println!("{:#?}", v);   // 美化打印
    
    // write! / writeln! 写入到 String
    let mut output = String::new();
    write!(output, "计数: {}", 42).unwrap();
    writeln!(output, "，名称: {}", "test").unwrap();
    
    // 自定义类型的格式化
    struct Point { x: i32, y: i32 }
    
    impl std::fmt::Display for Point {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "({}, {})", self.x, self.y)
        }
    }
    
    let p = Point { x: 1, y: 2 };
    println!("点: {}", p);  // 点: (1, 2)
}
```

### OsString/OsStr 和 CString/CStr

```rust
use std::ffi::{CString, CStr, OsString, OsStr};

fn main() {
    // OsString / OsStr：与操作系统交互，可能包含非 UTF-8 数据
    let os_string = OsString::from("文件名.txt");
    let os_str: &OsStr = &os_string;
    
    // 转换为 String（可能失败）
    if let Ok(s) = os_string.into_string() {
        println!("UTF-8 字符串: {}", s);
    }
    
    // 安全的转换（损失性）
    let lossy: String = os_str.to_string_lossy().into_owned();
    
    // CString / CStr：与 C 语言代码交互（以 null 结尾）
    let c_string = CString::new("Hello, C!").expect("不能包含 null 字节");
    let raw_ptr = c_string.as_ptr();  // 获取原始指针用于 FFI
    
    unsafe {
        let c_str = CStr::from_ptr(raw_ptr);
        if let Ok(s) = c_str.to_str() {
            println!("Rust 字符串: {}", s);
        }
    }
}
```

### 字符串迭代器

```rust
fn main() {
    let s = "Hello, 世界!";
    
    // chars() —— 按 Unicode 标量值迭代
    for c in s.chars() {
        print!("{} ", c);
    }
    
    // char_indices() —— 获取字符和字节位置
    for (idx, c) in s.char_indices() {
        println!("索引 {}: '{}' (长度 {} 字节)", idx, c, c.len_utf8());
    }
    
    // lines() —— 按行迭代
    let text = "第一行\n第二行";
    for line in text.lines() {
        println!("行: {}", line);
    }
    
    // split() —— 分割字符串
    let csv = "a,b,c";
    let items: Vec<&str> = csv.split(',').collect();
    
    // matches() —— 查找匹配的子串
    let s = "abc123def456";
    for m in s.matches(char::is_numeric) {
        print!("{} ", m);
    }
}
```

---

## 💡 最佳实践

### 1. 优先使用 `&str` 作为函数参数

```rust
// ✓ 推荐：灵活且零成本
fn process(input: &str) -> String {
    input.to_uppercase()
}

fn main() {
    let s = String::from("hello");
    let result = process(&s);    // ✓ 借用即可
    let result2 = process("hi"); // ✓ 字面量也可
}
```

### 2. 合理使用 `with_capacity` 避免重复分配

```rust
fn build_csv(items: &[&str]) -> String {
    // 预估所需容量，避免多次堆分配
    let total_len: usize = items.iter().map(|s| s.len()).sum();
    let mut result = String::with_capacity(total_len + items.len());
    
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            result.push(',');
        }
        result.push_str(item);
    }
    result
}
```

### 3. 使用 `format!` 进行复杂拼接

```rust
// 避免链式 + 操作符
let s = s1 + "/" + &s2 + "/" + &s3;  // 难以阅读

// 使用 format! 更清晰
let s = format!("{}/{}/{}", s1, s2, s3);

// 或使用 push_str（更高效）
let mut result = String::new();
result.push_str(&s1);
result.push('/');
result.push_str(&s2);
```

### 4. 谨慎处理字符串索引

```rust
// 不要假设字符位置
let s = "你好";
// let c = s[0];  // ❌ 编译错误

// 使用安全的 API
if let Some(c) = s.chars().nth(0) {
    println!("第一个字符: {}", c);
}
```

---

## ⚠️ 常见陷阱

### 陷阱 1：字符串索引

```rust
let s = "你好";
// let c = s[0];  // ❌ 编译错误：类型 `str` 不能索引

// 原因：UTF-8 编码下，字符边界不确定
// "你" = [228, 189, 160]（3 字节）
// "好" = [229, 165, 189]（3 字节）

// ✅ 正确做法
let first_char = s.chars().next().unwrap(); // '你'
```

### 陷阱 2：`+` 运算符的所有权转移

```rust
let s1 = String::from("Hello");
let s2 = String::from("World");

let s3 = s1 + " " + &s2;  // s1 被移动，之后不可用
// println!("{}", s1);  // ❌ 编译错误：s1 已被移动
println!("{}", s2);     // ✓ s2 仍可用（只被借用）
```

### 陷阱 3：字符串长度 vs 字符数

```rust
let s = "你好";
assert_eq!(s.len(), 6);            // 6 字节（UTF-8 编码）
assert_eq!(s.chars().count(), 2);  // 2 个字符

// 注意：某些 "字符" 可能是多个 Unicode 标量值的组合
let s = "é";  // 可以是 'é' 或 'e' + '́'
assert_eq!(s.len(), 2);  // 组合字符有 2 字节
```

### 陷阱 4：无效 UTF-8 的 CString

```rust
// CString 不能包含 null 字节（0x00）
let invalid = vec![b'H', b'i', 0, b'!'];
let result = CString::new(invalid);
assert!(result.is_err());  // 返回错误
```

### 陷阱 5：字符串切片越界

```rust
let s = "你好";
// let slice = &s[0..2];  // ❌ 运行时 panic：不是有效的 UTF-8 边界

// ✅ 使用安全的 get 方法
if let Some(slice) = s.get(0..3) {
    println!("{}", slice);  // "你"
}
```

---

## 🎮 动手练习

### 练习 1：反转单词顺序

```rust
fn reverse_words(s: &str) -> String {
    s.split_whitespace()
        .rev()
        .collect::<Vec<_>>()
        .join(" ")
}

fn main() {
    let text = "Rust is awesome";
    assert_eq!(reverse_words(text), "awesome is Rust");
}
```

### 练习 2：检查回文（考虑 Unicode）

```rust
fn is_palindrome(s: &str) -> bool {
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();
    
    for i in 0..len / 2 {
        if chars[i] != chars[len - 1 - i] {
            return false;
        }
    }
    true
}

fn main() {
    assert!(is_palindrome("racecar"));
    assert!(is_palindrome("上海自来水来自海上"));
    assert!(!is_palindrome("hello"));
}
```

### 练习 3：自定义格式化

```rust
use std::fmt;

struct Person {
    name: String,
    age: u32,
}

impl fmt::Display for Person {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ({} 岁)", self.name, self.age)
    }
}

fn main() {
    let p = Person {
        name: "Alice".to_string(),
        age: 30,
    };
    
    println!("Display: {}", p);
    println!("Debug: {:?}", p);
}
```

---

## 📖 延伸阅读

### 官方文档

- [Rust Book - 字符串](https://doc.rust-lang.org/book/ch08-02-strings.html)
- [std::string::String](https://doc.rust-lang.org/std/string/struct.String.html)
- [std::str](https://doc.rust-lang.org/std/str/index.html)

### 相关主题

- **生命周期**：理解字符串切片的生命周期标注
- **UTF-8 编码**：深入学习 Unicode 和字符编码
- **FFI**：使用 `CString` 与 C 语言库交互
- **正则表达式**：`regex` crate 的高级字符串匹配

### 推荐 crate

- `regex` —— 正则表达式支持
- `unicode-segmentation` —— Unicode 文本分割（字素簇）

---

> 💡 **学习提示**：字符串是 Rust 中最常用的类型之一，花点时间彻底理解 `String` 和 `&str` 的区别将大大提升你的 Rust 编程效率。记住：**读取时用 &str，拥有和修改时用 String**。
