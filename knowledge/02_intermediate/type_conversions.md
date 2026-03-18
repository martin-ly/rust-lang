# Rust 类型转换 (Type Conversions)

Rust 中的类型转换是系统编程的核心技能。与许多动态语言不同，Rust 要求显式处理类型转换，这虽然增加了代码量，但大大提高了安全性和可预测性。本教程将深入讲解 Rust 中各种类型转换的方法、trait 和最佳实践。

> **预估学习时长**: 45-60 分钟
> **难度**: 中级

---

## 🎯 学习目标

完成本教程后，你将能够：

- 熟练使用 `as` 关键字进行基本类型转换
- 掌握 `From`/`Into` 和 `TryFrom`/`TryInto` trait 的使用场景
- 理解安全转换与可能失败转换的区别
- 实现自定义类型的转换 trait
- 处理复杂的字符串类型转换场景
- 使用 Rust 1.94 新增的 `char` 到 `usize` 转换特性

---

## 📋 先决条件

在学习本教程之前，你应该：

- 熟悉 Rust 的基本语法和数据类型
- 理解 trait 的基本概念
- 了解所有权和借用规则
- 具备基本的错误处理知识（`Result` 类型）

---

## 🧠 核心概念

### 1. `as` 关键字：显式强制类型转换

`as` 是 Rust 中最直接的类型转换方式，用于编译器已知的、不会失败的转换。

#### 数值类型转换

```rust
fn main() {
    // 整数之间的转换
    let a: i32 = 1000;
    let b: i64 = a as i64;  // 小范围到大范围，安全

    let c: i64 = 100000;
    let d: i32 = c as i32;  // 大范围到小范围，可能截断！

    // 有符号与无符号之间的转换
    let e: i8 = -1;
    let f: u8 = e as u8;    // 变成 255（二进制补码）

    // 整数与浮点数转换
    let g: f64 = 3.7;
    let h: i32 = g as i32;  // 截断为 3，不是四舍五入！

    let i: i32 = 42;
    let j: f64 = i as f64;  // 精确转换

    println!("b = {}, d = {}, f = {}, h = {}, j = {}", b, d, f, h, j);
}
```

#### 指针类型转换

```rust
fn main() {
    let num: i32 = 42;
    let num_ptr: *const i32 = &num;

    // 将引用转换为原始指针
    let raw_ptr = &num as *const i32;

    // 原始指针之间的转换（unsafe 块中解引用）
    let byte_ptr = raw_ptr as *const u8;

    unsafe {
        println!("Value through byte pointer: {}", *byte_ptr);
    }
}
```

---

### 2. `From` 和 `Into`：安全、隐式转换 trait

当转换**保证不会失败**时，应该实现 `From` trait。`Into` 会自动被实现。

#### 基本使用

```rust
// String 实现了 From<&str>
let s1: String = String::from("hello");
let s2: String = "hello".into();  // 使用 Into

// 数字类型的 From 实现
let big: i64 = i64::from(42i32);  // i32 -> i64 总是安全

// Vec 实现了 From<[T; N]>
let vec: Vec<i32> = Vec::from([1, 2, 3]);
```

#### 为自定义类型实现 From

```rust
#[derive(Debug)]
struct Celsius(f64);

#[derive(Debug)]
struct Fahrenheit(f64);

// 华氏度转摄氏度
impl From<Fahrenheit> for Celsius {
    fn from(f: Fahrenheit) -> Self {
        Celsius((f.0 - 32.0) * 5.0 / 9.0)
    }
}

// 摄氏度转华氏度
impl From<Celsius> for Fahrenheit {
    fn from(c: Celsius) -> Self {
        Fahrenheit(c.0 * 9.0 / 5.0 + 32.0)
    }
}

fn main() {
    let f = Fahrenheit(68.0);
    let c: Celsius = f.into();  // 简洁的转换语法
    println!("68°F = {:.1}°C", c.0);  // 68°F = 20.0°C

    // 反向转换
    let c2 = Celsius(0.0);
    let f2: Fahrenheit = c2.into();
    println!("0°C = {:.1}°F", f2.0);  // 0°C = 32.0°F
}
```

#### 使用 From 进行错误转换

```rust
use std::fs::File;
use std::io::{self, Read};

#[derive(Debug)]
enum AppError {
    Io(io::Error),
    Parse(std::num::ParseIntError),
}

// 实现 From，自动支持 ? 操作符
impl From<io::Error> for AppError {
    fn from(err: io::Error) -> Self {
        AppError::Io(err)
    }
}

impl From<std::num::ParseIntError> for AppError {
    fn from(err: std::num::ParseIntError) -> Self {
        AppError::Parse(err)
    }
}

fn read_number(path: &str) -> Result<i32, AppError> {
    let mut content = String::new();
    File::open(path)?.read_to_string(&mut content)?;  // io::Error 自动转换
    let num: i32 = content.trim().parse()?;           // ParseIntError 自动转换
    Ok(num)
}
```

---

### 3. `TryFrom` 和 `TryInto`：可能失败的转换

当转换**可能失败**时，应该使用 `TryFrom`/`TryInto`，它们返回 `Result`。

```rust
use std::convert::TryFrom;
use std::convert::TryInto;

fn main() {
    // i64 转 i32 可能溢出
    let big: i64 = 3000000000;

    // 使用 TryInto
    match big.try_into() {
        Ok(small): i32 => println!("转换成功: {}", small),
        Err(e) => println!("转换失败: {}", e),
    }

    // 使用 TryFrom
    let result = i32::try_from(big);
    if let Err(e) = result {
        println!("错误: {}", e);  // 错误: out of range integral type conversion attempted
    }
}
```

#### 实现自定义 TryFrom

```rust
use std::convert::TryFrom;

#[derive(Debug)]
struct Port(u16);

#[derive(Debug)]
enum PortError {
    OutOfRange,
    Reserved,
}

impl std::fmt::Display for PortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PortError::OutOfRange => write!(f, "端口号必须在 0-65535 之间"),
            PortError::Reserved => write!(f, "不能使用保留端口（0-1023）"),
        }
    }
}

impl std::error::Error for PortError {}

impl TryFrom<u32> for Port {
    type Error = PortError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        if value > 65535 {
            Err(PortError::OutOfRange)
        } else if value < 1024 {
            Err(PortError::Reserved)
        } else {
            Ok(Port(value as u16))
        }
    }
}

fn main() {
    // 有效端口
    let port: Result<Port, _> = 8080u32.try_into();
    println!("{:?}", port);  // Ok(Port(8080))

    // 超出范围
    let port: Result<Port, _> = 70000u32.try_into();
    println!("{:?}", port);  // Err(OutOfRange)

    // 保留端口
    let port: Result<Port, _> = 80u32.try_into();
    println!("{:?}", port);  // Err(Reserved)
}
```

---

### 4. `IntoIterator`：可迭代对象转换

```rust
// Vec 实现了 IntoIterator
let vec = vec![1, 2, 3];
for item in vec {  // vec 被消费
    println!("{}", item);
}

// &Vec 也实现了 IntoIterator（产生引用）
let vec2 = vec![4, 5, 6];
for item in &vec2 {  // 不消费 vec2
    println!("{}", item);
}

// 数组也实现了 IntoIterator（Rust 2021 edition 起）
let arr = [7, 8, 9];
for item in arr {
    println!("{}", item);
}
```

#### 为自定义集合实现 IntoIterator

```rust
struct Queue<T> {
    items: Vec<T>,
}

impl<T> IntoIterator for Queue<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter()
    }
}

// 实现引用版本
impl<'a, T> IntoIterator for &'a Queue<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.iter()
    }
}
```

---

### 5. 切片和数组转换

```rust
fn main() {
    // 数组转切片（自动）
    let arr: [i32; 5] = [1, 2, 3, 4, 5];
    let slice: &[i32] = &arr;

    // Vec 转切片
    let vec = vec![1, 2, 3];
    let slice: &[i32] = &vec;

    // 切片转 Vec（拷贝数据）
    let new_vec = slice.to_vec();

    // 切片转数组（固定大小）
    let arr_from_slice: [i32; 3] = slice.try_into().unwrap();

    // 使用 copy_from_slice
    let mut arr2 = [0i32; 5];
    arr2.copy_from_slice(&[1, 2, 3, 4, 5]);
}
```

---

### 6. 字符串类型转换

Rust 提供了多种字符串类型，各有适用场景：

```rust
use std::ffi::{CString, CStr, OsString, OsStr};
use std::os::unix::ffi::OsStrExt;  // Unix 特定

fn main() {
    // String（拥有所有权，UTF-8）
    let s = String::from("Hello");

    // &str（字符串切片）
    let slice: &str = &s;

    // String 与 &str 的转换
    let s2: String = slice.to_string();
    let s3: String = slice.to_owned();
    let s4: String = String::from(slice);

    // OsString（与平台相关的字符串，用于系统接口）
    let os_string: OsString = s.into();

    // OsString 转 String（可能失败，因为 OsString 可能不是有效 UTF-8）
    let back_to_string = os_string.into_string();
    match back_to_string {
        Ok(s) => println!("转换成功: {}", s),
        Err(os) => println!("包含无效 UTF-8: {:?}", os),
    }

    // CString（C 兼容，以 null 结尾）
    let c_string = CString::new("Hello").expect("不能包含 null 字节");

    // CString 转 &CStr
    let c_str: &CStr = &c_string;

    // 尝试转回 Rust String
    if let Ok(rust_str) = c_str.to_str() {
        println!("C 字符串: {}", rust_str);
    }
}
```

#### 常见字符串转换速查表

| From | To | 方法 | 可能失败 |
|------|-----|------|---------|
| `String` | `&str` | `&s` 或 `s.as_str()` | 否 |
| `&str` | `String` | `s.to_string()` / `s.into()` | 否 |
| `String` | `OsString` | `s.into()` | 否 |
| `OsString` | `String` | `s.into_string()` | 是 |
| `&str` | `CString` | `CString::new(s)` | 是（含 null） |
| `CString` | `&CStr` | `&cs` | 否 |
| `&CStr` | `&str` | `cs.to_str()` | 是（无效 UTF-8） |

---

### 7. Rust 1.94 新特性：`char` 转 `usize`

Rust 1.94 引入了一个实用的新转换：`char` 可以直接转换为 `usize`，返回该字符的 Unicode 标量值。

```rust
fn main() {
    // Rust 1.94+ 新特性
    let c = 'A';
    let code: usize = c as usize;  // 65
    println!("'A' 的 Unicode 码点: {}", code);  // 65

    let emoji = '😀';
    let emoji_code: usize = emoji as usize;  // 128512
    println!("'😀' 的 Unicode 码点: {}", emoji_code);  // 128512

    // 与 as u32 的区别
    let as_u32: u32 = c as u32;      // 结果为 u32
    let as_usize: usize = c as usize; // 结果为 usize（通常与平台字长相同）

    // 实用场景：使用字符作为数组索引
    fn char_to_index(c: char) -> usize {
        // 假设输入是 'a'-'z' 的小写字母
        c as usize - 'a' as usize
    }

    let index = char_to_index('c');
    println!("'c' 的索引: {}", index);  // 2

    // 构建字符频率表
    let text = "hello world";
    let mut freq = [0usize; 26];

    for c in text.chars().filter(|c| c.is_ascii_lowercase()) {
        freq[c as usize - 'a' as usize] += 1;
    }

    for (i, count) in freq.iter().enumerate() {
        if *count > 0 {
            println!("{}: {}", (b'a' + i as u8) as char, count);
        }
    }
}
```

---

### 8. 为自定义类型实现转换 trait

```rust
use std::convert::{From, TryFrom, Into, TryInto};
use std::fmt;

// 一个表示百分比的类型
#[derive(Debug, Clone, Copy)]
struct Percentage(u8);

#[derive(Debug)]
enum PercentageError {
    OutOfRange,
}

impl fmt::Display for PercentageError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "百分比必须在 0-100 之间")
    }
}

impl std::error::Error for PercentageError {}

// TryFrom: 从原始值创建（可能失败）
impl TryFrom<u8> for Percentage {
    type Error = PercentageError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value <= 100 {
            Ok(Percentage(value))
        } else {
            Err(PercentageError::OutOfRange)
        }
    }
}

// TryFrom f64（四舍五入）
impl TryFrom<f64> for Percentage {
    type Error = PercentageError;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        if value >= 0.0 && value <= 100.0 {
            Ok(Percentage(value.round() as u8))
        } else {
            Err(PercentageError::OutOfRange)
        }
    }
}

// From: 总是成功的转换
impl From<Percentage> for f64 {
    fn from(p: Percentage) -> Self {
        p.0 as f64
    }
}

// From: 百分比转小数
impl From<Percentage> for f32 {
    fn from(p: Percentage) -> Self {
        p.0 as f32 / 100.0
    }
}

// 实现 Display
impl fmt::Display for Percentage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}%", self.0)
    }
}

fn main() {
    // 使用 TryFrom 创建
    let p1: Percentage = 75u8.try_into().unwrap();
    println!("创建百分比: {}", p1);  // 75%

    // 从浮点数创建
    let p2: Percentage = 66.7f64.try_into().unwrap();
    println!("从浮点数创建: {}", p2);  // 67%

    // 转换为 f64
    let f: f64 = p1.into();
    println!("作为 f64: {}", f);  // 75.0

    // 转换为小数形式的 f32
    let ratio: f32 = p1.into();
    println!("作为比例: {}", ratio);  // 0.75

    // 失败示例
    let invalid: Result<Percentage, _> = 150u8.try_into();
    println!("无效值: {:?}", invalid);  // Err(OutOfRange)
}
```

---

## 💡 最佳实践

### 1. 选择合适的转换方式

| 场景 | 推荐方式 | 原因 |
|------|---------|------|
| 数值截断/位模式转换 | `as` | 明确表达意图 |
| 安全类型转换 | `From`/`Into` | 利用类型系统保证安全 |
| 可能失败的转换 | `TryFrom`/`TryInto` | 强制错误处理 |
| 集合转换 | `IntoIterator` | 语义清晰，支持消费/借用 |

### 2. 避免滥用 `as`

```rust
// ❌ 不推荐：使用 as 进行可能溢出的转换
let x: i32 = 3000000000_i64 as i32;  // 静默截断！

// ✅ 推荐：使用 TryInto，强制处理溢出
let x: Result<i32, _> = 3000000000_i64.try_into();
// 或者明确使用 saturating/wrapping
let x = 3000000000_i64.saturating_cast::<i32>();  // i32::MAX
```

### 3. 实现转换 trait 的顺序

```rust
// 优先实现 TryFrom，From 会自动实现
impl TryFrom<ExternalType> for MyType { ... }

// 为具体类型实现，而非泛型（避免冲突）
impl From<SpecificType> for MyType { ... }

// 使用 derive_more 等 crate 减少样板代码
```

### 4. 错误处理的一致性

```rust
// 自定义错误类型时，实现标准 trait
#[derive(Debug)]
struct ConversionError {
    source: Box<dyn std::error::Error>,
    context: String,
}

impl std::fmt::Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "转换失败: {}", self.context)
    }
}

impl std::error::Error for ConversionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&*self.source)
    }
}
```

---

## ⚠️ 常见陷阱

### 1. 浮点数转换的精度问题

```rust
let f: f64 = 1.9;
let i = f as i32;  // 结果是 1，不是 2！

// 正确的四舍五入
let i = f.round() as i32;  // 2
```

### 2. 字节索引与字符索引混淆

```rust
let s = "你好";  // 6 字节，2 个字符
let first_char = s[0];  // ❌ 编译错误：不能索引 String

// 正确做法
let first = s.chars().next().unwrap();  // '你'
```

### 3. `as` 的链式转换陷阱

```rust
let x: i32 = -1;
let y = x as u32 as i32;  // 先变成 4294967295，再变成 4294967295
```

### 4. 忘记处理 OsString 的无效 UTF-8

```rust
// Unix 系统上文件名可能不是有效 UTF-8
let path = std::fs::read_dir(".").unwrap().next().unwrap().unwrap().file_name();
// path 是 OsString，直接转 String 可能失败
```

### 5. 指针转换的生命期问题

```rust
let ptr: *const i32 = &42;
// ptr 现在是一个悬挂指针！&42 的临时值已经释放
```

---

## 🎮 动手练习

### 练习 1：温度转换器

实现一个完整的温度转换程序，支持摄氏度、华氏度和开尔文之间的相互转换。

```rust
#[derive(Debug)]
enum Temperature {
    Celsius(f64),
    Fahrenheit(f64),
    Kelvin(f64),
}

// 实现 From 和 TryFrom trait 来支持各种转换
// 确保开尔文温度不会低于绝对零度
```

### 练习 2：安全整数包装器

创建一个 `SafeI32` 类型，包装 `i32` 但使用 `TryFrom` 处理所有来自更大类型的转换，防止静默溢出。

### 练习 3：配置文件解析器

实现一个配置解析器，能够将字符串值安全地转换为各种类型（端口、IP 地址、超时时间等），并返回有意义的错误信息。

### 练习 4：Unicode 工具

使用 Rust 1.94 的 `char` 转 `usize` 特性，实现一个工具函数，分析文本中每个 Unicode 码点的频率分布。

---

## 📖 延伸阅读

- [Rust 官方文档 - std::convert](https://doc.rust-lang.org/std/convert/index.html)
- [Rust 1.94 发布说明](https://blog.rust-lang.org/)
- [The Rust Programming Language - 类型转换章节](https://doc.rust-lang.org/book/ch03-02-data-types.html)
- [Rust by Example - 类型转换](https://doc.rust-lang.org/rust-by-example/types/cast.html)
- [RFC 2484 - TryFrom/TryInto](https://rust-lang.github.io/rfcs/2484-tryfrom-tryinto.html)

---

> 💡 **进阶提示**: 在实际项目中，可以考虑使用 [derive_more](https://crates.io/crates/derive_more) crate 来自动生成 `From`、`Into` 等 trait 的实现，减少样板代码。

> 📌 **版本注意**: 本文档中的 Rust 1.94 `char` 转 `usize` 特性需要 Rust 1.94 或更高版本。使用 `rustc --version` 检查你的版本。
