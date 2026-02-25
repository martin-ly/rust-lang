# 📝 Rust 字符串与格式化速查卡 {#-rust-字符串与格式化速查卡}

> **快速参考** | [完整文档](../../../crates/c02_type_system/docs/) | [代码示例](../../../crates/c02_type_system/examples/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-01-27
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [📝 Rust 字符串与格式化速查卡 {#-rust-字符串与格式化速查卡}](#-rust-字符串与格式化速查卡--rust-字符串与格式化速查卡)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [🔤 字符串类型 {#-字符串类型}](#-字符串类型--字符串类型)
    - [String vs \&str](#string-vs-str)
    - [类型特点](#类型特点)
  - [🆕 字符串创建 {#-字符串创建}](#-字符串创建--字符串创建)
    - [基本创建](#基本创建)
    - [从其他类型创建](#从其他类型创建)
  - [✂️ 字符串操作 {#️-字符串操作}](#️-字符串操作-️-字符串操作)
    - [追加内容](#追加内容)
    - [删除内容](#删除内容)
    - [替换](#替换)
    - [查找和检查](#查找和检查)
    - [分割](#分割)
    - [修剪](#修剪)
  - [🔄 字符串转换 {#-字符串转换}](#-字符串转换--字符串转换)
    - [String ↔ \&str](#string--str)
    - [大小写转换](#大小写转换)
    - [数字转换](#数字转换)
    - [字符和字节](#字符和字节)
  - [🖨️ 格式化输出 {#️-格式化输出}](#️-格式化输出-️-格式化输出)
    - [基本宏](#基本宏)
    - [format! 宏](#format-宏)
    - [write! 和 writeln](#write-和-writeln)
  - [🎨 格式化选项 {#-格式化选项}](#-格式化选项--格式化选项)
    - [对齐和填充](#对齐和填充)
    - [数字格式化](#数字格式化)
    - [浮点数格式化](#浮点数格式化)
    - [字符串格式化](#字符串格式化)
    - [指针和引用](#指针和引用)
  - [🎯 常用模式 {#-常用模式}](#-常用模式--常用模式)
    - [字符串拼接](#字符串拼接)
    - [字符串模板](#字符串模板)
    - [错误消息格式化](#错误消息格式化)
    - [表格格式化](#表格格式化)
    - [进度条格式化](#进度条格式化)
  - [💡 代码示例 {#-代码示例}](#-代码示例--代码示例)
    - [示例 1: 实现 Display trait](#示例-1-实现-display-trait)
    - [示例 2: 自定义格式化参数](#示例-2-自定义格式化参数)
    - [示例 3: 安全的字符串切片](#示例-3-安全的字符串切片)
    - [示例 4: 字符串模板引擎](#示例-4-字符串模板引擎)
    - [示例 5: CSV 解析器](#示例-5-csv-解析器)
  - [🎯 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景: 日志格式化系统](#场景-日志格式化系统)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: 在循环中拼接字符串](#反例-1-在循环中拼接字符串)
    - [反例 2: 按字节索引切片 UTF-8](#反例-2-按字节索引切片-utf-8)
    - [反例 3: 错误处理从字节到字符串的转换](#反例-3-错误处理从字节到字符串的转换)
    - [反例 4: format!  panic 导致的拒绝服务](#反例-4-format--panic-导致的拒绝服务)
    - [反例 5: 在热路径上频繁分配字符串](#反例-5-在热路径上频繁分配字符串)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)
  - [🧩 相关示例代码 {#-相关示例代码}](#-相关示例代码--相关示例代码)
  - [📚 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [形式化理论与类型系统](#形式化理论与类型系统)
    - [相关速查卡](#相关速查卡)

---

## 🔤 字符串类型 {#-字符串类型}

### String vs &str

```rust
// String - 可增长的堆分配字符串（拥有所有权）
let s1: String = String::from("hello");
let s2: String = "world".to_string();

// &str - 字符串切片（借用）
let s3: &str = "hello";
let s4: &str = &s1; // String 自动解引用为 &str
```

### 类型特点

| 类型     | 所有权 | 可变性 | 存储位置 | 大小            |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `&str`   | 借用   | 不可变 | 栈/堆    | 16 字节         |

---

## 🆕 字符串创建 {#-字符串创建}

### 基本创建

```rust
// 从字面量创建
let s1 = String::from("hello");
let s2 = "world".to_string();
let s3 = String::new();

// 从字符创建
let s4: String = "hello".chars().collect();

// 重复字符
let s5 = "a".repeat(5); // "aaaaa"

// 预分配容量
let mut s6 = String::with_capacity(10);
```

### 从其他类型创建

```rust
// 从数字
let s1 = 42.to_string();
let s2 = format!("{}", 42);

// 从字符
let s3 = 'a'.to_string();

// 从字节
let bytes = b"hello";
let s4 = String::from_utf8(bytes.to_vec()).unwrap();
```

---

## ✂️ 字符串操作 {#️-字符串操作}

### 追加内容

```rust
let mut s = String::from("hello");

// 追加字符串
s.push_str(", world");

// 追加字符
s.push('!');

// 插入
s.insert(5, ',');
s.insert_str(6, " Rust");

// 拼接（移动所有权）
let s1 = String::from("Hello, ");
let s2 = String::from("world!");
let s3 = s1 + &s2; // s1 被移动
```

### 删除内容

```rust
let mut s = String::from("hello, world");

// 移除字符
let c = s.remove(5); // 移除索引 5 的字符

// 截断
s.truncate(5); // 保留前 5 个字符

// 清空
s.clear();

// 移除范围
let mut s = String::from("hello");
s.drain(1..3); // 移除索引 1-2
```

### 替换

```rust
let s = String::from("hello world");

// replace - 替换所有匹配
let s1 = s.replace("world", "Rust");

// replacen - 替换前 n 个匹配
let s2 = s.replacen("l", "L", 2);

// 原地替换（可变）
let mut s = String::from("hello");
s.replace_range(0..1, "H");
```

### 查找和检查

```rust
let s = String::from("hello world");

// contains - 是否包含
let has = s.contains("world");

// starts_with - 是否以...开始
let starts = s.starts_with("hello");

// ends_with - 是否以...结束
let ends = s.ends_with("world");

// find - 查找位置
let pos = s.find("world"); // Option<usize>

// rfind - 从右查找
let pos = s.rfind("l");
```

### 分割

```rust
let s = "hello,world,rust";

// split - 分割为迭代器
for part in s.split(',') {
    println!("{}", part);
}

// split_whitespace - 按空白分割
for word in s.split_whitespace() {
    println!("{}", word);
}

// lines - 按行分割
for line in s.lines() {
    println!("{}", line);
}

// split_terminator - 分割（不包含分隔符）
for part in s.split_terminator(',') {
    println!("{}", part);
}
```

### 修剪

```rust
let s = "  hello world  ";

// trim - 去除两端空白
let trimmed = s.trim();

// trim_start - 去除开头空白
let start_trimmed = s.trim_start();

// trim_end - 去除结尾空白
let end_trimmed = s.trim_end();

// trim_matches - 去除匹配的字符
let trimmed = s.trim_matches(' ');
```

---

## 🔄 字符串转换 {#-字符串转换}

### String ↔ &str

```rust
// String → &str（自动解引用）
let s = String::from("hello");
let slice: &str = &s;

// &str → String
let s1 = "hello".to_string();
let s2 = String::from("hello");
let s3 = format!("{}", "hello");
```

### 大小写转换

```rust
let s = "Hello World";

// 转小写
let lower = s.to_lowercase();

// 转大写
let upper = s.to_uppercase();

// 首字母大写
let mut chars = s.chars();
let first = chars.next().unwrap().to_uppercase();
let rest: String = chars.as_str().to_lowercase();
let capitalized = format!("{}{}", first, rest);
```

### 数字转换

```rust
// 字符串 → 数字
let s = "42";
let n: i32 = s.parse().unwrap();
let n = s.parse::<i32>().unwrap();

// 数字 → 字符串
let n = 42;
let s = n.to_string();
let s = format!("{}", n);
```

### 字符和字节

```rust
let s = "hello";

// 字符迭代
for c in s.chars() {
    println!("{}", c);
}

// 字节迭代
for b in s.bytes() {
    println!("{}", b);
}

// 字符数量
let char_count = s.chars().count();

// 字节数量
let byte_count = s.len();
```

---

## 🖨️ 格式化输出 {#️-格式化输出}

### 基本宏

```rust
// println! - 输出到标准输出（带换行）
println!("Hello, world!");
println!("Value: {}", 42);

// print! - 输出到标准输出（不带换行）
print!("Hello, ");
print!("world!");

// eprintln! - 输出到标准错误（带换行）
eprintln!("Error: {}", "something went wrong");

// eprint! - 输出到标准错误（不带换行）
eprint!("Warning: ");
```

### format! 宏

```rust
// 基本格式化
let s = format!("Hello, {}!", "world");

// 多个参数
let s = format!("{} + {} = {}", 1, 2, 3);

// 命名参数（Rust 1.58+）
let name = "Alice";
let age = 30;
let s = format!("Name: {name}, Age: {age}");

// 位置参数
let s = format!("{1} and {0}", "first", "second");
```

### write! 和 writeln

```rust
use std::fmt::Write;

let mut s = String::new();

// write! - 写入到字符串
write!(s, "Hello, {}!", "world").unwrap();

// writeln! - 写入并换行
writeln!(s, "Line 1").unwrap();
writeln!(s, "Line 2").unwrap();
```

---

## 🎨 格式化选项 {#-格式化选项}

### 对齐和填充

> **扩展**: 内存对齐见 [ALIGNMENT_GUIDE](../ALIGNMENT_GUIDE.md)；此处为**格式化**对齐（文本排版）。

```rust
let value = 42;

// 默认（左对齐）
println!("{:10}", value);      // "42        "

// 左对齐
println!("{:<10}", value);     // "42        "

// 右对齐
println!("{:>10}", value);     // "        42"

// 居中对齐
println!("{:^10}", value);     // "    42    "

// 自定义填充字符
println!("{:*>10}", value);    // "********42"
println!("{:*<10}", value);    // "42********"
println!("{:*^10}", value);    // "****42****"
```

### 数字格式化

```rust
let n = 1234;

// 二进制
println!("{:b}", n);           // "10011010010"

// 八进制
println!("{:o}", n);           // "2322"

// 十六进制（小写）
println!("{:x}", n);           // "4d2"

// 十六进制（大写）
println!("{:X}", n);           // "4D2"

// 带前缀
println!("{:#b}", n);          // "0b10011010010"
println!("{:#o}", n);          // "0o2322"
println!("{:#x}", n);          // "0x4d2"

// 带符号
println!("{:+}", n);           // "+1234"

// 补零
println!("{:05}", n);          // "01234"
```

### 浮点数格式化

```rust
let f = 3.14159;

// 默认（6位小数）
println!("{}", f);             // "3.14159"

// 指定小数位数
println!("{:.2}", f);          // "3.14"
println!("{:.4}", f);          // "3.1416"

// 科学计数法
println!("{:e}", f);           // "3.14159e0"
println!("{:E}", f);           // "3.14159E0"

// 宽度和小数位数
println!("{:10.2}", f);        // "      3.14"
```

### 字符串格式化

```rust
let s = "hello";

// 宽度
println!("{:10}", s);          // "hello     "

// 截断
println!("{:.3}", s);          // "hel"

// 宽度和截断
println!("{:10.3}", s);        // "hel       "
```

### 指针和引用

```rust
let value = 42;

// 指针地址
println!("{:p}", &value);

// 调试格式
println!("{:?}", value);       // "42"
println!("{:#?}", vec![1, 2, 3]); // 美化格式
```

---

## 🎯 常用模式 {#-常用模式}

### 字符串拼接

```rust
// 方式 1: format!（推荐，不移动所有权）
let s1 = String::from("Hello");
let s2 = String::from("world");
let s3 = format!("{}, {}!", s1, s2); // s1, s2 仍可用

// 方式 2: + 操作符（移动第一个）
let s1 = String::from("Hello");
let s2 = String::from("world");
let s3 = s1 + ", " + &s2 + "!"; // s1 被移动

// 方式 3: push_str（可变）
let mut s = String::from("Hello");
s.push_str(", world!");

// 方式 4: 数组 join
let parts = vec!["Hello", "world"];
let s = parts.join(", ");
```

### 字符串模板

```rust
// 使用 format! 创建模板
let name = "Alice";
let age = 30;
let message = format!("Name: {}, Age: {}", name, age);

// 多行字符串
let text = format!(
    "Line 1: {}\nLine 2: {}\nLine 3: {}",
    "first", "second", "third"
);
```

### 错误消息格式化

```rust
use std::fmt;

#[derive(Debug)]
struct Error {
    code: i32,
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error {}: {}", self.code, self.message)
    }
}

let err = Error {
    code: 404,
    message: "Not Found".to_string(),
};
println!("{}", err); // "Error 404: Not Found"
```

### 表格格式化

```rust
let rows = vec![
    ("Alice", 30, "Engineer"),
    ("Bob", 25, "Designer"),
    ("Charlie", 35, "Manager"),
];

for (name, age, role) in rows {
    println!("{:<10} {:>5}  {}", name, age, role);
}
// Alice      30  Engineer
// Bob        25  Designer
// Charlie    35  Manager
```

### 进度条格式化

```rust
let current = 45;
let total = 100;
let percent = (current as f64 / total as f64) * 100.0;
let bar_width = 20;
let filled = (current * bar_width / total) as usize;

print!("\r[{}{}] {:.1}%",
    "=".repeat(filled),
    " ".repeat(bar_width - filled),
    percent
);
```

---

## 💡 代码示例 {#-代码示例}

### 示例 1: 实现 Display trait

```rust
use std::fmt;

struct Point {
    x: f64,
    y: f64,
}

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

impl fmt::Debug for Point {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Point")
            .field("x", &self.x)
            .field("y", &self.y)
            .finish()
    }
}

// 使用
let p = Point { x: 1.0, y: 2.0 };
println!("Display: {}", p);      // Display: (1, 2)
println!("Debug: {:?}", p);       // Debug: Point { x: 1.0, y: 2.0 }
println!("Pretty: {:#?}", p);      // Pretty: 格式化多行输出
```

### 示例 2: 自定义格式化参数

```rust
use std::fmt;

struct HexBytes<'a>(&'a [u8]);

impl<'a> fmt::Display for HexBytes<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, byte) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

impl<'a> fmt::LowerHex for HexBytes<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for byte in self.0 {
            write!(f, "{:02x}", byte)?;
        }
        Ok(())
    }
}

// 使用
let data = HexBytes(&[0x48, 0x65, 0x6c, 0x6c, 0x6f]);
println!("{}", data);        // 48 65 6c 6c 6f
println!("{:x}", data);      // 48656c6c6f
```

### 示例 3: 安全的字符串切片

```rust
fn safe_slice(s: &str, start: usize, end: usize) -> Option<&str> {
    // 获取所有字符边界位置
    let char_indices: Vec<usize> = s.char_indices().map(|(i, _)| i).collect();

    if start >= char_indices.len() || end > char_indices.len() {
        return None;
    }

    let start_byte = char_indices[start];
    let end_byte = if end < char_indices.len() {
        char_indices[end]
    } else {
        s.len()
    };

    Some(&s[start_byte..end_byte])
}

// 使用
let s = "Hello 世界";
println!("{:?}", safe_slice(s, 0, 5));  // Some("Hello")
println!("{:?}", safe_slice(s, 6, 8));  // Some("世界")
```

### 示例 4: 字符串模板引擎

```rust
use std::collections::HashMap;

struct Template {
    template: String,
}

impl Template {
    fn new(template: &str) -> Self {
        Self {
            template: template.to_string(),
        }
    }

    fn render(&self, vars: &HashMap<&str, &str>) -> String {
        let mut result = self.template.clone();
        for (key, value) in vars {
            result = result.replace(&format!("{{{{{}}}}}", key), value);
        }
        result
    }
}

// 使用
let template = Template::new("Hello, {{name}}! You have {{count}} new messages.");
let mut vars = HashMap::new();
vars.insert("name", "Alice");
vars.insert("count", "5");
println!("{}", template.render(&vars));
// Hello, Alice! You have 5 new messages.
```

### 示例 5: CSV 解析器

```rust
struct CsvRow {
    fields: Vec<String>,
}

impl CsvRow {
    fn from_line(line: &str) -> Self {
        let fields: Vec<String> = line
            .split(',')
            .map(|s| s.trim().trim_matches('"').to_string())
            .collect();
        Self { fields }
    }

    fn to_line(&self) -> String {
        self.fields
            .iter()
            .map(|f| {
                if f.contains(',') || f.contains('"') {
                    format!("\"{}\"", f.replace('"', "\"\""))
                } else {
                    f.clone()
                }
            })
            .collect::<Vec<_>>()
            .join(",")
    }
}

// 使用
let row = CsvRow::from_line(r#"John Doe, 30, "New York, NY""#);
println!("{:?}", row.fields);
// ["John Doe", "30", "New York, NY"]
```

---

## 🎯 使用场景 {#-使用场景}

### 场景: 日志格式化系统

在实际项目中，字符串格式化常用于日志记录和报告生成。以下是一个完整的日志格式化系统：

```rust
use std::fmt;
use std::time::SystemTime;

enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

impl fmt::Display for LogLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let level_str = match self {
            LogLevel::Debug => "DEBUG",
            LogLevel::Info => "INFO ",
            LogLevel::Warn => "WARN ",
            LogLevel::Error => "ERROR",
        };
        write!(f, "{}", level_str)
    }
}

struct LogEntry {
    timestamp: SystemTime,
    level: LogLevel,
    message: String,
    source: String,
}

impl LogEntry {
    fn format_colored(&self) -> String {
        let color = match self.level {
            LogLevel::Debug => "\x1b[36m",  // Cyan
            LogLevel::Info => "\x1b[32m",   // Green
            LogLevel::Warn => "\x1b[33m",   // Yellow
            LogLevel::Error => "\x1b[31m",  // Red
        };
        let reset = "\x1b[0m";

        format!(
            "{}[{}]{} [{}] {} - {}",
            color,
            self.format_timestamp(),
            reset,
            self.level,
            self.source,
            self.message
        )
    }

    fn format_timestamp(&self) -> String {
        let duration = self.timestamp
            .duration_since(SystemTime::UNIX_EPOCH)
            .unwrap();
        format!(
            "{:02}:{:02}:{:02}",
            (duration.as_secs() / 3600) % 24,
            (duration.as_secs() / 60) % 60,
            duration.as_secs() % 60
        )
    }
}

// 使用
let entry = LogEntry {
    timestamp: SystemTime::now(),
    level: LogLevel::Error,
    message: "Connection failed".to_string(),
    source: "network::client".to_string(),
};
println!("{}", entry.format_colored());
```

---

## 🚫 反例速查 {#-反例速查}

### 反例 1: 在循环中拼接字符串

**错误示例**:

```rust
let mut s = String::new();
for i in 0..1000 {
    s = s + &i.to_string();  // ❌ 每次分配新 String
}
```

**原因**: `+` 会分配新 String，频繁拼接开销大。

**修正**:

```rust
let s: String = (0..1000).map(|i| i.to_string()).collect();
// 或使用 s.push_str
```

---

### 反例 2: 按字节索引切片 UTF-8

**错误示例**:

```rust
let s = "hello";
let c = &s[1..2];  // 若 "he" 是字符边界则 OK
let c = &s[1..3];  // ❌ 可能 panic：非字符边界
```

**原因**: 字符串按字节索引，切分必须在 UTF-8 字符边界。

**修正**: 使用 `s.chars().nth(1)` 或 `char_indices()` 按字符处理。

---

### 反例 3: 错误处理从字节到字符串的转换

**错误示例**:

```rust
let bytes = vec![0x80, 0x81, 0x82];
let s = String::from_utf8(bytes).unwrap();  // ❌ panic: 无效的 UTF-8
```

**原因**: 不是所有字节序列都是有效的 UTF-8。

**修正**:

```rust
let bytes = vec![0x80, 0x81, 0x82];
match String::from_utf8(bytes) {
    Ok(s) => println!("Valid: {}", s),
    Err(e) => {
        let bytes = e.into_bytes();
        println!("Invalid UTF-8 sequence: {:?}", bytes);
    }
}

// 或使用 lossy 转换
let s = String::from_utf8_lossy(&[0x80, 0x81, 0x82]);
```

---

### 反例 4: format!  panic 导致的拒绝服务

**错误示例**:

```rust
fn log_user_input(input: &str) {
    // ❌ 如果 input 包含 { 会导致 panic
    println!(input);
}

log_user_input("Hello {world}");  // panic!
```

**原因**: `format!` 族宏会将字符串解释为格式字符串。

**修正**:

```rust
fn log_user_input(input: &str) {
    // ✅ 使用显式参数
    println!("{}", input);
    // 或
    println!("{input}");
}
```

---

### 反例 5: 在热路径上频繁分配字符串

**错误示例**:

```rust
fn process_logs(logs: &[LogEntry]) -> String {
    let mut result = String::new();
    for log in logs {
        // ❌ 每次循环都分配新字符串
        result += &format!("[{}] {}\n", log.level, log.message);
    }
    result
}
```

**原因**: 频繁的字符串分配和复制会严重影响性能。

**修正**:

```rust
fn process_logs(logs: &[LogEntry]) -> String {
    let mut result = String::with_capacity(logs.len() * 50);  // 预分配
    for log in logs {
        // ✅ 直接写入，避免中间分配
        use std::fmt::Write;
        writeln!(result, "[{}] {}", log.level, log.message).unwrap();
    }
    result
}
```

---

## 📚 相关文档 {#-相关文档}

- [类型系统模块（String/&str 相关）](../../../crates/c02_type_system/README.md)
- [算法模块（字符串算法与数据处理）](../../../crates/c08_algorithms/README.md)
- [WASM 模块（字符串互操作示例）](../../../crates/c12_wasm/README.md)

## 🧩 相关示例代码 {#-相关示例代码}

以下示例与字符串/格式化高度相关，可直接运行：

- [字符串算法演示（C08）](../../../crates/c08_algorithms/examples/string_algorithms_demo.rs)（`cargo run -p c08_algorithms --example string_algorithms_demo`）
- [WASM 字符串操作（C12）](../../../crates/c12_wasm/examples/02_string_operations.rs)（`cargo run -p c12_wasm --example 02_string_operations`）

## 📚 相关资源 {#-相关资源}

### 官方文档

- [Rust 字符串文档](https://doc.rust-lang.org/std/string/struct.String.html)
- [格式化文档](https://doc.rust-lang.org/std/fmt/)
- [Rust Reference - String Literals](https://doc.rust-lang.org/reference/tokens.html#string-literals)

### 项目内部文档

- [完整类型系统文档](../../../crates/c02_type_system/docs/)
- [字符串研究笔记](../../research_notes/)

### 形式化理论与类型系统

- [类型系统基础](../../research_notes/type_theory/type_system_foundations.md) — 字符串类型与类型理论
- [所有权模型](../../research_notes/formal_methods/ownership_model.md) — 字符串所有权转移形式化
- [生命周期形式化](../../research_notes/formal_methods/lifetime_formalization.md) — 字符串生命周期
- [构造能力理论](../../research_notes/type_theory/construction_capability.md) — 字符串操作表达能力

### 相关速查卡

- [类型系统速查卡](./type_system.md) - String 和 &str 类型
- [集合与迭代器速查卡](./collections_iterators_cheatsheet.md) - 字符串集合操作
- [错误处理速查卡](./error_handling_cheatsheet.md) - 字符串错误处理
- [模块系统速查卡](./modules_cheatsheet.md) - 模块中的字符串处理

---

**最后更新**: 2026-01-27
**维护者**: 文档团队
**状态**: ✅ **Rust 1.93.0 更新完成**

🎯 **掌握字符串与格式化，优雅处理文本！**
