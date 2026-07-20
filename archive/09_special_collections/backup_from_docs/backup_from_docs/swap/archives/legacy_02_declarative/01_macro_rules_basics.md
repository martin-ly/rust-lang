# macro_rules! 基础

> **文档定位**: 声明宏的基础语法和使用  
> **难度级别**: ⭐ 入门  
> **预计时间**: 2小时  
> **最后更新**: 2025-10-20

---

## 📊 目录

- [macro\_rules! 基础](#macro_rules-基础)
  - [📊 目录](#-目录)
  - [📋 学习目标](#-学习目标)
  - [1. 基本语法](#1-基本语法)
    - [1.1 宏定义结构](#11-宏定义结构)
    - [1.2 调用方式](#12-调用方式)
  - [2. 片段指定符](#2-片段指定符)
    - [2.1 常用指定符](#21-常用指定符)
    - [2.2 使用示例](#22-使用示例)
      - [expr - 表达式](#expr---表达式)
      - [ident - 标识符](#ident---标识符)
      - [ty - 类型](#ty---类型)
  - [3. 简单模式匹配](#3-简单模式匹配)
    - [3.1 多个模式](#31-多个模式)
    - [3.2 匹配顺序](#32-匹配顺序)
  - [4. 基本宏示例](#4-基本宏示例)
    - [4.1 简化println](#41-简化println)
    - [4.2 创建HashMap](#42-创建hashmap)
    - [4.3 条件编译](#43-条件编译)
    - [4.4 类型转换](#44-类型转换)
  - [5. 宏导出](#5-宏导出)
    - [5.1 模块内使用](#51-模块内使用)
    - [5.2 导出到crate根](#52-导出到crate根)
    - [5.3 导出路径控制](#53-导出路径控制)
  - [6. 调试技巧](#6-调试技巧)
    - [6.1 使用`stringify!`](#61-使用stringify)
    - [6.2 使用cargo expand](#62-使用cargo-expand)
    - [6.3 编译错误](#63-编译错误)
  - [7. 常见错误](#7-常见错误)
    - [错误1: 忘记分号](#错误1-忘记分号)
    - [错误2: 模式不匹配](#错误2-模式不匹配)
    - [错误3: 类型不明确](#错误3-类型不明确)
  - [8. 实践练习](#8-实践练习)
    - [练习1: 简单问候宏](#练习1-简单问候宏)
    - [练习2: 平方计算宏](#练习2-平方计算宏)
    - [练习3: 变量定义宏](#练习3-变量定义宏)
  - [9. 最佳实践](#9-最佳实践)
    - [✅ 推荐做法](#-推荐做法)
    - [❌ 避免做法](#-避免做法)
  - [10. 完整示例](#10-完整示例)
    - [示例: 配置创建宏](#示例-配置创建宏)
  - [📚 总结](#-总结)
    - [关键要点](#关键要点)
    - [下一步](#下一步)

## 📋 学习目标

完成本章后，你将能够：

- ✅ 理解`macro_rules!`的基本语法
- ✅ 编写简单的声明宏
- ✅ 使用基本的片段指定符
- ✅ 导出和使用宏
- ✅ 调试基本的宏错误

---

## 1. 基本语法

### 1.1 宏定义结构

```rust
macro_rules! 宏名 {
    (模式) => { 展开代码 };
}
```

**完整示例**:

```rust
macro_rules! say_hello {
    () => {
        println!("Hello, World!");
    };
}

// 使用
say_hello!();  // 输出: Hello, World!
```

### 1.2 调用方式

宏可以使用三种括号：

```rust
my_macro!()   // 圆括号
my_macro![]   // 方括号
my_macro!{}   // 花括号
```

**它们是等价的**，选择取决于惯例：

```rust
vec![1, 2, 3]          // 集合通常用[]
println!("text")       // 函数式宏用()
thread_local! { ... }  // 代码块宏用{}
```

---

## 2. 片段指定符

### 2.1 常用指定符

| 指定符 | 匹配内容 | 示例 |
|--------|---------|------|
| `expr` | 表达式 | `1 + 2`, `foo()` |
| `ident` | 标识符 | `foo`, `bar` |
| `ty` | 类型 | `i32`, `Vec<T>` |
| `pat` | 模式 | `Some(x)` |
| `stmt` | 语句 | `let x = 1;` |
| `block` | 代码块 | `{ ... }` |
| `item` | 项 | `fn foo() {}` |
| `tt` | Token树 | 任意token |

### 2.2 使用示例

#### expr - 表达式

```rust
macro_rules! print_result {
    ($e:expr) => {
        println!("{} = {}", stringify!($e), $e);
    };
}

print_result!(1 + 2);        // 输出: 1 + 2 = 3
print_result!(5 * 10);       // 输出: 5 * 10 = 50
```

#### ident - 标识符

```rust
macro_rules! create_function {
    ($func_name:ident) => {
        fn $func_name() {
            println!("You called {:?}", stringify!($func_name));
        }
    };
}

create_function!(hello);
hello();  // 输出: You called "hello"
```

#### ty - 类型

```rust
macro_rules! create_variable {
    ($var:ident, $ty:ty, $val:expr) => {
        let $var: $ty = $val;
    };
}

create_variable!(x, i32, 42);
println!("{}", x);  // 输出: 42
```

---

## 3. 简单模式匹配

### 3.1 多个模式

宏可以有多个匹配规则：

```rust
macro_rules! create {
    // 规则1: 无参数
    () => {
        Vec::new()
    };
    // 规则2: 一个参数
    ($element:expr) => {
        {
            let mut v = Vec::new();
            v.push($element);
            v
        }
    };
    // 规则3: 两个参数
    ($elem1:expr, $elem2:expr) => {
        {
            let mut v = Vec::new();
            v.push($elem1);
            v.push($elem2);
            v
        }
    };
}

let v1 = create!();           // []
let v2 = create!(1);          // [1]
let v3 = create!(1, 2);       // [1, 2]
```

### 3.2 匹配顺序

宏按**从上到下**的顺序尝试匹配：

```rust
macro_rules! test {
    ($x:expr) => { println!("Expression: {}", $x); };
    (special) => { println!("Special case!"); };  // ❌ 永远不会匹配
}

test!(special);  // 输出: Expression: special
```

**正确顺序**（具体到通用）:

```rust
macro_rules! test {
    (special) => { println!("Special case!"); };  // ✅ 先匹配特殊情况
    ($x:expr) => { println!("Expression: {}", $x); };
}

test!(special);  // 输出: Special case!
test!(42);       // 输出: Expression: 42
```

---

## 4. 基本宏示例

### 4.1 简化println

```rust
macro_rules! log {
    ($msg:expr) => {
        println!("[LOG] {}", $msg);
    };
}

log!("Application started");
// 输出: [LOG] Application started
```

### 4.2 创建HashMap

```rust
macro_rules! map {
    ($key:expr => $val:expr) => {
        {
            let mut m = std::collections::HashMap::new();
            m.insert($key, $val);
            m
        }
    };
}

let m = map!("key" => "value");
```

### 4.3 条件编译

```rust
macro_rules! debug_print {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
            print!("[DEBUG] ");
            println!($($arg)*);
        }
    };
}

debug_print!("x = {}", 42);  // 只在debug模式打印
```

### 4.4 类型转换

```rust
macro_rules! cast {
    ($val:expr => $ty:ty) => {
        $val as $ty
    };
}

let x: i32 = 42;
let y = cast!(x => f64);
println!("{}", y);  // 输出: 42.0
```

---

## 5. 宏导出

### 5.1 模块内使用

```rust
mod utils {
    macro_rules! private_macro {
        () => { println!("Private"); };
    }
    
    pub fn use_it() {
        private_macro!();  // ✅ 模块内可用
    }
}

fn main() {
    // private_macro!();  // ❌ 外部不可见
    utils::use_it();
}
```

### 5.2 导出到crate根

使用`#[macro_export]`：

```rust
// lib.rs
#[macro_export]
macro_rules! public_macro {
    () => { println!("Public!"); };
}
```

**使用**:

```rust
// main.rs 或其他模块
use my_crate::public_macro;

fn main() {
    public_macro!();
}
```

### 5.3 导出路径控制

```rust
#[macro_export]
macro_rules! my_macro {
    () => {
        // 使用$crate引用定义宏的crate
        $crate::internal_function()
    };
}
```

---

## 6. 调试技巧

### 6.1 使用`stringify!`

```rust
macro_rules! debug_expr {
    ($e:expr) => {
        println!("{} = {:?}", stringify!($e), $e);
    };
}

debug_expr!(2 + 2);  // 输出: 2 + 2 = 4
```

### 6.2 使用cargo expand

```bash
# 安装
cargo install cargo-expand

# 查看展开
cargo expand
```

### 6.3 编译错误

```rust
macro_rules! compile_time_error {
    ($msg:expr) => {
        compile_error!($msg);
    };
}

// compile_time_error!("This will not compile");
```

---

## 7. 常见错误

### 错误1: 忘记分号

```rust
// ❌ 错误
macro_rules! bad {
    () => { println!("Hello") }  // 缺少分号
}

// ✅ 正确
macro_rules! good {
    () => { println!("Hello") };
}
```

### 错误2: 模式不匹配

```rust
macro_rules! needs_two {
    ($a:expr, $b:expr) => { $a + $b };
}

// needs_two!(1);  // ❌ 编译错误：模式不匹配
needs_two!(1, 2);  // ✅ 正确
```

### 错误3: 类型不明确

```rust
macro_rules! ambiguous {
    ($x:expr) => { $x };
}

// let y = ambiguous!(42);  // 可能需要类型注解
let y: i32 = ambiguous!(42);  // ✅ 明确类型
```

---

## 8. 实践练习

### 练习1: 简单问候宏

**任务**: 创建一个宏，根据参数打印不同的问候语。

```rust
macro_rules! greet {
    () => {
        println!("Hello!");
    };
    ($name:expr) => {
        println!("Hello, {}!", $name);
    };
}

// 测试
greet!();
greet!("Alice");
```

### 练习2: 平方计算宏

**任务**: 创建一个计算平方的宏。

```rust
macro_rules! square {
    ($x:expr) => {
        $x * $x
    };
}

// 测试
assert_eq!(square!(5), 25);
assert_eq!(square!(3 + 2), 25);
```

### 练习3: 变量定义宏

**任务**: 创建一个简化变量定义的宏。

```rust
macro_rules! let_var {
    ($name:ident = $value:expr) => {
        let $name = $value;
    };
}

// 测试
let_var!(x = 42);
println!("{}", x);
```

---

## 9. 最佳实践

### ✅ 推荐做法

1. **明确的名称** - 使用描述性的宏名
2. **文档注释** - 为宏添加文档
3. **示例代码** - 在文档中提供使用示例
4. **错误处理** - 提供清晰的错误信息
5. **测试** - 为宏编写单元测试

```rust
/// 创建一个打印调试信息的宏
///
/// # 示例
///
/// ```
/// # #[macro_use] extern crate my_crate;
/// # fn main() {
/// debug!("value = {}", 42);
/// # }
/// ```
#[macro_export]
macro_rules! debug {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        eprintln!("[DEBUG] {}", format!($($arg)*));
    };
}
```

### ❌ 避免做法

1. **过于复杂** - 简单逻辑用函数
2. **隐藏副作用** - 避免不可预测的行为
3. **过度嵌套** - 保持宏逻辑简单
4. **缺少文档** - 宏使用不明确

---

## 10. 完整示例

### 示例: 配置创建宏

```rust
#[macro_export]
macro_rules! config {
    ($name:ident, $value:expr) => {
        pub const $name: &str = $value;
    };
    ($name:ident, $value:expr, $ty:ty) => {
        pub const $name: $ty = $value;
    };
}

// 使用
config!(APP_NAME, "MyApp");
config!(MAX_CONNECTIONS, 100, usize);
config!(VERSION, "1.0.0");

fn main() {
    println!("{}", APP_NAME);
    println!("{}", MAX_CONNECTIONS);
    println!("{}", VERSION);
}
```

---

## 📚 总结

### 关键要点

1. **基本语法**: `macro_rules! name { (pattern) => { code }; }`
2. **片段指定符**: `expr`, `ident`, `ty`, `pat`, 等
3. **多规则匹配**: 从具体到通用
4. **导出**: 使用`#[macro_export]`
5. **调试**: 使用`cargo expand`和`stringify!`

### 下一步

- 📖 学习 [模式匹配](./02_pattern_matching.md)
- 📖 实践 [重复语法](./03_repetition_syntax.md)
- 💻 运行: `cargo run --example 01_macro_rules_basics`

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
