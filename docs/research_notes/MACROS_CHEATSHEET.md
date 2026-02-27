# 宏速查卡

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展

---

## 声明宏 (macro_rules!)

### 基本语法

```rust
macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
}

say_hello!();  // 展开: println!("Hello!");
```

### 参数模式

```rust
macro_rules! print_value {
    // 表达式参数
    ($e:expr) => {
        println!("{}", $e);
    };

    // 多个参数
    ($e1:expr, $e2:expr) => {
        println!("{}, {}", $e1, $e2);
    };
}

print_value!(42);
print_value!(1, 2);
```

### 重复模式

```rust
macro_rules! vec {
    // 零个或多个
    ($($x:expr),*) => {{
        let mut temp_vec = Vec::new();
        $(temp_vec.push($x);)*
        temp_vec
    }};

    // 带结尾逗号
    ($($x:expr,)+) => { /* ... */ };
}

vec![1, 2, 3];
vec![1, 2, 3,];  // 带结尾逗号
```

### 常见片段类型

| 指示符 | 匹配 | 示例 |
| :--- | :--- | :--- |
| `expr` | 表达式 | `1 + 2`, `foo()` |
| `stmt` | 语句 | `let x = 1;` |
| `ty` | 类型 | `i32`, `Vec<T>` |
| `ident` | 标识符 | `foo`, `Bar` |
| `path` | 路径 | `std::option::Option` |
| `tt` | 标记树 | 任何标记 |
| `item` | 项 | `fn`, `struct`等 |
| `block` | 块 | `{ ... }` |
| `meta` | 属性内容 | `derive(Debug)` |
| `lifetime` | 生命周期 | `'a`, `'static` |

---

## 过程宏

### 派生宏

```rust
// 定义
use proc_macro::TokenStream;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // 解析input，生成输出
    let ast = syn::parse(input).unwrap();
    // ... 生成代码
    output.into()
}

// 使用
#[derive(MyDerive)]
struct MyStruct;
```

### 属性宏

```rust
// 定义
#[proc_macro_attribute]
pub fn my_attr(args: TokenStream, input: TokenStream) -> TokenStream {
    // args: 属性参数
    // input: 被修饰的项
    input
}

// 使用
#[my_attr(arg1, arg2)]
fn my_func() {}
```

### 函数式宏

```rust
// 定义
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    input
}

// 使用
my_macro!(...);
```

---

## 常见宏示例

### vec

```rust
// 创建Vec
let v = vec![1, 2, 3];
let v = vec![0; 5];  // [0, 0, 0, 0, 0]
```

### println! / format

```rust
println!("Hello");
println!("{}", value);
println!("{:?}", debug_value);
println!("{:.2}", float);  // 两位小数
println!("{:>8}", text);   // 右对齐，宽度8
```

### assert

```rust
assert!(condition);
assert_eq!(a, b);
assert_ne!(a, b);
assert!(cond, "message: {}", arg);  // 自定义消息
```

### todo! / unimplemented

```rust
fn not_yet() {
    todo!("实现这个功能");  // panic with message
}

fn stub() {
    unimplemented!();  // panic
}
```

### include

```rust
include!("path/to/file.rs");  // 包含文件内容
include_str!("path/to/file.txt");  // 包含为&str
include_bytes!("path/to/file.bin");  // 包含为&[u8]
```

---

## 宏调试技巧

### 查看展开

```bash
# 查看宏展开
cargo expand

# 或 nightly
cargo rustc -- -Z unpretty=expanded
```

### trace_macros

```rust
#![feature(trace_macros)]

trace_macros!(true);
my_macro!(...);  // 打印展开过程
trace_macros!(false);
```

---

## 宏卫生性 (Hygiene)

```rust
macro_rules! using_a {
    ($e:expr) => {
        { let a = 42; $e }
    };
}

let four = using_a!(a / 10);  // 错误! a在宏外不可见
```

宏内部定义的标识符不会与外部冲突。

---

## 递归宏

```rust
macro_rules! count_exprs {
    () => (0);
    ($head:expr) => (1);
    ($head:expr, $($tail:expr),*) => (1 + count_exprs!($($tail),*));
}

count_exprs!(1, 2, 3);  // 3
```

---

## 条件编译宏

```rust
#[cfg(target_os = "linux")]
fn linux_only() {}

#[cfg(all(feature = "serde", not(feature = "minimal")))]
impl Serialize for MyType {}

#[cfg_attr(feature = "serde", derive(Serialize))]
struct MyStruct;
```

---

## 编译器内置宏

| 宏 | 用途 |
| :--- | :--- |
| `column!()` | 当前列号 |
| `line!()` | 当前行号 |
| `file!()` | 当前文件名 |
| `module_path!()` | 当前模块路径 |
| `stringify!($e)` | 转为字符串 |
| `concat!(...)` | 字符串拼接 |
| `env!("VAR")` | 环境变量 |
| `option_env!("VAR")` | 可选环境变量 |

---

## 常用宏

| 宏 | 用途 | 示例 |
| :--- | :--- | :--- |
| `println!` | 打印 | `println!("{}", x)` |
| `format!` | 格式化字符串 | `format!("{}", x)` |
| `vec!` | 创建Vec | `vec![1, 2, 3]` |
| `assert!` | 断言 | `assert!(x > 0)` |
| `panic!` | panic | `panic!("error")` |
| `todo!` | 待实现 | `todo!("implement")` |
| `unreachable!` | 不可达 | `unreachable!()` |

---

## 派生宏

```rust
#[derive(Debug, Clone, PartialEq)]
struct Point { x: i32, y: i32 }
```

常用trait: `Debug`, `Clone`, `Copy`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Default`

---

## 属性宏

```rust
#[test]           // 测试函数
#[inline]         // 内联建议
#[cfg(test)]      // 条件编译
#[derive(...)]    // 自动实现
```

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 宏速查卡完整版
