# 宏系统概念思维导图

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.0+ (Edition 2024)

---

## 宏系统全景

```mermaid
mindmap
  root((宏系统<br/>Macro System))
    声明宏
      macro_rules!
        模式匹配
        重复规则
        片段类型
      语法元素
        匹配器 $name:ty
        转换器 =>
        重复 $(...)*
      卫生性
        标识符隔离
        避免捕获
        混合上下文
    过程宏
      派生宏
        #[derive(...)]
        结构体枚举
        自动实现
      属性宏
        #[custom_attr]
        代码转换
        元编程
      函数宏
        custom!(...)
        DSL构建
        代码生成
    编译流程
      解析
        TokenStream
        词法分析
      扩展
        宏展开
        递归处理
      编译
        类型检查
        代码生成
    应用场景
      DRY原则
        重复代码消除
        模板生成
      DSL
        领域特定语言
        语法糖
      元数据
        derive生成
        反射替代
    调试工具
      cargo expand
        查看展开
        调试宏
      trace_macros
        追踪展开
        递归观察
```

---

## 声明宏详解

### 基本结构

```rust
macro_rules! macro_name {
    // 模式 => 转换
    (matcher) => { transcriber };
}
```

### 片段类型

| 指示符 | 匹配内容 | 示例 |
| :--- | :--- | :--- |
| `item` | 项(函数、结构体等) | `fn foo() {}` |
| `block` | 代码块 | `{ ... }` |
| `stmt` | 语句 | `let x = 1;` |
| `expr` | 表达式 | `1 + 2` |
| `ty` | 类型 | `Vec<i32>` |
| `ident` | 标识符 | `foo` |
| `path` | 路径 | `std::option::Option` |
| `tt` | 标记树 | 任意token |
| `meta` | 元数据 | `derive(Debug)` |
| `lifetime` | 生命周期 | `'a` |
| `vis` | 可见性 | `pub` |

### 重复模式

```rust
macro_rules! vec {
    // 零个或多个，逗号分隔
    ($($x:expr),*) => {{
        let mut v = Vec::new();
        $(v.push($x);)*
        v
    }};

    // 带结尾逗号
    ($($x:expr,)+) => { vec![$($x),*] };
}

vec![1, 2, 3]
vec![1, 2, 3,]
```

---

## 过程宏详解

### 三种类型

```rust
// 1. 派生宏
#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    // 为结构体/枚举派生实现
}

// 2. 属性宏
#[proc_macro_attribute]
pub fn my_attr(args: TokenStream, input: TokenStream) -> TokenStream {
    // 修改被修饰的项
}

// 3. 函数宏
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 像函数一样调用
}
```

### 派生宏示例

```rust
// 定义
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(HelloMacro)]
pub fn hello_macro_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl HelloMacro for #name {
            fn hello() {
                println!("Hello, Macro! My name is {}", stringify!(#name));
            }
        }
    };

    TokenStream::from(expanded)
}

// 使用
#[derive(HelloMacro)]
struct Pancakes;

Pancakes::hello(); // Hello, Macro! My name is Pancakes
```

---

## 常用内置宏

### 编译期信息

| 宏 | 返回值 | 用途 |
| :--- | :--- | :--- |
| `file!()` | `&'static str` | 当前文件名 |
| `line!()` | `u32` | 当前行号 |
| `column!()` | `u32` | 当前列号 |
| `module_path!()` | `&'static str` | 模块路径 |

### 代码生成

| 宏 | 用途 |
| :--- | :--- |
| `stringify!($e)` | 将表达式转为字符串 |
| `concat!(...)` | 字符串拼接 |
| `include!("file")` | 包含文件内容 |
| `include_str!("file")` | 包含文件为字符串 |
| `include_bytes!("file")` | 包含文件为字节 |
| `env!("VAR")` | 编译期环境变量 |

---

## 宏调试技巧

### 查看展开结果

```bash
# 安装 cargo-expand
cargo install cargo-expand

# 查看展开
cargo expand

# 查看特定模块
cargo expand --lib module::name
```

### 追踪宏展开

```rust
#![feature(trace_macros)]

fn main() {
    trace_macros!(true);
    println!("Hello, {}!", "world");
    trace_macros!(false);
}
```

---

## 宏设计原则

### DO

- 保持简单，避免复杂递归
- 使用 `$crate` 避免名称冲突
- 提供清晰的错误消息
- 文档化宏的用法

### DON'T

- 不要用宏隐藏控制流
- 避免过度使用(可读性下降)
- 不要依赖未文档化的行为

## 宏系统层次

```
                            Rust宏系统
                                 │
            ┌────────────────────┼────────────────────┐
            │                    │                    │
       【声明宏】            【过程宏】          【编译器插件】
            │                    │                    │
    ┌───────┴───────┐    ┌───────┴───────┐    ┌───────┴───────┐
    │               │    │               │    │               │
 macro_rules!   自定义派生   属性宏         函数宏   编译器API    Lint
    │               │      │               │      │               │
 模式匹配         derive   #[]           !调用   内部接口        自定义检查
```

---

## 声明宏 (macro_rules!)

```
声明宏结构
│
├── 匹配规则
│   ├── 模式: $( )*
│   ├── 重复: + * ?
│   └── 分隔: $( ),*
│
├── 捕获类型
│   ├── $x:expr (表达式)
│   ├── $t:ty (类型)
│   ├── $i:ident (标识符)
│   └── $l:lifetime (生命周期)
│
└── 卫生性
    └── 避免命名冲突
```

| 捕获 | 用途 | 示例 |
| :--- | :--- | :--- |
| `expr` | 任意表达式 | `1 + 2` |
| `ty` | 类型 | `Vec<i32>` |
| `ident` | 标识符 | `foo` |
| `path` | 路径 | `std::vec::Vec` |

---

## 过程宏

```
过程宏类型
│
├── 派生宏 (Derive)
│   └── #[derive(Debug)]
│
├── 属性宏 (Attribute)
│   └── #[test]
│
└── 函数宏 (Function-like)
    └── sql!(SELECT * FROM table)
```

---

## Token处理

```
Token流程
│
├── 解析
│   └── TokenStream
│
├── 转换
│   └── proc_macro2
│
└── 生成
    └── quote!宏
```

---

## 常见应用

```
宏应用
│
├── 代码生成
│   ├── Builder模式
│   └── 序列化
│
├── DSL
│   ├── vec![1, 2, 3]
│   └── format!("{}", x)
│
└── 测试
    └── assert_eq!
```

---

## 与其他概念的关系

```
宏系统
├── 编译过程 → 语法扩展阶段
├── 卫生性 → 避免作用域污染
└── 元编程 → 代码生成代码
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 宏系统概念思维导图完整版
