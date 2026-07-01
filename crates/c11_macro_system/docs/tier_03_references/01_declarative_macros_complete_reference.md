# 声明宏完整参考 - macro_rules

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+

本文档提供 `macro_rules!` 声明宏的完整语法参考和详细规则。

---

## 📋 目录

- [声明宏完整参考 - macro\_rules](#声明宏完整参考---macro_rules)
  - [📋 目录](#-目录)
  - [1. 基础语法](#1-基础语法)
    - [1.1 宏定义结构](#11-宏定义结构)
    - [1.2 宏调用形式](#12-宏调用形式)
    - [1.3 宏导出](#13-宏导出)
  - [2. 片段说明符 (Fragment Specifiers)](#2-片段说明符-fragment-specifiers)
    - [2.1 完整列表](#21-完整列表)
    - [2.2 后续规则 (Follow-Set Ambiguity)](#22-后续规则-follow-set-ambiguity)
    - [2.3 使用示例](#23-使用示例)
  - [3. 重复模式 (Repetition)](#3-重复模式-repetition)
    - [3.1 重复语法](#31-重复语法)
    - [3.2 嵌套重复](#32-嵌套重复)
    - [3.3 分隔符规则](#33-分隔符规则)
  - [4. 模式匹配规则](#4-模式匹配规则)
    - [4.1 匹配优先级](#41-匹配优先级)
    - [4.2 贪婪匹配](#42-贪婪匹配)
    - [4.3 歧义处理](#43-歧义处理)
  - [5. 元变量 (Metavariables)](#5-元变量-metavariables)
    - [5.1 命名规则](#51-命名规则)
    - [5.2 作用域](#52-作用域)
    - [5.3 重复中的元变量](#53-重复中的元变量)
  - [6. 内置宏操作](#6-内置宏操作)
    - [6.1 stringify](#61-stringify)
    - [6.2 concat](#62-concat)
    - [6.3 其他工具宏](#63-其他工具宏)
  - [7. 递归宏](#7-递归宏)
    - [7.1 递归模式](#71-递归模式)
    - [7.2 递归限制](#72-递归限制)
    - [7.3 尾递归优化](#73-尾递归优化)
  - [8. 高级技巧](#8-高级技巧)
    - [8.1 TT Munching](#81-tt-munching)
    - [8.2 增量 TT Muncher](#82-增量-tt-muncher)
    - [8.3 回调模式](#83-回调模式)
  - [9. 常见陷阱](#9-常见陷阱)
    - [9.1 卫生性问题](#91-卫生性问题)
    - [9.2 类型推断失败](#92-类型推断失败)
    - [9.3 表达式歧义](#93-表达式歧义)

---

## 1. 基础语法

### 1.1 宏定义结构

```rust
macro_rules! macro_name {
    // 规则 1：模式 => 展开
    (pattern1) => {
        // 展开代码
    };

    // 规则 2
    (pattern2) => {
        // 展开代码
    };

    // 可以有任意多个规则
}
```
**完整示例**:

```rust
macro_rules! create_function {
    // 规则 1：无参数函数
    ($func_name:ident) => {
        fn $func_name() {
            println!("You called {:?}()", stringify!($func_name));
        }
    };

    // 规则 2：带参数函数
    ($func_name:ident, $arg:ident: $type:ty) => {
        fn $func_name($arg: $type) {
            println!("You called {:?}({}: {:?})",
                     stringify!($func_name),
                     stringify!($arg),
                     stringify!($type));
        }
    };
}

create_function!(foo);
create_function!(bar, x: i32);
```
---

### 1.2 宏调用形式

宏可以用三种分隔符调用：

```rust
// 圆括号 ()
my_macro!(arg1, arg2);

// 方括号 []
my_macro![arg1, arg2];

// 花括号 {}
my_macro! { arg1, arg2 }
```
**约定**:

- `()` - 函数式调用（如 `vec!()`, `println!()`）
- `[]` - 数组式调用（如 `vec![1, 2, 3]`）
- `{}` - 代码块式调用（如 `thread_local! {}`）

---

### 1.3 宏导出

```rust
// 导出到 crate 根
#[macro_export]
macro_rules! my_macro {
    () => { println!("Hello!"); };
}

// 用户使用
use my_crate::my_macro;
my_macro!();
```
**注意**: `#[macro_export]` 会将宏放在 crate 根，即使定义在模块中。

---

## 2. 片段说明符 (Fragment Specifiers)

### 2.1 完整列表

| 说明符     | 匹配内容   | 示例                                    |
| :--- | :--- | :--- || `ident`    | 标识符     | `x`, `foo`, `_value`                    |
| `expr`     | 表达式     | `1 + 2`, `foo()`                        |
| `ty`       | 类型       | `i32`, `Vec<T>`                         |
| `pat`      | 模式       | `Some(x)`, `_`                          |
| `stmt`     | 语句       | `let x = 5;`                            |
| `block`    | 代码块     | `{ ... }`                               |
| `item`     | 项         | `fn`, `struct`, `mod`                   |
| `meta`     | 属性内容   | `#[derive(Debug)]` 中的 `derive(Debug)` |
| `tt`       | Token Tree | 任意单个 token                          |
| `path`     | 路径       | `std::vec::Vec`                         |
| `literal`  | 字面量     | `42`, `"hello"`                         |
| `lifetime` | 生命周期   | `'a`, `'static`                         |
| `vis`      | 可见性     | `pub`, `pub(crate)`                     |

---

### 2.2 后续规则 (Follow-Set Ambiguity)

某些片段说明符后面只能跟特定 token：

| 说明符                                 | 后续允许的 token                                                   |
| :--- | :--- || `expr`, `stmt`                         | `=>`, `,`, `;`                                                     |
| `pat`                                  | `=>`, `,`, `=`, `\|`, `if`, `in`                                   |
| `path`, `ty`                           | `=>`, `,`, `=`, `\|`, `;`, `:`, `>`, `>>`, `[`, `{`, `as`, `where` |
| `vis`                                  | `,`, `ident` (非关键字), 任意非 `priv` 的 token                    |
| `ident`, `tt`, `item`, `block`, `meta` | 任意 token                                                         |

**示例**:

```rust
macro_rules! follow_set {
    // ✅ 合法：expr 后跟 =>
    ($e:expr => $b:block) => { $b };

    // ❌ 非法：expr 后不能直接跟 ident
    // ($e:expr $i:ident) => { };
}
```
---

### 2.3 使用示例

```rust
macro_rules! fragment_examples {
    // ident: 标识符
    (ident $i:ident) => {
        let $i = 42;
    };

    // expr: 表达式
    (expr $e:expr) => {
        println!("Result: {}", $e);
    };

    // ty: 类型
    (ty $t:ty) => {
        let _x: $t = Default::default();
    };

    // pat: 模式
    (pat $p:pat = $e:expr) => {
        let $p = $e;
    };

    // block: 代码块
    (block $b:block) => {
        $b
    };

    // tt: 任意 token
    (tt $($t:tt)*) => {
        $($t)*
    };
}

// 使用
fragment_examples!(ident my_var);
fragment_examples!(expr 1 + 2 * 3);
fragment_examples!(ty Vec<i32>);
fragment_examples!(pat Some(x) = Some(10));
fragment_examples!(block { println!("Block"); });
fragment_examples!(tt let x = vec![1, 2, 3];);
```
---

## 3. 重复模式 (Repetition)

### 3.1 重复语法

```rust
$( pattern )* separator
```
- `*` - 零次或多次
- `+` - 一次或多次
- `?` - 零次或一次

```rust
macro_rules! repeat_demo {
    // 零次或多次，逗号分隔
    ($($x:expr),*) => {
        vec![$($x),*]
    };

    // 一次或多次，分号分隔
    ($($x:expr);+) => {
        [$($x);+]
    };

    // 零次或一次（可选）
    ($x:expr $(, $y:expr)?) => {
        ($x $(, $y)?)
    };
}

// 使用
let v1 = repeat_demo!(1, 2, 3);        // vec![1, 2, 3]
let v2 = repeat_demo!(1; 2; 3);        // [1, 2, 3]
let t1 = repeat_demo!(1);              // (1,)
let t2 = repeat_demo!(1, 2);           // (1, 2)
```
---

### 3.2 嵌套重复

```rust
macro_rules! nested_repeat {
    ($(
        $outer:ident => [
            $($inner:expr),*
        ]
    ),*) => {
        $(
            let $outer = vec![$($inner),*];
        )*
    };
}

// 使用
nested_repeat!(
    a => [1, 2, 3],
    b => [4, 5],
    c => [6, 7, 8, 9]
);
// 展开为：
// let a = vec![1, 2, 3];
// let b = vec![4, 5];
// let c = vec![6, 7, 8, 9];
```
---

### 3.3 分隔符规则

```rust
macro_rules! separator_demo {
    // 无分隔符
    ($($x:expr)*) => { };

    // 逗号分隔
    ($($x:expr),*) => { };

    // 分号分隔
    ($($x:expr);*) => { };

    // 自定义分隔符
    ($($x:expr)and*) => { };
}

// 使用
separator_demo!(1 2 3);           // 无分隔符
separator_demo!(1, 2, 3);         // 逗号
separator_demo!(1; 2; 3);         // 分号
separator_demo!(1 and 2 and 3);   // 自定义
```
---

## 4. 模式匹配规则

### 4.1 匹配优先级

宏按定义顺序匹配，第一个匹配的规则被使用：

```rust
macro_rules! priority_demo {
    // 规则 1：更具体
    (special) => { println!("Special case"); };

    // 规则 2：更通用
    ($x:ident) => { println!("General case: {}", stringify!($x)); };
}

priority_demo!(special);  // 匹配规则 1
priority_demo!(foo);      // 匹配规则 2
```
---

### 4.2 贪婪匹配

重复匹配是贪婪的：

```rust
macro_rules! greedy {
    ($($x:expr),* , $last:expr) => {
        println!("Items: {:?}, Last: {:?}",
                 vec![$(stringify!($x)),*],
                 stringify!($last));
    };
}

greedy!(1, 2, 3, 4);
// 匹配: $x = [1, 2, 3], $last = 4
```
---

### 4.3 歧义处理

避免歧义的最佳实践：

```rust
macro_rules! avoid_ambiguity {
    // ❌ 歧义：难以区分
    // ($($x:expr),* $y:expr) => { };

    // ✅ 明确：使用不同分隔符
    ($($x:expr),* ; $y:expr) => {
        vec![$($x),* , $y]
    };
}

let v = avoid_ambiguity!(1, 2, 3 ; 4);
```
---

## 5. 元变量 (Metavariables)

### 5.1 命名规则

```rust
macro_rules! naming {
    // 合法名称
    ($x:expr) => { };
    ($value:expr) => { };
    ($_underscore:expr) => { };

    // 约定俗成
    ($e:expr) => { };      // e for expression
    ($i:ident) => { };     // i for identifier
    ($t:ty) => { };        // t for type
    ($p:pat) => { };       // p for pattern
}
```
---

### 5.2 作用域

元变量只在当前规则内有效：

```rust
macro_rules! scope_demo {
    ($x:expr) => {
        {
            let val = $x;  // ✅ 合法
            val * 2
        }
    };

    // 不能访问其他规则的 $x
    ($x:expr, $y:expr) => {
        $x + $y  // 这里的 $x 是新的捕获
    };
}
```
---

### 5.3 重复中的元变量

```rust
macro_rules! repeat_vars {
    ($($name:ident : $value:expr),*) => {
        $(
            let $name = $value;  // $name 和 $value 同步迭代
        )*
    };
}

repeat_vars!(x: 1, y: 2, z: 3);
// 展开为：
// let x = 1;
// let y = 2;
// let z = 3;
```
---

## 6. 内置宏操作

### 6.1 stringify

将 token 转换为字符串：

```rust
macro_rules! debug_var {
    ($var:ident) => {
        println!("{} = {:?}", stringify!($var), $var);
    };
}

let x = 42;
debug_var!(x);  // 输出: x = 42
```
---

### 6.2 concat

连接字符串字面量：

```rust
macro_rules! const_name {
    ($prefix:expr, $suffix:expr) => {
        concat!($prefix, "_", $suffix)
    };
}

const NAME: &str = const_name!("Hello", "World");
// NAME = "Hello_World"
```
---

### 6.3 其他工具宏

```rust
macro_rules! tools {
    () => {
        // line!() - 当前行号
        println!("Line: {}", line!());

        // column!() - 当前列号
        println!("Column: {}", column!());

        // file!() - 当前文件名
        println!("File: {}", file!());

        // module_path!() - 当前模块路径
        println!("Module: {}", module_path!());
    };
}
```
---

## 7. 递归宏

### 7.1 递归模式

```rust
macro_rules! count {
    // 递归终止：空
    () => { 0 };

    // 递归：消耗一个元素
    ($x:tt $($rest:tt)*) => {
        1 + count!($($rest)*)
    };
}

const LEN: usize = count!(a b c d e);  // 5
```
---

### 7.2 递归限制

默认递归深度限制为 128：

```rust
#![recursion_limit = "256"]  // 增加限制

macro_rules! deep_recursion {
    (0) => { 0 };
    ($n:tt) => { 1 + deep_recursion!($n - 1) };
}
```
---

### 7.3 尾递归优化

```rust
macro_rules! sum {
    // 累加器模式（尾递归）
    (@acc $acc:expr) => { $acc };
    (@acc $acc:expr, $x:expr $(, $rest:expr)*) => {
        sum!(@acc $acc + $x $(, $rest)*)
    };

    // 公开接口
    ($($x:expr),*) => {
        sum!(@acc 0 $(, $x)*)
    };
}

const TOTAL: i32 = sum!(1, 2, 3, 4, 5);  // 15
```
---

## 8. 高级技巧

### 8.1 TT Munching

逐个消费 token：

```rust
macro_rules! tt_muncher {
    // 终止条件
    () => { };

    // 消费一个 token
    ($tt:tt $($rest:tt)*) => {
        println!("Token: {}", stringify!($tt));
        tt_muncher!($($rest)*);
    };
}

tt_muncher!(let x = 1 + 2;);
```
---

### 8.2 增量 TT Muncher

构建结果的 TT muncher：

```rust
macro_rules! reverse {
    // 终止：输出累积结果
    (@rev [] [$($acc:tt)*]) => {
        $($acc)*
    };

    // 递归：将 head 添加到累积器前面
    (@rev [$head:tt $($tail:tt)*] [$($acc:tt)*]) => {
        reverse!(@rev [$($tail)*] [$head $($acc)*])
    };

    // 公开接口
    ($($tt:tt)*) => {
        reverse!(@rev [$($tt)*] [])
    };
}

reverse!(1 + 2 * 3);  // 展开为: 3 * 2 + 1
```
---

### 8.3 回调模式

将宏作为参数传递：

```rust
macro_rules! call_with_result {
    ($callback:ident, $value:expr) => {
        $callback!($value)
    };
}

macro_rules! double {
    ($x:expr) => { $x * 2 };
}

const RESULT: i32 = call_with_result!(double, 21);  // 42
```
---

## 9. 常见陷阱

### 9.1 卫生性问题

```rust
macro_rules! hygiene_trap {
    ($x:expr) => {
        {
            let value = $x;  // 局部 value，不会泄露
            value * 2
        }
    };
}

let value = 10;
let result = hygiene_trap!(5);  // value 不受影响
```
---

### 9.2 类型推断失败

```rust
macro_rules! infer_fail {
    () => {
        // ❌ 类型推断可能失败
        // vec![]

        // ✅ 明确类型
        Vec::<i32>::new()
    };
}
```
---

### 9.3 表达式歧义

```rust
macro_rules! expr_ambiguity {
    // ❌ 可能歧义：a + b * c
    ($a:expr + $b:expr * $c:expr) => { };

    // ✅ 使用括号明确优先级
    (($a:expr) + ($b:expr) * ($c:expr)) => { };
}
```
---

**相关文档**:

- [过程宏API参考](02_procedural_macro_api_reference.md)
- [syn-quote参考](03_syn_quote_reference.md)
- [宏卫生性参考](04_macro_hygiene_reference.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
