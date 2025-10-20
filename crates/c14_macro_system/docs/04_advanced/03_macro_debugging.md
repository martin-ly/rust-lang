# 宏调试高级技巧

> **学习目标**：掌握调试声明式宏和过程宏的高级技术和工具，快速定位和解决问题。

---

## 📖 目录

- [宏调试高级技巧](#宏调试高级技巧)
  - [📖 目录](#-目录)
  - [调试基础](#调试基础)
    - [宏调试的挑战](#宏调试的挑战)
    - [调试流程](#调试流程)
  - [声明式宏调试](#声明式宏调试)
    - [1. 使用 `cargo expand`](#1-使用-cargo-expand)
      - [示例](#示例)
    - [2. 使用 `trace_macros!`](#2-使用-trace_macros)
    - [3. 使用 `log_syntax!`](#3-使用-log_syntax)
    - [4. 自定义调试宏](#4-自定义调试宏)
    - [5. 模式匹配调试](#5-模式匹配调试)
    - [6. 步进式展开](#6-步进式展开)
  - [过程宏调试](#过程宏调试)
    - [1. 使用 `eprintln!` 打印调试信息](#1-使用-eprintln-打印调试信息)
    - [2. 使用 `dbg!` 宏](#2-使用-dbg-宏)
    - [3. 使用 `cargo expand`](#3-使用-cargo-expand)
    - [4. 编写测试用例](#4-编写测试用例)
    - [5. 使用 `trybuild` 进行集成测试](#5-使用-trybuild-进行集成测试)
    - [6. 使用 IDE 调试支持](#6-使用-ide-调试支持)
  - [展开检查技术](#展开检查技术)
    - [1. 渐进式展开验证](#1-渐进式展开验证)
    - [2. 使用类型系统验证](#2-使用类型系统验证)
    - [3. 展开差异对比](#3-展开差异对比)
  - [错误诊断](#错误诊断)
    - [1. 改进错误消息](#1-改进错误消息)
    - [2. Span 追踪](#2-span-追踪)
    - [3. 多错误累积](#3-多错误累积)
  - [调试工具链](#调试工具链)
    - [1. `cargo-expand`](#1-cargo-expand)
    - [2. `rust-analyzer`](#2-rust-analyzer)
    - [3. 自定义调试工具](#3-自定义调试工具)
    - [4. 环境变量调试](#4-环境变量调试)
  - [常见问题排查](#常见问题排查)
    - [1. "no rules expected this token"](#1-no-rules-expected-this-token)
    - [2. "recursion limit reached"](#2-recursion-limit-reached)
    - [3. "expected expression, found keyword"](#3-expected-expression-found-keyword)
    - [4. 卫生性问题](#4-卫生性问题)
    - [5. 过程宏解析错误](#5-过程宏解析错误)
  - [高级调试技巧](#高级调试技巧)
    - [1. 二分查找法](#1-二分查找法)
    - [2. 单元测试宏展开](#2-单元测试宏展开)
    - [3. 使用 `quote_spanned!` 保留位置信息](#3-使用-quote_spanned-保留位置信息)
    - [4. 创建调试宏的宏](#4-创建调试宏的宏)
    - [5. 性能分析](#5-性能分析)
  - [调试清单](#调试清单)
    - [开始调试前](#开始调试前)
    - [调试声明式宏](#调试声明式宏)
    - [调试过程宏](#调试过程宏)
    - [优化错误消息](#优化错误消息)
  - [总结](#总结)
  - [相关资源](#相关资源)

---

## 调试基础

### 宏调试的挑战

宏调试比普通代码调试更具挑战性：

```text
普通代码调试              vs     宏调试
├─ 运行时执行                     ├─ 编译时执行
├─ 可以打断点                     ├─ 无法打断点
├─ 可以查看变量                   ├─ 只能查看 Token
├─ 有调试器支持                   ├─ 工具链有限
└─ 错误信息明确                   └─ 错误信息抽象
```

### 调试流程

```text
┌─────────────────────────────────┐
│  1. 识别问题                     │
│     - 编译错误                   │
│     - 展开错误                   │
│     - 逻辑错误                   │
└─────────────────────────────────┘
             ↓
┌─────────────────────────────────┐
│  2. 隔离问题                     │
│     - 最小化复现                 │
│     - 查看展开结果               │
└─────────────────────────────────┘
             ↓
┌─────────────────────────────────┐
│  3. 分析原因                     │
│     - Token流分析                │
│     - 类型检查                   │
│     - 作用域问题                 │
└─────────────────────────────────┘
             ↓
┌─────────────────────────────────┐
│  4. 修复验证                     │
│     - 应用修复                   │
│     - 测试用例                   │
│     - 回归测试                   │
└─────────────────────────────────┘
```

---

## 声明式宏调试

### 1. 使用 `cargo expand`

最基本和最重要的调试工具：

```bash
# 安装
cargo install cargo-expand

# 查看宏展开
cargo expand

# 展开特定模块
cargo expand module_name

# 展开特定函数
cargo expand module_name::function_name

# 美化输出
cargo expand --ugly  # 不格式化（更接近实际输出）
```

#### 示例

```rust
macro_rules! debug_print {
    ($expr:expr) => {
        println!("{} = {:?}", stringify!($expr), $expr);
    };
}

fn test() {
    let x = 42;
    debug_print!(x);
}
```

运行 `cargo expand`：

```rust
fn test() {
    let x = 42;
    {
        ::std::io::_print(
            format_args!(
                "{0} = {1:?}\n",
                "x",
                x
            )
        );
    };
}
```

### 2. 使用 `trace_macros!`

查看宏调用链（需要 nightly）：

```rust
#![feature(trace_macros)]

trace_macros!(true);

macro_rules! my_macro {
    ($x:expr) => {
        $x + 1
    };
}

fn main() {
    let result = my_macro!(5);
    trace_macros!(false);
}
```

输出：

```text
note: trace_macro
 --> src/main.rs:8:18
  |
8 |     let result = my_macro!(5);
  |                  ^^^^^^^^^^^^
  |
  = note: expanding `my_macro! { 5 }`
  = note: to `5 + 1`
```

### 3. 使用 `log_syntax!`

打印 Token 流（需要 nightly）：

```rust
#![feature(log_syntax)]

macro_rules! show_tokens {
    ($($tokens:tt)*) => {
        log_syntax!($($tokens)*);
    };
}

fn main() {
    show_tokens!(let x = 42;);
}
```

### 4. 自定义调试宏

```rust
macro_rules! debug_tokens {
    ($($tokens:tt)*) => {{
        println!("Tokens: {}", stringify!($($tokens)*));
        $($tokens)*
    }};
}

// 使用
debug_tokens! {
    let x = 42;
    println!("{}", x);
}
```

### 5. 模式匹配调试

添加临时分支来追踪匹配路径：

```rust
macro_rules! complex_macro {
    // 添加调试分支
    (@debug $($tokens:tt)*) => {
        compile_error!(concat!(
            "Debug: ",
            stringify!($($tokens)*)
        ));
    };
    
    // 原有规则
    (single $x:expr) => { $x };
    (double $x:expr) => { $x * 2 };
    
    // 捕获所有其他情况
    ($($other:tt)*) => {
        complex_macro!(@debug $($other)*);
    };
}

// 使用调试
complex_macro!(unknown pattern);
// 编译错误会显示: Debug: unknown pattern
```

### 6. 步进式展开

逐步展开复杂宏：

```rust
macro_rules! step1 {
    ($($tokens:tt)*) => {
        step2!($($tokens)*);
    };
}

macro_rules! step2 {
    ($($tokens:tt)*) => {
        // 在这里添加 compile_error! 查看此时的 tokens
        compile_error!(stringify!($($tokens)*));
        step3!($($tokens)*);
    };
}

macro_rules! step3 {
    ($($tokens:tt)*) => {
        // 最终展开
        $($tokens)*
    };
}
```

---

## 过程宏调试

### 1. 使用 `eprintln!` 打印调试信息

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 调试：打印输入
    eprintln!("=== Input ===");
    eprintln!("{:#?}", input);
    
    let name = &input.ident;
    
    // 调试：打印名称
    eprintln!("=== Name ===");
    eprintln!("{}", name);
    
    let expanded = quote! {
        impl MyTrait for #name {
            fn method(&self) {
                println!("Called on {}", stringify!(#name));
            }
        }
    };
    
    // 调试：打印输出
    eprintln!("=== Output ===");
    eprintln!("{}", expanded);
    
    TokenStream::from(expanded)
}
```

### 2. 使用 `dbg!` 宏

```rust
#[proc_macro_derive(Debug)]
pub fn derive_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 使用 dbg! 查看中间值
    let fields = match dbg!(&input.data) {
        syn::Data::Struct(data) => match dbg!(&data.fields) {
            syn::Fields::Named(fields) => &fields.named,
            _ => panic!("Only named fields supported"),
        },
        _ => panic!("Only structs supported"),
    };
    
    // ...
}
```

### 3. 使用 `cargo expand`

对过程宏同样有效：

```bash
# 查看过程宏展开结果
cargo expand --bin my_binary
cargo expand --lib
```

### 4. 编写测试用例

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;
    
    #[test]
    fn test_derive_simple() {
        let input = quote! {
            struct Simple {
                field: i32,
            }
        };
        
        let output = my_derive(input.into());
        
        // 打印输出以供检查
        eprintln!("{}", output);
        
        // 或者解析输出进行断言
        let parsed: syn::File = syn::parse2(output.into()).unwrap();
        assert_eq!(parsed.items.len(), 1);
    }
}
```

### 5. 使用 `trybuild` 进行集成测试

```rust
// tests/ui.rs
#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.pass("tests/ui/pass/*.rs");
    t.compile_fail("tests/ui/fail/*.rs");
}
```

```rust
// tests/ui/fail/missing_field.rs
use my_macro::MyDerive;

#[derive(MyDerive)]
struct Test {
    // 故意缺少必需字段
}

fn main() {}
```

```text
// tests/ui/fail/missing_field.stderr
error: Field 'required_field' is missing
 --> tests/ui/fail/missing_field.rs:3:10
  |
3 | #[derive(MyDerive)]
  |          ^^^^^^^^
```

### 6. 使用 IDE 调试支持

```rust
// VS Code + rust-analyzer 支持
// 在过程宏代码中设置断点
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    // ← 在这里设置断点
    
    // 使用 "Debug" 配置运行测试
    // ...
}
```

配置 `.vscode/launch.json`：

```json
{
    "version": "0.2.0",
    "configurations": [
        {
            "type": "lldb",
            "request": "launch",
            "name": "Debug proc macro",
            "cargo": {
                "args": [
                    "test",
                    "--package=my_proc_macro",
                    "--lib"
                ]
            }
        }
    ]
}
```

---

## 展开检查技术

### 1. 渐进式展开验证

```rust
macro_rules! complex {
    // 第一阶段
    (step1: $($input:tt)*) => {
        // 检查点：查看 step1 的输出
        complex!(step2: transformed_$($input)*)
    };
    
    // 第二阶段
    (step2: $($input:tt)*) => {
        // 检查点：查看 step2 的输出
        complex!(step3: further_transformed_$($input)*)
    };
    
    // 最终阶段
    (step3: $($input:tt)*) => {
        // 最终代码
        $($input)*
    };
    
    // 入口
    ($($input:tt)*) => {
        complex!(step1: $($input)*)
    };
}
```

### 2. 使用类型系统验证

```rust
// 利用类型检查捕获问题
macro_rules! type_safe {
    ($expr:expr) => {{
        // 强制类型检查
        let _: i32 = $expr;
        $expr
    }};
}

// 如果 $expr 不是 i32，会得到清晰的类型错误
```

### 3. 展开差异对比

```bash
# 保存正确版本的展开
cargo expand > correct.rs

# 修改后保存新的展开
cargo expand > modified.rs

# 使用 diff 工具对比
diff -u correct.rs modified.rs
```

---

## 错误诊断

### 1. 改进错误消息

```rust
use syn::Error;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let fields = match &input.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => &fields.named,
            syn::Fields::Unnamed(_) => {
                return Error::new(
                    input.ident.span(),
                    "MyDerive only supports named fields. \
                     Hint: use `struct Name { field: Type }` instead of `struct Name(Type)`"
                )
                .to_compile_error()
                .into();
            }
            syn::Fields::Unit => {
                return Error::new(
                    input.ident.span(),
                    "MyDerive cannot be applied to unit structs"
                )
                .to_compile_error()
                .into();
            }
        },
        syn::Data::Enum(_) => {
            return Error::new(
                input.ident.span(),
                "MyDerive only supports structs, not enums"
            )
            .to_compile_error()
            .into();
        }
        syn::Data::Union(_) => {
            return Error::new(
                input.ident.span(),
                "MyDerive does not support unions"
            )
            .to_compile_error()
            .into();
        }
    };
    
    // ...
}
```

### 2. Span 追踪

```rust
use proc_macro2::Span;

fn validate_field(field: &syn::Field) -> Result<(), syn::Error> {
    if field.ident.is_none() {
        return Err(syn::Error::new(
            field.span(),  // 精确指向问题位置
            "Field must have a name"
        ));
    }
    
    // 更精确的错误位置
    if let syn::Type::Reference(_) = field.ty {
        return Err(syn::Error::new(
            field.ty.span(),  // 指向类型本身
            "Reference types are not supported"
        ));
    }
    
    Ok(())
}
```

### 3. 多错误累积

```rust
fn validate_all_fields(fields: &syn::FieldsNamed) -> Result<(), syn::Error> {
    let mut errors = Vec::new();
    
    for field in &fields.named {
        if let Err(e) = validate_field(field) {
            errors.push(e);
        }
    }
    
    if errors.is_empty() {
        Ok(())
    } else {
        // 合并所有错误
        let mut combined = errors.into_iter();
        let mut error = combined.next().unwrap();
        
        for e in combined {
            error.combine(e);
        }
        
        Err(error)
    }
}
```

---

## 调试工具链

### 1. `cargo-expand`

```bash
# 基本用法
cargo expand

# 高级选项
cargo expand --ugly           # 不格式化
cargo expand --theme=GitHub   # 语法高亮主题
cargo expand --color=always   # 强制颜色输出

# 展开特定项
cargo expand my_mod::my_fn
cargo expand --test test_name
cargo expand --example example_name
```

### 2. `rust-analyzer`

- 提供内联宏展开提示
- 支持"展开宏"命令
- 显示宏展开结果

### 3. 自定义调试工具

```rust
// debug_macro_utils/src/lib.rs
pub fn print_token_stream(ts: proc_macro2::TokenStream) {
    eprintln!("=== TokenStream ===");
    for token in ts {
        eprintln!("{:?}", token);
    }
}

pub fn print_syntax_tree(item: &syn::DeriveInput) {
    eprintln!("=== Syntax Tree ===");
    eprintln!("{:#?}", item);
}

// 在过程宏中使用
use debug_macro_utils::*;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input_ts: proc_macro2::TokenStream = input.clone().into();
    print_token_stream(input_ts);
    
    let input = parse_macro_input!(input as DeriveInput);
    print_syntax_tree(&input);
    
    // ...
}
```

### 4. 环境变量调试

```rust
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // 通过环境变量控制调试输出
    let debug = std::env::var("DEBUG_MACRO").is_ok();
    
    if debug {
        eprintln!("Input: {}", input);
    }
    
    // ...
}
```

使用：

```bash
DEBUG_MACRO=1 cargo build
```

---

## 常见问题排查

### 1. "no rules expected this token"

```rust
// 问题代码
macro_rules! bad {
    ($x:expr) => { $x };
}

bad!(let x = 5);  // 错误！
```

**原因**：`let x = 5` 不是一个表达式，是一个语句。

**修复**：

```rust
macro_rules! good {
    ($($stmt:stmt)*) => { $($stmt)* };
}

good!(let x = 5;);  // 正确
```

### 2. "recursion limit reached"

```rust
// 问题代码
macro_rules! infinite {
    () => { infinite!(); };
}
```

**修复**：

```rust
// 增加递归限制
#![recursion_limit = "256"]

// 或者修复递归逻辑
macro_rules! fixed {
    () => { 0 };
    ($x:expr) => { $x };
}
```

### 3. "expected expression, found keyword"

```rust
// 问题代码
macro_rules! bad {
    ($x:tt) => {
        let $x = 5;  // 如果 $x 是关键字会出错
    };
}
```

**修复**：

```rust
macro_rules! good {
    ($x:ident) => {  // 使用 ident 确保是标识符
        let $x = 5;
    };
}
```

### 4. 卫生性问题

```rust
// 问题：变量捕获
macro_rules! bad_hygiene {
    ($x:expr) => {
        let temp = $x;
        temp * 2
    };
}

let temp = 10;
println!("{}", bad_hygiene!(5));  // 可能意外使用外部的 temp
```

**修复**：

```rust
macro_rules! good_hygiene {
    ($x:expr) => {{
        let temp = $x;  // 在新的块作用域中
        temp * 2
    }};
}
```

### 5. 过程宏解析错误

```rust
// 问题代码
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 假设总是有字段
    let fields = &input.data.struct_data().fields;  // 可能 panic
    
    // ...
}
```

**修复**：

```rust
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let fields = match &input.data {
        syn::Data::Struct(data) => &data.fields,
        _ => {
            return syn::Error::new(
                input.ident.span(),
                "MyDerive only works on structs"
            )
            .to_compile_error()
            .into();
        }
    };
    
    // ...
}
```

---

## 高级调试技巧

### 1. 二分查找法

当宏很复杂时，逐步注释掉一半代码来定位问题：

```rust
macro_rules! complex {
    ($($tokens:tt)*) => {
        // 第一部分
        part1!($($tokens)*);
        
        // 第二部分 - 先注释
        // part2!($($tokens)*);
        
        // 第三部分 - 先注释
        // part3!($($tokens)*);
    };
}
```

### 2. 单元测试宏展开

```rust
#[cfg(test)]
mod tests {
    macro_rules! test_macro {
        ($input:expr) => {
            concat!("Result: ", stringify!($input))
        };
    }
    
    #[test]
    fn test_expansion() {
        assert_eq!(
            test_macro!(1 + 1),
            "Result: 1 + 1"
        );
    }
}
```

### 3. 使用 `quote_spanned!` 保留位置信息

```rust
use quote::quote_spanned;
use proc_macro2::Span;

fn generate_code(field: &syn::Field) -> proc_macro2::TokenStream {
    let span = field.span();
    let name = &field.ident;
    
    // 生成的代码将保留原始位置信息
    quote_spanned! {span=>
        pub fn #name(&self) -> &str {
            &self.#name
        }
    }
}
```

### 4. 创建调试宏的宏

```rust
macro_rules! debug_macro {
    ($name:ident, $($rules:tt)*) => {
        macro_rules! $name {
            $($rules)*
        }
        
        // 同时创建一个调试版本
        paste::paste! {
            macro_rules! [<debug_ $name>] {
                ($($input:tt)*) => {
                    {
                        eprintln!("Calling {}: {}", 
                            stringify!($name),
                            stringify!($($input)*)
                        );
                        $name!($($input)*)
                    }
                };
            }
        }
    };
}

// 使用
debug_macro!(my_macro, {
    ($x:expr) => { $x * 2 };
});

// 现在可以使用 debug_my_macro! 来查看调用
```

### 5. 性能分析

```rust
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let start = std::time::Instant::now();
    
    let input = parse_macro_input!(input as DeriveInput);
    let parse_time = start.elapsed();
    
    let result = generate_code(&input);
    let generate_time = start.elapsed() - parse_time;
    
    if std::env::var("MACRO_TIMING").is_ok() {
        eprintln!(
            "Timing for {}: parse={:?}, generate={:?}",
            input.ident,
            parse_time,
            generate_time
        );
    }
    
    result
}
```

---

## 调试清单

### 开始调试前

- [ ] 能否最小化复现问题？
- [ ] 错误消息说了什么？
- [ ] 是编译时错误还是展开错误？

### 调试声明式宏

- [ ] 使用 `cargo expand` 查看展开结果
- [ ] 检查模式匹配是否正确
- [ ] 验证 fragment specifier 是否合适
- [ ] 确认卫生性没有问题
- [ ] 检查递归是否正确终止

### 调试过程宏

- [ ] 添加 `eprintln!` 调试输出
- [ ] 检查 `syn` 解析是否成功
- [ ] 验证生成的 `TokenStream`
- [ ] 使用 `cargo expand` 查看结果
- [ ] 编写单元测试
- [ ] 使用 `trybuild` 测试错误情况

### 优化错误消息

- [ ] 错误是否指向正确的位置？
- [ ] 错误消息是否清晰易懂？
- [ ] 是否提供了修复建议？
- [ ] 是否覆盖了所有边界情况？

---

## 总结

宏调试虽然具有挑战性，但通过系统化的方法和工具可以有效进行：

- **声明式宏**：主要依赖 `cargo expand` 和模式分析
- **过程宏**：使用 `eprintln!`、测试和 IDE 支持
- **展开检查**：逐步验证和差异对比
- **错误诊断**：提供清晰的错误消息和精确的 Span
- **工具链**：充分利用 `cargo-expand`、`rust-analyzer` 等工具
- **问题排查**：识别常见模式并应用标准解决方案

掌握这些技巧，你将能够高效地调试任何宏相关问题！

## 相关资源

- [02_code_generation.md](./02_code_generation.md) - 代码生成技术
- [05_macro_testing.md](./05_macro_testing.md) - 宏测试策略
- [macro_metaprogramming.md](./macro_metaprogramming.md) - 元编程基础
