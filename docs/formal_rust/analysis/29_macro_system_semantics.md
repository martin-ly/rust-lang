# 宏系统语义分析


## 📊 目录

- [概述](#概述)
- [1. 宏系统理论基础](#1-宏系统理论基础)
  - [1.1 宏系统概念](#11-宏系统概念)
  - [1.2 Rust宏系统哲学](#12-rust宏系统哲学)
- [2. 声明宏语义](#2-声明宏语义)
  - [2.1 基本声明宏](#21-基本声明宏)
  - [2.2 宏参数类型](#22-宏参数类型)
  - [2.3 宏匹配规则](#23-宏匹配规则)
- [3. 过程宏语义](#3-过程宏语义)
  - [3.1 派生宏](#31-派生宏)
  - [3.2 属性宏](#32-属性宏)
  - [3.3 函数式宏](#33-函数式宏)
- [4. 宏展开机制](#4-宏展开机制)
  - [4.1 宏展开过程](#41-宏展开过程)
  - [4.2 宏卫生性](#42-宏卫生性)
- [5. 编译时计算](#5-编译时计算)
  - [5.1 编译时计算语义](#51-编译时计算语义)
  - [5.2 元编程技术](#52-元编程技术)
- [6. 宏的最佳实践](#6-宏的最佳实践)
  - [6.1 宏设计原则](#61-宏设计原则)
  - [6.2 宏调试技术](#62-宏调试技术)
- [7. 高级宏技术](#7-高级宏技术)
  - [7.1 递归宏](#71-递归宏)
  - [7.2 宏组合](#72-宏组合)
- [8. 测试和验证](#8-测试和验证)
  - [8.1 宏测试](#81-宏测试)
- [9. 总结](#9-总结)


## 概述

本文档详细分析Rust宏系统的语义，包括声明宏、过程宏、宏展开机制、卫生性、编译时计算、元编程技术和宏的最佳实践。

## 1. 宏系统理论基础

### 1.1 宏系统概念

**定义 1.1.1 (宏系统)**
宏系统是Rust的元编程机制，允许在编译时生成代码。它包括声明宏（macro_rules!）和过程宏（procedural macros），提供了强大的代码生成和抽象能力。

**宏系统的核心特性**：

1. **编译时执行**：宏在编译时展开，不增加运行时开销
2. **卫生性**：宏中的标识符不会与外部代码冲突
3. **类型安全**：宏展开后的代码仍然受类型系统检查
4. **元编程能力**：可以生成复杂的代码结构

### 1.2 Rust宏系统哲学

**Rust宏系统原则**：

```rust
// 宏应该提供清晰的抽象，而不是隐藏复杂性
macro_rules! simple_add {
    ($a:expr, $b:expr) => {
        $a + $b
    };
}

// 宏应该遵循Rust的语法和语义
macro_rules! safe_division {
    ($a:expr, $b:expr) => {
        if $b == 0 {
            None
        } else {
            Some($a / $b)
        }
    };
}

// 使用宏
fn main() {
    let result = simple_add!(5, 3);
    println!("Result: {}", result);
    
    let division = safe_division!(10, 2);
    println!("Division: {:?}", division);
}
```

## 2. 声明宏语义

### 2.1 基本声明宏

**声明宏基本语法**：

```rust
// 基本宏定义
macro_rules! greet {
    () => {
        println!("Hello, world!");
    };
    ($name:expr) => {
        println!("Hello, {}!", $name);
    };
    ($name:expr, $greeting:expr) => {
        println!("{}, {}!", $greeting, $name);
    };
}

// 使用宏
fn basic_macro_usage() {
    greet!();
    greet!("Alice");
    greet!("Bob", "Good morning");
}

// 重复模式宏
macro_rules! vector {
    ($($x:expr),*) => {
        {
            let mut temp_vec = Vec::new();
            $(temp_vec.push($x);)*
            temp_vec
        }
    };
}

// 使用重复宏
fn repeat_macro_usage() {
    let v = vector!(1, 2, 3, 4, 5);
    println!("Vector: {:?}", v);
}

// 条件宏
macro_rules! conditional_print {
    ($condition:expr, $message:expr) => {
        if $condition {
            println!("{}", $message);
        }
    };
}

// 使用条件宏
fn conditional_macro_usage() {
    conditional_print!(true, "This will be printed");
    conditional_print!(false, "This will not be printed");
}
```

### 2.2 宏参数类型

**宏参数类型语义**：

```rust
// 表达式参数
macro_rules! expr_macro {
    ($e:expr) => {
        $e * 2
    };
}

// 标识符参数
macro_rules! ident_macro {
    ($name:ident) => {
        let $name = 42;
    };
}

// 类型参数
macro_rules! type_macro {
    ($t:ty) => {
        fn get_default() -> $t {
            Default::default()
        }
    };
}

// 路径参数
macro_rules! path_macro {
    ($path:path) => {
        use $path;
    };
}

// 字面量参数
macro_rules! literal_macro {
    ($lit:literal) => {
        println!("Literal: {}", $lit);
    };
}

// 块参数
macro_rules! block_macro {
    ($block:block) => {
        $block
    };
}

// 语句参数
macro_rules! stmt_macro {
    ($stmt:stmt) => {
        $stmt
    };
}

// 令牌树参数
macro_rules! tt_macro {
    ($tt:tt) => {
        $tt
    };
}

// 使用各种参数类型
fn parameter_types_usage() {
    let doubled = expr_macro!(5);
    println!("Doubled: {}", doubled);
    
    ident_macro!(my_var);
    println!("Variable: {}", my_var);
    
    type_macro!(i32);
    let default_value = get_default();
    println!("Default: {}", default_value);
    
    literal_macro!("Hello");
    
    block_macro!({
        println!("This is a block");
    });
}
```

### 2.3 宏匹配规则

**宏匹配规则语义**：

```rust
// 基本匹配规则
macro_rules! basic_match {
    // 匹配空参数
    () => {
        println!("No arguments");
    };
    
    // 匹配单个表达式
    ($x:expr) => {
        println!("Expression: {}", $x);
    };
    
    // 匹配两个表达式
    ($x:expr, $y:expr) => {
        println!("Two expressions: {}, {}", $x, $y);
    };
    
    // 匹配任意数量的表达式
    ($($x:expr),*) => {
        println!("Multiple expressions: {:?}", vec![$($x),*]);
    };
}

// 递归宏
macro_rules! factorial {
    (0) => { 1 };
    ($n:expr) => { $n * factorial!($n - 1) };
}

// 使用递归宏
fn recursive_macro_usage() {
    let result = factorial!(5);
    println!("Factorial of 5: {}", result);
}

// 条件匹配宏
macro_rules! conditional_match {
    ($x:expr if $x > 0) => {
        println!("Positive: {}", $x);
    };
    ($x:expr) => {
        println!("Non-positive: {}", $x);
    };
}

// 使用条件匹配
fn conditional_match_usage() {
    conditional_match!(5);
    conditional_match!(-3);
}
```

## 3. 过程宏语义

### 3.1 派生宏

**派生宏语义**：

```rust
// 在单独的crate中定义派生宏
// 文件名: derive_macro.rs
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(HelloWorld)]
pub fn hello_world_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    
    let expanded = quote! {
        impl HelloWorld for #name {
            fn hello_world() {
                println!("Hello, World! My name is {}", stringify!(#name));
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用派生宏
#[derive(HelloWorld)]
struct MyStruct;

// 自定义派生宏
#[proc_macro_derive(Display, attributes(display))]
pub fn display_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    
    // 查找display属性
    let display_attr = input.attrs.iter()
        .find(|attr| attr.path.is_ident("display"))
        .and_then(|attr| attr.parse_meta().ok());
    
    let display_str = match display_attr {
        Some(syn::Meta::NameValue(syn::MetaNameValue { lit: syn::Lit::Str(s), .. })) => s.value(),
        _ => name.to_string(),
    };
    
    let expanded = quote! {
        impl std::fmt::Display for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", #display_str)
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用自定义派生宏
#[derive(Display)]
#[display = "Custom Display Name"]
struct CustomStruct;
```

### 3.2 属性宏

**属性宏语义**：

```rust
// 属性宏定义
#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as syn::LitStr);
    let item = parse_macro_input!(item as syn::ItemFn);
    
    let fn_name = &item.sig.ident;
    let route_path = attr.value();
    
    let expanded = quote! {
        #item
        
        impl Route for #fn_name {
            fn path() -> &'static str {
                #route_path
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用属性宏
#[route("/hello")]
fn hello_handler() {
    println!("Hello from handler!");
}

// 复杂属性宏
#[proc_macro_attribute]
pub fn api_endpoint(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as syn::Meta);
    let item = parse_macro_input!(item as syn::ItemFn);
    
    let fn_name = &item.sig.ident;
    let fn_block = &item.block;
    
    // 解析属性参数
    let (method, path) = match attr {
        syn::Meta::List(syn::MetaList { nested, .. }) => {
            let mut method = "GET".to_string();
            let mut path = "/".to_string();
            
            for nested_item in nested {
                if let syn::NestedMeta::Meta(syn::Meta::NameValue(nv)) = nested_item {
                    if nv.path.is_ident("method") {
                        if let syn::Lit::Str(s) = &nv.lit {
                            method = s.value();
                        }
                    } else if nv.path.is_ident("path") {
                        if let syn::Lit::Str(s) = &nv.lit {
                            path = s.value();
                        }
                    }
                }
            }
            (method, path)
        }
        _ => ("GET".to_string(), "/".to_string()),
    };
    
    let expanded = quote! {
        #item
        
        impl ApiEndpoint for #fn_name {
            fn method() -> &'static str {
                #method
            }
            
            fn path() -> &'static str {
                #path
            }
            
            fn handler() -> impl Fn() {
                || {
                    #fn_block
                }
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用复杂属性宏
#[api_endpoint(method = "POST", path = "/api/users")]
fn create_user() {
    println!("Creating user...");
}
```

### 3.3 函数式宏

**函数式宏语义**：

```rust
// 函数式宏定义
#[proc_macro]
pub fn make_struct(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::Ident);
    let struct_name = input;
    
    let expanded = quote! {
        struct #struct_name {
            id: i32,
            name: String,
            created_at: std::time::SystemTime,
        }
        
        impl #struct_name {
            fn new(name: String) -> Self {
                Self {
                    id: 0,
                    name,
                    created_at: std::time::SystemTime::now(),
                }
            }
            
            fn get_name(&self) -> &str {
                &self.name
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用函数式宏
make_struct!(MyGeneratedStruct);

// 复杂函数式宏
#[proc_macro]
pub fn builder_pattern(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::Ident);
    let struct_name = input;
    let builder_name = syn::Ident::new(&format!("{}Builder", struct_name), struct_name.span());
    
    let expanded = quote! {
        struct #struct_name {
            name: String,
            age: i32,
            email: Option<String>,
        }
        
        struct #builder_name {
            name: Option<String>,
            age: Option<i32>,
            email: Option<String>,
        }
        
        impl #builder_name {
            fn new() -> Self {
                Self {
                    name: None,
                    age: None,
                    email: None,
                }
            }
            
            fn name(mut self, name: String) -> Self {
                self.name = Some(name);
                self
            }
            
            fn age(mut self, age: i32) -> Self {
                self.age = Some(age);
                self
            }
            
            fn email(mut self, email: String) -> Self {
                self.email = Some(email);
                self
            }
            
            fn build(self) -> Result<#struct_name, String> {
                let name = self.name.ok_or("Name is required")?;
                let age = self.age.ok_or("Age is required")?;
                
                Ok(#struct_name {
                    name,
                    age,
                    email: self.email,
                })
            }
        }
        
        impl #struct_name {
            fn builder() -> #builder_name {
                #builder_name::new()
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用复杂函数式宏
builder_pattern!(Person);

// 使用生成的构建器
fn use_builder() {
    let person = Person::builder()
        .name("Alice".to_string())
        .age(30)
        .email("alice@example.com".to_string())
        .build()
        .unwrap();
    
    println!("Person: {:?}", person);
}
```

## 4. 宏展开机制

### 4.1 宏展开过程

**宏展开语义**：

```rust
// 宏展开示例
macro_rules! debug_print {
    ($($arg:tt)*) => {
        if cfg!(debug_assertions) {
            println!($($arg)*);
        }
    };
}

// 宏展开过程
fn macro_expansion_process() {
    // 原始代码
    debug_print!("Debug message: {}", 42);
    
    // 展开后的代码（概念上）
    /*
    if cfg!(debug_assertions) {
        println!("Debug message: {}", 42);
    }
    */
}

// 递归展开
macro_rules! count_exprs {
    () => { 0 };
    ($head:expr) => { 1 };
    ($head:expr, $($tail:expr),*) => {
        1 + count_exprs!($($tail),*)
    };
}

// 使用递归展开
fn recursive_expansion() {
    let count = count_exprs!(1, 2, 3, 4, 5);
    println!("Expression count: {}", count);
}

// 条件展开
macro_rules! conditional_expand {
    ($condition:expr, $then:expr, $else:expr) => {
        if $condition {
            $then
        } else {
            $else
        }
    };
}

// 使用条件展开
fn conditional_expansion() {
    let result = conditional_expand!(true, "Yes", "No");
    println!("Result: {}", result);
}
```

### 4.2 宏卫生性

**宏卫生性语义**：

```rust
// 卫生宏示例
macro_rules! hygienic_macro {
    ($x:expr) => {
        {
            let temp = $x;
            temp * 2
        }
    };
}

// 使用卫生宏
fn hygienic_macro_usage() {
    let temp = 5; // 这个temp不会与宏内的temp冲突
    let result = hygienic_macro!(temp);
    println!("Result: {}", result);
    println!("Original temp: {}", temp);
}

// 非卫生宏（如果存在的话）
// 注意：Rust的宏系统默认是卫生的，这里只是概念示例
macro_rules! non_hygienic_example {
    ($x:expr) => {
        {
            let temp = $x; // 这个temp会与外部作用域的temp冲突
            temp * 2
        }
    };
}

// 宏中的标识符生成
macro_rules! generate_identifiers {
    ($prefix:ident) => {
        {
            let $prefix_value = 42;
            let $prefix_string = "hello";
            ($prefix_value, $prefix_string)
        }
    };
}

// 使用标识符生成
fn identifier_generation() {
    let (my_value, my_string) = generate_identifiers!(my);
    println!("Value: {}, String: {}", my_value, my_string);
}
```

## 5. 编译时计算

### 5.1 编译时计算语义

**编译时计算机制**：

```rust
// 编译时常量计算
macro_rules! const_calc {
    ($x:expr + $y:expr) => {
        const RESULT: i32 = $x + $y;
        RESULT
    };
    ($x:expr * $y:expr) => {
        const RESULT: i32 = $x * $y;
        RESULT
    };
}

// 使用编译时计算
fn compile_time_calculation() {
    let sum = const_calc!(5 + 3);
    let product = const_calc!(4 * 6);
    println!("Sum: {}, Product: {}", sum, product);
}

// 编译时类型计算
macro_rules! type_calc {
    ($t:ty) => {
        std::mem::size_of::<$t>()
    };
}

// 使用类型计算
fn type_calculation() {
    let int_size = type_calc!(i32);
    let float_size = type_calc!(f64);
    println!("i32 size: {}, f64 size: {}", int_size, float_size);
}

// 编译时字符串处理
macro_rules! string_ops {
    ($s:literal) => {
        {
            const LENGTH: usize = $s.len();
            const UPPERCASE: &str = stringify!($s);
            (LENGTH, UPPERCASE)
        }
    };
}

// 使用字符串操作
fn string_operations() {
    let (len, upper) = string_ops!("hello");
    println!("Length: {}, Upper: {}", len, upper);
}
```

### 5.2 元编程技术

**元编程语义**：

```rust
// 代码生成宏
macro_rules! generate_getters {
    ($struct_name:ident { $($field:ident: $field_type:ty),* }) => {
        struct $struct_name {
            $($field: $field_type),*
        }
        
        impl $struct_name {
            $(
                fn $field(&self) -> &$field_type {
                    &self.$field
                }
            )*
        }
    };
}

// 使用代码生成宏
generate_getters!(Person {
    name: String,
    age: i32,
    email: String
});

// 使用生成的代码
fn use_generated_code() {
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
        email: "alice@example.com".to_string(),
    };
    
    println!("Name: {}", person.name());
    println!("Age: {}", person.age());
    println!("Email: {}", person.email());
}

// 条件编译宏
macro_rules! feature_gate {
    (feature = "advanced") => {
        fn advanced_function() {
            println!("Advanced feature enabled");
        }
    };
    (feature = "basic") => {
        fn basic_function() {
            println!("Basic feature enabled");
        }
    };
}

// 使用条件编译
feature_gate!(feature = "basic");

// 测试宏
macro_rules! test_suite {
    ($($test_name:ident: $test_body:block)*) => {
        $(
            #[test]
            fn $test_name() {
                $test_body
            }
        )*
    };
}

// 使用测试宏
test_suite! {
    test_addition: {
        assert_eq!(2 + 2, 4);
    }
    test_multiplication: {
        assert_eq!(3 * 4, 12);
    }
}
```

## 6. 宏的最佳实践

### 6.1 宏设计原则

**宏设计最佳实践**：

```rust
// 1. 提供清晰的文档
/// 安全的除法宏，避免除零错误
/// 
/// # Examples
/// ```
/// let result = safe_div!(10, 2);
/// assert_eq!(result, Some(5));
/// ```
macro_rules! safe_div {
    ($a:expr, $b:expr) => {
        if $b == 0 {
            None
        } else {
            Some($a / $b)
        }
    };
}

// 2. 使用有意义的错误消息
macro_rules! assert_positive {
    ($x:expr) => {
        assert!($x > 0, "Expected positive value, got {}", $x);
    };
}

// 3. 提供多个匹配模式
macro_rules! flexible_print {
    () => {
        println!();
    };
    ($x:expr) => {
        println!("{}", $x);
    };
    ($x:expr, $($rest:expr),*) => {
        print!("{}", $x);
        flexible_print!($($rest),*);
    };
}

// 4. 使用类型安全的参数
macro_rules! type_safe_operation {
    ($x:expr as $t:ty) => {
        $x as $t
    };
}

// 5. 提供合理的默认值
macro_rules! with_defaults {
    ($x:expr) => {
        with_defaults!($x, 0, "default")
    };
    ($x:expr, $default_num:expr) => {
        with_defaults!($x, $default_num, "default")
    };
    ($x:expr, $default_num:expr, $default_str:expr) => {
        match $x {
            Some(val) => val,
            None => ($default_num, $default_str.to_string()),
        }
    };
}
```

### 6.2 宏调试技术

**宏调试语义**：

```rust
// 调试宏展开
macro_rules! debug_macro {
    ($($t:tt)*) => {
        {
            println!("Macro input: {}", stringify!($($t)*));
            $($t)*
        }
    };
}

// 使用调试宏
fn debug_macro_usage() {
    let result = debug_macro!(5 + 3);
    println!("Result: {}", result);
}

// 宏展开检查
macro_rules! check_expansion {
    ($($t:tt)*) => {
        compile_error!(concat!(
            "Macro would expand to: ",
            stringify!($($t)*)
        ));
    };
}

// 条件调试宏
macro_rules! conditional_debug {
    ($($t:tt)*) => {
        if cfg!(debug_assertions) {
            println!("Debug: {}", stringify!($($t)*));
        }
        $($t)*
    };
}

// 使用条件调试
fn conditional_debug_usage() {
    conditional_debug!(let x = 42);
    conditional_debug!(println!("x = {}", x));
}
```

## 7. 高级宏技术

### 7.1 递归宏

**递归宏语义**：

```rust
// 递归宏：计算阶乘
macro_rules! factorial {
    (0) => { 1 };
    ($n:expr) => { $n * factorial!($n - 1) };
}

// 递归宏：构建向量
macro_rules! build_vec {
    () => { Vec::new() };
    ($x:expr) => { vec![$x] };
    ($x:expr, $($rest:expr),*) => {
        {
            let mut v = vec![$x];
            v.extend(build_vec!($($rest),*));
            v
        }
    };
}

// 递归宏：模式匹配
macro_rules! recursive_match {
    ($value:expr, $pattern:pat => $action:expr) => {
        match $value {
            $pattern => $action,
            _ => panic!("No match found"),
        }
    };
    ($value:expr, $pattern:pat => $action:expr, $($rest:pat => $rest_action:expr),*) => {
        match $value {
            $pattern => $action,
            recursive_match!($value, $($rest => $rest_action),*)
        }
    };
}

// 使用递归宏
fn recursive_macro_usage() {
    let fact = factorial!(5);
    println!("Factorial of 5: {}", fact);
    
    let vec = build_vec!(1, 2, 3, 4, 5);
    println!("Vector: {:?}", vec);
    
    let result = recursive_match!(42,
        0 => "zero",
        1..=10 => "small",
        11..=100 => "medium",
        _ => "large"
    );
    println!("Result: {}", result);
}
```

### 7.2 宏组合

**宏组合语义**：

```rust
// 基础宏
macro_rules! base_macro {
    ($x:expr) => {
        $x * 2
    };
}

// 组合宏
macro_rules! combined_macro {
    ($x:expr) => {
        {
            let doubled = base_macro!($x);
            doubled + 1
        }
    };
}

// 链式宏
macro_rules! chain_macro {
    ($x:expr) => {
        chain_macro!($x, 1)
    };
    ($x:expr, $y:expr) => {
        $x + $y
    };
}

// 使用宏组合
fn macro_composition() {
    let result1 = combined_macro!(5);
    println!("Combined result: {}", result1);
    
    let result2 = chain_macro!(10);
    println!("Chain result: {}", result2);
}

// 宏工厂
macro_rules! macro_factory {
    ($name:ident, $operation:tt) => {
        macro_rules! $name {
            ($x:expr, $y:expr) => {
                $x $operation $y
            };
        }
    };
}

// 使用宏工厂
macro_factory!(add_macro, +);
macro_factory!(sub_macro, -);
macro_factory!(mul_macro, *);

fn macro_factory_usage() {
    let sum = add_macro!(5, 3);
    let diff = sub_macro!(10, 4);
    let product = mul_macro!(6, 7);
    
    println!("Sum: {}, Diff: {}, Product: {}", sum, diff, product);
}
```

## 8. 测试和验证

### 8.1 宏测试

**宏测试框架**：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_macro() {
        let result = simple_add!(5, 3);
        assert_eq!(result, 8);
    }

    #[test]
    fn test_safe_division() {
        let result1 = safe_division!(10, 2);
        assert_eq!(result1, Some(5));
        
        let result2 = safe_division!(10, 0);
        assert_eq!(result2, None);
    }

    #[test]
    fn test_vector_macro() {
        let v = vector!(1, 2, 3, 4, 5);
        assert_eq!(v, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_factorial_macro() {
        assert_eq!(factorial!(0), 1);
        assert_eq!(factorial!(1), 1);
        assert_eq!(factorial!(5), 120);
    }

    #[test]
    fn test_build_vec_macro() {
        let empty: Vec<i32> = build_vec!();
        assert_eq!(empty, vec![]);
        
        let single = build_vec!(42);
        assert_eq!(single, vec![42]);
        
        let multiple = build_vec!(1, 2, 3);
        assert_eq!(multiple, vec![1, 2, 3]);
    }

    #[test]
    fn test_hygienic_macro() {
        let temp = 10;
        let result = hygienic_macro!(temp);
        assert_eq!(result, 20);
        assert_eq!(temp, 10); // 原始变量未被修改
    }

    #[test]
    fn test_debug_macro() {
        // 这个测试主要验证宏能正确展开
        let result = debug_macro!(5 + 3);
        assert_eq!(result, 8);
    }

    #[test]
    fn test_conditional_debug() {
        // 测试条件调试宏
        conditional_debug!(let x = 42);
        conditional_debug!(assert_eq!(x, 42));
    }

    #[test]
    fn test_macro_factory() {
        let sum = add_macro!(5, 3);
        let diff = sub_macro!(10, 4);
        let product = mul_macro!(6, 7);
        
        assert_eq!(sum, 8);
        assert_eq!(diff, 6);
        assert_eq!(product, 42);
    }

    #[test]
    fn test_with_defaults() {
        let result1 = with_defaults!(Some(42));
        assert_eq!(result1, 42);
        
        let result2 = with_defaults!(None::<i32>);
        assert_eq!(result2, (0, "default".to_string()));
    }
}
```

## 9. 总结

Rust的宏系统提供了强大的元编程能力，通过声明宏和过程宏，开发者可以在编译时生成代码，实现复杂的抽象和代码复用。

宏系统是Rust语言的重要特性，它通过编译时执行、卫生性保证、类型安全等机制，为开发者提供了既强大又安全的元编程工具。理解宏系统的语义对于编写高效、可维护的Rust程序至关重要。

宏系统体现了Rust在表达力和安全性之间的平衡，为开发者提供了灵活而可靠的代码生成机制，是构建复杂系统和库的重要工具。
