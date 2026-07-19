# 宏系统常见问题解答

## 目录

- [宏系统常见问题解答](#宏系统常见问题解答)
  - [目录](#目录)
  - [基础概念](#基础概念)
    - [Q1: 什么是宏？](#q1-什么是宏)
    - [Q2: 宏与函数有什么区别？](#q2-宏与函数有什么区别)
    - [Q3: 什么时候应该使用宏？](#q3-什么时候应该使用宏)
  - [声明式宏](#声明式宏)
    - [Q4: 如何编写声明式宏？](#q4-如何编写声明式宏)
    - [Q5: 宏的模式匹配如何工作？](#q5-宏的模式匹配如何工作)
    - [Q6: 如何处理宏的重复？](#q6-如何处理宏的重复)
  - [过程宏](#过程宏)
    - [Q7: 什么是过程宏？](#q7-什么是过程宏)
    - [Q8: 如何编写过程宏？](#q8-如何编写过程宏)
    - [Q9: 如何使用syn和quote库？](#q9-如何使用syn和quote库)
  - [属性宏](#属性宏)
    - [Q10: 什么是属性宏？](#q10-什么是属性宏)
    - [Q11: 如何创建自定义属性？](#q11-如何创建自定义属性)
  - [派生宏](#派生宏)
    - [Q12: 什么是派生宏？](#q12-什么是派生宏)
    - [Q13: 如何创建复杂的派生宏？](#q13-如何创建复杂的派生宏)
  - [宏卫生性](#宏卫生性)
    - [Q14: 什么是宏卫生性？](#q14-什么是宏卫生性)
    - [Q15: 如何处理宏的卫生性问题？](#q15-如何处理宏的卫生性问题)
  - [调试与故障排除](#调试与故障排除)
    - [Q16: 如何调试宏？](#q16-如何调试宏)
    - [Q17: 常见的宏错误有哪些？](#q17-常见的宏错误有哪些)
  - [性能与优化](#性能与优化)
    - [Q18: 宏如何影响性能？](#q18-宏如何影响性能)
    - [Q19: 如何优化宏的性能？](#q19-如何优化宏的性能)
  - [最佳实践](#最佳实践)
    - [Q20: 宏设计的最佳实践是什么？](#q20-宏设计的最佳实践是什么)
    - [Q21: 如何测试宏？](#q21-如何测试宏)
  - [总结](#总结)
  - [相关资源](#相关资源)

## 基础概念

### Q1: 什么是宏？

**A:** 宏是Rust中的元编程工具，允许在编译时生成代码。宏可以分为两类：

1. **声明式宏**：使用`macro_rules!`定义的宏
2. **过程宏**：使用Rust代码编写的宏

```rust
// 声明式宏
macro_rules! say_hello {
    () => {
        println!("Hello, world!");
    };
}

// 过程宏
use proc_macro::TokenStream;

#[proc_macro]
pub fn make_answer(_item: TokenStream) -> TokenStream {
    "fn answer() -> u32 { 42 }".parse().unwrap()
}

// 使用宏
fn main() {
    say_hello!();
    let answer = answer();
    println!("The answer is: {}", answer);
}
```

### Q2: 宏与函数有什么区别？

**A:** 宏和函数的主要区别：

| 特性 | 宏 | 函数 |
|------|----|----|
| 调用时机 | 编译时 | 运行时 |
| 参数类型 | 任意TokenStream | 具体类型 |
| 返回值 | 代码 | 值 |
| 性能 | 编译时展开 | 运行时调用 |
| 错误检查 | 编译时 | 运行时 |

```rust
// 宏 - 编译时展开
macro_rules! debug_print {
    ($x:expr) => {
        println!("{:?}", $x);
    };
}

// 函数 - 运行时调用
fn debug_print_fn<T: std::fmt::Debug>(x: T) {
    println!("{:?}", x);
}

// 使用
fn main() {
    debug_print!(42);        // 编译时展开为 println!("{:?}", 42);
    debug_print_fn(42);      // 运行时调用函数
}
```

### Q3: 什么时候应该使用宏？

**A:** 使用宏的场景：

```rust
// 1. 代码生成
macro_rules! create_getters {
    ($name:ident, $field:ident, $type:ty) => {
        impl $name {
            pub fn $field(&self) -> $type {
                self.$field
            }
        }
    };
}

struct Person {
    name: String,
    age: u32,
}

create_getters!(Person, name, String);
create_getters!(Person, age, u32);

// 2. 语法扩展
macro_rules! vec {
    ($($x:expr),*) => {
        {
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}

// 3. 条件编译
macro_rules! debug_only {
    ($($x:stmt)*) => {
        $(
            #[cfg(debug_assertions)]
            $x
        )*
    };
}

debug_only! {
    println!("Debug mode only");
}
```

## 声明式宏

### Q4: 如何编写声明式宏？

**A:** 声明式宏使用`macro_rules!`定义：

```rust
// 基本语法
macro_rules! macro_name {
    (pattern) => {
        // 展开的代码
    };
}

// 示例：简单的宏
macro_rules! say_hello {
    () => {
        println!("Hello, world!");
    };
}

// 带参数的宏
macro_rules! say_hello_to {
    ($name:expr) => {
        println!("Hello, {}!", $name);
    };
}

// 多个模式
macro_rules! say_hello_multiple {
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

// 使用
fn main() {
    say_hello!();
    say_hello_to!("Alice");
    say_hello_multiple!();
    say_hello_multiple!("Bob");
    say_hello_multiple!("Charlie", "Good morning");
}
```

### Q5: 宏的模式匹配如何工作？

**A:** 宏使用模式匹配来识别输入：

```rust
// 基本模式
macro_rules! pattern_examples {
    // 字面量
    (42) => { println!("The answer"); };
    
    // 标识符
    ($name:ident) => { println!("Identifier: {}", stringify!($name)); };
    
    // 表达式
    ($expr:expr) => { println!("Expression: {:?}", $expr); };
    
    // 类型
    ($type:ty) => { println!("Type: {}", stringify!($type)); };
    
    // 语句
    ($stmt:stmt) => { println!("Statement: {}", stringify!($stmt)); };
    
    // 块
    ($block:block) => { println!("Block: {}", stringify!($block)); };
    
    // 元组
    ($($x:expr),*) => { println!("Tuple: {:?}", ($($x),*)); };
    
    // 重复
    ($($x:expr),+ $(,)?) => { 
        println!("Multiple expressions: {:?}", [$($x),*]); 
    };
}

// 使用
fn main() {
    pattern_examples!(42);
    pattern_examples!(my_variable);
    pattern_examples!(1 + 2);
    pattern_examples!(String);
    pattern_examples!(let x = 42;);
    pattern_examples!({ 1 + 2 });
    pattern_examples!(1, 2, 3);
    pattern_examples!(1, 2, 3,);
}
```

### Q6: 如何处理宏的重复？

**A:** 使用重复模式处理多个参数：

```rust
// 基本重复
macro_rules! sum {
    ($($x:expr),*) => {
        {
            let mut sum = 0;
            $(
                sum += $x;
            )*
            sum
        }
    };
}

// 带分隔符的重复
macro_rules! print_all {
    ($($x:expr),* $(,)?) => {
        $(
            println!("{}", $x);
        )*
    };
}

// 条件重复
macro_rules! conditional_repeat {
    ($($x:expr),*; $condition:expr) => {
        $(
            if $condition {
                println!("{}", $x);
            }
        )*
    };
}

// 嵌套重复
macro_rules! nested_repeat {
    ($($outer:expr),*; $($inner:expr),*) => {
        $(
            $(
                println!("{} + {} = {}", $outer, $inner, $outer + $inner);
            )*
        )*
    };
}

// 使用
fn main() {
    let result = sum!(1, 2, 3, 4, 5);
    println!("Sum: {}", result);
    
    print_all!(1, 2, 3, 4, 5);
    
    conditional_repeat!(1, 2, 3, 4, 5; true);
    
    nested_repeat!(1, 2; 10, 20);
}
```

## 过程宏

### Q7: 什么是过程宏？

**A:** 过程宏是使用Rust代码编写的宏，分为三类：

```rust
use proc_macro::TokenStream;

// 1. 函数式宏
#[proc_macro]
pub fn make_answer(_item: TokenStream) -> TokenStream {
    "fn answer() -> u32 { 42 }".parse().unwrap()
}

// 2. 派生宏
#[proc_macro_derive(HelloMacro)]
pub fn hello_macro_derive(input: TokenStream) -> TokenStream {
    let ast = syn::parse(input).unwrap();
    impl_hello_macro(&ast)
}

// 3. 属性宏
#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    // 处理属性参数和函数
    item
}

// 使用
fn main() {
    let answer = answer(); // 由make_answer宏生成
}

#[derive(HelloMacro)]
struct MyStruct;

#[route(GET, "/")]
fn index() {
    // 处理函数
}
```

### Q8: 如何编写过程宏？

**A:** 编写过程宏的步骤：

```rust
// Cargo.toml
// [dependencies]
// proc-macro2 = "1.0"
// quote = "1.0"
// syn = { version = "1.0", features = ["full"] }

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

// 1. 函数式宏
#[proc_macro]
pub fn make_function(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::Ident);
    let name = input;
    
    let expanded = quote! {
        fn #name() -> &'static str {
            "Hello from macro!"
        }
    };
    
    TokenStream::from(expanded)
}

// 2. 派生宏
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    
    let expanded = quote! {
        impl #name {
            pub fn new() -> Self {
                Self {}
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 3. 属性宏
#[proc_macro_attribute]
pub fn my_attribute(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as syn::Ident);
    let item = parse_macro_input!(item as syn::ItemFn);
    
    let fn_name = &item.sig.ident;
    let expanded = quote! {
        #item
        
        fn #attr() {
            println!("Called from attribute macro");
        }
    };
    
    TokenStream::from(expanded)
}
```

### Q9: 如何使用syn和quote库？

**A:** syn和quote是编写过程宏的核心库：

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields};

// 使用syn解析输入
#[proc_macro_derive(FieldNames)]
pub fn field_names(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    
    // 使用syn分析结构体
    let fields = match input.data {
        Data::Struct(data_struct) => match data_struct.fields {
            Fields::Named(fields_named) => fields_named.named,
            _ => panic!("Only named fields are supported"),
        },
        _ => panic!("Only structs are supported"),
    };
    
    // 使用quote生成代码
    let field_names: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let field_count = field_names.len();
    
    let expanded = quote! {
        impl #name {
            pub fn field_names() -> &'static [&'static str] {
                &[#(stringify!(#field_names)),*]
            }
            
            pub fn field_count() -> usize {
                #field_count
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[derive(FieldNames)]
struct Person {
    name: String,
    age: u32,
    email: String,
}

fn main() {
    println!("Fields: {:?}", Person::field_names());
    println!("Count: {}", Person::field_count());
}
```

## 属性宏

### Q10: 什么是属性宏？

**A:** 属性宏是附加到函数、结构体等项上的宏：

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn, AttributeArgs, NestedMeta, Lit};

// 属性宏定义
#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as AttributeArgs);
    let item = parse_macro_input!(item as ItemFn);
    
    // 解析属性参数
    let method = match &attr[0] {
        NestedMeta::Meta(meta) => match meta {
            syn::Meta::Path(path) => path.segments.last().unwrap().ident.to_string(),
            _ => panic!("Expected method"),
        },
        _ => panic!("Expected method"),
    };
    
    let path = match &attr[1] {
        NestedMeta::Lit(Lit::Str(lit)) => lit.value(),
        _ => panic!("Expected path string"),
    };
    
    let fn_name = &item.sig.ident;
    
    // 生成代码
    let expanded = quote! {
        #item
        
        fn #fn_name() {
            println!("Route: {} {}", method, path);
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[route(GET, "/users")]
fn get_users() {
    // 处理获取用户列表
}

#[route(POST, "/users")]
fn create_user() {
    // 处理创建用户
}
```

### Q11: 如何创建自定义属性？

**A:** 创建自定义属性的方法：

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn, AttributeArgs, NestedMeta, Lit};

// 1. 简单属性
#[proc_macro_attribute]
pub fn simple_attr(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let item = parse_macro_input!(item as ItemFn);
    let fn_name = &item.sig.ident;
    
    let expanded = quote! {
        #item
        
        fn #fn_name() {
            println!("Called from simple attribute");
        }
    };
    
    TokenStream::from(expanded)
}

// 2. 带参数的属性
#[proc_macro_attribute]
pub fn with_params(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as AttributeArgs);
    let item = parse_macro_input!(item as ItemFn);
    
    let param = match &attr[0] {
        NestedMeta::Lit(Lit::Str(lit)) => lit.value(),
        _ => panic!("Expected string parameter"),
    };
    
    let fn_name = &item.sig.ident;
    
    let expanded = quote! {
        #item
        
        fn #fn_name() {
            println!("Parameter: {}", #param);
        }
    };
    
    TokenStream::from(expanded)
}

// 3. 复杂属性
#[proc_macro_attribute]
pub fn complex_attr(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as AttributeArgs);
    let item = parse_macro_input!(item as ItemFn);
    
    let mut name = String::new();
    let mut value = String::new();
    
    for arg in attr {
        match arg {
            NestedMeta::Meta(meta) => match meta {
                syn::Meta::NameValue(nv) => {
                    if nv.path.is_ident("name") {
                        if let syn::Expr::Lit(lit) = &nv.value {
                            if let syn::Lit::Str(s) = &lit.lit {
                                name = s.value();
                            }
                        }
                    } else if nv.path.is_ident("value") {
                        if let syn::Expr::Lit(lit) = &nv.value {
                            if let syn::Lit::Str(s) = &lit.lit {
                                value = s.value();
                            }
                        }
                    }
                }
                _ => {}
            }
            _ => {}
        }
    }
    
    let fn_name = &item.sig.ident;
    
    let expanded = quote! {
        #item
        
        fn #fn_name() {
            println!("Name: {}, Value: {}", #name, #value);
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[simple_attr]
fn simple_function() {}

#[with_params("hello")]
fn param_function() {}

#[complex_attr(name = "test", value = "example")]
fn complex_function() {}
```

## 派生宏

### Q12: 什么是派生宏？

**A:** 派生宏是为结构体和枚举自动生成代码的宏：

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields};

// 派生宏定义
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    
    // 分析结构体字段
    let fields = match input.data {
        Data::Struct(data_struct) => match data_struct.fields {
            Fields::Named(fields_named) => fields_named.named,
            _ => panic!("Only named fields are supported"),
        },
        _ => panic!("Only structs are supported"),
    };
    
    // 生成字段访问器
    let field_accessors: Vec<_> = fields.iter().map(|field| {
        let field_name = &field.ident;
        let field_type = &field.ty;
        
        quote! {
            pub fn #field_name(&self) -> &#field_type {
                &self.#field_name
            }
        }
    }).collect();
    
    // 生成构造函数
    let field_names: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let field_types: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    
    let constructor = quote! {
        pub fn new(#(#field_names: #field_types),*) -> Self {
            Self {
                #(#field_names),*
            }
        }
    };
    
    let expanded = quote! {
        impl #name {
            #constructor
            
            #(#field_accessors)*
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[derive(MyDerive)]
struct Person {
    name: String,
    age: u32,
    email: String,
}

fn main() {
    let person = Person::new("Alice".to_string(), 30, "alice@example.com".to_string());
    println!("Name: {}", person.name());
    println!("Age: {}", person.age());
    println!("Email: {}", person.email());
}
```

### Q13: 如何创建复杂的派生宏？

**A:** 创建复杂派生宏的方法：

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields, Field};

// 复杂派生宏
#[proc_macro_derive(ComplexDerive)]
pub fn complex_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    
    // 分析结构体
    let fields = match input.data {
        Data::Struct(data_struct) => match data_struct.fields {
            Fields::Named(fields_named) => fields_named.named,
            _ => panic!("Only named fields are supported"),
        },
        _ => panic!("Only structs are supported"),
    };
    
    // 生成各种方法
    let field_names: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let field_types: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    
    // 构造函数
    let constructor = quote! {
        pub fn new(#(#field_names: #field_types),*) -> Self {
            Self {
                #(#field_names),*
            }
        }
    };
    
    // 字段访问器
    let getters: Vec<_> = fields.iter().map(|field| {
        let field_name = &field.ident;
        let field_type = &field.ty;
        
        quote! {
            pub fn #field_name(&self) -> &#field_type {
                &self.#field_name
            }
        }
    }).collect();
    
    // 字段设置器
    let setters: Vec<_> = fields.iter().map(|field| {
        let field_name = &field.ident;
        let field_type = &field.ty;
        
        quote! {
            pub fn set_#field_name(&mut self, value: #field_type) {
                self.#field_name = value;
            }
        }
    }).collect();
    
    // 字段名称列表
    let field_name_strings: Vec<_> = fields.iter().map(|f| {
        let name = &f.ident;
        quote! { stringify!(#name) }
    }).collect();
    
    let field_names_method = quote! {
        pub fn field_names() -> &'static [&'static str] {
            &[#(#field_name_strings),*]
        }
    };
    
    // 字段数量
    let field_count = fields.len();
    let field_count_method = quote! {
        pub fn field_count() -> usize {
            #field_count
        }
    };
    
    // 调试方法
    let debug_method = quote! {
        pub fn debug_info(&self) -> String {
            format!("{} with {} fields", stringify!(#name), #field_count)
        }
    };
    
    let expanded = quote! {
        impl #name {
            #constructor
            
            #(#getters)*
            #(#setters)*
            
            #field_names_method
            #field_count_method
            #debug_method
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[derive(ComplexDerive)]
struct User {
    id: u32,
    username: String,
    email: String,
    active: bool,
}

fn main() {
    let mut user = User::new(1, "alice".to_string(), "alice@example.com".to_string(), true);
    
    println!("Field names: {:?}", User::field_names());
    println!("Field count: {}", User::field_count());
    println!("Debug info: {}", user.debug_info());
    
    println!("Username: {}", user.username());
    user.set_username("alice_updated".to_string());
    println!("Updated username: {}", user.username());
}
```

## 宏卫生性

### Q14: 什么是宏卫生性？

**A:** 宏卫生性是指宏中定义的标识符不会与外部作用域冲突：

```rust
// 卫生性示例
macro_rules! hygienic_macro {
    () => {
        let x = 42;
        println!("x = {}", x);
    };
}

fn main() {
    let x = "hello";
    hygienic_macro!(); // 不会影响外部的x
    println!("x = {}", x); // 仍然是"hello"
}

// 非卫生性示例（使用tt片段）
macro_rules! non_hygienic_macro {
    ($var:ident) => {
        let $var = 42;
        println!("{} = {}", stringify!($var), $var);
    };
}

fn main() {
    let x = "hello";
    non_hygienic_macro!(x); // 会创建新的x变量
    println!("x = {}", x); // 仍然是"hello"
}
```

### Q15: 如何处理宏的卫生性问题？

**A:** 处理宏卫生性的策略：

```rust
// 1. 使用tt片段
macro_rules! safe_macro {
    ($var:ident) => {
        let $var = 42;
        println!("{} = {}", stringify!($var), $var);
    };
}

// 2. 使用expr片段
macro_rules! expression_macro {
    ($expr:expr) => {
        let result = $expr;
        println!("Result: {}", result);
    };
}

// 3. 使用block片段
macro_rules! block_macro {
    ($block:block) => {
        $block
    };
}

// 4. 使用path片段
macro_rules! path_macro {
    ($path:path) => {
        use $path;
    };
}

// 5. 使用ty片段
macro_rules! type_macro {
    ($ty:ty) => {
        fn get_type() -> &'static str {
            stringify!($ty)
        }
    };
}

// 使用
fn main() {
    safe_macro!(my_var);
    
    expression_macro!(1 + 2);
    
    block_macro!({
        let x = 42;
        x * 2
    });
    
    path_macro!(std::collections::HashMap);
    
    type_macro!(String);
    println!("Type: {}", get_type());
}
```

## 调试与故障排除

### Q16: 如何调试宏？

**A:** 调试宏的方法：

```rust
// 1. 使用cargo expand
// 安装: cargo install cargo-expand
// 使用: cargo expand

// 2. 使用trace_macros!
#![feature(trace_macros)]

trace_macros!(true);

macro_rules! debug_macro {
    ($x:expr) => {
        println!("Debug: {}", $x);
    };
}

fn main() {
    debug_macro!(42);
}

trace_macros!(false);

// 3. 使用log_syntax!
#![feature(log_syntax)]

macro_rules! log_macro {
    ($($x:tt)*) => {
        log_syntax!($($x)*);
    };
}

fn main() {
    log_macro!(hello world);
}

// 4. 使用stringify!
macro_rules! stringify_macro {
    ($x:expr) => {
        println!("Expression: {}", stringify!($x));
    };
}

fn main() {
    stringify_macro!(1 + 2 * 3);
}
```

### Q17: 常见的宏错误有哪些？

**A:** 常见的宏错误及解决方案：

```rust
// 1. 模式匹配错误
// 错误：模式不匹配
macro_rules! bad_macro {
    ($x:expr) => {
        println!("{}", $x);
    };
}

// 解决：添加更多模式
macro_rules! good_macro {
    ($x:expr) => {
        println!("{}", $x);
    };
    ($x:expr, $y:expr) => {
        println!("{}, {}", $x, $y);
    };
}

// 2. 重复错误
// 错误：重复模式冲突
macro_rules! bad_repeat {
    ($($x:expr),*) => {
        $(
            println!("{}", $x);
        )*
    };
    ($($x:expr),+ $(,)?) => {
        $(
            println!("{}", $x);
        )*
    };
}

// 解决：使用更具体的模式
macro_rules! good_repeat {
    ($($x:expr),*) => {
        $(
            println!("{}", $x);
        )*
    };
}

// 3. 卫生性错误
// 错误：标识符冲突
macro_rules! bad_hygiene {
    () => {
        let x = 42;
        println!("{}", x);
    };
}

// 解决：使用参数
macro_rules! good_hygiene {
    ($var:ident) => {
        let $var = 42;
        println!("{}", $var);
    };
}

// 4. 类型错误
// 错误：类型不匹配
macro_rules! bad_type {
    ($x:expr) => {
        let y: i32 = $x;
        println!("{}", y);
    };
}

// 解决：使用泛型
macro_rules! good_type {
    ($x:expr) => {
        let y = $x;
        println!("{:?}", y);
    };
}
```

## 性能与优化

### Q18: 宏如何影响性能？

**A:** 宏对性能的影响：

```rust
// 1. 编译时展开 - 零运行时开销
macro_rules! zero_cost_macro {
    ($x:expr) => {
        $x * 2
    };
}

// 编译后直接展开为: 42 * 2
let result = zero_cost_macro!(42);

// 2. 避免函数调用开销
macro_rules! inline_macro {
    ($x:expr) => {
        if $x > 0 {
            $x
        } else {
            -$x
        }
    };
}

// 3. 编译时计算
macro_rules! compile_time_calc {
    ($x:expr) => {
        const RESULT: i32 = $x * 2;
        RESULT
    };
}

// 4. 避免动态分配
macro_rules! no_allocation {
    ($($x:expr),*) => {
        {
            let mut arr = [0; 3];
            let mut i = 0;
            $(
                arr[i] = $x;
                i += 1;
            )*
            arr
        }
    };
}
```

### Q19: 如何优化宏的性能？

**A:** 优化宏性能的策略：

```rust
// 1. 使用const泛型
macro_rules! const_generic_macro {
    ($x:expr) => {
        const RESULT: i32 = $x;
        RESULT
    };
}

// 2. 避免重复计算
macro_rules! efficient_macro {
    ($x:expr) => {
        {
            let temp = $x;
            temp * temp
        }
    };
}

// 3. 使用内联
#[inline]
macro_rules! inline_macro {
    ($x:expr) => {
        $x
    };
}

// 4. 避免不必要的分配
macro_rules! no_alloc_macro {
    ($x:expr) => {
        {
            let mut result = 0;
            result = $x;
            result
        }
    };
}

// 5. 使用编译时计算
macro_rules! compile_time_macro {
    ($x:expr) => {
        const RESULT: i32 = $x;
        RESULT
    };
}
```

## 最佳实践

### Q20: 宏设计的最佳实践是什么？

**A:** 宏设计的最佳实践：

```rust
// 1. 保持简单
macro_rules! simple_macro {
    ($x:expr) => {
        $x
    };
}

// 2. 提供清晰的文档
/// 计算两个数的和
/// 
/// # 示例
/// ```
/// let result = add!(1, 2);
/// assert_eq!(result, 3);
/// ```
macro_rules! add {
    ($x:expr, $y:expr) => {
        $x + $y
    };
}

// 3. 使用有意义的名称
macro_rules! calculate_sum {
    ($($x:expr),*) => {
        {
            let mut sum = 0;
            $(
                sum += $x;
            )*
            sum
        }
    };
}

// 4. 提供错误处理
macro_rules! safe_divide {
    ($x:expr, $y:expr) => {
        {
            if $y == 0 {
                panic!("Division by zero");
            }
            $x / $y
        }
    };
}

// 5. 使用类型安全
macro_rules! type_safe_macro {
    ($x:expr) => {
        {
            let result: i32 = $x;
            result
        }
    };
}

// 6. 提供默认值
macro_rules! macro_with_default {
    ($x:expr) => {
        $x
    };
    () => {
        0
    };
}

// 7. 使用特征约束
macro_rules! trait_bound_macro {
    ($x:expr) => {
        {
            let result: String = $x.to_string();
            result
        }
    };
}
```

### Q21: 如何测试宏？

**A:** 测试宏的方法：

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    // 1. 基本测试
    #[test]
    fn test_basic_macro() {
        let result = add!(1, 2);
        assert_eq!(result, 3);
    }
    
    // 2. 边界测试
    #[test]
    fn test_edge_cases() {
        assert_eq!(add!(0, 0), 0);
        assert_eq!(add!(-1, 1), 0);
    }
    
    // 3. 类型测试
    #[test]
    fn test_types() {
        assert_eq!(add!(1.0, 2.0), 3.0);
        assert_eq!(add!(1, 2), 3);
    }
    
    // 4. 编译时测试
    #[test]
    fn test_compile_time() {
        const RESULT: i32 = add!(1, 2);
        assert_eq!(RESULT, 3);
    }
    
    // 5. 错误测试
    #[test]
    #[should_panic(expected = "Division by zero")]
    fn test_division_by_zero() {
        safe_divide!(1, 0);
    }
}

// 6. 使用属性测试
#[cfg(test)]
mod property_tests {
    use super::*;
    
    #[test]
    fn test_commutativity() {
        assert_eq!(add!(1, 2), add!(2, 1));
    }
    
    #[test]
    fn test_associativity() {
        assert_eq!(add!(add!(1, 2), 3), add!(1, add!(2, 3)));
    }
}
```

## 总结

宏系统是Rust中强大的元编程工具，提供了编译时代码生成的能力。通过合理使用声明式宏和过程宏，可以大大减少代码重复，提高开发效率。关键是要理解宏的工作原理，遵循最佳实践，并注意宏的卫生性和性能影响。

## 相关资源

- [Rust Book - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/)
- [syn crate documentation](https://docs.rs/syn/)
- [quote crate documentation](https://docs.rs/quote/)
