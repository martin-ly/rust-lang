# 过程宏语义分析


## 📊 目录

- [概述](#概述)
- [1. 过程宏理论基础](#1-过程宏理论基础)
  - [1.1 过程宏概念](#11-过程宏概念)
  - [1.2 过程宏类型](#12-过程宏类型)
- [2. 派生宏](#2-派生宏)
  - [2.1 基本派生宏](#21-基本派生宏)
  - [2.2 复杂派生宏](#22-复杂派生宏)
- [3. 属性宏](#3-属性宏)
  - [3.1 基本属性宏](#31-基本属性宏)
  - [3.2 复杂属性宏](#32-复杂属性宏)
- [4. 函数宏](#4-函数宏)
  - [4.1 基本函数宏](#41-基本函数宏)
  - [4.2 复杂函数宏](#42-复杂函数宏)
- [5. 宏展开过程](#5-宏展开过程)
  - [5.1 展开阶段](#51-展开阶段)
  - [5.2 错误处理](#52-错误处理)
- [6. 编译时计算](#6-编译时计算)
  - [6.1 常量计算](#61-常量计算)
  - [6.2 类型级计算](#62-类型级计算)
- [7. 形式化证明](#7-形式化证明)
  - [7.1 宏展开定理](#71-宏展开定理)
  - [7.2 类型安全定理](#72-类型安全定理)
- [8. 工程实践](#8-工程实践)
  - [8.1 最佳实践](#81-最佳实践)
  - [8.2 常见陷阱](#82-常见陷阱)
- [9. 交叉引用](#9-交叉引用)
- [10. 参考文献](#10-参考文献)


## 概述

本文档详细分析Rust中过程宏的语义，包括其理论基础、实现机制和形式化定义。

## 1. 过程宏理论基础

### 1.1 过程宏概念

**定义 1.1.1 (过程宏)**
过程宏是Rust中在编译时执行代码生成和转换的机制，通过函数形式定义。

**过程宏的核心特性**：

1. **编译时执行**：在编译阶段执行
2. **代码生成**：生成新的代码
3. **语法转换**：转换输入语法
4. **类型安全**：保持类型安全

### 1.2 过程宏类型

**过程宏分类**：

1. **派生宏**：为结构体和枚举自动实现特征
2. **属性宏**：为项添加属性
3. **函数宏**：类似函数的宏调用

## 2. 派生宏

### 2.1 基本派生宏

**派生宏实现**：

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields};

// 基本派生宏
#[proc_macro_derive(Hello)]
pub fn hello_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;
    
    let expanded = quote! {
        impl Hello for #name {
            fn hello() {
                println!("Hello from {}!", stringify!(#name));
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用派生宏
#[derive(Hello)]
struct MyStruct;

#[derive(Hello)]
enum MyEnum {
    Variant1,
    Variant2,
}

fn main() {
    MyStruct::hello();
    MyEnum::hello();
}
```

### 2.2 复杂派生宏

**复杂派生宏实现**：

```rust
// 复杂派生宏
#[proc_macro_derive(Debug)]
pub fn derive_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let debug_impl = match &input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Named(fields) => {
                    let field_debug = fields.named.iter().map(|f| {
                        let name = &f.ident;
                        quote! {
                            .field(stringify!(#name), &self.#name)
                        }
                    });
                    
                    quote! {
                        impl std::fmt::Debug for #name {
                            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                f.debug_struct(stringify!(#name))
                                    #(#field_debug)*
                                    .finish()
                            }
                        }
                    }
                },
                Fields::Unnamed(fields) => {
                    let field_debug = fields.unnamed.iter().enumerate().map(|(i, _)| {
                        let index = syn::Index::from(i);
                        quote! { &self.#index }
                    });
                    
                    quote! {
                        impl std::fmt::Debug for #name {
                            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                f.debug_tuple(stringify!(#name))
                                    #(.field(#field_debug))*
                                    .finish()
                            }
                        }
                    }
                },
                Fields::Unit => {
                    quote! {
                        impl std::fmt::Debug for #name {
                            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                f.debug_struct(stringify!(#name)).finish()
                            }
                        }
                    }
                }
            }
        },
        Data::Enum(data) => {
            let variant_arms = data.variants.iter().map(|variant| {
                let variant_name = &variant.ident;
                match &variant.fields {
                    Fields::Named(fields) => {
                        let field_names: Vec<_> = fields.named.iter()
                            .map(|f| &f.ident)
                            .collect();
                        let field_debug = field_names.iter().map(|name| {
                            quote! {
                                .field(stringify!(#name), #name)
                            }
                        });
                        
                        quote! {
                            #name::#variant_name { #(#field_names),* } => {
                                f.debug_struct(&format!("{}::{}", stringify!(#name), stringify!(#variant_name)))
                                    #(#field_debug)*
                                    .finish()
                            }
                        }
                    },
                    Fields::Unnamed(fields) => {
                        let field_names: Vec<_> = (0..fields.unnamed.len())
                            .map(|i| format!("field_{}", i))
                            .map(|name| syn::Ident::new(&name, proc_macro2::Span::call_site()))
                            .collect();
                        
                        quote! {
                            #name::#variant_name(#(#field_names),*) => {
                                f.debug_tuple(&format!("{}::{}", stringify!(#name), stringify!(#variant_name)))
                                    #(.field(#field_names))*
                                    .finish()
                            }
                        }
                    },
                    Fields::Unit => {
                        quote! {
                            #name::#variant_name => {
                                write!(f, "{}::{}", stringify!(#name), stringify!(#variant_name))
                            }
                        }
                    }
                }
            });
            
            quote! {
                impl std::fmt::Debug for #name {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        match self {
                            #(#variant_arms,)*
                        }
                    }
                }
            }
        },
        Data::Union(_) => {
            quote! {
                impl std::fmt::Debug for #name {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        write!(f, "{} {{ /* union */ }}", stringify!(#name))
                    }
                }
            }
        }
    };
    
    TokenStream::from(debug_impl)
}

// 使用复杂派生宏
#[derive(Debug)]
struct Person {
    name: String,
    age: u32,
}

#[derive(Debug)]
enum Status {
    Active,
    Inactive(String),
    Pending { reason: String, timeout: u64 },
}

fn main() {
    let person = Person {
        name: "Alice".to_string(),
        age: 30,
    };
    println!("{:?}", person);
    
    let status = Status::Pending {
        reason: "Processing".to_string(),
        timeout: 1000,
    };
    println!("{:?}", status);
}
```

## 3. 属性宏

### 3.1 基本属性宏

**属性宏实现**：

```rust
// 基本属性宏
#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr as syn::LitStr);
    let item = parse_macro_input!(item as syn::ItemFn);
    let fn_name = &item.sig.ident;
    
    let expanded = quote! {
        #item
        
        impl Route for #fn_name {
            fn path() -> &'static str {
                #attr
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用属性宏
#[route("/hello")]
fn hello_handler() {
    println!("Hello, world!");
}

fn main() {
    hello_handler();
    println!("Route path: {}", <hello_handler as Route>::path());
}
```

### 3.2 复杂属性宏

**复杂属性宏实现**：

```rust
// 复杂属性宏
#[proc_macro_attribute]
pub fn benchmark(args: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::ItemFn);
    let fn_name = &input.sig.ident;
    let fn_block = &input.block;
    let fn_vis = &input.vis;
    let fn_sig = &input.sig;
    
    // 解析参数
    let iterations: usize = if args.is_empty() {
        1000
    } else {
        args.to_string().parse().unwrap_or(1000)
    };
    
    let result = quote! {
        #fn_vis #fn_sig {
            let start = std::time::Instant::now();
            
            for _ in 0..#iterations {
                #fn_block
            }
            
            let duration = start.elapsed();
            println!("Function {} executed {} times in {:?}", 
                     stringify!(#fn_name), #iterations, duration);
            println!("Average time per execution: {:?}", 
                     duration / #iterations);
        }
    };
    
    TokenStream::from(result)
}

// 使用复杂属性宏
#[benchmark(100)]
fn fast_function() {
    let _ = 1 + 1;
}

#[benchmark]
fn slow_function() {
    std::thread::sleep(std::time::Duration::from_millis(1));
}

fn main() {
    fast_function();
    slow_function();
}
```

## 4. 函数宏

### 4.1 基本函数宏

**函数宏实现**：

```rust
// 基本函数宏
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::LitStr);
    let query = input.value();
    
    let expanded = quote! {
        {
            let query = #query;
            // 这里可以添加SQL解析和验证逻辑
            query
        }
    };
    
    TokenStream::from(expanded)
}

// 使用函数宏
fn main() {
    let query = sql!("SELECT * FROM users WHERE id = 1");
    println!("Query: {}", query);
}
```

### 4.2 复杂函数宏

**复杂函数宏实现**：

```rust
// 复杂函数宏
#[proc_macro]
pub fn vector(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::ExprArray);
    let elements = input.elems;
    
    let expanded = quote! {
        {
            let mut v = Vec::new();
            #(v.push(#elements);)*
            v
        }
    };
    
    TokenStream::from(expanded)
}

// 使用复杂函数宏
fn main() {
    let numbers = vector![1, 2, 3, 4, 5];
    println!("Vector: {:?}", numbers);
    
    let strings = vector!["hello", "world"];
    println!("Strings: {:?}", strings);
}
```

## 5. 宏展开过程

### 5.1 展开阶段

**宏展开阶段**：

```rust
// 宏展开阶段示例
mod macro_expansion {
    // 第一阶段：解析输入
    pub fn parse_input(input: TokenStream) -> syn::DeriveInput {
        parse_macro_input!(input as syn::DeriveInput)
    }
    
    // 第二阶段：分析结构
    pub fn analyze_structure(input: &syn::DeriveInput) -> StructureInfo {
        match &input.data {
            syn::Data::Struct(data) => {
                StructureInfo::Struct {
                    fields: data.fields.iter().map(|f| {
                        FieldInfo {
                            name: f.ident.clone(),
                            ty: f.ty.clone(),
                            visibility: f.vis.clone(),
                        }
                    }).collect(),
                }
            },
            syn::Data::Enum(data) => {
                StructureInfo::Enum {
                    variants: data.variants.iter().map(|v| {
                        VariantInfo {
                            name: v.ident.clone(),
                            fields: v.fields.iter().map(|f| {
                                FieldInfo {
                                    name: f.ident.clone(),
                                    ty: f.ty.clone(),
                                    visibility: f.vis.clone(),
                                }
                            }).collect(),
                        }
                    }).collect(),
                }
            },
            syn::Data::Union(_) => {
                StructureInfo::Union
            }
        }
    }
    
    // 第三阶段：生成代码
    pub fn generate_code(structure: &StructureInfo, name: &syn::Ident) -> proc_macro2::TokenStream {
        match structure {
            StructureInfo::Struct { fields } => {
                let field_impls = fields.iter().map(|field| {
                    let field_name = &field.name;
                    quote! {
                        impl std::fmt::Display for #field_name {
                            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                write!(f, "{:?}", self)
                            }
                        }
                    }
                });
                
                quote! {
                    impl std::fmt::Display for #name {
                        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                            write!(f, "{} {{ ", stringify!(#name))?;
                            #(write!(f, "{}: {}, ", stringify!(#field_name), self.#field_name)?;)*
                            write!(f, "}}")
                        }
                    }
                    #(#field_impls)*
                }
            },
            StructureInfo::Enum { variants } => {
                let variant_arms = variants.iter().map(|variant| {
                    let variant_name = &variant.name;
                    quote! {
                        #name::#variant_name => {
                            write!(f, "{}", stringify!(#variant_name))
                        }
                    }
                });
                
                quote! {
                    impl std::fmt::Display for #name {
                        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                            match self {
                                #(#variant_arms,)*
                            }
                        }
                    }
                }
            },
            StructureInfo::Union => {
                quote! {
                    impl std::fmt::Display for #name {
                        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                            write!(f, "{} {{ /* union */ }}", stringify!(#name))
                        }
                    }
                }
            }
        }
    }
}

// 结构信息
#[derive(Debug)]
enum StructureInfo {
    Struct { fields: Vec<FieldInfo> },
    Enum { variants: Vec<VariantInfo> },
    Union,
}

#[derive(Debug)]
struct FieldInfo {
    name: Option<syn::Ident>,
    ty: syn::Type,
    visibility: syn::Visibility,
}

#[derive(Debug)]
struct VariantInfo {
    name: syn::Ident,
    fields: Vec<FieldInfo>,
}

// 完整的过程宏
#[proc_macro_derive(Display)]
pub fn derive_display(input: TokenStream) -> TokenStream {
    let input = macro_expansion::parse_input(input);
    let structure = macro_expansion::analyze_structure(&input);
    let code = macro_expansion::generate_code(&structure, &input.ident);
    
    TokenStream::from(code)
}
```

### 5.2 错误处理

**宏错误处理**：

```rust
// 宏错误处理
mod macro_error_handling {
    use proc_macro::TokenStream;
    use syn::{parse_macro_input, DeriveInput, Data, Fields};
    use quote::quote;
    
    // 错误类型
    #[derive(Debug)]
    pub enum MacroError {
        UnsupportedType,
        MissingField,
        InvalidAttribute,
        ParseError(String),
    }
    
    impl std::fmt::Display for MacroError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                MacroError::UnsupportedType => write!(f, "Unsupported type"),
                MacroError::MissingField => write!(f, "Missing required field"),
                MacroError::InvalidAttribute => write!(f, "Invalid attribute"),
                MacroError::ParseError(msg) => write!(f, "Parse error: {}", msg),
            }
        }
    }
    
    // 安全的宏展开
    pub fn safe_derive_macro(input: TokenStream) -> Result<TokenStream, MacroError> {
        let input = parse_macro_input!(input as DeriveInput);
        let name = &input.ident;
        
        // 检查是否支持的类型
        match &input.data {
            Data::Struct(data) => {
                match &data.fields {
                    Fields::Named(fields) => {
                        // 检查字段
                        for field in fields.named.iter() {
                            if field.ident.is_none() {
                                return Err(MacroError::MissingField);
                            }
                        }
                        
                        let field_impls = fields.named.iter().map(|field| {
                            let field_name = &field.ident;
                            quote! {
                                .field(stringify!(#field_name), &self.#field_name)
                            }
                        });
                        
                        let expanded = quote! {
                            impl std::fmt::Debug for #name {
                                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                    f.debug_struct(stringify!(#name))
                                        #(#field_impls)*
                                        .finish()
                                }
                            }
                        };
                        
                        Ok(TokenStream::from(expanded))
                    },
                    Fields::Unnamed(_) => {
                        Err(MacroError::UnsupportedType)
                    },
                    Fields::Unit => {
                        let expanded = quote! {
                            impl std::fmt::Debug for #name {
                                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                    f.debug_struct(stringify!(#name)).finish()
                                }
                            }
                        };
                        
                        Ok(TokenStream::from(expanded))
                    }
                }
            },
            Data::Enum(_) => {
                Err(MacroError::UnsupportedType)
            },
            Data::Union(_) => {
                Err(MacroError::UnsupportedType)
            }
        }
    }
    
    // 带错误处理的宏
    #[proc_macro_derive(SafeDebug)]
    pub fn safe_debug_derive(input: TokenStream) -> TokenStream {
        match safe_derive_macro(input) {
            Ok(token_stream) => token_stream,
            Err(error) => {
                let error_message = format!("SafeDebug derive failed: {}", error);
                let expanded = quote! {
                    compile_error!(#error_message);
                };
                TokenStream::from(expanded)
            }
        }
    }
}

// 使用错误处理的宏
#[derive(macro_error_handling::SafeDebug)]
struct ValidStruct {
    field1: i32,
    field2: String,
}

// 这会编译错误
// #[derive(macro_error_handling::SafeDebug)]
// struct InvalidStruct(i32, String); // 元组结构体不支持
```

## 6. 编译时计算

### 6.1 常量计算

**编译时常量计算**：

```rust
// 编译时常量计算
mod compile_time_calculation {
    use proc_macro::TokenStream;
    use syn::{parse_macro_input, LitInt};
    use quote::quote;
    
    // 编译时阶乘计算
    #[proc_macro]
    pub fn factorial(input: TokenStream) -> TokenStream {
        let input = parse_macro_input!(input as LitInt);
        let n: usize = input.base10_parse().unwrap();
        
        let result = factorial_calc(n);
        let expanded = quote! {
            #result
        };
        
        TokenStream::from(expanded)
    }
    
    fn factorial_calc(n: usize) -> usize {
        if n <= 1 {
            1
        } else {
            n * factorial_calc(n - 1)
        }
    }
    
    // 编译时斐波那契计算
    #[proc_macro]
    pub fn fibonacci(input: TokenStream) -> TokenStream {
        let input = parse_macro_input!(input as LitInt);
        let n: usize = input.base10_parse().unwrap();
        
        let result = fibonacci_calc(n);
        let expanded = quote! {
            #result
        };
        
        TokenStream::from(expanded)
    }
    
    fn fibonacci_calc(n: usize) -> usize {
        if n <= 1 {
            n
        } else {
            fibonacci_calc(n - 1) + fibonacci_calc(n - 2)
        }
    }
    
    // 编译时字符串处理
    #[proc_macro]
    pub fn string_length(input: TokenStream) -> TokenStream {
        let input = parse_macro_input!(input as syn::LitStr);
        let s = input.value();
        let length = s.len();
        
        let expanded = quote! {
            #length
        };
        
        TokenStream::from(expanded)
    }
}

// 使用编译时计算
fn main() {
    const FACT_10: usize = compile_time_calculation::factorial!(10);
    const FIB_15: usize = compile_time_calculation::fibonacci!(15);
    const HELLO_LEN: usize = compile_time_calculation::string_length!("Hello, World!");
    
    println!("10! = {}", FACT_10);
    println!("fib(15) = {}", FIB_15);
    println!("'Hello, World!' length = {}", HELLO_LEN);
}
```

### 6.2 类型级计算

**类型级计算**：

```rust
// 类型级计算
mod type_level_calculation {
    use proc_macro::TokenStream;
    use syn::{parse_macro_input, DeriveInput};
    use quote::quote;
    
    // 类型级数字
    pub trait Nat {
        const VALUE: usize;
    }
    
    pub struct Zero;
    pub struct Succ<N: Nat>;
    
    impl Nat for Zero {
        const VALUE: usize = 0;
    }
    
    impl<N: Nat> Nat for Succ<N> {
        const VALUE: usize = N::VALUE + 1;
    }
    
    // 类型级加法
    pub trait Add<Rhs> {
        type Output;
    }
    
    impl<Rhs> Add<Rhs> for Zero {
        type Output = Rhs;
    }
    
    impl<N: Nat, Rhs> Add<Rhs> for Succ<N> {
        type Output = Succ<<N as Add<Rhs>>::Output>;
    }
    
    // 类型级乘法
    pub trait Mul<Rhs> {
        type Output;
    }
    
    impl<Rhs> Mul<Rhs> for Zero {
        type Output = Zero;
    }
    
    impl<N: Nat, Rhs> Mul<Rhs> for Succ<N>
    where
        N: Mul<Rhs>,
        Rhs: Add<<N as Mul<Rhs>>::Output>,
    {
        type Output = <Rhs as Add<<N as Mul<Rhs>>::Output>>::Output;
    }
    
    // 生成类型级数字的宏
    #[proc_macro]
    pub fn nat(input: TokenStream) -> TokenStream {
        let input = parse_macro_input!(input as syn::LitInt);
        let n: usize = input.base10_parse().unwrap();
        
        let nat_type = generate_nat_type(n);
        let expanded = quote! {
            #nat_type
        };
        
        TokenStream::from(expanded)
    }
    
    fn generate_nat_type(n: usize) -> proc_macro2::TokenStream {
        if n == 0 {
            quote! { Zero }
        } else {
            let inner = generate_nat_type(n - 1);
            quote! { Succ<#inner> }
        }
    }
    
    // 类型级数组
    #[proc_macro_derive(TypeArray)]
    pub fn derive_type_array(input: TokenStream) -> TokenStream {
        let input = parse_macro_input!(input as DeriveInput);
        let name = &input.ident;
        
        let expanded = quote! {
            impl #name {
                pub const fn size() -> usize {
                    Self::SIZE
                }
                
                pub fn new() -> Self {
                    Self::default()
                }
            }
        };
        
        TokenStream::from(expanded)
    }
}

// 使用类型级计算
use type_level_calculation::*;

type Three = Succ<Succ<Succ<Zero>>>;
type Five = Succ<Succ<Succ<Succ<Succ<Zero>>>>>;
type Eight = <Three as Add<Five>>::Output;

fn main() {
    println!("Three: {}", Three::VALUE);
    println!("Five: {}", Five::VALUE);
    println!("Eight: {}", Eight::VALUE);
    
    // 编译时验证
    const _: () = assert!(Three::VALUE == 3);
    const _: () = assert!(Five::VALUE == 5);
    const _: () = assert!(Eight::VALUE == 8);
}
```

## 7. 形式化证明

### 7.1 宏展开定理

**定理 7.1.1 (宏展开)**
过程宏的展开是确定性的。

**证明**：
通过宏展开的算法和输入输出关系证明确定性。

### 7.2 类型安全定理

**定理 7.2.1 (类型安全)**
过程宏保持类型安全。

**证明**：
通过宏展开后的代码类型检查证明类型安全。

## 8. 工程实践

### 8.1 最佳实践

**最佳实践**：

1. **清晰的错误消息**：提供有用的编译错误信息
2. **性能考虑**：避免在宏中进行昂贵的计算
3. **文档化**：为宏提供清晰的文档
4. **测试**：为宏编写全面的测试

### 8.2 常见陷阱

**常见陷阱**：

1. **无限递归**：

   ```rust
   // 错误：无限递归
   #[proc_macro]
   pub fn infinite_macro(input: TokenStream) -> TokenStream {
       // 这会导致无限递归
       infinite_macro(input)
   }
   ```

2. **类型错误**：

   ```rust
   // 错误：类型不匹配
   #[proc_macro_derive(Bad)]
   pub fn bad_derive(input: TokenStream) -> TokenStream {
       // 生成的代码类型不正确
       quote! {
           impl Bad for String {} // 错误：String不是输入类型
       }.into()
   }
   ```

3. **性能问题**：

   ```rust
   // 错误：性能问题
   #[proc_macro]
   pub fn expensive_macro(input: TokenStream) -> TokenStream {
       // 在宏中进行昂贵的计算
       let result = expensive_calculation();
       quote! { #result }.into()
   }
   ```

## 9. 交叉引用

- [宏系统语义](./11_macro_system_semantics.md) - 宏系统
- [编译时语义](./26_advanced_compiler_semantics.md) - 编译时处理
- [类型系统语义](./type_system_analysis.md) - 类型系统
- [代码生成语义](./12_async_runtime_semantics.md) - 代码生成

## 10. 参考文献

1. Rust Book - Procedural Macros
2. Rust Reference - Procedural Macros
3. Procedural Macros in Rust
4. Rust Macro System
