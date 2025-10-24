# 属性宏详解

> **文档定位**: 深入理解和实现Rust属性宏  
> **难度级别**: ⭐⭐⭐ 高级  
> **预计时间**: 3小时  
> **最后更新**: 2025-10-20

---

## 📊 目录

- [属性宏详解](#属性宏详解)
  - [📊 目录](#-目录)
  - [📋 学习目标](#-学习目标)
  - [1. 属性宏基础](#1-属性宏基础)
    - [1.1 什么是属性宏](#11-什么是属性宏)
    - [1.2 属性宏 vs 派生宏](#12-属性宏-vs-派生宏)
    - [1.3 常见属性宏](#13-常见属性宏)
  - [2. 实现第一个属性宏](#2-实现第一个属性宏)
    - [2.1 基本结构](#21-基本结构)
    - [2.2 使用属性宏](#22-使用属性宏)
  - [3. 解析属性参数](#3-解析属性参数)
    - [3.1 简单参数](#31-简单参数)
    - [3.2 复杂参数](#32-复杂参数)
  - [4. 装饰不同类型的项](#4-装饰不同类型的项)
    - [4.1 装饰函数](#41-装饰函数)
    - [4.2 装饰结构体](#42-装饰结构体)
    - [4.3 装饰模块](#43-装饰模块)
  - [5. 实用属性宏示例](#5-实用属性宏示例)
    - [5.1 计时器宏（完整版）](#51-计时器宏完整版)
    - [5.2 缓存宏](#52-缓存宏)
    - [5.3 异步重试宏](#53-异步重试宏)
  - [6. 处理返回值和泛型](#6-处理返回值和泛型)
    - [6.1 保留函数签名](#61-保留函数签名)
    - [6.2 处理泛型函数](#62-处理泛型函数)
  - [7. 条件编译和特性](#7-条件编译和特性)
    - [7.1 条件代码注入](#71-条件代码注入)
    - [7.2 特性门控](#72-特性门控)
  - [8. 错误处理](#8-错误处理)
    - [8.1 友好的错误消息](#81-友好的错误消息)
    - [8.2 位置信息](#82-位置信息)
  - [9. 测试属性宏](#9-测试属性宏)
    - [9.1 单元测试](#91-单元测试)
    - [9.2 集成测试](#92-集成测试)
  - [10. 实战项目：Web路由宏](#10-实战项目web路由宏)
    - [10.1 定义路由宏](#101-定义路由宏)
    - [10.2 使用路由宏](#102-使用路由宏)
  - [📚 总结](#-总结)
    - [关键概念](#关键概念)
    - [核心技能](#核心技能)
    - [下一步](#下一步)

## 📋 学习目标

完成本章后，你将能够：

- ✅ 理解属性宏的工作原理
- ✅ 实现自定义属性宏
- ✅ 装饰函数、结构体、模块
- ✅ 解析宏参数
- ✅ 转换和增强代码

---

## 1. 属性宏基础

### 1.1 什么是属性宏

**属性宏 (Attribute Macros)** 允许创建自定义属性来装饰和转换代码项（函数、结构体、模块等）。

```rust
// 装饰函数
#[route(GET, "/users")]
fn get_users() { }

// 装饰结构体
#[api_model]
struct User {
    id: i32,
    name: String,
}

// 装饰模块
#[instrumented]
mod api {
    // 模块内容
}
```

### 1.2 属性宏 vs 派生宏

| 特性 | 属性宏 | 派生宏 |
|------|--------|--------|
| **位置** | `#[macro_name]` | `#[derive(Trait)]` |
| **输入** | 任何代码项 | 结构体/枚举 |
| **输出** | 替换代码项 | 添加impl块 |
| **用途** | 装饰和转换 | trait实现 |

### 1.3 常见属性宏

```rust
// Web框架
#[get("/users")]
#[post("/users")]
fn handler() { }

// 测试
#[async_test]
async fn my_test() { }

// 序列化
#[serde(rename = "userName")]
field_name: String,

// 日志
#[tracing::instrument]
fn process() { }
```

---

## 2. 实现第一个属性宏

### 2.1 基本结构

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

/// 简单的调试宏
#[proc_macro_attribute]
pub fn debug_fn(attr: TokenStream, item: TokenStream) -> TokenStream {
    // attr: 属性参数
    // item: 被装饰的代码
    
    let input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let fn_block = &input_fn.block;
    let fn_sig = &input_fn.sig;
    
    let expanded = quote! {
        #fn_sig {
            println!("[DEBUG] 进入函数: {}", stringify!(#fn_name));
            #fn_block
            println!("[DEBUG] 退出函数: {}", stringify!(#fn_name));
        }
    };
    
    TokenStream::from(expanded)
}
```

### 2.2 使用属性宏

```rust
use my_macro::debug_fn;

#[debug_fn]
fn my_function() {
    println!("Hello, World!");
}

fn main() {
    my_function();
    // 输出:
    // [DEBUG] 进入函数: my_function
    // Hello, World!
    // [DEBUG] 退出函数: my_function
}
```

---

## 3. 解析属性参数

### 3.1 简单参数

```rust
use syn::{parse_macro_input, ItemFn, LitStr};

#[proc_macro_attribute]
pub fn log_with_prefix(attr: TokenStream, item: TokenStream) -> TokenStream {
    // 解析参数为字符串
    let prefix = parse_macro_input!(attr as LitStr);
    let input_fn = parse_macro_input!(item as ItemFn);
    
    let fn_name = &input_fn.sig.ident;
    let fn_sig = &input_fn.sig;
    let fn_block = &input_fn.block;
    
    let expanded = quote! {
        #fn_sig {
            println!("[{}] 调用函数: {}", #prefix, stringify!(#fn_name));
            #fn_block
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[log_with_prefix("INFO")]
fn my_function() { }
```

### 3.2 复杂参数

```rust
use syn::{parse::Parse, parse::ParseStream, Ident, Token, LitStr};

// 定义参数结构
struct RouteArgs {
    method: Ident,
    _comma: Token![,],
    path: LitStr,
}

impl Parse for RouteArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(RouteArgs {
            method: input.parse()?,
            _comma: input.parse()?,
            path: input.parse()?,
        })
    }
}

#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(attr as RouteArgs);
    let input_fn = parse_macro_input!(item as ItemFn);
    
    let method = &args.method;
    let path = &args.path;
    let fn_name = &input_fn.sig.ident;
    
    let expanded = quote! {
        pub fn #fn_name() -> Route {
            Route {
                method: Method::#method,
                path: #path.to_string(),
                handler: Box::new(|| {
                    #input_fn
                    // 调用原函数
                }),
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[route(GET, "/users")]
fn get_users() { }
```

---

## 4. 装饰不同类型的项

### 4.1 装饰函数

```rust
use syn::{ItemFn, Signature};

#[proc_macro_attribute]
pub fn timed(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut input_fn = parse_macro_input!(item as ItemFn);
    
    let fn_name = &input_fn.sig.ident;
    let original_block = &input_fn.block;
    
    // 修改函数体
    let new_block = syn::parse2(quote! {
        {
            let _start = std::time::Instant::now();
            let _result = #original_block;
            let _duration = _start.elapsed();
            println!("[TIMER] {} took {:?}", stringify!(#fn_name), _duration);
            _result
        }
    }).unwrap();
    
    input_fn.block = Box::new(new_block);
    
    TokenStream::from(quote! { #input_fn })
}

// 使用
#[timed]
fn slow_function() {
    std::thread::sleep(std::time::Duration::from_millis(100));
}
```

### 4.2 装饰结构体

```rust
use syn::ItemStruct;

#[proc_macro_attribute]
pub fn api_model(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_struct = parse_macro_input!(item as ItemStruct);
    let struct_name = &input_struct.ident;
    
    let expanded = quote! {
        // 保留原结构体
        #input_struct
        
        // 添加API相关实现
        impl #struct_name {
            pub fn to_json(&self) -> String {
                // JSON序列化逻辑
                format!("{{\"type\": \"{}\"}}", stringify!(#struct_name))
            }
            
            pub fn from_json(json: &str) -> Result<Self, String> {
                // JSON反序列化逻辑
                Err("Not implemented".to_string())
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[api_model]
struct User {
    id: i32,
    name: String,
}
```

### 4.3 装饰模块

```rust
use syn::ItemMod;

#[proc_macro_attribute]
pub fn instrumented(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_mod = parse_macro_input!(item as ItemMod);
    let mod_name = &input_mod.ident;
    
    let expanded = quote! {
        #input_mod
        
        // 添加模块级工具
        impl #mod_name {
            pub fn init() {
                println!("初始化模块: {}", stringify!(#mod_name));
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[instrumented]
mod api {
    pub fn handler() { }
}
```

---

## 5. 实用属性宏示例

### 5.1 计时器宏（完整版）

```rust
#[proc_macro_attribute]
pub fn measure_time(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    
    let fn_vis = &input_fn.vis;
    let fn_sig = &input_fn.sig;
    let fn_name = &fn_sig.ident;
    let fn_block = &input_fn.block;
    let fn_attrs = &input_fn.attrs;
    
    // 检查是否是async函数
    let is_async = fn_sig.asyncness.is_some();
    
    let wrapped_block = if is_async {
        quote! {
            {
                let __start = std::time::Instant::now();
                let __result = async {
                    #fn_block
                }.await;
                let __duration = __start.elapsed();
                eprintln!("[TIME] {} took {:?}", stringify!(#fn_name), __duration);
                __result
            }
        }
    } else {
        quote! {
            {
                let __start = std::time::Instant::now();
                let __result = #fn_block;
                let __duration = __start.elapsed();
                eprintln!("[TIME] {} took {:?}", stringify!(#fn_name), __duration);
                __result
            }
        }
    };
    
    let mut new_fn = input_fn.clone();
    new_fn.block = Box::new(syn::parse2(wrapped_block).unwrap());
    
    TokenStream::from(quote! {
        #(#fn_attrs)*
        #fn_vis #fn_sig #new_fn
    })
}
```

### 5.2 缓存宏

```rust
use std::collections::HashMap;
use std::sync::Mutex;

#[proc_macro_attribute]
pub fn cached(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let fn_sig = &input_fn.sig;
    let fn_block = &input_fn.block;
    
    // 生成缓存键类型
    let cache_key_type = quote! { String };
    let cache_name = syn::Ident::new(
        &format!("__CACHE_{}", fn_name.to_string().to_uppercase()),
        fn_name.span()
    );
    
    let expanded = quote! {
        lazy_static::lazy_static! {
            static ref #cache_name: Mutex<HashMap<#cache_key_type, _>> = 
                Mutex::new(HashMap::new());
        }
        
        #fn_sig {
            let cache_key = format!("{:?}", /* 参数 */);
            
            // 检查缓存
            if let Ok(cache) = #cache_name.lock() {
                if let Some(cached_value) = cache.get(&cache_key) {
                    return cached_value.clone();
                }
            }
            
            // 计算结果
            let result = #fn_block;
            
            // 存入缓存
            if let Ok(mut cache) = #cache_name.lock() {
                cache.insert(cache_key, result.clone());
            }
            
            result
        }
    };
    
    TokenStream::from(expanded)
}
```

### 5.3 异步重试宏

```rust
#[proc_macro_attribute]
pub fn retry(attr: TokenStream, item: TokenStream) -> TokenStream {
    // 解析重试次数
    let retry_count: syn::LitInt = parse_macro_input!(attr);
    let input_fn = parse_macro_input!(item as ItemFn);
    
    let fn_sig = &input_fn.sig;
    let fn_block = &input_fn.block;
    let fn_name = &fn_sig.ident;
    
    let max_retries = retry_count.base10_parse::<usize>().unwrap();
    
    let expanded = quote! {
        #fn_sig {
            let mut attempts = 0;
            loop {
                attempts += 1;
                
                match (async #fn_block).await {
                    Ok(result) => return Ok(result),
                    Err(e) if attempts < #max_retries => {
                        eprintln!(
                            "[RETRY] {} failed (attempt {}/{}): {:?}",
                            stringify!(#fn_name),
                            attempts,
                            #max_retries,
                            e
                        );
                        tokio::time::sleep(
                            std::time::Duration::from_millis(100 * attempts as u64)
                        ).await;
                    }
                    Err(e) => return Err(e),
                }
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
#[retry(3)]
async fn fetch_data() -> Result<String, Error> {
    // 可能失败的操作
}
```

---

## 6. 处理返回值和泛型

### 6.1 保留函数签名

```rust
#[proc_macro_attribute]
pub fn wrap_result(attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut input_fn = parse_macro_input!(item as ItemFn);
    
    let fn_sig = &input_fn.sig;
    let fn_block = &input_fn.block;
    let fn_name = &fn_sig.ident;
    let return_type = &fn_sig.output;
    
    // 根据返回类型包装
    let wrapped_block = match return_type {
        syn::ReturnType::Type(_, ty) => {
            quote! {
                {
                    let result: #ty = #fn_block;
                    println!("[RESULT] {} returned: {:?}", stringify!(#fn_name), result);
                    result
                }
            }
        }
        syn::ReturnType::Default => {
            quote! {
                {
                    #fn_block
                    println!("[RESULT] {} completed", stringify!(#fn_name));
                }
            }
        }
    };
    
    input_fn.block = Box::new(syn::parse2(wrapped_block).unwrap());
    
    TokenStream::from(quote! { #input_fn })
}
```

### 6.2 处理泛型函数

```rust
#[proc_macro_attribute]
pub fn debug_generic(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    
    let fn_vis = &input_fn.vis;
    let fn_sig = &input_fn.sig;
    let fn_generics = &fn_sig.generics;
    let fn_name = &fn_sig.ident;
    let fn_block = &input_fn.block;
    
    // 保留泛型参数
    let expanded = quote! {
        #fn_vis fn #fn_name #fn_generics (...) {
            println!("[DEBUG] 调用泛型函数: {}", stringify!(#fn_name));
            #fn_block
        }
    };
    
    TokenStream::from(expanded)
}
```

---

## 7. 条件编译和特性

### 7.1 条件代码注入

```rust
#[proc_macro_attribute]
pub fn debug_only(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    
    let expanded = quote! {
        #[cfg(debug_assertions)]
        #input_fn
        
        #[cfg(not(debug_assertions))]
        fn #fn_name() {
            // 发布版本的空实现
        }
    };
    
    TokenStream::from(expanded)
}
```

### 7.2 特性门控

```rust
#[proc_macro_attribute]
pub fn feature_gated(attr: TokenStream, item: TokenStream) -> TokenStream {
    let feature_name = parse_macro_input!(attr as syn::Ident);
    let input_fn = parse_macro_input!(item as ItemFn);
    
    let expanded = quote! {
        #[cfg(feature = #feature_name)]
        #input_fn
    };
    
    TokenStream::from(expanded)
}

// 使用
#[feature_gated(advanced_logging)]
fn detailed_log() { }
```

---

## 8. 错误处理

### 8.1 友好的错误消息

```rust
use syn::Error;

#[proc_macro_attribute]
pub fn validate_fn(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    
    // 验证函数签名
    if input_fn.sig.inputs.is_empty() {
        return Error::new_spanned(
            &input_fn.sig,
            "validate_fn 需要至少一个参数"
        ).to_compile_error().into();
    }
    
    if input_fn.sig.asyncness.is_some() {
        return Error::new_spanned(
            &input_fn.sig.asyncness,
            "validate_fn 不支持async函数\n提示: 使用 #[async_validate_fn] 代替"
        ).to_compile_error().into();
    }
    
    TokenStream::from(quote! { #input_fn })
}
```

### 8.2 位置信息

```rust
use proc_macro2::Span;

#[proc_macro_attribute]
pub fn with_location(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let fn_sig = &input_fn.sig;
    let fn_block = &input_fn.block;
    
    // 获取宏调用位置
    let call_site = Span::call_site();
    let file = call_site.source_file().path().display().to_string();
    let line = call_site.start().line;
    
    let expanded = quote! {
        #fn_sig {
            println!(
                "[LOCATION] {} defined at {}:{}",
                stringify!(#fn_name),
                #file,
                #line
            );
            #fn_block
        }
    };
    
    TokenStream::from(expanded)
}
```

---

## 9. 测试属性宏

### 9.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;
    
    #[test]
    fn test_timed_macro() {
        let input = quote! {
            fn test_fn() {
                println!("test");
            }
        };
        
        let output = timed(TokenStream::new(), input.into());
        let output_str = output.to_string();
        
        assert!(output_str.contains("Instant::now"));
        assert!(output_str.contains("test_fn"));
    }
}
```

### 9.2 集成测试

```rust
// tests/attribute_macro.rs
use my_macro::timed;

#[timed]
fn test_function() -> i32 {
    42
}

#[test]
fn test_timed_works() {
    let result = test_function();
    assert_eq!(result, 42);
}
```

---

## 10. 实战项目：Web路由宏

### 10.1 定义路由宏

```rust
use syn::{parse::Parse, parse::ParseStream, Ident, LitStr, Token};

struct RouteArgs {
    method: Ident,
    _comma: Token![,],
    path: LitStr,
}

impl Parse for RouteArgs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(RouteArgs {
            method: input.parse()?,
            _comma: input.parse()?,
            path: input.parse()?,
        })
    }
}

#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(attr as RouteArgs);
    let input_fn = parse_macro_input!(item as ItemFn);
    
    let method = &args.method;
    let path = &args.path;
    let fn_name = &input_fn.sig.ident;
    let fn_vis = &input_fn.vis;
    let fn_block = &input_fn.block;
    
    // 生成路由注册代码
    let route_name = syn::Ident::new(
        &format!("__ROUTE_{}", fn_name),
        fn_name.span()
    );
    
    let expanded = quote! {
        #[automatically_derived]
        #[doc(hidden)]
        pub fn #fn_name() -> Response {
            #fn_block
        }
        
        #[automatically_derived]
        #[linkme::distributed_slice(ROUTES)]
        static #route_name: Route = Route {
            method: Method::#method,
            path: #path,
            handler: #fn_name,
        };
    };
    
    TokenStream::from(expanded)
}
```

### 10.2 使用路由宏

```rust
use my_macro::route;

#[route(GET, "/")]
fn index() -> Response {
    Response::new("Hello, World!")
}

#[route(GET, "/users")]
fn list_users() -> Response {
    Response::json(vec!["Alice", "Bob"])
}

#[route(POST, "/users")]
fn create_user() -> Response {
    Response::created()
}
```

---

## 📚 总结

### 关键概念

1. **装饰** - 转换代码项
2. **参数解析** - 处理宏参数
3. **签名保留** - 维护原始类型信息
4. **代码注入** - 添加功能代码
5. **错误处理** - 提供清晰错误

### 核心技能

- ✅ 实现属性宏
- ✅ 解析复杂参数
- ✅ 装饰不同代码项
- ✅ 处理泛型和返回值
- ✅ 条件编译

### 下一步

- 📖 学习 [函数式宏教程](./04_function_macros.md)
- 📖 学习 [TokenStream详解](./05_token_streams.md)
- 📖 回顾 [过程宏基础](./01_proc_macro_basics.md)

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
