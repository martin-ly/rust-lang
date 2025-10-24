# Rust 1.90 宏系统实例集合

> **文档定位**: 可运行的Rust 1.90宏示例代码  
> **难度级别**: ⭐⭐⭐ 高级  
> **最后更新**: 2025-10-20

---


## 📊 目录

- [📋 示例索引](#示例索引)
- [1. 声明宏示例](#1-声明宏示例)
  - [示例 1.1: 类型安全的单位转换宏](#示例-11-类型安全的单位转换宏)
  - [示例 1.2: 配置DSL宏](#示例-12-配置dsl宏)
  - [示例 1.3: 日志宏族](#示例-13-日志宏族)
- [2. 派生宏示例](#2-派生宏示例)
  - [示例 2.1: Builder模式生成器](#示例-21-builder模式生成器)
  - [示例 2.2: 自动Debug实现](#示例-22-自动debug实现)
- [3. 属性宏示例](#3-属性宏示例)
  - [示例 3.1: 性能监控宏](#示例-31-性能监控宏)
  - [示例 3.2: 缓存宏](#示例-32-缓存宏)
- [4. 函数式宏示例](#4-函数式宏示例)
  - [示例 4.1: SQL查询宏](#示例-41-sql查询宏)
  - [示例 4.2: HTML模板宏](#示例-42-html模板宏)
- [5. 综合应用示例](#5-综合应用示例)
  - [示例 5.1: API路由注册系统](#示例-51-api路由注册系统)
- [返回导航](#返回导航)


## 📋 示例索引

1. [声明宏示例](#1-声明宏示例)
2. [派生宏示例](#2-派生宏示例)
3. [属性宏示例](#3-属性宏示例)
4. [函数式宏示例](#4-函数式宏示例)
5. [综合应用示例](#5-综合应用示例)

---

## 1. 声明宏示例

### 示例 1.1: 类型安全的单位转换宏

```rust
/// Rust 1.90特性：使用所有片段说明符
#[macro_export]
macro_rules! unit_conversion {
    // 长度转换
    (length: $value:expr, $from:ident => $to:ident) => {
        unit_conversion!(@length $value, $from, $to)
    };
    
    // 内部规则：米到其他单位
    (@length $value:expr, meter, kilometer) => { $value / 1000.0 };
    (@length $value:expr, meter, meter) => { $value };
    (@length $value:expr, meter, centimeter) => { $value * 100.0 };
    
    // 内部规则：千米到其他单位
    (@length $value:expr, kilometer, meter) => { $value * 1000.0 };
    (@length $value:expr, kilometer, kilometer) => { $value };
    
    // 时间转换
    (time: $value:expr, $from:ident => $to:ident) => {
        unit_conversion!(@time $value, $from, $to)
    };
    
    (@time $value:expr, second, minute) => { $value / 60.0 };
    (@time $value:expr, minute, second) => { $value * 60.0 };
    (@time $value:expr, hour, minute) => { $value * 60.0 };
}

// 使用示例
#[cfg(test)]
mod tests {
    #[test]
    fn test_unit_conversion() {
        let km = unit_conversion!(length: 1000.0, meter => kilometer);
        assert_eq!(km, 1.0);
        
        let sec = unit_conversion!(time: 2.0, minute => second);
        assert_eq!(sec, 120.0);
    }
}
```

### 示例 1.2: 配置DSL宏

```rust
/// 使用Rust 1.90的嵌套重复和可选尾随分隔符
#[macro_export]
macro_rules! config {
    // 主入口
    {
        $(
            $section:ident {
                $(
                    $key:ident = $value:expr
                ),* $(,)?
            }
        )*
    } => {
        {
            use std::collections::HashMap;
            let mut config = HashMap::new();
            $(
                let mut section = HashMap::new();
                $(
                    section.insert(stringify!($key), $value.to_string());
                )*
                config.insert(stringify!($section), section);
            )*
            config
        }
    };
}

// 使用示例
#[test]
fn test_config_dsl() {
    let app_config = config! {
        database {
            host = "localhost",
            port = "5432",
            name = "mydb",
        }
        server {
            host = "0.0.0.0",
            port = "8080",
        }
    };
    
    assert_eq!(app_config.get("database").unwrap().get("host").unwrap(), "localhost");
}
```

### 示例 1.3: 日志宏族

```rust
/// 展示Rust 1.90的条件编译和宏卫生性
#[macro_export]
macro_rules! log {
    // Debug级别日志
    (debug: $($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
            eprintln!("[DEBUG] {}", format!($($arg)*));
        }
    };
    
    // Info级别日志
    (info: $($arg:tt)*) => {
        eprintln!("[INFO] {}", format!($($arg)*));
    };
    
    // Warning级别日志
    (warn: $($arg:tt)*) => {
        eprintln!("[WARN] {}", format!($($arg)*));
    };
    
    // Error级别日志
    (error: $($arg:tt)*) => {
        eprintln!("[ERROR] {}", format!($($arg)*));
    };
    
    // 带位置信息的日志
    (at: $level:ident, $($arg:tt)*) => {
        log!($level: "{} at {}:{}", format!($($arg)*), file!(), line!());
    };
}

// 使用示例
#[test]
fn test_logging() {
    log!(debug: "Debug message: {}", 42);
    log!(info: "Info message");
    log!(at: error, "Error occurred");
}
```

---

## 2. 派生宏示例

### 示例 2.1: Builder模式生成器

```rust
// 文件: src/lib.rs (proc-macro crate)
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields};

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = syn::Ident::new(&format!("{}Builder", name), name.span());
    
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("Builder only supports named fields"),
        },
        _ => panic!("Builder only supports structs"),
    };
    
    // 提取字段名和类型
    let field_names: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let field_types: Vec<_> = fields.iter().map(|f| &f.ty).collect();
    
    // 生成Builder结构体
    let builder_fields = quote! {
        #(#field_names: Option<#field_types>),*
    };
    
    // 生成setter方法
    let setters = field_names.iter().zip(field_types.iter()).map(|(name, ty)| {
        quote! {
            pub fn #name(mut self, value: #ty) -> Self {
                self.#name = Some(value);
                self
            }
        }
    });
    
    // 生成build方法
    let build_fields = field_names.iter().map(|name| {
        quote! {
            #name: self.#name.ok_or(format!("Field {} not set", stringify!(#name)))?
        }
    });
    
    let expanded = quote! {
        pub struct #builder_name {
            #builder_fields
        }
        
        impl #builder_name {
            pub fn new() -> Self {
                Self {
                    #(#field_names: None),*
                }
            }
            
            #(#setters)*
            
            pub fn build(self) -> Result<#name, String> {
                Ok(#name {
                    #(#build_fields),*
                })
            }
        }
        
        impl #name {
            pub fn builder() -> #builder_name {
                #builder_name::new()
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 示例 2.2: 自动Debug实现

```rust
#[proc_macro_derive(CustomDebug)]
pub fn derive_custom_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let debug_impl = match &input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Named(fields) => {
                    let field_debugs = fields.named.iter().map(|f| {
                        let field_name = &f.ident;
                        let field_str = field_name.as_ref().unwrap().to_string();
                        quote! {
                            .field(#field_str, &self.#field_name)
                        }
                    });
                    
                    quote! {
                        impl std::fmt::Debug for #name {
                            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                f.debug_struct(stringify!(#name))
                                    #(#field_debugs)*
                                    .finish()
                            }
                        }
                    }
                }
                Fields::Unnamed(fields) => {
                    let field_debugs = (0..fields.unnamed.len()).map(|i| {
                        let index = syn::Index::from(i);
                        quote! { .field(&self.#index) }
                    });
                    
                    quote! {
                        impl std::fmt::Debug for #name {
                            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                f.debug_tuple(stringify!(#name))
                                    #(#field_debugs)*
                                    .finish()
                            }
                        }
                    }
                }
                Fields::Unit => {
                    quote! {
                        impl std::fmt::Debug for #name {
                            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                                write!(f, "{}", stringify!(#name))
                            }
                        }
                    }
                }
            }
        }
        Data::Enum(data) => {
            let variants = data.variants.iter().map(|v| {
                let variant_name = &v.ident;
                match &v.fields {
                    Fields::Unit => quote! {
                        #name::#variant_name => write!(f, "{}::{}", stringify!(#name), stringify!(#variant_name))
                    },
                    _ => quote! {
                        #name::#variant_name(..) => write!(f, "{}::{}(..)", stringify!(#name), stringify!(#variant_name))
                    },
                }
            });
            
            quote! {
                impl std::fmt::Debug for #name {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        match self {
                            #(#variants),*
                        }
                    }
                }
            }
        }
        Data::Union(_) => {
            return syn::Error::new_spanned(&input, "CustomDebug does not support unions")
                .to_compile_error()
                .into();
        }
    };
    
    TokenStream::from(debug_impl)
}
```

---

## 3. 属性宏示例

### 示例 3.1: 性能监控宏

```rust
#[proc_macro_attribute]
pub fn monitor(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let fn_name = &input.sig.ident;
    let fn_vis = &input.vis;
    let fn_sig = &input.sig;
    let fn_block = &input.block;
    
    // 解析属性参数（可选的监控级别）
    let level = if attr.is_empty() {
        quote! { "INFO" }
    } else {
        let level_str = parse_macro_input!(attr as LitStr);
        quote! { #level_str }
    };
    
    let expanded = quote! {
        #fn_vis #fn_sig {
            let __start = std::time::Instant::now();
            let __result = {
                #fn_block
            };
            let __duration = __start.elapsed();
            
            eprintln!(
                "[{}] Function {} took {:?}",
                #level,
                stringify!(#fn_name),
                __duration
            );
            
            __result
        }
    };
    
    TokenStream::from(expanded)
}

// 使用示例
#[monitor]
fn slow_function() {
    std::thread::sleep(std::time::Duration::from_millis(100));
}

#[monitor("DEBUG")]
fn another_function() -> i32 {
    42
}
```

### 示例 3.2: 缓存宏

```rust
use std::collections::HashMap;
use std::sync::Mutex;

#[proc_macro_attribute]
pub fn cached(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let fn_name = &input.sig.ident;
    let fn_vis = &input.vis;
    let fn_sig = &input.sig;
    let fn_block = &input.block;
    
    // 生成缓存键的类型
    let cache_name = syn::Ident::new(
        &format!("__CACHE_{}", fn_name.to_string().to_uppercase()),
        fn_name.span()
    );
    
    let expanded = quote! {
        lazy_static::lazy_static! {
            static ref #cache_name: Mutex<HashMap<String, _>> = 
                Mutex::new(HashMap::new());
        }
        
        #fn_vis #fn_sig {
            // 生成缓存键（简化版，实际应基于参数）
            let cache_key = format!("{}", stringify!(#fn_name));
            
            // 检查缓存
            if let Ok(cache) = #cache_name.lock() {
                if let Some(cached) = cache.get(&cache_key) {
                    return cached.clone();
                }
            }
            
            // 执行原函数
            let result = {
                #fn_block
            };
            
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

---

## 4. 函数式宏示例

### 示例 4.1: SQL查询宏

```rust
use syn::parse::{Parse, ParseStream};
use syn::{Ident, Token, LitStr};

struct SqlQuery {
    select: Vec<Ident>,
    from: Ident,
    where_clause: Option<SqlWhere>,
}

struct SqlWhere {
    field: Ident,
    _eq: Token![=],
    value: syn::Expr,
}

impl Parse for SqlQuery {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // SELECT
        input.parse::<kw::SELECT>()?;
        let mut select = vec![input.parse()?];
        while input.peek(Token![,]) {
            input.parse::<Token![,]>()?;
            select.push(input.parse()?);
        }
        
        // FROM
        input.parse::<kw::FROM>()?;
        let from = input.parse()?;
        
        // WHERE (optional)
        let where_clause = if input.peek(kw::WHERE) {
            input.parse::<kw::WHERE>()?;
            Some(SqlWhere {
                field: input.parse()?,
                _eq: input.parse()?,
                value: input.parse()?,
            })
        } else {
            None
        };
        
        Ok(SqlQuery { select, from, where_clause })
    }
}

mod kw {
    syn::custom_keyword!(SELECT);
    syn::custom_keyword!(FROM);
    syn::custom_keyword!(WHERE);
}

#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let query = parse_macro_input!(input as SqlQuery);
    
    let select_fields = &query.select;
    let table = &query.from;
    
    let where_code = if let Some(w) = &query.where_clause {
        let field = &w.field;
        let value = &w.value;
        quote! {
            .filter(|row| row.#field == #value)
        }
    } else {
        quote! {}
    };
    
    let expanded = quote! {
        {
            let mut result = Vec::new();
            for row in database.table(stringify!(#table)).rows() {
                result.push((#(row.#select_fields),*));
            }
            result #where_code
        }
    };
    
    TokenStream::from(expanded)
}

// 使用示例
/*
let users = sql!(SELECT id, name FROM users WHERE active = true);
*/
```

### 示例 4.2: HTML模板宏

```rust
#[proc_macro]
pub fn html(input: TokenStream) -> TokenStream {
    let html_str = input.to_string();
    
    // 简化的HTML解析和验证
    let expanded = quote! {
        {
            let mut buffer = String::new();
            buffer.push_str(&format!(#html_str));
            buffer
        }
    };
    
    TokenStream::from(expanded)
}

// 使用示例
/*
let page = html! {
    <html>
        <body>
            <h1>Title</h1>
            <p>Content</p>
        </body>
    </html>
};
*/
```

---

## 5. 综合应用示例

### 示例 5.1: API路由注册系统

```rust
// 声明宏：定义路由
#[macro_export]
macro_rules! routes {
    (
        $(
            $method:ident $path:literal => $handler:path
        ),* $(,)?
    ) => {
        {
            vec![
                $(
                    Route {
                        method: Method::$method,
                        path: $path.to_string(),
                        handler: Box::new($handler),
                    }
                ),*
            ]
        }
    };
}

// 属性宏：自动提取参数
#[proc_macro_attribute]
pub fn handler(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    // 实现自动参数提取...
    TokenStream::from(quote! { #input })
}

// 使用
/*
let app_routes = routes! {
    GET "/users" => list_users,
    POST "/users" => create_user,
    GET "/users/:id" => get_user,
};

#[handler]
fn list_users(req: Request) -> Response {
    // ...
}
*/
```

---

**文档版本**: v1.0  
**适用版本**: Rust 1.90+  
**最后更新**: 2025-10-20

---

## 返回导航

- [返回特性目录](README.md)
- [完整特性清单](COMPREHENSIVE_FEATURES.md)
- [返回主索引](../00_MASTER_INDEX.md)
