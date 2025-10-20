# 代码生成高级技术

> **学习目标**：掌握使用宏进行高级代码生成的技术，包括模式、策略和最佳实践。

---

## 📖 目录

- [代码生成高级技术](#代码生成高级技术)
  - [📖 目录](#-目录)
  - [代码生成基础](#代码生成基础)
    - [什么是代码生成？](#什么是代码生成)
    - [代码生成的层次](#代码生成的层次)
    - [代码生成的优势](#代码生成的优势)
  - [声明式代码生成](#声明式代码生成)
    - [基本模式](#基本模式)
      - [1. 重复展开模式](#1-重复展开模式)
      - [2. 类型派生模式](#2-类型派生模式)
      - [3. 代码块生成](#3-代码块生成)
    - [高级模式](#高级模式)
      - [1. 嵌套代码生成](#1-嵌套代码生成)
      - [2. 条件代码生成](#2-条件代码生成)
  - [过程宏代码生成](#过程宏代码生成)
    - [Derive 宏生成](#derive-宏生成)
      - [完整的 Builder 生成器](#完整的-builder-生成器)
      - [使用示例](#使用示例)
    - [Attribute 宏生成](#attribute-宏生成)
      - [性能监控宏](#性能监控宏)
      - [使用示例1](#使用示例1)
    - [Function-like 宏生成](#function-like-宏生成)
      - [SQL 查询生成器](#sql-查询生成器)
  - [代码模板系统](#代码模板系统)
    - [模板引擎设计](#模板引擎设计)
    - [模板组合](#模板组合)
  - [类型驱动生成](#类型驱动生成)
    - [基于类型信息的代码生成](#基于类型信息的代码生成)
    - [泛型代码生成](#泛型代码生成)
  - [元数据驱动生成](#元数据驱动生成)
    - [属性解析](#属性解析)
    - [配置驱动生成](#配置驱动生成)
  - [增量代码生成](#增量代码生成)
    - [条件编译](#条件编译)
    - [特性门控](#特性门控)
  - [代码生成优化](#代码生成优化)
    - [1. 减少生成代码量](#1-减少生成代码量)
    - [2. 避免重复生成](#2-避免重复生成)
    - [3. 延迟生成](#3-延迟生成)
  - [实战案例](#实战案例)
    - [案例1：ORM 代码生成](#案例1orm-代码生成)
    - [案例2：API 路由生成](#案例2api-路由生成)
    - [案例3：状态机生成](#案例3状态机生成)
  - [最佳实践](#最佳实践)
    - [1. 保持生成代码的可读性](#1-保持生成代码的可读性)
    - [2. 提供清晰的错误消息](#2-提供清晰的错误消息)
    - [3. 文档化生成的代码](#3-文档化生成的代码)
    - [4. 测试生成器](#4-测试生成器)
  - [总结](#总结)
  - [相关资源](#相关资源)

---

## 代码生成基础

### 什么是代码生成？

代码生成是在编译时自动创建 Rust 代码的过程：

```rust
// 输入：高层次抽象
#[derive(Builder)]
struct Config {
    host: String,
    port: u16,
}

// 输出：生成的代码
impl Config {
    fn builder() -> ConfigBuilder { /* ... */ }
}

struct ConfigBuilder { /* ... */ }
impl ConfigBuilder {
    fn host(mut self, host: String) -> Self { /* ... */ }
    fn port(mut self, port: u16) -> Self { /* ... */ }
    fn build(self) -> Config { /* ... */ }
}
```

### 代码生成的层次

```text
┌─────────────────────────────────┐
│  高层抽象（用户输入）             │
│  - 简洁的语法                    │
│  - 声明式表达                    │
└─────────────────────────────────┘
             ↓
┌─────────────────────────────────┐
│  代码生成器（宏）                 │
│  - 解析输入                      │
│  - 应用规则                      │
│  - 生成代码                      │
└─────────────────────────────────┘
             ↓
┌─────────────────────────────────┐
│  低层实现（生成的代码）           │
│  - 完整的实现                    │
│  - 类型安全                      │
│  - 性能优化                      │
└─────────────────────────────────┘
```

### 代码生成的优势

1. **减少样板代码**：自动生成重复性代码
2. **类型安全**：编译时保证类型正确性
3. **一致性**：统一的代码风格和模式
4. **可维护性**：单点修改，全局生效
5. **性能**：编译时处理，零运行时开销

---

## 声明式代码生成

### 基本模式

#### 1. 重复展开模式

```rust
macro_rules! repeat_n {
    ($n:expr, $code:expr) => {{
        let mut result = Vec::new();
        for _ in 0..$n {
            result.push($code);
        }
        result
    }};
}

// 使用
let values = repeat_n!(5, rand::random::<i32>());
```

#### 2. 类型派生模式

```rust
macro_rules! impl_display {
    ($type:ty) => {
        impl std::fmt::Display for $type {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(f, "{:?}", self)
            }
        }
    };
}

impl_display!(MyStruct);
```

#### 3. 代码块生成

```rust
macro_rules! generate_accessor {
    ($struct_name:ident, $($field:ident: $type:ty),*) => {
        impl $struct_name {
            $(
                pub fn $field(&self) -> &$type {
                    &self.$field
                }
                
                paste::paste! {
                    pub fn [<set_ $field>](&mut self, value: $type) {
                        self.$field = value;
                    }
                }
            )*
        }
    };
}

// 使用
struct User {
    name: String,
    age: u32,
}

generate_accessor!(User, name: String, age: u32);
```

### 高级模式

#### 1. 嵌套代码生成

```rust
macro_rules! generate_nested {
    (
        struct $name:ident {
            $($field:ident: $type:ty),* $(,)?
        }
    ) => {
        // 生成结构体
        struct $name {
            $($field: $type),*
        }
        
        // 生成构造器
        impl $name {
            pub fn new($($field: $type),*) -> Self {
                Self { $($field),* }
            }
        }
        
        // 生成访问器
        impl $name {
            $(
                paste::paste! {
                    pub fn $field(&self) -> &$type {
                        &self.$field
                    }
                    
                    pub fn [<$field _mut>](&mut self) -> &mut $type {
                        &mut self.$field
                    }
                }
            )*
        }
    };
}

// 使用
generate_nested! {
    struct Point {
        x: f64,
        y: f64,
    }
}
```

#### 2. 条件代码生成

```rust
macro_rules! conditional_impl {
    (
        $(#[$attr:meta])*
        $vis:vis struct $name:ident {
            $($field:ident: $type:ty),* $(,)?
        }
        
        $(impl $trait:ident)?
    ) => {
        $(#[$attr])*
        $vis struct $name {
            $($field: $type),*
        }
        
        $(
            impl $trait for $name {
                // 根据trait生成不同实现
            }
        )?
    };
}
```

---

## 过程宏代码生成

### Derive 宏生成

#### 完整的 Builder 生成器

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields};

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = format_ident!("{}Builder", name);
    
    // 提取字段信息
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("Builder only supports named fields"),
        },
        _ => panic!("Builder only supports structs"),
    };
    
    // 生成 Builder 结构体字段（所有字段都是 Option）
    let builder_fields = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! { #name: Option<#ty> }
    });
    
    // 生成 setter 方法
    let setters = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! {
            pub fn #name(mut self, #name: #ty) -> Self {
                self.#name = Some(#name);
                self
            }
        }
    });
    
    // 生成 build 方法
    let build_fields = fields.iter().map(|f| {
        let name = &f.ident;
        quote! {
            #name: self.#name.ok_or(concat!(
                "Field '",
                stringify!(#name),
                "' is required"
            ))?
        }
    });
    
    // 生成完整代码
    let expanded = quote! {
        pub struct #builder_name {
            #(#builder_fields),*
        }
        
        impl #name {
            pub fn builder() -> #builder_name {
                #builder_name {
                    #(#fields: None),*
                }
            }
        }
        
        impl #builder_name {
            #(#setters)*
            
            pub fn build(self) -> Result<#name, &'static str> {
                Ok(#name {
                    #(#build_fields),*
                })
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

#### 使用示例

```rust
#[derive(Builder)]
struct ServerConfig {
    host: String,
    port: u16,
    ssl_enabled: bool,
    max_connections: usize,
}

// 生成的代码可以这样使用：
let config = ServerConfig::builder()
    .host("localhost".to_string())
    .port(8080)
    .ssl_enabled(true)
    .max_connections(1000)
    .build()
    .expect("Failed to build config");
```

### Attribute 宏生成

#### 性能监控宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn timed(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let name = &input.sig.ident;
    let body = &input.block;
    let sig = &input.sig;
    let vis = &input.vis;
    let attrs = &input.attrs;
    
    let expanded = quote! {
        #(#attrs)*
        #vis #sig {
            let _timer = {
                let start = std::time::Instant::now();
                struct Timer<'a> {
                    name: &'a str,
                    start: std::time::Instant,
                }
                impl<'a> Drop for Timer<'a> {
                    fn drop(&mut self) {
                        let duration = self.start.elapsed();
                        eprintln!(
                            "[TIMING] {} took {:.2?}",
                            self.name,
                            duration
                        );
                    }
                }
                Timer {
                    name: stringify!(#name),
                    start,
                }
            };
            
            #body
        }
    };
    
    TokenStream::from(expanded)
}
```

#### 使用示例1

```rust
#[timed]
fn expensive_computation(n: usize) -> u64 {
    (0..n).map(|x| x as u64).sum()
}

// 调用时会自动打印执行时间
expensive_computation(1_000_000);
// 输出: [TIMING] expensive_computation took 2.34ms
```

### Function-like 宏生成

#### SQL 查询生成器

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, parse::Parse, parse::ParseStream, Ident, Token};

struct SqlQuery {
    table: Ident,
    fields: Vec<Ident>,
}

impl Parse for SqlQuery {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        input.parse::<Token![SELECT]>()?;
        
        let mut fields = Vec::new();
        loop {
            fields.push(input.parse::<Ident>()?);
            if input.parse::<Token![,]>().is_err() {
                break;
            }
        }
        
        input.parse::<Token![FROM]>()?;
        let table = input.parse::<Ident>()?;
        
        Ok(SqlQuery { table, fields })
    }
}

#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let query = parse_macro_input!(input as SqlQuery);
    let table = &query.table;
    let fields = &query.fields;
    
    let field_names = fields.iter()
        .map(|f| f.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    
    let expanded = quote! {
        {
            let query = format!(
                "SELECT {} FROM {}",
                #field_names,
                stringify!(#table)
            );
            
            // 生成类型安全的查询结构
            struct Query;
            impl Query {
                fn execute(&self) -> Result<Vec<Row>, Error> {
                    // 执行查询逻辑
                    todo!()
                }
            }
            
            Query
        }
    };
    
    TokenStream::from(expanded)
}
```

---

## 代码模板系统

### 模板引擎设计

```rust
use quote::quote;

pub struct CodeTemplate {
    name: String,
    params: Vec<(String, String)>, // (name, type)
    body: String,
}

impl CodeTemplate {
    pub fn generate(&self) -> proc_macro2::TokenStream {
        let name = format_ident!("{}", self.name);
        
        let params = self.params.iter().map(|(n, t)| {
            let param_name = format_ident!("{}", n);
            let param_type = format_ident!("{}", t);
            quote! { #param_name: #param_type }
        });
        
        quote! {
            pub fn #name(#(#params),*) -> Result<(), Error> {
                // 模板体
            }
        }
    }
}
```

### 模板组合

```rust
pub struct CompositeTemplate {
    templates: Vec<CodeTemplate>,
}

impl CompositeTemplate {
    pub fn add_template(&mut self, template: CodeTemplate) {
        self.templates.push(template);
    }
    
    pub fn generate_all(&self) -> proc_macro2::TokenStream {
        let generated = self.templates
            .iter()
            .map(|t| t.generate());
        
        quote! {
            #(#generated)*
        }
    }
}
```

---

## 类型驱动生成

### 基于类型信息的代码生成

```rust
use syn::{Type, TypePath};

fn generate_serializer(ty: &Type) -> proc_macro2::TokenStream {
    match ty {
        Type::Path(TypePath { path, .. }) => {
            let ident = &path.segments.last().unwrap().ident;
            
            match ident.to_string().as_str() {
                "String" => quote! {
                    fn serialize(&self) -> Vec<u8> {
                        self.as_bytes().to_vec()
                    }
                },
                "i32" | "u32" | "i64" | "u64" => quote! {
                    fn serialize(&self) -> Vec<u8> {
                        self.to_le_bytes().to_vec()
                    }
                },
                _ => quote! {
                    fn serialize(&self) -> Vec<u8> {
                        bincode::serialize(self).unwrap()
                    }
                },
            }
        }
        _ => panic!("Unsupported type"),
    }
}
```

### 泛型代码生成

```rust
fn generate_generic_impl(
    name: &Ident,
    generics: &syn::Generics,
) -> proc_macro2::TokenStream {
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    
    quote! {
        impl #impl_generics MyTrait for #name #ty_generics #where_clause {
            fn process(&self) -> String {
                format!("{:?}", self)
            }
        }
    }
}
```

---

## 元数据驱动生成

### 属性解析

```rust
use syn::{Attribute, Meta, NestedMeta};

fn parse_attributes(attrs: &[Attribute]) -> HashMap<String, String> {
    let mut config = HashMap::new();
    
    for attr in attrs {
        if attr.path.is_ident("config") {
            if let Ok(Meta::List(meta_list)) = attr.parse_meta() {
                for nested in meta_list.nested {
                    if let NestedMeta::Meta(Meta::NameValue(nv)) = nested {
                        if let Some(ident) = nv.path.get_ident() {
                            if let syn::Lit::Str(lit) = &nv.lit {
                                config.insert(
                                    ident.to_string(),
                                    lit.value()
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    
    config
}

// 使用
#[config(db = "postgres", cache = "redis")]
struct AppConfig;
```

### 配置驱动生成

```rust
fn generate_from_config(config: &HashMap<String, String>) -> TokenStream {
    let db_type = config.get("db").unwrap();
    let cache_type = config.get("cache").unwrap();
    
    let db_impl = match db_type.as_str() {
        "postgres" => quote! {
            use sqlx::PgPool;
            type DbPool = PgPool;
        },
        "mysql" => quote! {
            use sqlx::MySqlPool;
            type DbPool = MySqlPool;
        },
        _ => panic!("Unsupported database"),
    };
    
    let cache_impl = match cache_type.as_str() {
        "redis" => quote! {
            use redis::Client as CacheClient;
        },
        "memcached" => quote! {
            use memcache::Client as CacheClient;
        },
        _ => panic!("Unsupported cache"),
    };
    
    quote! {
        #db_impl
        #cache_impl
        
        pub struct App {
            db: DbPool,
            cache: CacheClient,
        }
    }
    .into()
}
```

---

## 增量代码生成

### 条件编译

```rust
#[proc_macro_attribute]
pub fn conditional_generate(attr: TokenStream, item: TokenStream) -> TokenStream {
    let condition = attr.to_string();
    let input = parse_macro_input!(item as ItemStruct);
    
    let expanded = if condition == "debug" {
        quote! {
            #[cfg(debug_assertions)]
            #input
        }
    } else {
        quote! {
            #[cfg(not(debug_assertions))]
            #input
        }
    };
    
    TokenStream::from(expanded)
}
```

### 特性门控

```rust
fn generate_with_features(features: &[String]) -> TokenStream {
    let impls = features.iter().map(|feature| {
        let feature_ident = format_ident!("{}", feature);
        quote! {
            #[cfg(feature = #feature)]
            impl MyTrait for #feature_ident {
                fn process(&self) { /* ... */ }
            }
        }
    });
    
    quote! {
        #(#impls)*
    }
    .into()
}
```

---

## 代码生成优化

### 1. 减少生成代码量

```rust
// ❌ 为每个字段生成独立方法
macro_rules! bad_accessors {
    ($($field:ident),*) => {
        $(
            fn $field(&self) -> &String {
                &self.$field
            }
        )*
    };
}

// ✅ 使用泛型减少代码
macro_rules! good_accessors {
    ($($field:ident: $ty:ty),*) => {
        fn get<T>(&self, name: &str) -> Option<&T> {
            match name {
                $(stringify!($field) => Some(&self.$field as &T),)*
                _ => None,
            }
        }
    };
}
```

### 2. 避免重复生成

```rust
// 使用缓存机制
static GENERATED_CODE: Lazy<HashMap<String, TokenStream>> = 
    Lazy::new(HashMap::new);

#[proc_macro_derive(Cached)]
pub fn cached_derive(input: TokenStream) -> TokenStream {
    let input_str = input.to_string();
    
    if let Some(cached) = GENERATED_CODE.get(&input_str) {
        return cached.clone();
    }
    
    let generated = generate_code(&input);
    GENERATED_CODE.insert(input_str, generated.clone());
    generated
}
```

### 3. 延迟生成

```rust
// 只在需要时生成代码
macro_rules! lazy_generate {
    ($name:ident) => {
        mod $name {
            // 使用 include! 延迟加载生成的代码
            include!(concat!(env!("OUT_DIR"), "/", stringify!($name), ".rs"));
        }
    };
}
```

---

## 实战案例

### 案例1：ORM 代码生成

```rust
#[derive(Table)]
#[table(name = "users")]
struct User {
    #[column(primary_key)]
    id: i32,
    
    #[column(unique)]
    email: String,
    
    name: String,
    
    #[column(default = "now()")]
    created_at: DateTime,
}

// 生成的代码：
impl User {
    pub async fn find(id: i32) -> Result<Self, Error> {
        sqlx::query_as!(
            User,
            "SELECT id, email, name, created_at FROM users WHERE id = $1",
            id
        )
        .fetch_one(&pool)
        .await
    }
    
    pub async fn create(&self) -> Result<(), Error> {
        sqlx::query!(
            "INSERT INTO users (email, name) VALUES ($1, $2)",
            self.email,
            self.name
        )
        .execute(&pool)
        .await?;
        Ok(())
    }
}
```

### 案例2：API 路由生成

```rust
#[api_routes]
mod user_api {
    #[get("/users/:id")]
    async fn get_user(id: i32) -> Result<Json<User>, Error> {
        // 处理逻辑
    }
    
    #[post("/users")]
    async fn create_user(body: Json<CreateUser>) -> Result<Json<User>, Error> {
        // 处理逻辑
    }
}

// 生成的代码：
pub fn configure_routes(app: &mut App) {
    app.route("/users/:id", get(get_user))
       .route("/users", post(create_user));
}
```

### 案例3：状态机生成

```rust
state_machine! {
    enum OrderState {
        Pending => Processing | Cancelled,
        Processing => Shipped | Cancelled,
        Shipped => Delivered,
        Delivered => {},
        Cancelled => {},
    }
}

// 生成的代码：
impl OrderState {
    pub fn transition(&mut self, event: Event) -> Result<(), Error> {
        *self = match (&self, event) {
            (Self::Pending, Event::StartProcessing) => Self::Processing,
            (Self::Pending, Event::Cancel) => Self::Cancelled,
            (Self::Processing, Event::Ship) => Self::Shipped,
            // ... 其他转换
            _ => return Err(Error::InvalidTransition),
        };
        Ok(())
    }
}
```

---

## 最佳实践

### 1. 保持生成代码的可读性

```rust
// ✅ 好的实践：格式化生成的代码
let expanded = quote! {
    impl MyStruct {
        pub fn method(&self) -> Result<(), Error> {
            // 清晰的缩进
            if self.check() {
                Ok(())
            } else {
                Err(Error::CheckFailed)
            }
        }
    }
};
```

### 2. 提供清晰的错误消息

```rust
if fields.is_empty() {
    return syn::Error::new(
        input.span(),
        "Struct must have at least one field"
    )
    .to_compile_error()
    .into();
}
```

### 3. 文档化生成的代码

```rust
let expanded = quote! {
    #[doc = "Auto-generated builder for `Config`"]
    pub struct ConfigBuilder {
        // ...
    }
};
```

### 4. 测试生成器

```rust
#[test]
fn test_builder_generation() {
    let input = quote! {
        struct User {
            name: String,
            age: u32,
        }
    };
    
    let output = derive_builder(input.into());
    // 验证生成的代码
}
```

---

## 总结

代码生成是 Rust 宏系统最强大的应用之一：

- **声明式生成**：适合简单的模式和重复
- **过程宏生成**：提供最大的灵活性和控制
- **模板系统**：有助于组织复杂的生成逻辑
- **类型驱动**：利用类型信息生成精确的代码
- **元数据驱动**：通过配置控制生成行为
- **增量生成**：优化编译时间和代码大小

掌握这些技术，你可以构建强大的代码生成工具，大幅提升开发效率！

## 相关资源

- [macro_metaprogramming.md](./macro_metaprogramming.md) - 元编程基础
- [dsl_construction.md](./dsl_construction.md) - DSL 构建技术
- [macro_optimization.md](./macro_optimization.md) - 性能优化
