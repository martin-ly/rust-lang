# 函数式宏详解

> **文档定位**: 深入理解和实现Rust函数式宏  
> **难度级别**: ⭐⭐⭐ 高级  
> **预计时间**: 2.5小时  
> **最后更新**: 2025-10-20

---

## 📋 学习目标

完成本章后，你将能够：

- ✅ 理解函数式宏的特点
- ✅ 实现自定义函数式宏
- ✅ 处理复杂的输入语法
- ✅ 与macro_rules!对比
- ✅ 构建DSL（领域特定语言）

---

## 1. 函数式宏基础

### 1.1 什么是函数式宏

**函数式宏 (Function-like Macros)** 看起来像函数调用，但在编译时展开。

```rust
// 调用方式类似函数
let sql = sql!(SELECT * FROM users WHERE id = 1);
let html = html!(<div>Hello, World!</div>);
let json = json!({"name": "Alice", "age": 25});
```

### 1.2 与macro_rules!的区别

| 特性 | macro_rules! | 函数式宏 |
|------|--------------|----------|
| **定义** | `macro_rules!` | `#[proc_macro]` |
| **解析** | 模式匹配 | 完整的Rust代码 |
| **能力** | 受限 | 强大 |
| **crate** | 同一crate | 独立crate |
| **错误** | 简单 | 详细 |

### 1.3 常见函数式宏

```rust
// sqlx
let query = query!("SELECT * FROM users");

// html-macro
let page = html! {
    <html>
        <body><h1>Hello</h1></body>
    </html>
};

// quote
let tokens = quote! {
    impl MyTrait for MyStruct {}
};
```

---

## 2. 实现第一个函数式宏

### 2.1 基本结构

```rust
use proc_macro::TokenStream;
use quote::quote;

#[proc_macro]
pub fn hello(input: TokenStream) -> TokenStream {
    // input: 宏的输入
    // 返回: 生成的代码
    
    let expanded = quote! {
        println!("Hello from function-like macro!");
    };
    
    TokenStream::from(expanded)
}
```

### 2.2 使用函数式宏

```rust
use my_macro::hello;

fn main() {
    hello!(); // 输出: Hello from function-like macro!
}
```

---

## 3. 解析输入

### 3.1 简单输入

```rust
use syn::{parse::Parse, parse::ParseStream, LitStr};

struct MacroInput {
    message: LitStr,
}

impl Parse for MacroInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(MacroInput {
            message: input.parse()?,
        })
    }
}

#[proc_macro]
pub fn greet(input: TokenStream) -> TokenStream {
    let MacroInput { message } = parse_macro_input!(input as MacroInput);
    
    let expanded = quote! {
        println!("Greeting: {}", #message);
    };
    
    TokenStream::from(expanded)
}

// 使用
greet!("Hello, World!");
```

### 3.2 复杂输入

```rust
use syn::{Token, Ident, punctuated::Punctuated};

struct KeyValuePairs {
    pairs: Punctuated<KeyValue, Token![,]>,
}

struct KeyValue {
    key: Ident,
    _colon: Token![:],
    value: syn::Expr,
}

impl Parse for KeyValuePairs {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(KeyValuePairs {
            pairs: input.parse_terminated(KeyValue::parse)?,
        })
    }
}

impl Parse for KeyValue {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(KeyValue {
            key: input.parse()?,
            _colon: input.parse()?,
            value: input.parse()?,
        })
    }
}

#[proc_macro]
pub fn config(input: TokenStream) -> TokenStream {
    let KeyValuePairs { pairs } = parse_macro_input!(input as KeyValuePairs);
    
    let assignments: Vec<_> = pairs.iter().map(|kv| {
        let key = &kv.key;
        let value = &kv.value;
        quote! {
            config.#key = #value;
        }
    }).collect();
    
    let expanded = quote! {
        {
            let mut config = Config::default();
            #(#assignments)*
            config
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
let cfg = config! {
    host: "localhost",
    port: 8080,
    timeout: 30
};
```

---

## 4. 构建DSL

### 4.1 SQL DSL

```rust
use syn::{Ident, Token};

enum SqlStatement {
    Select(SelectStmt),
    Insert(InsertStmt),
    Update(UpdateStmt),
}

struct SelectStmt {
    fields: Vec<Ident>,
    table: Ident,
    condition: Option<syn::Expr>,
}

impl Parse for SqlStatement {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let lookahead = input.lookahead1();
        
        if lookahead.peek(kw::SELECT) {
            input.parse::<kw::SELECT>()?;
            // 解析SELECT语句
            Ok(SqlStatement::Select(input.parse()?))
        } else if lookahead.peek(kw::INSERT) {
            input.parse::<kw::INSERT>()?;
            // 解析INSERT语句
            Ok(SqlStatement::Insert(input.parse()?))
        } else {
            Err(lookahead.error())
        }
    }
}

#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let stmt = parse_macro_input!(input as SqlStatement);
    
    match stmt {
        SqlStatement::Select(select) => {
            let fields = &select.fields;
            let table = &select.table;
            
            let expanded = quote! {
                Query::new()
                    .select(&[#(stringify!(#fields)),*])
                    .from(stringify!(#table))
            };
            
            TokenStream::from(expanded)
        }
        _ => unimplemented!(),
    }
}

// 使用
let query = sql!(SELECT id, name FROM users WHERE id = 1);
```

### 4.2 HTML DSL

```rust
enum HtmlElement {
    Tag {
        name: Ident,
        attrs: Vec<HtmlAttr>,
        children: Vec<HtmlElement>,
    },
    Text(LitStr),
}

struct HtmlAttr {
    name: Ident,
    value: LitStr,
}

#[proc_macro]
pub fn html(input: TokenStream) -> TokenStream {
    let element = parse_macro_input!(input as HtmlElement);
    
    fn generate_element(elem: &HtmlElement) -> proc_macro2::TokenStream {
        match elem {
            HtmlElement::Tag { name, attrs, children } => {
                let attr_code: Vec<_> = attrs.iter().map(|attr| {
                    let name = &attr.name;
                    let value = &attr.value;
                    quote! {
                        el.attr(stringify!(#name), #value);
                    }
                }).collect();
                
                let children_code: Vec<_> = children.iter()
                    .map(generate_element)
                    .collect();
                
                quote! {
                    {
                        let mut el = Element::new(stringify!(#name));
                        #(#attr_code)*
                        #(el.append_child(#children_code);)*
                        el
                    }
                }
            }
            HtmlElement::Text(text) => {
                quote! { TextNode::new(#text) }
            }
        }
    }
    
    let code = generate_element(&element);
    TokenStream::from(code)
}

// 使用
let page = html! {
    <div class="container">
        <h1>Title</h1>
        <p>Content</p>
    </div>
};
```

---

## 5. 实用示例

### 5.1 JSON构建器

```rust
#[proc_macro]
pub fn json(input: TokenStream) -> TokenStream {
    let value = parse_macro_input!(input as JsonValue);
    
    let code = generate_json(&value);
    
    TokenStream::from(quote! {
        {
            use serde_json::json;
            #code
        }
    })
}

// 使用
let data = json!({
    "name": "Alice",
    "age": 25,
    "tags": ["rust", "programming"]
});
```

### 5.2 测试数据生成器

```rust
#[proc_macro]
pub fn test_data(input: TokenStream) -> TokenStream {
    let spec = parse_macro_input!(input as DataSpec);
    
    let generators: Vec<_> = spec.fields.iter().map(|field| {
        let name = &field.name;
        let ty = &field.ty;
        
        quote! {
            #name: generate_#ty()
        }
    }).collect();
    
    let expanded = quote! {
        TestData {
            #(#generators),*
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
let data = test_data! {
    name: String,
    age: u32,
    email: Email
};
```

### 5.3 路由定义器

```rust
#[proc_macro]
pub fn routes(input: TokenStream) -> TokenStream {
    let routes = parse_macro_input!(input as RouteList);
    
    let route_items: Vec<_> = routes.routes.iter().map(|route| {
        let method = &route.method;
        let path = &route.path;
        let handler = &route.handler;
        
        quote! {
            Route::new(Method::#method, #path, #handler)
        }
    }).collect();
    
    let expanded = quote! {
        vec![
            #(#route_items),*
        ]
    };
    
    TokenStream::from(expanded)
}

// 使用
let app_routes = routes! {
    GET "/" => index,
    GET "/users" => list_users,
    POST "/users" => create_user,
    GET "/users/:id" => get_user
};
```

---

## 6. 错误处理

### 6.1 语法错误

```rust
use syn::Error;

impl Parse for MyInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        if input.is_empty() {
            return Err(Error::new(
                input.span(),
                "宏不能为空\n\
                 示例: my_macro!(value)"
            ));
        }
        
        // 解析逻辑
        let value: LitStr = input.parse()?;
        
        if !input.is_empty() {
            return Err(Error::new(
                input.span(),
                "预期宏结束，但发现多余的token"
            ));
        }
        
        Ok(MyInput { value })
    }
}
```

### 6.2 语义错误

```rust
#[proc_macro]
pub fn validate_sql(input: TokenStream) -> TokenStream {
    let stmt = parse_macro_input!(input as SqlStatement);
    
    // 验证SQL语义
    if let SqlStatement::Select(select) = &stmt {
        if select.fields.is_empty() {
            return Error::new_spanned(
                &stmt,
                "SELECT语句必须至少有一个字段"
            ).to_compile_error().into();
        }
        
        // 检查保留字
        for field in &select.fields {
            if is_reserved_keyword(field) {
                return Error::new_spanned(
                    field,
                    format!("'{}' 是SQL保留字", field)
                ).to_compile_error().into();
            }
        }
    }
    
    // 生成代码
    generate_sql(&stmt)
}
```

---

## 7. 高级技巧

### 7.1 延迟求值

```rust
#[proc_macro]
pub fn lazy_eval(input: TokenStream) -> TokenStream {
    let expr = parse_macro_input!(input as syn::Expr);
    
    let expanded = quote! {
        {
            static ONCE: std::sync::Once = std::sync::Once::new();
            static mut VALUE: Option<_> = None;
            
            ONCE.call_once(|| unsafe {
                VALUE = Some(#expr);
            });
            
            unsafe { VALUE.as_ref().unwrap() }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用
let config = lazy_eval!(expensive_computation());
```

### 7.2 编译时计算

```rust
#[proc_macro]
pub fn const_eval(input: TokenStream) -> TokenStream {
    let expr = parse_macro_input!(input as syn::Expr);
    
    // 尝试在编译时求值
    match evaluate_at_compile_time(&expr) {
        Ok(result) => {
            quote! { #result }.into()
        }
        Err(_) => {
            // 回退到运行时
            quote! { #expr }.into()
        }
    }
}
```

---

## 8. 测试

### 8.1 宏输出测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_json_macro() {
        let input = quote! {
            {"name": "Alice", "age": 25}
        };
        
        let output = json(input.into());
        let output_str = output.to_string();
        
        assert!(output_str.contains("name"));
        assert!(output_str.contains("Alice"));
    }
}
```

### 8.2 集成测试

```rust
// tests/function_macro.rs
use my_macro::json;

#[test]
fn test_json_works() {
    let data = json!({
        "name": "Alice",
        "age": 25
    });
    
    assert_eq!(data["name"], "Alice");
    assert_eq!(data["age"], 25);
}
```

---

## 📚 总结

### 关键概念

1. **TokenStream解析** - 自定义输入语法
2. **DSL构建** - 领域特定语言
3. **代码生成** - 转换为Rust代码
4. **错误处理** - 友好的编译错误
5. **语义验证** - 编译时检查

### 核心技能

- ✅ 实现函数式宏
- ✅ 解析复杂输入
- ✅ 构建DSL
- ✅ 生成类型安全代码
- ✅ 错误处理

### 下一步

- 📖 学习 [TokenStream详解](./05_token_streams.md)
- 📖 回顾 [过程宏基础](./01_proc_macro_basics.md)
- 📖 实践 DSL构建项目

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT

