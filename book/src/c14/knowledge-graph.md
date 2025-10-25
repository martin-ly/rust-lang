# 知识图谱

本页展示宏系统的概念关系。

---

## 📊 核心概念关系图

```text
                    [Rust宏系统]
                         |
         +---------------+---------------+
         |               |               |
     [声明宏]       [过程宏]         [元编程]
         |               |               |
    +----+----+     +----+----+     +----+----+
    |    |    |     |    |    |     |    |    |
  模式  递归  卫生   派生  属性  DSL  代码  编译时
  匹配  展开  性    宏    宏    生成  生成  计算
                  函数式宏
```

---

## 🎯 概念层次

### 1. 声明宏 (Declarative Macros)

**macro_rules!**:

- **模式匹配**: 类似match表达式
- **重复**: `$(...)` 语法
- **分隔符**: `,`, `;` 等
- **片段指定符**: `expr`, `ident`, `ty`, `pat` 等

**特性**:

- **卫生性** (Hygiene): 避免名称冲突
- **递归展开**: 宏调用宏
- **编译时执行**: 零运行时开销

**常见模式**:

- DSL构建
- 重复代码消除
- 语法糖实现

---

### 2. 过程宏 (Procedural Macros)

**派生宏** (Derive Macros):

- **自动实现trait**: `#[derive(Debug, Clone)]`
- **代码生成**: 基于结构体生成代码
- **自定义派生**: 扩展derive功能

**属性宏** (Attribute Macros):

- **函数装饰**: `#[attribute]`
- **代码转换**: 修改输入代码
- **AOP实现**: 面向切面编程

**函数式宏** (Function-like Macros):

- **类似函数调用**: `macro!()`
- **任意输入**: 不限于item
- **自由代码生成**: 完全控制输出

**实现基础**:

- **TokenStream**: 词法单元流
- **syn**: 语法解析
- **quote**: 代码生成

---

### 3. 元编程 (Metaprogramming)

**编译时计算**:

- **const fn**: 编译时函数
- **const generics**: 编译时泛型
- **type-level计算**: 类型级编程

**代码生成**:

- **build脚本**: build.rs
- **宏展开**: 编译时代码生成
- **代码模板**: 重复代码生成

**DSL构建**:

- **内部DSL**: 使用宏扩展语法
- **外部DSL**: 独立语言
- **类型安全**: 编译时检查

---

## 🔗 概念关联

### 声明宏 ←→ 模式匹配

```rust
// 向量创建宏
macro_rules! vec_of {
    // 单一值重复N次
    ($elem:expr; $n:expr) => {
        {
            let mut v = Vec::new();
            for _ in 0..$n {
                v.push($elem);
            }
            v
        }
    };
    
    // 可变数量的值
    ($($x:expr),+ $(,)?) => {
        {
            let mut v = Vec::new();
            $(
                v.push($x);
            )+
            v
        }
    };
}

// 使用示例
let v1 = vec_of![0; 5];           // [0, 0, 0, 0, 0]
let v2 = vec_of![1, 2, 3, 4, 5];  // [1, 2, 3, 4, 5]
```

### 派生宏 ←→ 自动实现

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

// 派生宏定义
#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = format!("{}Builder", name);
    let builder_ident = syn::Ident::new(&builder_name, name.span());
    
    // 提取字段
    let fields = if let syn::Data::Struct(data) = &input.data {
        &data.fields
    } else {
        panic!("Builder只能用于结构体");
    };
    
    // 生成builder字段
    let builder_fields = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! { #name: Option<#ty> }
    });
    
    // 生成setter方法
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
    
    // 生成build方法
    let build_fields = fields.iter().map(|f| {
        let name = &f.ident;
        quote! {
            #name: self.#name.ok_or(concat!(stringify!(#name), " is required"))?
        }
    });
    
    // 生成最终代码
    let expanded = quote! {
        pub struct #builder_ident {
            #(#builder_fields,)*
        }
        
        impl #builder_ident {
            pub fn new() -> Self {
                Self {
                    #(#name: None,)*
                }
            }
            
            #(#setters)*
            
            pub fn build(self) -> Result<#name, String> {
                Ok(#name {
                    #(#build_fields,)*
                })
            }
        }
        
        impl #name {
            pub fn builder() -> #builder_ident {
                #builder_ident::new()
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用示例
#[derive(Builder)]
struct Config {
    host: String,
    port: u16,
}

// 自动生成
let config = Config::builder()
    .host("localhost".to_string())
    .port(8080)
    .build()
    .unwrap();
```

### 属性宏 ←→ AOP

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

// 计时属性宏
#[proc_macro_attribute]
pub fn timed(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let fn_name = &input.sig.ident;
    let fn_block = &input.block;
    let fn_sig = &input.sig;
    
    let expanded = quote! {
        #fn_sig {
            let start = std::time::Instant::now();
            let result = (|| #fn_block)();
            let duration = start.elapsed();
            println!("{} took {:?}", stringify!(#fn_name), duration);
            result
        }
    };
    
    TokenStream::from(expanded)
}

// 使用示例
#[timed]
fn expensive_operation() {
    std::thread::sleep(std::time::Duration::from_millis(100));
}
```

---

## 📚 学习路径图

```text
第一步: 理解宏的基本概念
    ↓
第二步: 掌握声明宏(macro_rules!)
    ↓
第三步: 学习过程宏(derive, attribute, function-like)
    ↓
第四步: 实现DSL和代码生成
    ↓
第五步: 宏调试与优化
```

---

## 🎓 宏类型对比

### 宏分类

| 类型 | 语法 | 复杂度 | 功能 |
|------|------|--------|------|
| **声明宏** | `macro_rules!` | 低-中 | 模式匹配 |
| **派生宏** | `#[derive(...)]` | 中 | trait实现 |
| **属性宏** | `#[attr]` | 中-高 | 代码装饰 |
| **函数式宏** | `macro!()` | 高 | 自由生成 |

### 使用场景

| 场景 | 推荐宏类型 | 示例 |
|------|-----------|------|
| **简单重复** | 声明宏 | vec!, println! |
| **trait实现** | 派生宏 | #[derive(Debug)] |
| **代码装饰** | 属性宏 | #[async_trait], #[timed] |
| **DSL** | 函数式宏 | html!, sql! |

---

## 💡 核心原则

### 1. 卫生性优先

```text
卫生宏 → 避免名称冲突 → 安全展开
```

### 2. 编译时计算

```text
宏展开 → 编译时生成 → 零运行时开销
```

### 3. 类型安全

```text
语法检查 → 类型检查 → 编译时错误
```

---

## 🔍 Rust 1.90 增强特性

### 1. 声明宏改进

```rust
// 使用$crate避免路径问题
#[macro_export]
macro_rules! my_vec {
    ($($x:expr),*) => {
        {
            let mut v = $crate::Vec::new();
            $(
                v.push($x);
            )*
            v
        }
    };
}

// 使用片段指定符
macro_rules! create_function {
    ($func_name:ident, $return_type:ty) => {
        fn $func_name() -> $return_type {
            Default::default()
        }
    };
}

create_function!(get_num, i32);
create_function!(get_string, String);
```

### 2. 过程宏工具链

```rust
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{parse_macro_input, DeriveInput, Data, Fields};

#[proc_macro_derive(Getters)]
pub fn derive_getters(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let getters = if let Data::Struct(data) = &input.data {
        if let Fields::Named(fields) = &data.fields {
            fields.named.iter().map(|f| {
                let field_name = f.ident.as_ref().unwrap();
                let field_type = &f.ty;
                let getter_name = format_ident!("get_{}", field_name);
                
                quote! {
                    pub fn #getter_name(&self) -> &#field_type {
                        &self.#field_name
                    }
                }
            }).collect::<Vec<_>>()
        } else {
            vec![]
        }
    } else {
        vec![]
    };
    
    let expanded = quote! {
        impl #name {
            #(#getters)*
        }
    };
    
    TokenStream::from(expanded)
}
```

### 3. DSL构建

```rust
// 构建SQL查询DSL
macro_rules! select {
    ($($col:ident),+ from $table:ident where $condition:expr) => {
        {
            let cols = vec![$(stringify!($col)),+];
            let table = stringify!($table);
            let condition = $condition;
            
            format!(
                "SELECT {} FROM {} WHERE {}",
                cols.join(", "),
                table,
                condition
            )
        }
    };
}

// 使用
let query = select!(id, name, email from users where "age > 18");
// "SELECT id, name, email FROM users WHERE age > 18"
```

---

## 📖 相关章节

- **[基础概念](./foundations.md)** - 宏理论基础
- **[实践指南](./guides.md)** - 宏编写技巧
- **[代码示例](./examples.md)** - 完整实现 ⭐
- **[返回模块首页](./README.md)**

---

## 🔗 扩展学习

### 深入阅读

- [Rust宏完整指南](../../crates/c14_macro_system/README.md)
- [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/)
- [Procedural Macros Workshop](https://github.com/dtolnay/proc-macro-workshop)

### 相关模块

- **[C02: 类型系统](../c02/README.md)** - 类型级编程
- **[C04: 泛型编程](../c04/README.md)** - 泛型与宏
- **[C09: 设计模式](../c09/README.md)** - 宏模式

---

## 🎯 实践项目建议

### 入门级

- 简单声明宏
- derive宏实现
- 属性宏示例

### 进阶级

- 自定义DSL
- 代码生成工具
- 宏库开发

### 高级

- 编译器插件
- 语言扩展
- 形式化验证

---

## 🛠️ 宏调试技巧

### 展开宏

```bash
# 查看宏展开结果
cargo expand

# 展开特定模块
cargo expand --lib module_name

# 展开特定函数
cargo expand function_name
```

### 调试技巧

```rust
// 打印宏输入
#[proc_macro]
pub fn debug_macro(input: TokenStream) -> TokenStream {
    eprintln!("Input: {}", input);
    input
}

// 使用trace_macros
#![feature(trace_macros)]

fn main() {
    trace_macros!(true);
    println!("Hello");
    trace_macros!(false);
}
```

---

## 📊 宏系统层次

```text
高层抽象:  DSL, 代码生成
    ↓
宏层:      声明宏, 过程宏
    ↓
语法层:    TokenStream, syn, quote
    ↓
编译器:    rustc宏展开
```

---

**掌握宏系统是Rust元编程的关键！** 🚀
