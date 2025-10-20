# DSL构建实战指南

> **文档定位**: 从零构建领域特定语言完整指南  
> **创建日期**: 2025-10-20  
> **适用版本**: Rust 1.90+ | Edition 2024  
> **文档类型**: 高级主题 + 实战项目

---

## 📊 目录

- [DSL构建实战指南](#dsl构建实战指南)
  - [📊 目录](#-目录)
  - [1. DSL设计原则](#1-dsl设计原则)
    - [1.1 设计目标](#11-设计目标)
    - [1.2 语法风格选择](#12-语法风格选择)
  - [2. 语法设计](#2-语法设计)
    - [2.1 词法分析](#21-词法分析)
    - [2.2 语法分析](#22-语法分析)
  - [3. SQL-like DSL实战](#3-sql-like-dsl实战)
    - [3.1 完整实现](#31-完整实现)
    - [3.2 类型安全查询](#32-类型安全查询)
  - [4. HTML模板DSL](#4-html模板dsl)
    - [4.1 语法设计](#41-语法设计)
    - [4.2 组件系统](#42-组件系统)
  - [5. 配置文件DSL](#5-配置文件dsl)
    - [5.1 声明式配置](#51-声明式配置)
    - [5.2 类型安全配置](#52-类型安全配置)
  - [6. 测试DSL框架](#6-测试dsl框架)
    - [6.1 行为驱动测试](#61-行为驱动测试)
    - [6.2 表格驱动测试](#62-表格驱动测试)
  - [总结](#总结)
  - [相关文档](#相关文档)
  - [返回导航](#返回导航)

---

## 1. DSL设计原则

### 1.1 设计目标

**好的DSL应该**:

- 🎯 **领域特定**: 精确表达领域概念
- 📖 **易读易写**: 接近自然语言
- 🛡️ **类型安全**: 编译时检查
- ⚡ **高性能**: 零开销抽象
- 🔧 **可扩展**: 易于添加新功能

### 1.2 语法风格选择

```rust
// 1. 函数式风格
query()
    .select(&["id", "name"])
    .from("users")
    .where_eq("age", 25)
    .execute();

// 2. 声明式风格
sql! {
    SELECT id, name
    FROM users
    WHERE age = 25
}

// 3. 混合风格
html! {
    <div class="container">
        { for item in items {
            <p>{ item.name }</p>
        }}
    </div>
}
```

---

## 2. 语法设计

### 2.1 词法分析

```rust
/// Token类型定义
#[derive(Debug, Clone)]
pub enum Token {
    // 关键字
    Keyword(Keyword),
    
    // 标识符
    Ident(String),
    
    // 字面量
    Literal(Literal),
    
    // 运算符
    Operator(Operator),
    
    // 分隔符
    Delimiter(Delimiter),
}

#[derive(Debug, Clone)]
pub enum Keyword {
    Select,
    From,
    Where,
    // ...
}

/// 简单词法分析器
pub struct Lexer {
    input: String,
    position: usize,
}

impl Lexer {
    pub fn tokenize(&mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        
        while let Some(token) = self.next_token() {
            tokens.push(token);
        }
        
        tokens
    }
    
    fn next_token(&mut self) -> Option<Token> {
        self.skip_whitespace();
        
        if self.is_at_end() {
            return None;
        }
        
        // 识别关键字
        if let Some(keyword) = self.try_keyword() {
            return Some(Token::Keyword(keyword));
        }
        
        // 识别标识符
        if self.current_char().is_alphabetic() {
            return Some(self.read_identifier());
        }
        
        // 识别数字
        if self.current_char().is_numeric() {
            return Some(self.read_number());
        }
        
        None
    }
}
```

---

### 2.2 语法分析

```rust
/// AST节点
#[derive(Debug)]
pub enum Expr {
    Select {
        columns: Vec<String>,
        from: String,
        where_clause: Option<Box<WhereClause>>,
    },
    BinaryOp {
        left: Box<Expr>,
        op: Operator,
        right: Box<Expr>,
    },
    // ...
}

/// 解析器
pub struct Parser {
    tokens: Vec<Token>,
    current: usize,
}

impl Parser {
    pub fn parse(&mut self) -> Result<Expr, ParseError> {
        self.parse_select()
    }
    
    fn parse_select(&mut self) -> Result<Expr, ParseError> {
        self.expect_keyword(Keyword::Select)?;
        
        let columns = self.parse_column_list()?;
        
        self.expect_keyword(Keyword::From)?;
        let from = self.parse_identifier()?;
        
        let where_clause = if self.check_keyword(Keyword::Where) {
            Some(Box::new(self.parse_where()?))
        } else {
            None
        };
        
        Ok(Expr::Select {
            columns,
            from,
            where_clause,
        })
    }
}
```

---

## 3. SQL-like DSL实战

### 3.1 完整实现

```rust
/// SQL DSL宏
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let query = parse_sql_query(input);
    generate_query_code(query)
}

/// 查询AST
#[derive(Debug)]
pub struct SelectQuery {
    pub columns: Vec<Column>,
    pub table: Table,
    pub where_clause: Option<WhereClause>,
    pub joins: Vec<Join>,
    pub order_by: Vec<OrderBy>,
    pub limit: Option<u64>,
}

/// 代码生成
fn generate_query_code(query: SelectQuery) -> TokenStream {
    let table = &query.table.name;
    let columns = generate_columns(&query.columns);
    let where_sql = generate_where(&query.where_clause);
    
    quote! {
        {
            let mut query = String::from("SELECT ");
            query.push_str(#columns);
            query.push_str(" FROM ");
            query.push_str(#table);
            
            if let Some(where_clause) = #where_sql {
                query.push_str(" WHERE ");
                query.push_str(where_clause);
            }
            
            query
        }
    }.into()
}

/// 使用示例
use sql_dsl::sql;

let query = sql! {
    SELECT id, name, email
    FROM users
    WHERE age > 18
    ORDER BY created_at DESC
    LIMIT 10
};

// 生成的代码：
// "SELECT id, name, email FROM users WHERE age > 18 ORDER BY created_at DESC LIMIT 10"
```

---

### 3.2 类型安全查询

```rust
/// 类型安全的查询构建器
pub struct Query<T> {
    _phantom: PhantomData<T>,
}

pub trait Table {
    type Columns;
}

/// 宏生成表定义
macro_rules! define_table {
    ($name:ident { $($column:ident: $ty:ty),* }) => {
        pub struct $name;
        
        impl Table for $name {
            type Columns = ( $($ty),* );
        }
        
        pub mod [<$name:snake>] {
            $(
                pub struct $column;
            )*
        }
    };
}

// 使用
define_table! {
    Users {
        id: i64,
        name: String,
        email: String,
        age: i32
    }
}

// 类型安全查询
let results = Users::select()
    .columns((users::id, users::name))
    .where_(users::age.gt(18))
    .order_by(users::created_at.desc())
    .limit(10)
    .load(&conn)?;
```

---

## 4. HTML模板DSL

### 4.1 语法设计

```rust
/// HTML宏
#[proc_macro]
pub fn html(input: TokenStream) -> TokenStream {
    let template = parse_html_template(input);
    generate_html_code(template)
}

/// HTML AST
#[derive(Debug)]
pub enum HtmlNode {
    Element {
        tag: String,
        attributes: Vec<(String, String)>,
        children: Vec<HtmlNode>,
    },
    Text(String),
    Expression(Expr),
    ForLoop {
        var: String,
        iter: Expr,
        body: Box<HtmlNode>,
    },
    IfCond {
        condition: Expr,
        then_branch: Box<HtmlNode>,
        else_branch: Option<Box<HtmlNode>>,
    },
}

/// 使用示例
html! {
    <div class="container">
        <h1>{ title }</h1>
        
        { if show_list {
            <ul>
                { for item in items {
                    <li key={ item.id }>
                        <a href={ item.url }>{ item.name }</a>
                    </li>
                }}
            </ul>
        }}
        
        <button onclick={ handle_click }>
            "Click me"
        </button>
    </div>
}
```

---

### 4.2 组件系统

```rust
/// 组件宏
#[proc_macro_attribute]
pub fn component(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);
    
    // 生成组件结构
    let component_name = &func.sig.ident;
    let props = extract_props(&func.sig.inputs);
    
    quote! {
        pub struct #component_name {
            props: #props,
        }
        
        impl Component for #component_name {
            type Props = #props;
            
            fn render(&self) -> Html {
                #func
            }
        }
    }.into()
}

// 使用
#[component]
fn UserCard(name: String, age: u32) -> Html {
    html! {
        <div class="card">
            <h2>{ name }</h2>
            <p>"Age: " { age }</p>
        </div>
    }
}
```

---

## 5. 配置文件DSL

### 5.1 声明式配置

```rust
/// 配置宏
macro_rules! config {
    (
        $($section:ident {
            $($key:ident = $value:expr),* $(,)?
        })*
    ) => {
        {
            let mut config = Config::new();
            
            $(
                let mut section = Section::new(stringify!($section));
                $(
                    section.set(stringify!($key), $value);
                )*
                config.add_section(section);
            )*
            
            config
        }
    };
}

// 使用
let config = config! {
    database {
        host = "localhost",
        port = 5432,
        username = "admin",
        password = "secret",
    }
    
    server {
        address = "0.0.0.0",
        port = 8080,
        workers = 4,
    }
    
    logging {
        level = "info",
        format = "json",
    }
};
```

---

### 5.2 类型安全配置

```rust
/// 配置derive宏
#[derive(Config)]
#[config(file = "config.toml")]
struct AppConfig {
    #[config(section = "database")]
    database: DatabaseConfig,
    
    #[config(section = "server")]
    server: ServerConfig,
}

#[derive(Config)]
struct DatabaseConfig {
    host: String,
    
    #[config(default = 5432)]
    port: u16,
    
    #[config(env = "DB_USERNAME")]
    username: String,
    
    #[config(secret)]
    password: String,
}

// 使用
let config = AppConfig::from_file("config.toml")?;
println!("Database: {}:{}", config.database.host, config.database.port);
```

---

## 6. 测试DSL框架

### 6.1 行为驱动测试

```rust
/// BDD风格测试宏
macro_rules! describe {
    ($name:expr, $body:block) => {
        mod test_suite {
            #[cfg(test)]
            mod tests {
                use super::*;
                
                $body
            }
        }
    };
}

macro_rules! it {
    ($description:expr, $test_body:block) => {
        #[test]
        fn test() {
            println!("Test: {}", $description);
            $test_body
        }
    };
}

// 使用
describe!("User authentication", {
    it!("should login with valid credentials", {
        let user = User::new("alice", "password123");
        assert!(user.login("alice", "password123").is_ok());
    });
    
    it!("should reject invalid password", {
        let user = User::new("alice", "password123");
        assert!(user.login("alice", "wrong").is_err());
    });
});
```

---

### 6.2 表格驱动测试

```rust
/// 表格测试宏
macro_rules! table_test {
    (
        $test_name:ident,
        inputs: [$($input:expr),* $(,)?],
        expected: [$($expected:expr),* $(,)?],
        test: $test_fn:expr
    ) => {
        #[test]
        fn $test_name() {
            let inputs = vec![$($input),*];
            let expected = vec![$($expected),*];
            
            for (input, expected) in inputs.into_iter().zip(expected) {
                assert_eq!(
                    $test_fn(input),
                    expected,
                    "Failed for input: {:?}",
                    input
                );
            }
        }
    };
}

// 使用
table_test! {
    test_add,
    inputs: [
        (1, 2),
        (3, 4),
        (5, 6),
    ],
    expected: [3, 7, 11],
    test: |(a, b)| a + b
}
```

---

## 总结

DSL构建的关键步骤：

1. **设计阶段**: 明确领域概念和语法
2. **词法分析**: Token化输入
3. **语法分析**: 构建AST
4. **代码生成**: 生成Rust代码
5. **类型安全**: 利用Rust类型系统
6. **测试验证**: 确保正确性

---

## 相关文档

- [宏元编程](./macro_metaprogramming.md)
- [过程宏基础](../03_procedural/01_proc_macro_basics.md)
- [真实案例](../05_practice/04_real_world_examples.md)

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20

## 返回导航

- [返回高级主题](README.md)
- [返回主索引](../00_MASTER_INDEX.md)
