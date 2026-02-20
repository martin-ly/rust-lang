# 02 DSL构建实践

## 目录

- [02 DSL构建实践](#02-dsl构建实践)
  - [目录](#目录)
  - [📐 知识结构](#-知识结构)
    - [概念定义](#概念定义)
    - [属性特征](#属性特征)
    - [关系连接](#关系连接)
    - [思维导图](#思维导图)
    - [多维概念对比矩阵](#多维概念对比矩阵)
    - [决策树图](#决策树图)
  - [1. 概述](#1-概述)
  - [2. DSL设计原则](#2-dsl设计原则)
    - [2.1 领域分析](#21-领域分析)
      - [2.1.1 识别核心概念](#211-识别核心概念)
      - [2.1.2 用户研究](#212-用户研究)
    - [2.2 语法设计](#22-语法设计)
      - [2.2.1 声明式 vs. 命令式](#221-声明式-vs-命令式)
      - [2.2.2 语法糖设计](#222-语法糖设计)
      - [2.2.3 类型安全](#223-类型安全)
    - [2.3 表达能力与简洁性平衡](#23-表达能力与简洁性平衡)
      - [2.3.1 分层设计](#231-分层设计)
    - [2.4 错误处理设计](#24-错误处理设计)
      - [2.4.1 编译期 vs. 运行时错误](#241-编译期-vs-运行时错误)
      - [2.4.2 错误消息质量](#242-错误消息质量)
  - [3. 解析器构建](#3-解析器构建)
    - [3.1 宏解析器基础](#31-宏解析器基础)
      - [3.1.1 简单键值对解析](#311-简单键值对解析)
      - [3.1.2 表达式解析](#312-表达式解析)
    - [3.2 Nom 组合子](#32-nom-组合子)
      - [3.2.1 基础解析器](#321-基础解析器)
      - [3.2.2 复杂表达式解析](#322-复杂表达式解析)
    - [3.3 Pest PEG解析器](#33-pest-peg解析器)
      - [3.3.1 语法定义](#331-语法定义)
      - [3.3.2 Rust 解析器](#332-rust-解析器)
    - [3.4 手写递归下降解析器](#34-手写递归下降解析器)
      - [3.4.1 词法分析](#341-词法分析)
      - [3.4.2 语法分析](#342-语法分析)
  - [4. 错误恢复](#4-错误恢复)
    - [4.1 错误位置追踪](#41-错误位置追踪)
      - [4.1.1 Span 追踪](#411-span-追踪)
    - [4.2 部分解析与恢复](#42-部分解析与恢复)
      - [4.2.1 同步点恢复](#421-同步点恢复)
    - [4.3 友好错误消息](#43-友好错误消息)
      - [4.3.1 上下文提示](#431-上下文提示)
    - [4.4 多错误报告](#44-多错误报告)
  - [5. 实战案例](#5-实战案例)
    - [5.1 HTML DSL](#51-html-dsl)
    - [5.2 SQL查询构建器](#52-sql查询构建器)
    - [5.3 配置文件DSL](#53-配置文件dsl)
    - [5.4 状态机描述语言](#54-状态机描述语言)
  - [6. 性能优化](#6-性能优化)
    - [6.1 编译时间优化](#61-编译时间优化)
      - [6.1.1 避免过度展开](#611-避免过度展开)
    - [6.2 生成代码优化](#62-生成代码优化)
      - [6.2.1 内联生成的函数](#621-内联生成的函数)
  - [7. 相关资源](#7-相关资源)
    - [7.1 工具与库](#71-工具与库)
    - [7.2 学习资源](#72-学习资源)

---

## 📐 知识结构

### 概念定义

**DSL构建实践 (DSL Construction Practice)**:

- **定义**: Rust 1.92.0 DSL（领域特定语言）构建实践，包括 DSL 设计原则、解析器构建、错误恢复、性能优化等
- **类型**: 高级主题文档
- **范畴**: 元编程、DSL 设计
- **版本**: Rust 1.92.0+ (Edition 2024)
- **相关概念**: DSL、解析器、Nom、Pest、递归下降、错误恢复

### 属性特征

**核心属性**:

- **DSL设计原则**: 领域分析、语法设计、表达能力与简洁性平衡、错误处理设计
- **解析器构建**: 宏解析器基础、Nom 组合子、Pest PEG解析器、手写递归下降解析器
- **错误恢复**: 错误位置追踪、部分解析与恢复、友好错误消息、多错误报告
- **性能优化**: 编译时间优化、生成代码优化

**Rust 1.92.0 新特性**:

- **改进的解析器库**: 更好的 Nom 和 Pest 支持
- **增强的错误处理**: 更友好的错误消息
- **优化的编译时间**: 更快的 DSL 编译

**性能特征**:

- **解析性能**: 高效的解析器实现
- **编译时间**: 优化的编译时间
- **适用场景**: DSL 开发、领域特定语言、代码生成

### 关系连接

**组合关系**:

- DSL构建实践 --[covers]--> DSL 构建完整流程
- DSL 应用 --[uses]--> DSL构建实践

**依赖关系**:

- DSL构建实践 --[depends-on]--> 解析器库
- DSL 开发 --[depends-on]--> DSL构建实践

### 思维导图

```text
DSL构建实践
│
├── DSL设计原则
│   ├── 领域分析
│   └── 语法设计
├── 解析器构建
│   ├── 宏解析器
│   ├── Nom 组合子
│   └── Pest PEG
├── 错误恢复
│   ├── 错误位置追踪
│   └── 友好错误消息
└── 性能优化
    └── 编译时间优化
```

### 多维概念对比矩阵

| 解析器技术     | 性能 | 复杂度 | 错误恢复 | 适用场景   | Rust 1.92.0 |
| :--- | :--- | :--- | :--- | :--- | :--- || **宏解析器**   | 高   | 中     | 低       | 简单 DSL   | ✅          |
| **Nom 组合子** | 高   | 中     | 中       | 复杂解析   | ✅ 改进     |
| **Pest PEG**   | 中   | 低     | 高       | 声明式解析 | ✅          |
| **递归下降**   | 高   | 高     | 高       | 完全控制   | ✅          |

### 决策树图

```text
选择解析器技术
│
├── 是否需要声明式语法？
│   ├── 是 → Pest PEG
│   └── 否 → 继续判断
│       ├── 是否需要完全控制？
│       │   ├── 是 → 递归下降
│       │   └── 否 → 继续判断
│       │       ├── 是否需要高性能？
│       │       │   ├── 是 → Nom 组合子
│       │       │   └── 否 → 宏解析器
```

---

## 1. 概述

**领域特定语言（DSL）** 是为特定问题领域设计的语言，Rust 的宏系统使得我们能够构建**内嵌 DSL（Embedded DSL）**，享受编译器的类型检查和性能优化。

**本文档涵盖**：

- **DSL 设计原则**：领域分析、语法设计、错误处理
- **解析器构建**：宏解析器、Nom、Pest、手写解析器
- **错误恢复**：位置追踪、部分解析、友好错误消息
- **实战案例**：HTML、SQL、配置、状态机 DSL

**适用场景**：

- ✅ 构建内部工具的配置语言
- ✅ 设计类型安全的查询语言
- ✅ 实现声明式 UI 框架
- ✅ 创建业务规则引擎

**学习路径**：

1. 理解 DSL 设计原则
2. 掌握解析器构建技术
3. 学习错误恢复策略
4. 实践真实 DSL 开发
5. 优化编译和运行时性能

---

## 2. DSL设计原则

### 2.1 领域分析

#### 2.1.1 识别核心概念

**步骤**：

1. **定义问题域**：明确 DSL 要解决的问题
2. **提取核心实体**：识别领域中的主要对象
3. **定义操作**：确定对象之间的交互
4. **建立约束**：定义规则和限制

**示例：HTML DSL**:

```rust
// 核心实体：元素、属性、文本
// 操作：嵌套、添加属性
// 约束：某些元素不能嵌套（如 <br>）

html! {
    <div class="container">
        <h1>"Welcome"</h1>
        <p>"Hello, Rust!"</p>
    </div>
}
```

#### 2.1.2 用户研究

**考虑因素**：

- **目标用户**：开发者、运维、业务人员？
- **熟悉的语法**：SQL、JSON、YAML、自然语言？
- **使用频率**：一次性配置 vs. 频繁编写？
- **学习曲线**：简单直观 vs. 功能强大？

---

### 2.2 语法设计

#### 2.2.1 声明式 vs. 命令式

```rust
// ❌ 命令式：告诉如何做
let mut ui = UI::new();
ui.add_button("Click me");
ui.add_label("Status: OK");
ui.render();

// ✅ 声明式：描述是什么
ui! {
    Button { text: "Click me" }
    Label { text: "Status: OK" }
}
```

#### 2.2.2 语法糖设计

```rust
// ❌ 冗长
query! {
    SELECT(field("id"), field("name"))
    FROM(table("users"))
    WHERE(eq(field("age"), value(30)))
}

// ✅ 简洁
query! {
    SELECT id, name FROM users WHERE age = 30
}
```

#### 2.2.3 类型安全

```rust
// ✅ 编译期类型检查
sql! {
    SELECT users.id, orders.total
    FROM users
    JOIN orders ON users.id = orders.user_id
}

// ❌ 编译错误：字段不存在
// sql! {
//     SELECT users.invalid_field FROM users
// }
```

---

### 2.3 表达能力与简洁性平衡

#### 2.3.1 分层设计

```rust
// Tier 1: 简单常见情况（80% 用例）
config! {
    host: "localhost",
    port: 8080,
}

// Tier 2: 复杂情况（15% 用例）
config! {
    host: env!("APP_HOST"),
    port: 8080,
    middleware: [cors, logging],
}

// Tier 3: 完全控制（5% 用例）
config! {
    host: {
        if cfg!(debug_assertions) {
            "localhost"
        } else {
            env!("PROD_HOST")
        }
    },
    port: 8080,
    middleware: [
        Middleware::Cors { origins: ["*"] },
        Middleware::Logging { level: Info },
    ],
}
```

---

### 2.4 错误处理设计

#### 2.4.1 编译期 vs. 运行时错误

```rust
// ✅ 编译期捕获错误
validate! {
    email: "test@example.com", // ✅ OK
    // email: "invalid-email",  // ❌ 编译错误：格式无效
}

// ❌ 运行时错误（不推荐）
fn validate_email(email: &str) -> Result<(), String> {
    if !email.contains('@') {
        Err("Invalid email".into())
    } else {
        Ok(())
    }
}
```

#### 2.4.2 错误消息质量

```rust
// ❌ 糟糕的错误消息
// error: parse error

// ✅ 清晰的错误消息
// error: expected '}' after object body
//   --> config.rs:10:5
//    |
// 10 |     host: "localhost",
//    |                       ^ expected '}' here
//    |
//    = note: to close object starting at line 8
```

---

## 3. 解析器构建

### 3.1 宏解析器基础

#### 3.1.1 简单键值对解析

```rust
macro_rules! simple_config {
    // Base case: 空配置
    () => {
        std::collections::HashMap::new()
    };
    // Single entry
    ($key:ident: $value:expr) => {{
        let mut map = std::collections::HashMap::new();
        map.insert(stringify!($key).to_string(), $value.to_string());
        map
    }};
    // Multiple entries
    ($key:ident: $value:expr, $($rest_key:ident: $rest_value:expr),+ $(,)?) => {{
        let mut map = simple_config!($($rest_key: $rest_value),+);
        map.insert(stringify!($key).to_string(), $value.to_string());
        map
    }};
}

// 使用示例
fn macro_parser_example() {
    let config = simple_config! {
        host: "localhost",
        port: 8080,
        debug: true,
    };

    println!("{:?}", config);
}
```

#### 3.1.2 表达式解析

```rust
macro_rules! calc {
    // Number literal
    ($num:expr) => {
        $num
    };
    // Addition
    ($left:expr + $right:expr) => {
        calc!($left) + calc!($right)
    };
    // Multiplication
    ($left:expr * $right:expr) => {
        calc!($left) * calc!($right)
    };
    // Parentheses
    (( $($inner:tt)+ )) => {
        calc!($($inner)+)
    };
}

// 使用示例
fn expression_parser() {
    let result = calc!(2 + 3 * 4); // 14
    println!("Result: {}", result);
}
```

---

### 3.2 Nom 组合子

#### 3.2.1 基础解析器

```toml
[dependencies]
nom = "7.1"
```

```rust
use nom::{
    IResult,
    bytes::complete::{tag, take_while1},
    character::complete::{char, digit1, multispace0},
    combinator::map_res,
    sequence::{delimited, preceded, tuple},
    branch::alt,
};

// 解析整数
fn parse_integer(input: &str) -> IResult<&str, i32> {
    map_res(digit1, |s: &str| s.parse::<i32>())(input)
}

// 解析标识符
fn parse_identifier(input: &str) -> IResult<&str, String> {
    map_res(
        take_while1(|c: char| c.is_alphanumeric() || c == '_'),
        |s: &str| Ok::<_, std::convert::Infallible>(s.to_string())
    )(input)
}

// 解析键值对
fn parse_key_value(input: &str) -> IResult<&str, (String, i32)> {
    let (input, key) = parse_identifier(input)?;
    let (input, _) = delimited(multispace0, char('='), multispace0)(input)?;
    let (input, value) = parse_integer(input)?;

    Ok((input, (key, value)))
}

// 使用示例
fn nom_parser_example() {
    let result = parse_key_value("count = 42");
    match result {
        Ok((remaining, (key, value))) => {
            println!("Key: {}, Value: {}, Remaining: '{}'", key, value, remaining);
        }
        Err(e) => println!("Parse error: {:?}", e),
    }
}
```

#### 3.2.2 复杂表达式解析

```rust
use nom::{
    IResult,
    branch::alt,
    character::complete::{char, multispace0},
    combinator::map,
    multi::many0,
    sequence::{delimited, preceded, tuple},
};

#[derive(Debug, PartialEq)]
enum Expr {
    Number(i32),
    Add(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
}

fn parse_number(input: &str) -> IResult<&str, Expr> {
    map(parse_integer, Expr::Number)(input)
}

fn parse_factor(input: &str) -> IResult<&str, Expr> {
    alt((
        parse_number,
        delimited(char('('), parse_expr, char(')')),
    ))(input)
}

fn parse_term(input: &str) -> IResult<&str, Expr> {
    let (input, first) = parse_factor(input)?;
    let (input, rest) = many0(preceded(
        delimited(multispace0, char('*'), multispace0),
        parse_factor
    ))(input)?;

    Ok((input, rest.into_iter().fold(first, |acc, expr| {
        Expr::Mul(Box::new(acc), Box::new(expr))
    })))
}

fn parse_expr(input: &str) -> IResult<&str, Expr> {
    let (input, first) = parse_term(input)?;
    let (input, rest) = many0(preceded(
        delimited(multispace0, char('+'), multispace0),
        parse_term
    ))(input)?;

    Ok((input, rest.into_iter().fold(first, |acc, expr| {
        Expr::Add(Box::new(acc), Box::new(expr))
    })))
}

// 使用示例
#[test]
fn test_nom_expression() {
    let result = parse_expr("2 + 3 * 4");
    assert_eq!(
        result,
        Ok(("", Expr::Add(
            Box::new(Expr::Number(2)),
            Box::new(Expr::Mul(
                Box::new(Expr::Number(3)),
                Box::new(Expr::Number(4))
            ))
        )))
    );
}
```

---

### 3.3 Pest PEG解析器

#### 3.3.1 语法定义

```toml
[dependencies]
pest = "2.7"
pest_derive = "2.7"
```

```pest
// grammar.pest
WHITESPACE = _{ " " | "\t" | "\n" }

identifier = @{ ASCII_ALPHA ~ (ASCII_ALPHANUMERIC | "_")* }
number = @{ ASCII_DIGIT+ }

key_value = { identifier ~ "=" ~ number }
config = { SOI ~ key_value ~ ("," ~ key_value)* ~ EOI }
```

#### 3.3.2 Rust 解析器

```rust
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct ConfigParser;

fn parse_config(input: &str) -> Result<Vec<(String, i32)>, pest::error::Error<Rule>> {
    let pairs = ConfigParser::parse(Rule::config, input)?;
    let mut result = Vec::new();

    for pair in pairs {
        for inner in pair.into_inner() {
            if inner.as_rule() == Rule::key_value {
                let mut kv = inner.into_inner();
                let key = kv.next().unwrap().as_str().to_string();
                let value = kv.next().unwrap().as_str().parse::<i32>().unwrap();
                result.push((key, value));
            }
        }
    }

    Ok(result)
}

// 使用示例
#[test]
fn test_pest_parser() {
    let result = parse_config("port=8080, timeout=30");
    assert_eq!(
        result.unwrap(),
        vec![
            ("port".to_string(), 8080),
            ("timeout".to_string(), 30),
        ]
    );
}
```

---

### 3.4 手写递归下降解析器

#### 3.4.1 词法分析

```rust
#[derive(Debug, PartialEq, Clone)]
enum Token {
    Number(i32),
    Identifier(String),
    Plus,
    Minus,
    Star,
    Slash,
    LParen,
    RParen,
    Equals,
    EOF,
}

struct Lexer {
    input: Vec<char>,
    pos: usize,
}

impl Lexer {
    fn new(input: &str) -> Self {
        Self {
            input: input.chars().collect(),
            pos: 0,
        }
    }

    fn current(&self) -> Option<char> {
        self.input.get(self.pos).copied()
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.current() {
            if c.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn read_number(&mut self) -> i32 {
        let start = self.pos;
        while let Some(c) = self.current() {
            if c.is_ascii_digit() {
                self.advance();
            } else {
                break;
            }
        }

        self.input[start..self.pos]
            .iter()
            .collect::<String>()
            .parse()
            .unwrap()
    }

    fn read_identifier(&mut self) -> String {
        let start = self.pos;
        while let Some(c) = self.current() {
            if c.is_alphanumeric() || c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        self.input[start..self.pos].iter().collect()
    }

    fn next_token(&mut self) -> Token {
        self.skip_whitespace();

        match self.current() {
            None => Token::EOF,
            Some('+') => { self.advance(); Token::Plus }
            Some('-') => { self.advance(); Token::Minus }
            Some('*') => { self.advance(); Token::Star }
            Some('/') => { self.advance(); Token::Slash }
            Some('(') => { self.advance(); Token::LParen }
            Some(')') => { self.advance(); Token::RParen }
            Some('=') => { self.advance(); Token::Equals }
            Some(c) if c.is_ascii_digit() => Token::Number(self.read_number()),
            Some(c) if c.is_alphabetic() => Token::Identifier(self.read_identifier()),
            Some(c) => panic!("Unexpected character: {}", c),
        }
    }
}
```

#### 3.4.2 语法分析

```rust
struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(input: &str) -> Self {
        let mut lexer = Lexer::new(input);
        let mut tokens = Vec::new();

        loop {
            let token = lexer.next_token();
            if token == Token::EOF {
                tokens.push(token);
                break;
            }
            tokens.push(token);
        }

        Self { tokens, pos: 0 }
    }

    fn current(&self) -> &Token {
        &self.tokens[self.pos]
    }

    fn advance(&mut self) {
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
    }

    fn expect(&mut self, expected: Token) -> Result<(), String> {
        if self.current() == &expected {
            self.advance();
            Ok(())
        } else {
            Err(format!("Expected {:?}, got {:?}", expected, self.current()))
        }
    }

    // expr = term (('+' | '-') term)*
    fn parse_expr(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_term()?;

        while let Token::Plus | Token::Minus = self.current() {
            let op = self.current().clone();
            self.advance();
            let right = self.parse_term()?;

            left = match op {
                Token::Plus => Expr::Add(Box::new(left), Box::new(right)),
                Token::Minus => Expr::Sub(Box::new(left), Box::new(right)),
                _ => unreachable!(),
            };
        }

        Ok(left)
    }

    // term = factor (('*' | '/') factor)*
    fn parse_term(&mut self) -> Result<Expr, String> {
        let mut left = self.parse_factor()?;

        while let Token::Star | Token::Slash = self.current() {
            let op = self.current().clone();
            self.advance();
            let right = self.parse_factor()?;

            left = match op {
                Token::Star => Expr::Mul(Box::new(left), Box::new(right)),
                Token::Slash => Expr::Div(Box::new(left), Box::new(right)),
                _ => unreachable!(),
            };
        }

        Ok(left)
    }

    // factor = number | '(' expr ')'
    fn parse_factor(&mut self) -> Result<Expr, String> {
        match self.current() {
            Token::Number(n) => {
                let num = *n;
                self.advance();
                Ok(Expr::Number(num))
            }
            Token::LParen => {
                self.advance();
                let expr = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(expr)
            }
            _ => Err(format!("Unexpected token: {:?}", self.current())),
        }
    }
}

#[derive(Debug, PartialEq)]
enum Expr {
    Number(i32),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

// 使用示例
#[test]
fn test_recursive_descent() {
    let mut parser = Parser::new("2 + 3 * 4");
    let result = parser.parse_expr().unwrap();

    assert_eq!(
        result,
        Expr::Add(
            Box::new(Expr::Number(2)),
            Box::new(Expr::Mul(
                Box::new(Expr::Number(3)),
                Box::new(Expr::Number(4))
            ))
        )
    );
}
```

---

## 4. 错误恢复

### 4.1 错误位置追踪

#### 4.1.1 Span 追踪

```rust
#[derive(Debug, Clone, Copy)]
struct Span {
    start: usize,
    end: usize,
}

#[derive(Debug)]
struct Token {
    kind: TokenKind,
    span: Span,
}

#[derive(Debug)]
enum TokenKind {
    Number(i32),
    Identifier(String),
    // ...
}

// 错误报告
fn report_error(input: &str, span: Span, message: &str) {
    let line_start = input[..span.start].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_end = input[span.start..].find('\n').map(|i| span.start + i).unwrap_or(input.len());

    let line = &input[line_start..line_end];
    let column = span.start - line_start;

    eprintln!("Error: {}", message);
    eprintln!("  |");
    eprintln!("  | {}", line);
    eprintln!("  | {}^", " ".repeat(column));
}
```

---

### 4.2 部分解析与恢复

#### 4.2.1 同步点恢复

```rust
impl Parser {
    fn recover_to_sync_point(&mut self) {
        // 跳过错误的 token 直到找到同步点（如分号、右括号）
        while let Some(token) = self.current() {
            match token {
                Token::Semicolon | Token::RParen | Token::RBrace | Token::EOF => break,
                _ => self.advance(),
            }
        }
    }

    fn parse_statement(&mut self) -> Result<Stmt, Vec<String>> {
        let mut errors = Vec::new();

        match self.try_parse_statement() {
            Ok(stmt) => Ok(stmt),
            Err(e) => {
                errors.push(e);
                self.recover_to_sync_point();
                Err(errors)
            }
        }
    }
}
```

---

### 4.3 友好错误消息

#### 4.3.1 上下文提示

```rust
fn format_error(span: Span, message: &str, hint: Option<&str>) -> String {
    let mut output = format!("Error at line {}, column {}: {}",
        span.start, span.end, message);

    if let Some(h) = hint {
        output.push_str(&format!("\n  Help: {}", h));
    }

    output
}

// 使用示例
let error = format_error(
    Span { start: 10, end: 15 },
    "expected '}' after object body",
    Some("to close object starting at line 8")
);
```

---

### 4.4 多错误报告

```rust
struct ErrorCollector {
    errors: Vec<(Span, String)>,
}

impl ErrorCollector {
    fn new() -> Self {
        Self { errors: Vec::new() }
    }

    fn add_error(&mut self, span: Span, message: String) {
        self.errors.push((span, message));
    }

    fn report_all(&self, input: &str) {
        for (span, message) in &self.errors {
            report_error(input, *span, message);
        }
    }
}
```

---

## 5. 实战案例

### 5.1 HTML DSL

```rust
macro_rules! html {
    // 自闭合标签
    (<$tag:ident $($attr:ident=$value:expr)* />) => {
        format!("<{} {}/>", stringify!($tag), $(format!("{}=\"{}\"", stringify!($attr), $value)),*)
    };
    // 带子元素的标签
    (<$tag:ident $($attr:ident=$value:expr)*> $($child:tt)+ </$close:ident>) => {{
        assert_eq!(stringify!($tag), stringify!($close), "Mismatched tags");
        format!(
            "<{} {}>{}</{}>",
            stringify!($tag),
            $(format!("{}=\"{}\" ", stringify!($attr), $value)),*,
            html!($($child)+),
            stringify!($tag)
        )
    }};
    // 文本内容
    ($text:expr) => {
        $text.to_string()
    };
    // 多个子元素
    ($($child:tt)+) => {
        vec![$(html!($child)),+].join("")
    };
}

// 使用示例
fn html_dsl_example() {
    let output = html! {
        <div class="container">
            <h1>"Welcome"</h1>
            <p>"Hello, Rust!"</p>
            <br/>
        </div>
    };

    println!("{}", output);
}
```

---

### 5.2 SQL查询构建器

```rust
macro_rules! sql {
    (SELECT $($field:ident),+ FROM $table:ident WHERE $cond:expr) => {{
        format!(
            "SELECT {} FROM {} WHERE {}",
            stringify!($($field),+).replace(" ", ""),
            stringify!($table),
            stringify!($cond)
        )
    }};
    (SELECT $($field:ident),+ FROM $table:ident) => {{
        format!(
            "SELECT {} FROM {}",
            stringify!($($field),+).replace(" ", ""),
            stringify!($table)
        )
    }};
}

// 使用示例
fn sql_dsl_example() {
    let query1 = sql!(SELECT id, name FROM users);
    let query2 = sql!(SELECT id, name FROM users WHERE id > 100);

    println!("{}", query1);
    println!("{}", query2);
}
```

---

### 5.3 配置文件DSL

```rust
macro_rules! config {
    (
        $($key:ident: $value:expr),+ $(,)?
    ) => {{
        let mut map = std::collections::HashMap::new();
        $(
            map.insert(stringify!($key), $value.to_string());
        )+
        map
    }};
}

// 使用示例
fn config_dsl_example() {
    let cfg = config! {
        host: "localhost",
        port: 8080,
        debug: true,
    };

    println!("{:?}", cfg);
}
```

---

### 5.4 状态机描述语言

```rust
macro_rules! state_machine {
    (
        states: [$($state:ident),+ $(,)?],
        initial: $initial:ident,
        transitions: {
            $($from:ident -[$event:ident]-> $to:ident),+ $(,)?
        }
    ) => {
        #[derive(Debug, PartialEq, Clone, Copy)]
        enum State {
            $($state),+
        }

        #[derive(Debug, PartialEq, Clone, Copy)]
        enum Event {
            $($event),+
        }

        struct StateMachine {
            current: State,
        }

        impl StateMachine {
            fn new() -> Self {
                Self {
                    current: State::$initial,
                }
            }

            fn transition(&mut self, event: Event) -> Result<State, &'static str> {
                match (self.current, event) {
                    $(
                        (State::$from, Event::$event) => {
                            self.current = State::$to;
                            Ok(self.current)
                        }
                    )+
                    _ => Err("Invalid transition"),
                }
            }
        }
    };
}

// 使用示例
state_machine! {
    states: [Idle, Running, Stopped],
    initial: Idle,
    transitions: {
        Idle -[Start]-> Running,
        Running -[Stop]-> Stopped,
        Stopped -[Reset]-> Idle,
    }
}

fn state_machine_example() {
    let mut sm = StateMachine::new();
    assert_eq!(sm.current, State::Idle);

    sm.transition(Event::Start).unwrap();
    assert_eq!(sm.current, State::Running);

    sm.transition(Event::Stop).unwrap();
    assert_eq!(sm.current, State::Stopped);
}
```

---

## 6. 性能优化

### 6.1 编译时间优化

#### 6.1.1 避免过度展开

```rust
// ❌ 糟糕：每次调用都展开
macro_rules! bad_repeat {
    ($n:expr, $body:expr) => {
        for _ in 0..$n {
            $body;
        }
    };
}

// ✅ 好：使用运行时循环
#[inline]
fn good_repeat<F: Fn()>(n: usize, f: F) {
    for _ in 0..n {
        f();
    }
}
```

---

### 6.2 生成代码优化

#### 6.2.1 内联生成的函数

```rust
macro_rules! generate_getter {
    ($name:ident, $field:ident, $ty:ty) => {
        #[inline(always)]
        pub fn $name(&self) -> &$ty {
            &self.$field
        }
    };
}
```

---

## 7. 相关资源

### 7.1 工具与库

- **Nom**: 解析器组合子库
- **Pest**: PEG 解析器生成器
- **syn**: Rust 代码解析库
- **quote**: 代码生成库

### 7.2 学习资源

- [Nom Tutorial](https://github.com/Geal/nom/blob/main/doc/choosing_a_combinator.md)
- [Pest Book](https://pest.rs/book/)
- [Crafting Interpreters](https://craftinginterpreters.com/)

---

**下一步**：

- → 阅读 [03\_代码生成优化.md](./03_代码生成优化.md) 学习优化技术
- → 参考 [C11 主索引](../../02_主索引导航.md) 探索其他主题
- → 实践 [Tier 2 宏开发指南](../../tier_02_guides/README.md) 巩固知识

---

_最后更新: 2025-12-11_
_版本: 1.0.0_
_作者: Rust 学习系统团队_
