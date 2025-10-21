# 解析器与解析组合子

> **核心库**: nom, pest, serde, winnow  
> **适用场景**: 文本解析、协议解析、配置文件、编译器前端

---

## 📋 目录

- [解析器与解析组合子](#解析器与解析组合子)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [解析器类型](#解析器类型)
    - [库选择指南](#库选择指南)
  - [🔧 nom - 解析组合子](#-nom---解析组合子)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
    - [实战示例: HTTP 请求解析](#实战示例-http-请求解析)
  - [🦗 pest - PEG 解析器](#-pest---peg-解析器)
    - [核心特性](#核心特性-1)
    - [基础用法](#基础用法-1)
  - [💡 最佳实践](#-最佳实践)
    - [1. nom vs pest](#1-nom-vs-pest)
    - [2. 错误处理](#2-错误处理)
    - [3. 性能优化](#3-性能优化)
  - [🔧 常见场景](#-常见场景)
    - [场景 1: 日志解析](#场景-1-日志解析)
    - [场景 2: 配置文件解析](#场景-2-配置文件解析)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

### 解析器类型

1. **解析组合子 (Parser Combinator)**: nom, winnow
   - 特点: 灵活、可组合、零拷贝
   - 学习曲线: 中等

2. **PEG 解析器 (Parsing Expression Grammar)**: pest
   - 特点: 声明式语法、易于理解
   - 学习曲线: 平缓

3. **手写解析器**:
   - 特点: 完全控制、最高性能
   - 学习曲线: 陡峭

### 库选择指南

| 特性 | nom | pest | 手写 |
|------|-----|------|------|
| **易用性** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ |
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **灵活性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **错误信息** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |

---

## 🔧 nom - 解析组合子

### 核心特性

- ✅ 零拷贝解析
- ✅ 流式处理
- ✅ 字节和字符解析
- ✅ 错误恢复

### 基础用法

```rust
use nom::{
    IResult,
    bytes::complete::{tag, take_while},
    character::complete::{alpha1, digit1, space0},
    sequence::{tuple, delimited},
    combinator::map_res,
};

// 解析数字
fn parse_number(input: &str) -> IResult<&str, i32> {
    map_res(digit1, |s: &str| s.parse::<i32>())(input)
}

// 解析标识符
fn parse_identifier(input: &str) -> IResult<&str, &str> {
    alpha1(input)
}

// 解析键值对: "key = 123"
fn parse_key_value(input: &str) -> IResult<&str, (&str, i32)> {
    let (input, key) = alpha1(input)?;
    let (input, _) = delimited(space0, tag("="), space0)(input)?;
    let (input, value) = parse_number(input)?;
    Ok((input, (key, value)))
}

fn main() {
    match parse_key_value("count = 42") {
        Ok((remaining, (key, value))) => {
            println!("Key: {}, Value: {}", key, value);
        }
        Err(e) => println!("Error: {:?}", e),
    }
}
```

### 实战示例: HTTP 请求解析

```rust
use nom::{
    IResult,
    bytes::complete::{tag, take_while1},
    character::complete::{space1, line_ending},
    sequence::{tuple, terminated},
};

#[derive(Debug)]
struct HttpRequest<'a> {
    method: &'a str,
    path: &'a str,
    version: &'a str,
}

fn parse_http_request(input: &str) -> IResult<&str, HttpRequest> {
    let (input, (method, _, path, _, version, _)) = tuple((
        take_while1(|c: char| c.is_alphabetic()),
        space1,
        take_while1(|c: char| c != ' '),
        space1,
        take_while1(|c: char| c != '\r' && c != '\n'),
        line_ending,
    ))(input)?;

    Ok((input, HttpRequest { method, path, version }))
}

fn main() {
    let request = "GET /index.html HTTP/1.1\r\n";
    match parse_http_request(request) {
        Ok((_, req)) => println!("{:?}", req),
        Err(e) => println!("Error: {:?}", e),
    }
}
```

---

## 🦗 pest - PEG 解析器

### 核心特性

- ✅ 声明式语法规则
- ✅ 自动生成解析器
- ✅ 优秀的错误报告
- ✅ Unicode 支持

### 基础用法

**1. 定义语法 (grammar.pest)**

```pest
WHITESPACE = _{ " " | "\t" | "\r" | "\n" }

number = @{ "-"? ~ ASCII_DIGIT+ }
identifier = @{ ASCII_ALPHA ~ (ASCII_ALPHANUMERIC | "_")* }
string = @{ "\"" ~ (!"\"" ~ ANY)* ~ "\"" }

key_value = { identifier ~ "=" ~ (number | string) }
config = { SOI ~ key_value ~ (WHITESPACE* ~ key_value)* ~ EOI }
```

**2. 使用解析器**

```rust
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct ConfigParser;

fn parse_config(input: &str) {
    match ConfigParser::parse(Rule::config, input) {
        Ok(pairs) => {
            for pair in pairs {
                println!("{:?}: {}", pair.as_rule(), pair.as_str());
            }
        }
        Err(e) => println!("Parse error: {}", e),
    }
}

fn main() {
    parse_config("name = \"Alice\"\nage = 30");
}
```

---

## 💡 最佳实践

### 1. nom vs pest

**选择 nom**:
- ✅ 需要最高性能
- ✅ 二进制协议解析
- ✅ 流式处理
- ✅ 零拷贝要求

**选择 pest**:
- ✅ 快速原型开发
- ✅ 复杂语法
- ✅ 需要良好错误提示
- ✅ 团队协作 (语法文件易读)

### 2. 错误处理

```rust
use nom::{
    IResult,
    error::{Error, ErrorKind, ParseError},
    Err as NomErr,
};

// 自定义错误类型
#[derive(Debug)]
enum ParseError {
    InvalidNumber,
    InvalidIdentifier,
    UnexpectedToken(String),
}

// 提供有用的错误信息
fn parse_with_context(input: &str) -> Result<i32, ParseError> {
    match parse_number(input) {
        Ok((_, num)) => Ok(num),
        Err(NomErr::Error(e)) | Err(NomErr::Failure(e)) => {
            Err(ParseError::InvalidNumber)
        }
        Err(NomErr::Incomplete(_)) => {
            Err(ParseError::UnexpectedToken("EOF".to_string()))
        }
    }
}
```

### 3. 性能优化

```rust
// ✅ 使用 complete 而非 streaming (如果输入完整)
use nom::bytes::complete::tag;

// ✅ 避免回溯
use nom::branch::alt;
use nom::combinator::peek;

// ✅ 零拷贝
fn zero_copy_parse(input: &str) -> IResult<&str, &str> {
    // 直接返回切片，不分配
    alpha1(input)
}
```

---

## 🔧 常见场景

### 场景 1: 日志解析

```rust
use nom::{
    IResult,
    bytes::complete::{tag, take_until},
    character::complete::{space1, alpha1},
    sequence::tuple,
};

#[derive(Debug)]
struct LogEntry<'a> {
    level: &'a str,
    timestamp: &'a str,
    message: &'a str,
}

fn parse_log_entry(input: &str) -> IResult<&str, LogEntry> {
    let (input, (_, level, _, timestamp, _, message)) = tuple((
        tag("["),
        alpha1,
        tag("] "),
        take_until(" - "),
        tag(" - "),
        take_until("\n"),
    ))(input)?;

    Ok((input, LogEntry { level, timestamp, message }))
}
```

### 场景 2: 配置文件解析

```rust
use nom::{
    IResult,
    bytes::complete::{tag, take_while1},
    character::complete::{space0, digit1},
    sequence::{delimited, separated_pair},
    multi::separated_list0,
};

fn parse_ini_section(input: &str) -> IResult<&str, Vec<(&str, &str)>> {
    separated_list0(
        tag("\n"),
        separated_pair(
            take_while1(|c: char| c.is_alphanumeric()),
            delimited(space0, tag("="), space0),
            take_while1(|c: char| c != '\n'),
        ),
    )(input)
}
```

---

## 📚 延伸阅读

- [nom 官方文档](https://docs.rs/nom/)
- [pest 官方文档](https://pest.rs/)
- [nom 食谱](https://github.com/rust-bakery/nom/blob/main/doc/choosing_a_combinator.md)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20

