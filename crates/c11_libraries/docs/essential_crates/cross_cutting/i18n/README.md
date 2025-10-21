# 国际化 (Internationalization - i18n)

**类别**: 横切关注点  
**重要程度**: ⭐⭐⭐ (多语言应用必备)  
**更新日期**: 2025-10-20

---

## 📋 目录

- [国际化 (Internationalization - i18n)](#国际化-internationalization---i18n)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🔧 核心工具](#-核心工具)
    - [1. fluent (现代i18n ⭐⭐⭐⭐⭐)](#1-fluent-现代i18n-)
      - [基础用法](#基础用法)
      - [复数规则](#复数规则)
    - [2. rust-i18n (宏驱动 ⭐⭐⭐⭐)](#2-rust-i18n-宏驱动-)
      - [配置](#配置)
      - [翻译文件](#翻译文件)
      - [使用](#使用)
    - [3. gettext (传统i18n 💡)](#3-gettext-传统i18n-)
    - [4. tr (简单翻译 💡)](#4-tr-简单翻译-)
  - [💡 最佳实践](#-最佳实践)
    - [1. Web 应用国际化](#1-web-应用国际化)
    - [2. CLI 工具国际化](#2-cli-工具国际化)
    - [3. 动态语言切换](#3-动态语言切换)
    - [4. 日期和时间本地化](#4-日期和时间本地化)
  - [📊 工具对比](#-工具对比)
  - [🎯 实战场景](#-实战场景)
    - [场景1: 多语言 API 响应](#场景1-多语言-api-响应)
    - [场景2: 表单验证错误](#场景2-表单验证错误)
  - [🔗 相关资源](#-相关资源)

## 📋 概述

国际化（i18n）是让应用支持多语言的过程。Rust 生态提供了现代化的国际化解决方案，支持翻译、本地化、复数规则等。

---

## 🔧 核心工具

### 1. fluent (现代i18n ⭐⭐⭐⭐⭐)

**添加依赖**: `cargo add fluent fluent-bundle unic-langid`  
**用途**: Mozilla 的 Fluent 本地化系统

#### 基础用法

**messages/en-US.ftl**:

```fluent
hello = Hello, { $name }!
unread-messages = 
    { $count ->
        [0] No unread messages
        [1] One unread message
       *[other] { $count } unread messages
    }
```

**messages/zh-CN.ftl**:

```fluent
hello = 你好，{ $name }！
unread-messages = 
    { $count ->
        [0] 没有未读消息
       *[other] { $count } 条未读消息
    }
```

**Rust 代码**:

```rust
use fluent::{FluentBundle, FluentResource};
use unic_langid::langid;

fn main() {
    let langid_en = langid!("en-US");
    let mut bundle = FluentBundle::new(vec![langid_en]);
    
    // 加载翻译资源
    let ftl_string = std::fs::read_to_string("messages/en-US.ftl").unwrap();
    let res = FluentResource::try_new(ftl_string).unwrap();
    bundle.add_resource(res).unwrap();
    
    // 使用翻译
    let msg = bundle.get_message("hello").unwrap();
    let pattern = msg.value().unwrap();
    
    let mut errors = vec![];
    let mut args = fluent::FluentArgs::new();
    args.set("name", "Alice");
    
    let value = bundle.format_pattern(&pattern, Some(&args), &mut errors);
    println!("{}", value);  // 输出: Hello, Alice!
}
```

#### 复数规则

```rust
use fluent::FluentArgs;

let msg = bundle.get_message("unread-messages").unwrap();
let pattern = msg.value().unwrap();

for count in [0, 1, 5] {
    let mut args = FluentArgs::new();
    args.set("count", count);
    
    let value = bundle.format_pattern(&pattern, Some(&args), &mut vec![]);
    println!("{}", value);
}
// 输出:
// No unread messages
// One unread message
// 5 unread messages
```

---

### 2. rust-i18n (宏驱动 ⭐⭐⭐⭐)

**添加依赖**: `cargo add rust-i18n`  
**用途**: 编译时i18n，零运行时开销

#### 配置

**Cargo.toml**:

```toml
[dependencies]
rust-i18n = "3"

[package.metadata.i18n]
available-locales = ["en", "zh-CN"]
default-locale = "en"
```

#### 翻译文件

**locales/en.yml**:

```yaml
hello: Hello, %{name}!
items:
  zero: No items
  one: One item
  other: "%{count} items"
```

**locales/zh-CN.yml**:

```yaml
hello: 你好，%{name}！
items:
  zero: 没有项目
  other: "%{count} 个项目"
```

#### 使用

```rust
use rust_i18n::t;

// 初始化
rust_i18n::i18n!("locales");

fn main() {
    // 设置语言
    rust_i18n::set_locale("zh-CN");
    
    // 翻译
    println!("{}", t!("hello", name = "Alice"));
    // 输出: 你好，Alice！
    
    // 复数
    println!("{}", t!("items", count = 0));  // 没有项目
    println!("{}", t!("items", count = 5));  // 5 个项目
}
```

---

### 3. gettext (传统i18n 💡)

**添加依赖**: `cargo add gettext-rs`  
**用途**: GNU gettext 实现

```rust
use gettext::{Catalog, Translation};

fn main() {
    let mut catalog = Catalog::empty();
    catalog.add_translation("Hello", "你好");
    catalog.add_translation("Goodbye", "再见");
    
    println!("{}", catalog.gettext("Hello"));  // 输出: 你好
}
```

---

### 4. tr (简单翻译 💡)

**添加依赖**: `cargo add tr`  
**用途**: 轻量级翻译工具

```rust
use tr::tr;

fn main() {
    tr::set_lang("zh-CN");
    
    println!("{}", tr!("Hello, World!"));
}
```

---

## 💡 最佳实践

### 1. Web 应用国际化

```rust
use axum::{
    Router,
    routing::get,
    extract::Request,
    middleware::{self, Next},
    response::Response,
};
use rust_i18n::{i18n, set_locale, t};

// 初始化翻译
i18n!("locales");

// 语言检测中间件
async fn detect_language(req: Request, next: Next) -> Response {
    // 从 Accept-Language 头检测语言
    if let Some(accept_lang) = req.headers().get("Accept-Language") {
        if let Ok(lang) = accept_lang.to_str() {
            if lang.starts_with("zh") {
                set_locale("zh-CN");
            } else {
                set_locale("en");
            }
        }
    }
    
    next.run(req).await
}

async fn index() -> String {
    t!("welcome")
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(index))
        .layer(middleware::from_fn(detect_language));
    
    // ...
}
```

### 2. CLI 工具国际化

```rust
use clap::Parser;
use rust_i18n::{i18n, set_locale, t};

i18n!("locales");

#[derive(Parser)]
struct Cli {
    /// Language (en, zh-CN, ja)
    #[arg(short, long, default_value = "en")]
    lang: String,
}

fn main() {
    let cli = Cli::parse();
    set_locale(&cli.lang);
    
    println!("{}", t!("app.title"));
    println!("{}", t!("app.description"));
}
```

### 3. 动态语言切换

```rust
use rust_i18n::{i18n, set_locale, t};
use std::sync::RwLock;

i18n!("locales");

static CURRENT_LANG: RwLock<String> = RwLock::new(String::new());

pub fn get_lang() -> String {
    CURRENT_LANG.read().unwrap().clone()
}

pub fn set_lang(lang: &str) {
    *CURRENT_LANG.write().unwrap() = lang.to_string();
    set_locale(lang);
}

fn main() {
    set_lang("en");
    println!("{}", t!("hello"));  // Hello
    
    set_lang("zh-CN");
    println!("{}", t!("hello"));  // 你好
}
```

### 4. 日期和时间本地化

```rust
use chrono::{DateTime, Utc, Local};
use chrono::format::strftime::StrftimeItems;

fn format_date(dt: DateTime<Utc>, locale: &str) -> String {
    match locale {
        "zh-CN" => dt.format("%Y年%m月%d日").to_string(),
        "ja" => dt.format("%Y年%m月%d日").to_string(),
        _ => dt.format("%B %d, %Y").to_string(),
    }
}

fn main() {
    let now = Utc::now();
    
    println!("{}", format_date(now, "en"));     // October 20, 2025
    println!("{}", format_date(now, "zh-CN"));  // 2025年10月20日
}
```

---

## 📊 工具对比

| 工具 | 性能 | 易用性 | 功能 | 生态 | 推荐场景 |
|------|------|--------|------|------|---------|
| **fluent** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 复杂应用 |
| **rust-i18n** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | Web应用 |
| **gettext-rs** | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 传统项目 |
| **tr** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐ | 简单场景 |

---

## 🎯 实战场景

### 场景1: 多语言 API 响应

```rust
use axum::{Json, response::IntoResponse};
use serde::{Serialize, Deserialize};
use rust_i18n::t;

#[derive(Serialize)]
struct ApiResponse {
    message: String,
    data: Option<serde_json::Value>,
}

async fn get_user(lang: Option<String>) -> impl IntoResponse {
    // 设置语言
    if let Some(lang) = lang {
        rust_i18n::set_locale(&lang);
    }
    
    Json(ApiResponse {
        message: t!("api.user.success"),
        data: Some(serde_json::json!({ "id": 123 })),
    })
}
```

### 场景2: 表单验证错误

**locales/en.yml**:

```yaml
validation:
  required: "%{field} is required"
  email: "Invalid email format"
  min_length: "%{field} must be at least %{min} characters"
```

**locales/zh-CN.yml**:

```yaml
validation:
  required: "%{field} 是必填的"
  email: "邮箱格式不正确"
  min_length: "%{field} 至少需要 %{min} 个字符"
```

```rust
use rust_i18n::t;

fn validate_email(email: &str) -> Result<(), String> {
    if email.is_empty() {
        return Err(t!("validation.required", field = "Email"));
    }
    
    if !email.contains('@') {
        return Err(t!("validation.email"));
    }
    
    Ok(())
}
```

---

## 🔗 相关资源

- [Fluent Project](https://projectfluent.org/)
- [rust-i18n Documentation](https://docs.rs/rust-i18n/)
- [CLDR - Unicode Locale Data](https://cldr.unicode.org/)

---

**导航**: [返回横切关注点](../README.md) | [下一类别：序列化](../serialization/README.md)
