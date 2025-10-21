# Validation - 数据验证

## 📋 目录

- [Validation - 数据验证](#validation---数据验证)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [validator](#validator)
    - [基础验证](#基础验证)
    - [自定义验证](#自定义验证)
    - [嵌套验证](#嵌套验证)
  - [garde](#garde)
    - [基础用法](#基础用法)
  - [实战示例](#实战示例)
    - [Axum 集成](#axum-集成)
    - [API 输入验证](#api-输入验证)
  - [错误处理](#错误处理)
    - [友好的错误消息](#友好的错误消息)
  - [参考资源](#参考资源)

---

## 概述

数据验证确保输入数据符合预期格式和约束。

### 核心依赖

```toml
[dependencies]
validator = { version = "0.18", features = ["derive"] }
garde = { version = "0.18", features = ["full"] }
```

---

## validator

### 基础验证

```rust
use validator::{Validate, ValidationError};

#[derive(Debug, Validate)]
struct SignupForm {
    #[validate(email)]
    email: String,
    
    #[validate(length(min = 8, max = 100))]
    password: String,
    
    #[validate(range(min = 18, max = 120))]
    age: u32,
    
    #[validate(url)]
    website: Option<String>,
    
    #[validate(must_match = "password")]
    password_confirmation: String,
}

fn validate_form() {
    let form = SignupForm {
        email: "user@example.com".to_string(),
        password: "password123".to_string(),
        age: 25,
        website: Some("https://example.com".to_string()),
        password_confirmation: "password123".to_string(),
    };
    
    match form.validate() {
        Ok(_) => println!("验证通过"),
        Err(e) => println!("验证失败: {:?}", e),
    }
}
```

### 自定义验证

```rust
use validator::{Validate, ValidationError};

fn validate_username(username: &str) -> Result<(), ValidationError> {
    if username.contains('@') {
        return Err(ValidationError::new("username_invalid"));
    }
    Ok(())
}

#[derive(Debug, Validate)]
struct User {
    #[validate(custom = "validate_username")]
    username: String,
}
```

### 嵌套验证

```rust
use validator::Validate;

#[derive(Debug, Validate)]
struct Address {
    #[validate(length(min = 1))]
    street: String,
    
    #[validate(length(min = 1))]
    city: String,
}

#[derive(Debug, Validate)]
struct Profile {
    #[validate(email)]
    email: String,
    
    #[validate]
    address: Address,
}
```

---

## garde

### 基础用法

```rust
use garde::{Validate, rules};

#[derive(Debug, Validate)]
struct CreateUser {
    #[garde(length(min = 3, max = 50))]
    username: String,
    
    #[garde(email)]
    email: String,
    
    #[garde(range(min = 18))]
    age: u8,
}

fn main() {
    let user = CreateUser {
        username: "john".to_string(),
        email: "john@example.com".to_string(),
        age: 25,
    };
    
    if let Err(e) = user.validate() {
        println!("验证错误: {:?}", e);
    }
}
```

---

## 实战示例

### Axum 集成

```rust
use axum::{Router, routing::post, Json, http::StatusCode};
use validator::Validate;
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Validate)]
struct CreatePost {
    #[validate(length(min = 1, max = 200))]
    title: String,
    
    #[validate(length(min = 1))]
    content: String,
    
    #[validate(email)]
    author_email: String,
}

#[derive(Serialize)]
struct ErrorResponse {
    errors: Vec<String>,
}

async fn create_post(
    Json(payload): Json<CreatePost>,
) -> Result<StatusCode, (StatusCode, Json<ErrorResponse>)> {
    payload.validate().map_err(|e| {
        let errors: Vec<String> = e
            .field_errors()
            .iter()
            .flat_map(|(field, errors)| {
                errors.iter().map(move |error| {
                    format!("{}: {}", field, error.message.as_ref().unwrap_or(&"Invalid".into()))
                })
            })
            .collect();
        
        (
            StatusCode::BAD_REQUEST,
            Json(ErrorResponse { errors })
        )
    })?;
    
    // 处理有效数据
    Ok(StatusCode::CREATED)
}

#[tokio::main]
async fn main() {
    let app = Router::new().route("/posts", post(create_post));
    
    println!("服务器运行中...");
}
```

### API 输入验证

```rust
use validator::{Validate, ValidationError};

#[derive(Debug, Validate)]
struct SearchQuery {
    #[validate(length(min = 1, max = 100))]
    query: String,
    
    #[validate(range(min = 1, max = 100))]
    page: Option<u32>,
    
    #[validate(range(min = 10, max = 100))]
    per_page: Option<u32>,
    
    #[validate(custom = "validate_sort_field")]
    sort: Option<String>,
}

fn validate_sort_field(sort: &str) -> Result<(), ValidationError> {
    let valid_fields = ["created_at", "updated_at", "title"];
    
    if !valid_fields.contains(&sort) {
        return Err(ValidationError::new("invalid_sort_field"));
    }
    
    Ok(())
}
```

---

## 错误处理

### 友好的错误消息

```rust
use validator::{Validate, ValidationErrors};
use std::collections::HashMap;

fn format_validation_errors(errors: &ValidationErrors) -> HashMap<String, Vec<String>> {
    let mut result = HashMap::new();
    
    for (field, errors) in errors.field_errors() {
        let messages: Vec<String> = errors
            .iter()
            .map(|error| {
                error.message
                    .as_ref()
                    .map(|m| m.to_string())
                    .unwrap_or_else(|| error.code.to_string())
            })
            .collect();
        
        result.insert(field.to_string(), messages);
    }
    
    result
}
```

---

## 参考资源

- [validator 文档](https://docs.rs/validator/)
- [garde GitHub](https://github.com/jprochazk/garde)
