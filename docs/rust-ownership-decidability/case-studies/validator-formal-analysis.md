# Validator 数据验证形式化分析

> **主题**: 声明式数据验证
>
> **形式化框架**: 验证规则组合 + 错误聚合
>
> **参考**: validator crate Documentation

---

## 目录

- [Validator 数据验证形式化分析](#validator-数据验证形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 派生宏语义](#2-派生宏语义)
    - [定理 2.1 (编译时生成)](#定理-21-编译时生成)
  - [3. 验证规则](#3-验证规则)
    - [定理 3.1 (规则短路)](#定理-31-规则短路)
  - [4. 嵌套验证](#4-嵌套验证)
    - [定理 4.1 (递归验证)](#定理-41-递归验证)
  - [5. 自定义验证](#5-自定义验证)
    - [定理 5.1 (自定义函数)](#定理-51-自定义函数)
  - [6. 反例](#6-反例)
    - [反例 6.1 (忘记调用validate)](#反例-61-忘记调用validate)
    - [反例 6.2 (并发修改)](#反例-62-并发修改)

---

## 1. 引言

validator提供:

- 派生宏自动生成验证
- 丰富内置验证器
- 嵌套结构验证
- 自定义验证函数

---

## 2. 派生宏语义

### 定理 2.1 (编译时生成)

> Validate派生宏在编译时生成验证代码。

```rust
#[derive(Validate)]
struct User {
    #[validate(email)]
    email: String,

    #[validate(length(min = 8))]
    password: String,
}

// 展开后实现Validate trait
impl Validate for User {
    fn validate(&self) -> Result<(), ValidationErrors> {
        // 验证email格式
        // 验证password长度
    }
}
```

∎

---

## 3. 验证规则

### 定理 3.1 (规则短路)

> 验证失败立即停止该字段后续验证。

| 验证器 | 语义 |
|--------|------|
| email | RFC合规邮箱 |
| url | 有效URL |
| length(min, max) | 长度范围 |
| range(min, max) | 数值范围 |
| regex | 正则匹配 |
| must_match | 字段相等 |

∎

---

## 4. 嵌套验证

### 定理 4.1 (递归验证)

> 嵌套结构自动递归验证。

```rust
#[derive(Validate)]
struct Company {
    #[validate]
    ceo: User,  // 递归验证User

    #[validate(length(min = 1))]
    employees: Vec<User>,  // 验证每个元素
}
```

∎

---

## 5. 自定义验证

### 定理 5.1 (自定义函数)

> 支持自定义验证逻辑。

```rust
#[derive(Validate)]
struct Order {
    #[validate(custom = "validate_delivery_date")]
    delivery_date: String,
}

fn validate_delivery_date(date: &str) -> Result<(), ValidationError> {
    // 自定义逻辑
}
```

∎

---

## 6. 反例

### 反例 6.1 (忘记调用validate)

```rust
let user = User { email, password };
// 错误: 直接使用未验证数据
save_to_db(&user);

// 正确
user.validate()?;
save_to_db(&user);
```

### 反例 6.2 (并发修改)

```rust
// 验证后修改数据绕过验证
user.validate()?;
user.email = "invalid".to_string();  // 绕过!
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
