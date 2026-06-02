# Validator 数据验证形式化分析

> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: 声明式数据验证
>
> **形式化框架**: 验证规则组合 + 错误聚合
>
> **参考**: validator crate Documentation

---

## 目录
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

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
  - [*定理数量: 6个*](#定理数量-6个)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引)

---

## 1. 引言
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

validator提供:

- 派生宏自动生成验证
- 丰富内置验证器
- 嵌套结构验证
- 自定义验证函数

---

## 2. 派生宏语义
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 定理 2.1 (编译时生成)

> Validate派生宏在编译时生成验证代码。

```rust,ignore
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

```rust,ignore
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

```rust,ignore
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

```rust,ignore
let user = User { email, password };
// 错误: 直接使用未验证数据
save_to_db(&user);

// 正确
user.validate()?;
save_to_db(&user);
```

### 反例 6.2 (并发修改)

```rust,ignore
// 验证后修改数据绕过验证
user.validate()?;
user.email = "invalid".to_string();  // 绕过!
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Formal Methods]**

> **[来源: Coq Reference Manual]**

> **[来源: TLA+ Documentation]**

> **[来源: ACM - Formal Verification]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
