# Rust 1.95.0 `if let` Guards on Match Arms 深度专题

> **稳定版本**: Rust 1.95.0 (2026-04-16)
> **权威来源**: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)

---

## 概述

`if let` guards 是 Rust 1.95.0 稳定化的重要语言特性，它允许在 `match` 表达式的 arm 上直接使用 `if let` 进行模式匹配和条件判断，从而将原本需要嵌套的 `match + if let` 结构扁平化为单一表达式。

这一特性与 Rust 2024 Edition 的 `let chains`（稳定于 1.88.0）形成互补：

- `let chains` 用于 `if` / `while` 条件表达式
- `if let` guards 用于 `match` arm 的守卫条件

---

## 语法

```rust
match value {
    Some(x) if let Ok(y) = parse(x) => {
        // x 和 y 在此作用域内同时可用
        println!("parsed: {}, {}", x, y);
    }
    Some(_) => println!("parse failed"),
    None => println!("no value"),
}
```

### 关键规则

1. **`if let` guard 必须跟在模式之后**，位于 `=>` 之前
2. **guard 中绑定的变量在 arm 体中可用**，与模式绑定的变量共同作用
3. **exhaustiveness 检查不会考虑 guard 中的模式**：编译器不会将 `if let Ok(y) = ...` 视为已覆盖 `Err` 分支（与普通的 `if` guard 行为一致）
4. **可以与普通布尔条件混合使用**：`Some(x) if x > 0 && let Ok(y) = parse(x) => ...`

---

## 与传统写法的对比

### 传统嵌套写法（Rust 1.94 及之前）

```rust
fn handle_value(value: Option<&str>) -> &'static str {
    match value {
        Some(s) => {
            if let Ok(n) = s.parse::<i32>() {
                if n > 0 && n <= 100 {
                    "valid positive number"
                } else {
                    "number out of range"
                }
            } else {
                "not a number"
            }
        }
        None => "no value",
    }
}
```

### `if let` guard 扁平化写法（Rust 1.95.0+）

```rust
fn handle_value(value: Option<&str>) -> &'static str {
    match value {
        Some(s) if let Ok(n) = s.parse::<i32>() && n > 0 && n <= 100 => {
            "valid positive number"
        }
        Some(_) => "invalid input",
        None => "no value",
    }
}
```

**优势**：

- 嵌套层级从 4 层降至 1 层
- 每个 `match` arm 的职责单一、清晰
- 避免右漂移（rightward drift）

---

## 完整示例

### 示例 1：命令解析器

```rust
#[derive(Debug, PartialEq)]
enum Command {
    Move { x: i32, y: i32 },
    Say(String),
    Quit,
}

fn parse_command(input: &str) -> Result<Command, &'static str> {
    let parts: Vec<&str> = input.split_whitespace().collect();

    match parts.as_slice() {
        ["move", x_str, y_str] if let Ok(x) = x_str.parse::<i32>() && let Ok(y) = y_str.parse::<i32>() => {
            Ok(Command::Move { x, y })
        }
        ["say", text @ ..] if !text.is_empty() => {
            Ok(Command::Say(text.join(" ")))
        }
        ["quit"] => Ok(Command::Quit),
        [] => Err("empty command"),
        _ => Err("unknown command"),
    }
}
```

### 示例 2：链式 API 响应处理

```rust
enum ApiResponse {
    Success { data: String, status: u16 },
    Error { code: u16, message: String },
}

fn process_response(resp: ApiResponse) -> &'static str {
    match resp {
        ApiResponse::Success { data, status }
            if status == 200 && let Ok(json) = serde_json::from_str::<serde_json::Value>(&data) && json.get("ok").is_some() =>
        {
            "successful with valid payload"
        }
        ApiResponse::Success { status, .. } if status == 204 => "successful no content",
        ApiResponse::Success { .. } => "successful but unexpected format",
        ApiResponse::Error { code, .. } if (400..500).contains(&code) => "client error",
        ApiResponse::Error { .. } => "server error",
    }
}
```

### 示例 3：递归数据结构遍历

```rust
enum Expr {
    Literal(i32),
    Add(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
}

fn eval(expr: &Expr) -> Option<i32> {
    match expr {
        Expr::Literal(n) => Some(*n),
        Expr::Add(a, b) if let Some(x) = eval(a) && let Some(y) = eval(b) => Some(x + y),
        Expr::Div(a, b)
            if let Some(x) = eval(a) && let Some(y) = eval(b) && y != 0 =>
        {
            Some(x / y)
        }
        _ => None,
    }
}
```

---

## 与 `let chains` 的协同使用

```rust
fn process_records(records: Vec<Option<&str>>) -> Vec<i32> {
    let mut results = Vec::new();

    for record in records {
        // let chains 用于循环内过滤
        if let Some(s) = record
            && let Ok(n) = s.parse::<i32>()
            && n > 0
        {
            results.push(n);
        }
    }

    results
}

fn classify_value(value: Option<&str>) -> &'static str {
    // if let guard 用于 match 分发
    match value {
        Some(s) if let Ok(n) = s.parse::<i32>() && n > 0 => "positive integer",
        Some(s) if let Ok(n) = s.parse::<i32>() && n < 0 => "negative integer",
        Some(s) if s.is_empty() => "empty string",
        Some(_) => "non-numeric string",
        None => "no value",
    }
}
```

---

## 注意事项与限制

1. **Exhaustiveness 不感知 guard**：以下代码编译通过，但运行时可能 panic（如果 `parse` 失败会落入 `_`）：

   ```rust
   match Some("hello") {
       Some(s) if let Ok(n) = s.parse::<i32>() => println!("{}", n),
       None => println!("none"),
       // 编译器不会要求处理 Some(s) where parse fails 的情况
       _ => println!("other"),
   }
   ```

2. **变量遮蔽**：guard 中绑定的变量名如果与模式变量冲突，会遵循正常的遮蔽规则。

3. **性能**：`if let` guards 不会引入额外的运行时开销，它们在语义上等价于在 arm 体内部展开的条件判断。

---

## 迁移建议

对于现有代码中大量存在的 `match + 内部 if let` 模式，建议在升级到 Rust 1.95.0 后逐步重构：

- **优先重构深度嵌套（>2 层）**的 `match → if → if let` 结构
- **保持语义等价**：确保重构前后所有分支的行为一致
- **利用 guard 减少 `_ =>` 通配分支**：更精确的模式匹配意味着更少的兜底处理

---

## 参考

- [Rust 1.95.0 发布公告 - if let guards](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)
- [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html)
- [RFC 2294 - if let chains](https://rust-lang.github.io/rfcs/2294-if-let-chains.html)（基础语法设计）
