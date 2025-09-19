# 模式匹配进阶（覆盖至 Rust 1.90）

本篇聚焦 `match`/`let`/`if let` 中的高级模式语法与实践要点，涵盖解构、守卫、绑定、切片/数组模式、或模式、引用/可变引用匹配、`matches!` 宏等。

## 解构与绑定（`@`）

```rust
enum Token { Ident(String), Number(i64), Symbol(char) }

fn classify(tok: Token) -> String {
    match tok {
        name @ Token::Ident(_) => format!("ident: {:?}", name),
        n @ Token::Number(_) => format!("number: {:?}", n),
        Token::Symbol(c) if c.is_ascii_punctuation() => "punct".into(),
        Token::Symbol(_) => "symbol".into(),
    }
}
```

要点：`pat @ subpat` 可同时保留整体与子结构。

## 或模式（`|`）与范围

```rust
fn classify_char(c: char) -> &'static str {
    match c {
        'a'..='z' | 'A'..='Z' => "alpha",
        '0'..='9' => "digit",
        '_' | '-' => "name_sep",
        _ => "other",
    }
}
```

## 守卫（`if`）

```rust
fn pos_or_neg(n: i32) -> &'static str {
    match n {
        x if x > 0 => "pos",
        0 => "zero",
        _ => "neg",
    }
}
```

## 引用与可变引用匹配（`ref`/`ref mut`）

```rust
fn first_char_uppercase(s: &mut String) -> Option<char> {
    match s.as_bytes_mut() {
        // 切片可变借用 + 解构第一个字节
        [first @ .., ..] if !first.is_empty() => {
            // 这里只展示解构的写法，实际对 UTF-8 需谨慎处理
            s.make_ascii_uppercase();
            s.chars().next()
        }
        _ => None,
    }
}
```

说明：现代 Rust 中，`ref`/`ref mut` 多被借用方式替代；当在 `match` 中取引用绑定时仍然有用。

## 元组/结构体/枚举解构

```rust
struct Point { x: i32, y: i32 }

fn on_axis(p: Point) -> bool {
    match p {
        Point { x: 0, .. } | Point { y: 0, .. } => true,
        _ => false,
    }
}
```

## 数组与切片模式

```rust
fn head_tail(nums: &[i32]) -> Option<(i32, i32)> {
    match nums {
        [first, .., last] => Some((*first, *last)),
        [one] => Some((*one, *one)),
        _ => None,
    }
}
```

注意：切片模式会发生借用，关注生命周期与可变性。

## `matches!` 宏

```rust
fn is_ok_even(x: Result<i32, ()>) -> bool {
    matches!(x, Ok(n) if n % 2 == 0)
}
```

## 非穷尽与兜底

对未来可能扩展的枚举，公开 API 使用 `_` 或显式兜底分支，以保持向后兼容。

---

工程提示：

- 复杂条件优先使用“解构 + 守卫”而非多层 `if`。
- 需要同时保留整体值与局部字段时使用 `@` 绑定。
- 切片/数组模式有可读性优势，但注意性能敏感路径上的拷贝/借用成本。
