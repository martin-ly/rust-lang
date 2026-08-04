---
title: 类型转换最佳实践（From/Into/TryFrom/AsRef/AsMut/Deref）
lang: zh-CN
---

目标：在 Rust 1.90 语境下梳理常见转换 Trait 的使用边界与风格建议。

核心建议：

- 优先实现 `From<T> for U`，自动获得 `Into<U> for T`；对可能失败的转换实现 `TryFrom<T> for U`。
- 参数位置优先用 `AsRef<T>`/`AsMut<T>` 以兼容更多传入类型；返回位置避免过度抽象。
- `Deref` 仅用于“智能指针语义”的透明解引用；不要滥用它来做逻辑转换。
- 公共 API 中尽量返回所有权类型（如 `String`, `Vec<T>`），减少借用外溢；内部复用用借用传递。

示例：

```rust
use core::convert::{From, TryFrom};

struct UserId(u64);

impl From<u64> for UserId { fn from(x: u64) -> Self { UserId(x) } }

#[derive(Debug)]
enum ParseUserIdError { Empty, NotNumber(core::num::ParseIntError) }

impl TryFrom<&str> for UserId {
    type Error = ParseUserIdError;
    fn try_from(s: &str) -> Result<Self, Self::Error> {
        if s.is_empty() { return Err(ParseUserIdError::Empty); }
        let n: u64 = s.parse().map_err(ParseUserIdError::NotNumber)?;
        Ok(UserId(n))
    }
}

fn takes_path<P: AsRef<std::path::Path>>(p: P) {
    let _ = p.as_ref();
}
```
