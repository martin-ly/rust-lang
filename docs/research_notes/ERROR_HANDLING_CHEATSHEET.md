# 错误处理速查卡

> **一页纸速查** - Result、Option、错误处理模式

---

## Result与Option

| 类型 | 用途 | 方法 |
| :--- | :--- | :--- |
| `Option<T>` | 可能有值 | `Some(T)` / `None` |
| `Result<T, E>` | 可能成功 | `Ok(T)` / `Err(E)` |

---

## 常用方法

### Option

```rust
opt.unwrap()        // 获取值，None时panic
opt.unwrap_or(def)  // 获取值或默认值
opt.ok_or(err)      // Option -> Result
opt.map(|v| ...)    // 映射
opt.and_then(|v| ...) // 链式操作
```

### Result

```rust
res.unwrap()        // 获取值，Err时panic
res?                // 传播错误
res.map_err(|e| ...) // 错误映射
res.and_then(|v| ...) // 链式操作
```

---

## ?操作符

```rust
fn may_fail() -> Result<T, Error> {
    let x = operation1()?;  // 错误时提前返回
    let y = operation2()?;
    Ok(y)
}
```

---

## 错误转换

```rust
// From trait自动转换
impl From<IOError> for MyError {
    fn from(e: IOError) -> Self { ... }
}

// 使用
let file = File::open("file")?;  // IOError自动转为MyError
```

---

## panic vs Result

| 情况 | 使用 |
| :--- | :--- |
| 不可恢复错误 | `panic!` |
| 可恢复错误 | `Result` |
| 可选值 | `Option` |
| 编程错误 | `assert!` / `unreachable!` |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 错误处理速查卡 (4/5)
