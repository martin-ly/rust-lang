# while let / if let 链（覆盖至 Rust 1.90）

系统化展示 `if let` 链、`while let` 流水式解构与守卫，简化层层嵌套判断。

## if let 链

```rust
fn parse(input: Option<Result<&str, &'static str>>) -> &'static str {
    if let Some(Ok(s)) = input {
        if s.is_empty() { "empty" } else { "ok" }
    } else if let Some(Err(_)) = input {
        "err"
    } else {
        "none"
    }
}
```

## while let 流水处理

```rust
fn drain_until_neg(mut v: Vec<i32>) -> Vec<i32> {
    let mut out = Vec::new();
    while let Some(x) = v.pop() {
        if x < 0 { break; }
        out.push(x);
    }
    out
}
```

---

工程建议：

- 链式 `if let` 适合“逐步缩小条件空间”的判断；
- 连续弹出/消费类逻辑优先 `while let`；
- 分支复杂时考虑改用 `match`。
