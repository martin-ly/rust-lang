# let-else 模式手册（覆盖至 Rust 1.90）

`let PATTERN = EXPR else { ... };` 当解构失败时立刻执行 `else`，常用于早退、跳过或继续。

## 典型用法：参数校验 + 早退

```rust
fn get_port(s: &str) -> Result<u16, String> {
    let Some(rest) = s.strip_prefix("port=") else { return Err("missing".into()); };
    let Ok(n) = rest.parse::<u16>() else { return Err("nan".into()); };
    Ok(n)
}
```

## 在循环中使用：继续/跳出

```rust
fn collect_even(nums: &[i32]) -> Vec<i32> {
    let mut out = Vec::new();
    for &n in nums {
        let true = n % 2 == 0 else { continue };
        out.push(n);
    }
    out
}
```

---

工程建议：

- 将失败路径前置，保持主路径直行；
- `else` 内使用 `return/break/continue` 明确控制流；
- 与 `?` 互补：结构性检查（let-else）与错误传播（`?`）。
