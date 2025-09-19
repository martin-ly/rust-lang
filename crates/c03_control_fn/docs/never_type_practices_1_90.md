# 发散类型 `!` 实战（覆盖至 Rust 1.90）

`!` 表示永不返回。用于不可达分支、终止程序、无限循环等场景，并能在类型推断中“流入”期望位置。

## 与 `Option::unwrap_or_else` 配合

```rust
fn abort(msg: &str) -> ! { panic!("{}", msg); }

fn must(v: Option<i32>) -> i32 {
    v.unwrap_or_else(|| abort("none"))
}
```

## 不可达分支（如 `match` 的逻辑保证）

```rust
fn only_true(b: bool) {
    match b {
        true => {}
        false => unreachable!(),
    }
}
```

## 无限循环/进程退出

```rust
fn never_returns() -> ! { loop {} }
```

---

工程建议：

- 谨慎使用 `panic!/abort`，限定在不可恢复错误；
- `!` 有助于 API 设计中的“永不返回”表达，但注意可测试性。
