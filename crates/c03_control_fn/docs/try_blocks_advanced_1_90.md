# try 块进阶（覆盖至 Rust 1.90）

本篇深入 `try { ... }` 表达式在复杂错误组合中的使用：本地化错误传播、细粒度映射、与 `?`、`Option`/`Result`、自定义错误类型的协作。

## 将一段逻辑变成表达式

```rust
fn sum2(a: Result<i32, &'static str>, b: Result<i32, &'static str>) -> Result<i32, &'static str> {
    let s: Result<i32, _> = try { a? + b? };
    s
}
```

## 在表达式位置做错误映射

```rust
#[derive(Debug, PartialEq)]
enum AppErr { Parse, Io }

fn parse_num(s: &str) -> Result<i32, AppErr> {
    s.parse::<i32>().map_err(|_| AppErr::Parse)
}

fn add_from_str(x: &str, y: &str) -> Result<i32, AppErr> {
    // try 块使得我们可以在一处完成 ? 传播并整体 map_err
    try { parse_num(x)? + parse_num(y)? }
}
```

## Option 与 Result 混用

```rust
fn head_plus_parsed(rest: &[&str]) -> Option<i32> {
    let v: Option<i32> = try {
        let s = *rest.get(0)?;
        let n = s.parse::<i32>().ok()?;
        n
    };
    v
}
```

## 建议

- 在复杂表达式中使用 `try` 收拢局部错误传播，减少临时变量；
- 与 `map_err`/自定义错误枚举配合，清晰表达边界；
- 对外接口维持稳定的错误类型，内部自由组合。
