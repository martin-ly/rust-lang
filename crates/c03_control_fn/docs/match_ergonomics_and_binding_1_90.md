# match 人体工学与绑定技巧（覆盖至 Rust 1.90）

本篇聚焦 `match` 的可读性与工程实践：穷尽性检查、绑定 (`@`)、守卫、引用/可变引用匹配、最小捕获的人体工学、枚举未来兼容性设计。

## 穷尽性与兜底

- 让编译器帮助你覆盖所有分支；
- 对外 API 建议保留兜底 `_`，避免未来枚举新增破坏下游。

```rust
enum Msg { Ping, Pong, Data(i32) }

fn handle(m: Msg) -> &'static str {
    match m {
        Msg::Ping => "ping",
        Msg::Pong => "pong",
        Msg::Data(x) if x > 0 => "pos",
        Msg::Data(_) => "nonpos",
    }
}
```

## 绑定与再利用（`@`）

```rust
fn describe(bytes: &[u8]) -> String {
    match bytes {
        head @ [0x7F, b'E', b'L', b'F', ..] => format!("ELF: {} bytes", head.len()),
        other => format!("raw: {} bytes", other.len()),
    }
}
```

## 引用与可变引用匹配

```rust
fn touch_first(v: &mut Vec<i32>) {
    match v.as_mut_slice() {
        [x, ..] => *x += 1,
        [] => {}
    }
}
```

## 人体工学：最小捕获与字段捕获

- 现代 Rust 会按需最小捕获，仅捕获闭包/匹配用到的部分字段；
- 利用结构体/枚举解构让“读必要字段”的意图更加明确。

```rust
struct Config { host: String, port: u16, tls: bool }

fn port_enabled(c: &Config) -> bool {
    match c {
        Config { port, .. } if *port != 0 => true,
        _ => false,
    }
}
```

---

工程建议：

- 在复杂布尔表达式前优先考虑“解构 + 守卫”；
- 同时需要整体值与部分字段时使用 `@`；
- 公共枚举匹配保留兜底，私有内部枚举不必过度兜底以获得更强的穷尽性检查。
