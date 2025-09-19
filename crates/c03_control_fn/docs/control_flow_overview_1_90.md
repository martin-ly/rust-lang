# 控制流总览（覆盖至 Rust 1.90）

本节系统梳理 Rust 的控制流与函数相关语法，覆盖至 Rust 1.90 版本可用的稳定特性。文中给出简明定义、使用语义、注意事项与可运行示例，便于读者在实际工程中对照使用。

- 目标读者：具备基础 Rust 语法的开发者
- 参考版本：Rust 1.90（稳定通道），如无特别说明，均为稳定特性

## 目录

- if / if let / if let 链
- let-else 提前返回
- match 模式匹配（见进阶篇）
- while / loop / for 及标签跳转
- break/continue 与值
- 函数与返回值、发散类型 `!`
- 闭包与 `Fn*` 特征（见专章）
- 迭代器与 `try_fold`（见专章）
- 错误处理与 `?`（见专章）

---

## if / if let / if let 链

- `if` 支持常规条件分支；
- `if let` 用于“匹配 + 解构 + 守卫”的快捷场景；
- `if let` 可以链式使用（`else if let`）以渐进匹配不同形态。

示例：

```rust
fn demo_if_iflet_chain(input: Option<Result<i32, &'static str>>) -> i32 {
    if let Some(Ok(x)) = input {
        x
    } else if let Some(Err(_e)) = input {
        0
    } else {
        -1
    }
}
```

要点：

- `if let` 失败时不会引入绑定；
- 当分支很多且结构复杂时，优先考虑 `match` 提升可读性。

## let-else 提前返回

- 语义：当解构失败时，立即执行 `else` 代码块（通常为提前返回、break、continue）。
- 适合“必须成功解构，否则立即终止”的场景，提升可读性。

```rust
fn parse_port(s: &str) -> Result<u16, String> {
    let Some(rest) = s.strip_prefix("port=") else {
        return Err("缺少前缀 port=".into());
    };
    let Ok(num) = rest.parse::<u16>() else {
        return Err("端口不是 u16 数字".into());
    };
    Ok(num)
}
```

要点：

- `let PATTERN = EXPR else { ... };`
- `else` 代码块中常见操作：`return`、`break`、`continue`、`panic!`。

## match 概览（进阶详解见专章）

- 覆盖：字面量、范围、枚举、结构体/元组解构、守卫、可空引用匹配等。
- “穷尽性检查”保证覆盖所有可能分支，常配合 `_` 通配符处理兜底。

```rust
fn kind_of_char(c: char) -> &'static str {
    match c {
        '0'..='9' => "digit",
        'a'..='z' | 'A'..='Z' => "alpha",
        _ => "other",
    }
}
```

## while / loop / for 与标签跳转

- `loop` 无限循环，配合 `break` 跳出；
- `while` 条件循环；
- `for` 基于 `IntoIterator` 的迭代；
- 支持标签跳转：`'label: loop { ... break 'label; }`。

```rust
fn find_first_even(nums: &[i32]) -> Option<i32> {
    'outer: for &n in nums {
        if n % 2 != 0 { continue; }
        // 命中即返回
        break 'outer Some(n);
    }
}
```

要点：

- `break` 可带值结束循环：`let x = loop { break 42; };`；
- 多层嵌套时用标签明确控制流走向。

## break/continue 与值

- `break` 可返回一个值给循环表达式：

```rust
fn index_of(nums: &[i32], target: i32) -> Option<usize> {
    let idx = loop {
        for (i, &n) in nums.iter().enumerate() {
            if n == target { break Some(i); }
        }
        break None;
    };
    idx
}
```

## 函数返回与发散类型 `!`

- 常规函数返回具体类型或 `()`；
- 发散类型 `!` 表示“不会返回”的计算（如 `panic!`、`loop {}`、`std::process::exit`）。

```rust
fn never_returns() -> ! {
    panic!("永不返回");
}

fn pick(a: Option<i32>) -> i32 {
    a.unwrap_or_else(|| never_returns())
}
```

---

## 工程建议

- 优先让控制流“正向直行”，异常/早退放在早期分支（`let-else`、`?`）。
- 嵌套层级>2时，考虑拆分函数或使用标签/`match` 提升可读性。
- 对外可见 API 保持返回类型稳定、清晰；内部可使用断言保障不变量。
