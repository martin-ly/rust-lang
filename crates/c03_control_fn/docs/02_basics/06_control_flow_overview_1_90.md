# 06. Rust 1.90 控制流特性总览 (Control Flow Overview - Rust 1.90)

> **文档类型**：基础/参考  
> **难度等级**：⭐⭐  
> **预计阅读时间**：1小时  
> **前置知识**：Rust 基础语法


## 📊 目录

- [06. Rust 1.90 控制流特性总览 (Control Flow Overview - Rust 1.90)](#06-rust-190-控制流特性总览-control-flow-overview---rust-190)
  - [📊 目录](#-目录)
  - [📚 目录](#-目录-1)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [if / if let / if let 链](#if--if-let--if-let-链)
  - [let-else 提前返回](#let-else-提前返回)
  - [match 概览（进阶详解见专章）](#match-概览进阶详解见专章)
  - [while / loop / for 与标签跳转](#while--loop--for-与标签跳转)
  - [break/continue 与值](#breakcontinue-与值)
  - [函数返回与发散类型 `!`](#函数返回与发散类型-)
  - [工程建议](#工程建议)


## 📚 目录

- [06. Rust 1.90 控制流特性总览 (Control Flow Overview - Rust 1.90)](#06-rust-190-控制流特性总览-control-flow-overview---rust-190)
  - [� 目录](#-目录)
  - [📚 目录](#-目录-1)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [if / if let / if let 链](#if--if-let--if-let-链)
  - [let-else 提前返回](#let-else-提前返回)
  - [match 概览（进阶详解见专章）](#match-概览进阶详解见专章)
  - [while / loop / for 与标签跳转](#while--loop--for-与标签跳转)
  - [break/continue 与值](#breakcontinue-与值)
  - [函数返回与发散类型 `!`](#函数返回与发散类型-)
  - [工程建议](#工程建议)

## 📖 内容概述

本文档系统梳理 Rust 1.90 版本可用的所有稳定控制流特性。采用简明定义、使用语义、注意事项的结构，配合可运行示例，便于读者快速查阅和实际工程中对照使用。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 了解 Rust 1.90 所有稳定的控制流特性
- [ ] 掌握 let-else、if let 链等新语法
- [ ] 理解循环标签和嵌套控制
- [ ] 使用 break 返回值
- [ ] 理解发散类型 ! 的作用

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
