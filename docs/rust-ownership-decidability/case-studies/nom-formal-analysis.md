# Nom 解析器组合子形式化分析

> **主题**: 零拷贝解析器组合子库
>
> **形式化框架**: 解析器组合子 + 剩余输入传递
>
> **参考**: nom Documentation

---

## 目录

- [Nom 解析器组合子形式化分析](#nom-解析器组合子形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. IResult类型](#2-iresult类型)
    - [定义 2.1 (IResult)](#定义-21-iresult)
    - [定理 2.1 (剩余输入传递)](#定理-21-剩余输入传递)
  - [3. 组合子代数](#3-组合子代数)
    - [定理 3.1 (序列组合)](#定理-31-序列组合)
    - [定理 3.2 (选择组合)](#定理-32-选择组合)
    - [定理 3.3 (重复组合)](#定理-33-重复组合)
  - [4. 零拷贝保证](#4-零拷贝保证)
    - [定理 4.1 (切片重用)](#定理-41-切片重用)
  - [5. 流式解析](#5-流式解析)
    - [定理 5.1 (不完整输入)](#定理-51-不完整输入)
  - [6. 反例](#6-反例)
    - [反例 6.1 (递归深度)](#反例-61-递归深度)
    - [反例 6.2 (UTF8边界)](#反例-62-utf8边界)

---

## 1. 引言

nom提供:

- 解析器组合子
- 零拷贝解析
- 无alloc选项
- 流式解析支持

---

## 2. IResult类型

### 定义 2.1 (IResult)

```rust
type IResult<I, O, E = Error<I>> = Result<(I, O), Err<E>>;
// (剩余输入, 输出值) 或 错误
```

### 定理 2.1 (剩余输入传递)

> 解析器返回剩余输入供后续解析。

```rust
fn pair_parser(input: &str) -> IResult<&str, (u32, u32)> {
    let (input, n1) = u32_parser(input)?;
    let (input, _) = space_parser(input)?;
    let (input, n2) = u32_parser(input)?;
    Ok((input, (n1, n2)))
}
```

∎

---

## 3. 组合子代数

### 定理 3.1 (序列组合)

> `tuple`组合子顺序执行解析器。

```rust
let parser = tuple((u32_parser, space_parser, u32_parser));
// 类型: (u32, (), u32)
```

∎

### 定理 3.2 (选择组合)

> `alt`尝试多个解析器，返回第一个成功。

```rust
let parser = alt((hex_parser, decimal_parser, binary_parser));
// 优先级: 从左到右
```

∎

### 定理 3.3 (重复组合)

| 组合子 | 语义 |
|--------|------|
| many0 | 零次或多次 |
| many1 | 一次或多次 |
| many_till | 重复直到 |
| separated_list | 分隔列表 |

∎

---

## 4. 零拷贝保证

### 定理 4.1 (切片重用)

> 解析返回原始输入的子切片。

```rust
fn take_until_parser(input: &str) -> IResult<&str, &str> {
    take_until(":")(input)
    // 返回&str是input的子切片
}
```

∎

---

## 5. 流式解析

### 定理 5.1 (不完整输入)

> nom区分完整错误和不完整输入。

```rust
pub enum Err<E> {
    Incomplete(Needed),  // 需要更多输入
    Error(E),            // 解析错误
    Failure(E),          // 不可恢复错误
}
```

∎

---

## 6. 反例

### 反例 6.1 (递归深度)

```rust
// 递归解析可能导致栈溢出
fn expr(input: &str) -> IResult<&str, Expr> {
    alt((
        parens(expr),  // 递归
        number,
    ))(input)
}

// 使用nom递归组合子
use nom::combinator::recursive;
let parser = recursive(|expr| {
    alt((parens(expr), number))
});
```

### 反例 6.2 (UTF8边界)

```rust
// 字节解析可能破坏UTF8边界
fn bad_parser(input: &str) -> IResult<&str, &str> {
    take(3usize)(input)  // 可能截断多字节字符
}

// 正确: 使用字符解析器
use nom::character::complete::take;
```

---

*文档版本: 1.0.0*
*定理数量: 8个*
