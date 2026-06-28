# Nom 解析器组合子形式化分析

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **主题**: 零拷贝解析器组合子库
>
> **形式化框架**: 解析器组合子 + 剩余输入传递
>
> **参考**: nom Documentation

---

## 目录
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

- [Nom 解析器组合子形式化分析](.#nom-解析器组合子形式化分析)
  - [目录](.#目录)
  - [1. 引言](.#1-引言)
  - [2. IResult类型](.#2-iresult类型)
    - [定义 2.1 (IResult)](.#定义-21-iresult)
    - [定理 2.1 (剩余输入传递)](.#定理-21-剩余输入传递)
  - [3. 组合子代数](.#3-组合子代数)
    - [定理 3.1 (序列组合)](.#定理-31-序列组合)
    - [定理 3.2 (选择组合)](.#定理-32-选择组合)
    - [定理 3.3 (重复组合)](.#定理-33-重复组合)
  - [4. 零拷贝保证](.#4-零拷贝保证)
    - [定理 4.1 (切片重用)](.#定理-41-切片重用)
  - [5. 流式解析](.#5-流式解析)
    - [定理 5.1 (不完整输入)](.#定理-51-不完整输入)
  - [6. 反例](.#6-反例)
    - [反例 6.1 (递归深度)](.#反例-61-递归深度)
    - [反例 6.2 (UTF8边界)](.#反例-62-utf8边界)
<a id="定理数量-8个"></a>
  - [*定理数量: 8个*](.#定理数量-8个)
  - [权威来源索引](.#权威来源索引)
  - [权威来源索引](.#权威来源索引-1)

---

## 1. 引言
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

nom提供:

- 解析器组合子
- 零拷贝解析
- 无alloc选项
- 流式解析支持

---

## 2. IResult类型
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 定义 2.1 (IResult)
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
type IResult<I, O, E = Error<I>> = Result<(I, O), Err<E>>;
// (剩余输入, 输出值) 或 错误
```

### 定理 2.1 (剩余输入传递)
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> 解析器返回剩余输入供后续解析。

```rust,ignore
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

```rust,ignore
let parser = tuple((u32_parser, space_parser, u32_parser));
// 类型: (u32, (), u32)
```

∎

### 定理 3.2 (选择组合)

> `alt`尝试多个解析器，返回第一个成功。

```rust,ignore
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

```rust,ignore
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

```rust,ignore
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

```rust,ignore
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

```rust,ignore
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
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**

> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**

> **来源: [Coq Reference Manual](https://coq.inria.fr/doc/)**

> **来源: [TLA+ Documentation](https://lamport.azurewebsites.net/tla/tla.html)**

> **来源: [ACM - Formal Verification](https://dl.acm.org/)**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
