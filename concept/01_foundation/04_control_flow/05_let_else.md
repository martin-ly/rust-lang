# let-else：失败分支提前返回

> **EN**: Let-Else: Early Return on Pattern Mismatch
> **Summary**: `let-else` is a stable Rust construct that refutes an irrefutable `let` binding: it binds variables on match and diverges into an `else` block when the pattern does not match, enabling ergonomic early-return/error-exit code.
>
> **受众**: [进阶]
> **Bloom 层级**: L2
> **内容分级**: [综述级]
> **权威来源**: 本文件为 `concept/` 权威页。
> **Rust 版本**: 1.65.0+ stable
> **最后更新**: 2026-07-16
>
> **前置概念**: [Control Flow](01_control_flow.md) · [Patterns](02_patterns.md) · [Let Chains](03_let_chains.md) · [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md) · [术语表](../../00_meta/01_terminology/01_terminology_glossary.md)
> **后置概念**: [Statements and Expressions](04_statements_and_expressions.md) · [Option/Result Idioms](../../02_intermediate/03_error_handling/02_error_handling_deep_dive.md)
>
> **权威来源**:
> · [Rust Reference — Let statements](https://doc.rust-lang.org/reference/statements.html#let-statements) ·
> [RFC 3137 — let_else](https://rust-lang.github.io/rfcs/3137-let-else.html) ·
> [TRPL — Patterns](https://doc.rust-lang.org/book/ch18-00-patterns.html) ·
> [Rust 1.65 Release Notes](https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html)

---

## 🧠 知识结构图

```mermaid
mindmap
  root((let-else))
    语法
      let PAT = EXPR else { DIVERGE };
      模式必须可反驳
      else 块必须发散
    语义
      匹配成功 → 绑定变量
      匹配失败 → 执行 else 块并离开当前作用域
    对比
      match 表达式
      if let / while let
      let chains
    场景
      早期返回
      错误退出
      Option/Result 解构
```

## 📑 目录

- [let-else：失败分支提前返回](#let-else失败分支提前返回)
  - [🧠 知识结构图](#-知识结构图)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 什么是 let-else](#11-什么是-let-else)
    - [1.2 语法规则](#12-语法规则)
    - [1.3 与 match / if let 的对比](#13-与-match--if-let-的对比)
  - [二、技术细节](#二技术细节)
    - [2.1 else 块必须发散](#21-else-块必须发散)
    - [2.2 绑定范围](#22-绑定范围)
    - [2.3 可反驳模式要求](#23-可反驳模式要求)
    - [2.4 与 let chains 的关系](#24-与-let-chains-的关系)
  - [三、常见模式](#三常见模式)
    - [3.1 从 Option 中提取](#31-从-option-中提取)
    - [3.2 从 Result 中提取](#32-从-result-中提取)
    - [3.3 嵌套结构解构](#33-嵌套结构解构)
    - [3.4 与 ? 运算符配合](#34-与--运算符配合)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 常见错误](#42-常见错误)
  - [五、风格建议](#五风格建议)
  - [六、来源与延伸阅读](#六来源与延伸阅读)

---

## 一、核心概念

### 1.1 什么是 let-else

`let-else` 是 Rust 1.65 稳定的控制流构造，它把**模式匹配（Pattern Matching）绑定**与**失败分支发散**合并到一条语句中：

```rust
fn main() {
    let opt: Option<i32> = Some(42);

    let Some(x) = opt else {
        println!("none");
        return;
    };

    println!("value: {}", x);
}
```

语义上等价于：

```rust
fn main() {
    let opt: Option<i32> = Some(42);

    let x = match opt {
        Some(x) => x,
        None => {
            println!("none");
            return;
        }
    };

    println!("value: {}", x);
}
```

`let-else` 的价值在于**减少缩进**和**明确主路径**：把异常/失败处理压缩到一行，后续代码专注处理成功情形。

### 1.2 语法规则

```text
let <pattern> = <expression> else {
    <diverging-statements>
};
```

| 规则 | 说明 |
|---|---|
| **可反驳模式** | `<pattern>` 必须是可反驳的（refutable），即存在不匹配的可能 |
| **else 块发散** | else 块必须以 `return` / `break` / `continue` / `panic!` / `?` 等发散表达式结束 |
| **分号结尾** | 整个构造以 `};` 结束 |
| **绑定向后可见** | 匹配成功绑定的变量在 `let-else` 之后可见 |

### 1.3 与 match / if let 的对比

| 构造 | 适用场景 | 失败分支 |
|---|---|---|
| `match` | 多分支、复杂逻辑 | 任意表达式 |
| `if let` | 单分支匹配、可选执行 | 不绑定变量，继续执行 if 后代码 |
| `let-else` | 单分支匹配、失败即退出 | 必须发散，成功后绑定变量 |
| `let chains` | 多个条件连续判断 | 通过 `&&` 短路 |

示例对比：

```rust
fn process(opt: Option<i32>) {
    // if let：失败时继续执行
    if let Some(x) = opt {
        println!("got {}", x);
    }
    println!("continuing...");

    // let-else：失败时直接返回
    let Some(x) = opt else { return; };
    println!("got {} and continuing", x);
}

fn main() {}
```

---

## 二、技术细节

### 2.1 else 块必须发散

`else` 块的**类型**必须是 `!`（never type）或能发散到其他类型。常见写法：

```rust
fn foo(x: Option<i32>) -> i32 {
    let Some(n) = x else {
        return 0;      // return 发散
    };
    n
}

fn bar(x: Option<i32>) {
    let Some(n) = x else {
        panic!("expected Some"); // panic! 发散
    };
    println!("{}", n);
}

fn baz(x: Result<i32, ()>) -> Result<(), ()> {
    let Ok(n) = x else {
        return Err(()); // ? 也可用于 Try 类型
    };
    println!("{}", n);
    Ok(())
}

fn main() {}
```

如果 `else` 块不发散，编译器报错：

```rust,compile_fail
fn foo(x: Option<i32>) {
    let Some(n) = x else {
        println!("none"); // 错误：else 块必须发散
    };
    println!("{}", n);
}
```

### 2.2 绑定范围

`let-else` 绑定的变量**只在匹配成功后的当前作用域**可见，不会泄漏到 `else` 块：

```rust
fn main() {
    let opt: Option<i32> = Some(5);

    let Some(x) = opt else {
        // x 在这里不可见
        return;
    };

    // x 在这里可见
    println!("{}", x);
}
```

### 2.3 可反驳模式要求

`let-else` 要求模式是可反驳的。使用不可反驳模式会报错：

实际上，更常见的“错误”是写了一个永远匹配的模式——此时编译器只会警告 `irrefutable_let_patterns`，而不会报错：

```rust
fn main() {
    let x = 5;
    let n = x else { return; }; // ⚠️ warning: unreachable `else` clause
    println!("{}", n);
}
```

> 这说明 `let-else` 的语法上**允许**不可反驳模式，但失去了提前退出的意义；lint 会提示你改用普通 `let`。

### 2.4 与 let chains 的关系

`let-else` 与 `let chains` 是互补特性：

- `let chains` 用于**连续判断多个条件**，所有条件都成立才进入块；
- `let-else` 用于**单条件失败即退出**。

两者不能混合。不能在 `let-else` 的 pattern 位置写 `&&` 链。

---

## 三、常见模式

### 3.1 从 Option 中提取

```rust
fn double(opt: Option<i32>) -> Option<i32> {
    let Some(x) = opt else { return None; };
    Some(x * 2)
}

fn main() {
    assert_eq!(double(Some(3)), Some(6));
    assert_eq!(double(None), None);
}
```

### 3.2 从 Result 中提取

```rust
fn parse_add(s1: &str, s2: &str) -> Result<i32, std::num::ParseIntError> {
    let n1 = s1.parse::<i32>()?;
    let n2 = s2.parse::<i32>()?;
    Ok(n1 + n2)
}

// 等价于 let-else 风格（当需要自定义错误信息时）
fn parse_add_custom(s1: &str, s2: &str) -> Result<i32, String> {
    let n1 = s1.parse::<i32>().map_err(|e| format!("s1: {}", e))?;
    let n2 = s2.parse::<i32>().map_err(|e| format!("s2: {}", e))?;
    Ok(n1 + n2)
}

fn main() {}
```

### 3.3 嵌套结构解构

```rust
enum Expr {
    Literal(i32),
    Add(Box<Expr>, Box<Expr>),
}

fn eval_add(e: Expr) -> Option<i32> {
    let Expr::Add(left, right) = e else { return None; };
    let Expr::Literal(l) = *left else { return None; };
    let Expr::Literal(r) = *right else { return None; };
    Some(l + r)
}

fn main() {}
```

### 3.4 与 ? 运算符配合

`let-else` 的 `else` 块里可以使用 `?`：

```rust
fn read_config(path: &str) -> Result<String, std::io::Error> {
    let contents = std::fs::read_to_string(path)?;
    let first = contents.lines().next() else {
        return Err(std::io::Error::other("empty config"));
    };
    Ok(first.to_string())
}

fn main() {}
```

---

## 四、反命题与边界分析

### 4.1 反命题树

```
是否使用 let-else？
├── 需要从 Option/Result/enum 中提取绑定？
│   ├── 否 → 不需要 let-else
│   └── 是 → 继续
├── 提取失败时需要立即退出当前作用域？
│   ├── 否 → 考虑 if let / match
│   └── 是 → 继续
├── 只需要单模式匹配？
│   ├── 否 → 使用 match
│   └── 是 → 使用 let-else
└── else 块能否发散？
    ├── 否 → 改用 if let
    └── 是 → let-else 合适
```

### 4.2 常见错误

| 错误 | 示例 | 说明 |
|---|---|---|
| else 块不发散 | `let Some(x) = opt else { println!("none"); };` | 必须 return/break/continue/panic/? |
| 不可反驳模式 | `let n = x else { return; };` | 模式必须可反驳 |
| 误用 `\|` | `let A(x) | B(x) = e else { return; };` | let-else 不支持或模式 |
| 绑定泄漏到 else | 在 else 块访问匹配变量 | else 块内无绑定 |

---

## 五、风格建议

1. **简短 else 块**：`let Some(x) = opt else { return; };` 一行即可。
2. **复杂失败处理**：如果 else 块超过 2–3 行，考虑改用 `match` 提高可读性。
3. **避免嵌套过深**：连续多个 `let-else` 可以替代深层嵌套的 `if let`。
4. **与 `?` 区分**：`?` 用于 `Try` 类型自动传播；`let-else` 用于非 `Try` 类型或需要自定义失败分支的场景。

---

## 六、来源与延伸阅读

- [Rust Reference — Let statements](https://doc.rust-lang.org/reference/statements.html#let-statements)
- [RFC 3137 — let_else](https://rust-lang.github.io/rfcs/3137-let-else.html)
- [Rust 1.65 Release Notes](https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html)
- [Let Chains 权威页](03_let_chains.md)
- [Pattern Matching 权威页](02_patterns.md)
