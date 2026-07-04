> **内容分级**: [基础级]

# Functions（函数）
>
> **EN**: Functions
> **Summary**: Functions: Rust's primary unit of executable behavior, covering declarations, parameters, return types, the `->` syntax, diverging functions, and the relationship to ownership and move semantics.
> **受众**: [初学者]
> **Bloom 层级**: 记忆 → 理解
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: F×Und — 理解函数作为 Rust 行为单元的基础结构
> **定位**: 系统讲解 Rust 函数声明、参数传递、返回值、发散函数与所有权的交互，为后续 Trait、闭包、Async 打下语法基础。
> **前置概念**: [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) · [Type System](../02_type_system/04_type_system.md) · [Statements and Expressions](../04_control_flow/41_statements_and_expressions.md) · [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md)
> **后置概念**: [Traits](../../02_intermediate/00_traits/01_traits.md) · [Closures](../00_start/15_closure_basics.md) · [Modules and Paths](11_modules_and_paths.md)
>
> **来源**: [The Rust Programming Language — Functions](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html) · [Rust Reference — Functions](https://doc.rust-lang.org/reference/items/functions.html) · [Rust By Example — Functions](https://doc.rust-lang.org/rust-by-example/fn.html)

---

> **对应 Crate**: [`c03_control_fn`](../../crates/c03_control_fn)
> **对应练习**: [`exercises/src/control_flow/`](../../exercises/src/control_flow)

## 📑 目录

- [Functions（函数）](#functions函数)
  - [📑 目录](#-目录)
  - [一、核心命题](#一核心命题)
  - [二、函数声明与调用](#二函数声明与调用)
  - [三、参数与所有权](#三参数与所有权)
  - [四、返回值](#四返回值)
  - [五、发散函数](#五发散函数)
  - [六、函数与变量遮蔽](#六函数与变量遮蔽)
  - [七、反例与边界测试](#七反例与边界测试)
    - [7.1 忘记返回表达式](#71-忘记返回表达式)
    - [7.2 移动后继续使用](#72-移动后继续使用)
    - [7.3 可变借用冲突](#73-可变借用冲突)
  - [八、权威来源索引](#八权威来源索引)

---

## 一、核心命题

> **命题 1**: 函数是 Rust 中**命名的、可复用的执行单元**，由签名（参数 + 返回类型）和函数体组成。
>
> **命题 2**: Rust 函数默认使用**移动语义**传递参数；借用必须通过显式引用 `&T` / `&mut T` 表达。
>
> **命题 3**: 函数的返回类型不写时默认为单元类型 `()`；使用 `->` 显式声明返回类型。
>
> **命题 4**: 发散函数（Diverging Functions）返回 `!`（never type），承诺永不正常返回。

---

## 二、函数声明与调用

```rust
fn greet(name: &str) {
    println!("Hello, {name}!");
}

fn main() {
    greet("Rust");          // 函数调用
}
```

**语法要素**:

| 要素 | 说明 | 示例 |
|:---|:---|:---|
| `fn` | 函数关键字 | `fn foo() {}` |
| 函数名 | snake_case | `fn do_thing() {}` |
| 参数列表 | 名称: 类型 | `(x: i32, y: &str)` |
| 返回类型 | `-> T` | `fn add(x: i32) -> i32` |
| 函数体 | 语句块 | `{ x + 1 }` |

> **关键洞察**: Rust 函数签名是**合约**: 调用者必须提供正确类型的参数，编译器保证返回值类型匹配。

---

## 三、参数与所有权

```rust
fn take_ownership(s: String) {
    println!("{s}"); // s 在此有效
} // s 被 drop

fn borrow(s: &String) {
    println!("{s}"); // 不获取所有权
}

fn main() {
    let s = String::from("hello");
    take_ownership(s); // s 被移动
    // println!("{s}"); // ❌ 编译错误

    let t = String::from("world");
    borrow(&t);        // 借用
    println!("{t}");   // ✅ 仍可使用
}
```

**规则**:

1. 默认按值传递 = 移动（Move）对于非 `Copy` 类型。
2. `Copy` 类型（如 `i32`、`bool`、引用）按位复制，不转移所有权。
3. 可变借用 `&mut T` 允许函数修改传入数据，但需满足借用检查规则。

---

## 四、返回值

```rust
fn add(a: i32, b: i32) -> i32 {
    a + b // 末尾表达式作为返回值（无分号）
}

fn early_return(x: i32) -> i32 {
    if x < 0 {
        return 0; // 显式提前返回
    }
    x
}
```

> **注意**: 函数体最后一个**无分号表达式**是返回值；若加分号则变为语句，返回 `()`。

```rust,compile_fail
fn wrong() -> i32 {
    5; // ❌ 类型不匹配：实际返回 ()，期望 i32
}
```

---

## 五、发散函数

发散函数返回 `!`（never type），常用于 `panic!`、`loop {}`、`std::process::exit`。

```rust
fn forever() -> ! {
    loop {
        println!("again");
    }
}

fn must_not_happen() -> ! {
    panic!("unreachable");
}
```

**作用**:

- 在 `match` 分支中，发散分支可被合并到任意返回类型。
- 表达"此路径不会继续执行"的强保证。

---

## 六、函数与变量遮蔽

函数参数会遮蔽（shadow）外层同名变量，但仅在函数体内有效：

```rust
let x = 5;
fn print_x(x: i32) {
    println!("{x}");
}
print_x(10); // 输出 10，不影响外层 x
```

---

## 七、反例与边界测试

### 7.1 忘记返回表达式

```rust,compile_fail
fn double(x: i32) -> i32 {
    x * 2; // ❌ 语句返回 ()
}
```

**修正**: 去掉分号：`x * 2`

### 7.2 移动后继续使用

```rust,compile_fail
fn consume(s: String) {}

fn main() {
    let s = String::from("hi");
    consume(s);
    println!("{s}"); // ❌ borrow of moved value
}
```

**修正**: 传递引用 `&s` 或改用 `Clone`。

### 7.3 可变借用冲突

```rust,compile_fail
fn append(dest: &mut String, src: &String) {
    dest.push_str(src);
}

fn main() {
    let mut s = String::from("a");
    append(&mut s, &s); // ❌ 不可变借用与可变借用重叠
}
```

**修正**: 确保借用的生命周期不重叠。

---

## 八、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Functions](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html) | ✅ 一级 | 官方入门教程 |
| [Rust Reference — Functions](https://doc.rust-lang.org/reference/items/functions.html) | ✅ 一级 | 语言规范 |
| [Rust By Example — Functions](https://doc.rust-lang.org/rust-by-example/fn.html) | ✅ 二级 | 交互示例 |
