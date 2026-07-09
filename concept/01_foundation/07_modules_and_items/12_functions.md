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

## 认知路径

> **认知路径**: 本节从“为什么需要函数”出发，依次建立函数声明、参数传递、返回值、发散函数与所有权交互的完整图景。

1. **问题识别**: 当代码重复出现时，如何封装为可复用单元？
2. **概念建立**: 掌握 `fn`、参数列表、返回类型、`->` 语法与函数体。
3. **机制推理**: 通过 ⟹ 定理链将函数签名、所有权移动与借用规则串联起来。
4. **边界辨析**: 借助反命题/反例理解忘记返回表达式、移动后继续使用、可变借用冲突等错误。
5. **迁移应用**: 将函数与 Trait、闭包、Async 等后置概念链接，形成跨层知识网络。

---

> **过渡**: 从函数的直观描述转向其形式化定义，需要先把日常经验中的“子程序”直觉转化为 Rust 中可验证的签名与类型规则。

> **过渡**: 在建立函数的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将函数与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 1]: 函数签名精确声明参数类型与返回类型 ⟹ 编译器可在调用点静态检查类型一致性。
>
> **定理 2** [Tier 1]: 函数参数默认按值传递 ⟹ 调用者需显式使用 `&T` / `&mut T` 表达借用，否则发生所有权移动。
>
> **定理 3** [Tier 1]: 发散函数返回 `!` ⟹ 任何需要 `T` 的位置都可安全替换为发散函数调用（never 的底类型性质）。

---

> **反向推理 1** [Tier 1]: 若编译器报错 `mismatched types` 或 `value borrowed here after move` ⟸ 应首先检查函数签名与调用点是否一致、参数传递方式是否正确。
>
> **反向推理 2** [Tier 1]: 若代码逻辑需要函数“不返回” ⟸ 考虑使用 `!` 返回类型并确保所有控制路径确实不返回。

---

## 📑 目录

- [Functions（函数）](#functions函数)
  - [认知路径](#认知路径)
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
  - [补充：来自 `crates/c03_control_fn` 函数参考的语法速查](#补充来自-cratesc03_control_fn-函数参考的语法速查)
    - [函数 BNF 语法概要](#函数-bnf-语法概要)
    - [参数传递语义](#参数传递语义)
    - [返回值要点](#返回值要点)

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

---

## 补充：来自 `crates/c03_control_fn` 函数参考的语法速查

> 本节由原 `crates/c03_control_fn/docs/tier_03_references/03_functions_reference.md` 合并而来，保留函数完整语法参考。

### 函数 BNF 语法概要

```text
function :=
    function_qualifiers "fn" IDENTIFIER generic_params?
    "(" function_parameters? ")" function_return_type? where_clause?
    block_expression

function_qualifiers :=
    "const"? "async"? "unsafe"? ("extern" abi?)?
```

### 参数传递语义

| 声明形式 | 调用侧行为 | 适用场景 |
| :--- | :--- | :--- |
| `fn f(x: T)` | 移动（Move）所有权 | 小类型或明确转移所有权 |
| `fn f(x: &T)` | 不可变借用 | 只读访问 |
| `fn f(x: &mut T)` | 可变借用 | 需要修改 |
| `fn f(x: impl Trait)` | 静态分发单态化 | 简单泛型约束 |
| `fn f(x: dyn Trait)` | 动态分发，胖指针 | 需要运行时多态 |

### 返回值要点

- 默认返回单元类型 `()`；显式返回使用 `-> T`。
- 发散函数返回 `!`，可被强制转换为任意类型。
- 返回 `impl Trait` 隐藏具体类型，但调用方只能使用该 trait 的方法。

> 更多示例与所有权交互分析参见本节正文。
