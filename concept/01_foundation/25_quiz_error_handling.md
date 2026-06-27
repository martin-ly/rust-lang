> **内容分级**:
>
> [综述级]

# 测验：错误处理（试点扩展）
>
> **EN**: Error Handling
> **Summary**: Quiz Error Handling. Core Rust concept.
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

> **后置概念**: N/A
---

> **来源**:
> [The Rust Programming Language — Ch9 Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html) ·
> [Rust Reference — Attributes](https://doc.rust-lang.org/reference/attributes.html) ·
> [The Rust Programming Language — Ch18 Patterns](https://doc.rust-lang.org/book/ch18-00-patterns.html)
>
> **前置概念**:
> [Error Handling Basics](./10_error_handling_basics.md) ·
> [Type System](./04_type_system.md) ·
> [Ownership](./01_ownership.md)
>
> **对应练习**:
> [`exercises/src/error_handling/`](../../exercises/src/error_handling/)

---

> **Bloom 层级**: 理解 → 应用
> **定位**: 嵌入式互动测验扩展——验证 L1 错误处理（Error Handling）核心概念（Result/Option、`?` 运算符、panic、自定义错误）的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、Result 与 Option

### Q1. 以下代码的输出是什么？

```rust
fn main() {
    let x: Result<i32, &str> = Ok(5);
    let y: Result<i32, &str> = Err("error");
    println!("{:?} {:?}", x.is_ok(), y.is_err());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`true true`

**解析**：

- `x.is_ok()` → `true`（`x` 是 `Ok`）
- `y.is_err()` → `true`（`y` 是 `Err`）

**`Result<T, E>` 常用方法**：

| 方法 | 签名 | 行为 |
|:---|:---|:---|
| `is_ok()` | `-> bool` | 是否为 `Ok` |
| `is_err()` | `-> bool` | 是否为 `Err` |
| `ok()` | `-> Option<T>` | `Ok(v)` → `Some(v)`，`Err(_)` → `None` |
| `err()` | `-> Option<E>` | `Ok(_)` → `None`，`Err(e)` → `Some(e)` |
| `unwrap()` | `-> T` | `Ok(v)` → `v`，`Err(_)` → **panic** |
| `expect(msg)` | `-> T` | 同 `unwrap`，但带自定义 panic 消息 |

**知识点**：`Result` 是 Rust 错误处理（Error Handling）的核心类型，强迫调用者显式处理错误路径。[→ 错误处理基础详解](LINK_PLACEHOLDER)

</details>

---

### Q2. 以下代码能否编译？`?` 运算符的作用是什么？

```rust
fn may_fail() -> Result<i32, String> {
    Ok(42)
}

fn caller() -> Result<i32, String> {
    let val = may_fail()?;
    println!("Got: {val}");
    Ok(val * 2)
}

fn main() {
    println!("{:?}", caller());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `Got: 42` 然后 `Ok(84)`

**解析**：`?` 运算符是 Rust 错误传播的**语法糖**：

```rust,ignore
let val = may_fail()?;

// 等价于：
let val = match may_fail() {
    Ok(v) => v,
    Err(e) => return Err(e.into()),
};
```

**关键约束**：`?` 只能在返回 `Result`、`Option` 或实现 `Try` trait 的类型的函数中使用。

**转换能力**：`?` 会自动调用 `.into()` 进行错误类型转换（要求目标错误类型实现 `From<SourceError>`）。

**知识点**：`?` 运算符消除了 Go/Java 中冗长的 `if err != nil` 或 `try-catch` 样板代码，同时保持显式错误传播。[→ 错误处理基础详解](./10_error_handling_basics.md)

</details>

---

### Q3. 以下代码能否编译？解释 `unwrap` 和 `expect` 的风险

```rust
fn main() {
    let s = "42";
    let n: i32 = s.parse().unwrap();
    println!("{n}");

    let bad = "not a number";
    let m: i32 = bad.parse().expect("should be a number");
    println!("{m}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 能编译，但在运行第 7 行时 **panic**

**输出**：

```
42
thread 'main' panicked at 'should be a number: ParseIntError { ... }'
```

**解析**：

- `s.parse().unwrap()` ✅ `"42"` 可解析为 `i32`
- `bad.parse().expect("...")` ❌ `"not a number"` 解析失败，`expect` 触发 panic

**`unwrap` / `expect` 使用原则**：

| 场景 | 推荐做法 |
|:---|:---|
| 测试代码、原型 | `unwrap()` 可接受 |
| 确实不可能失败（已验证） | `unwrap()` + 注释说明 |
| 生产代码 | `match`、`if let`、`?` 或 `unwrap_or` |
| 需要上下文信息 | `expect("为什么这里不应该失败")` |

**安全替代**：

```rust,ignore
let m = bad.parse().unwrap_or(0);        // 失败时用默认值
let m = bad.parse().unwrap_or_default(); // 失败时用类型默认值
let m = bad.parse()?;                    // 传播错误
```

**知识点**：`unwrap` 是 Rust 中最常见的 panic 来源之一。生产代码应尽量避免，或用 `unwrap_or` / `unwrap_or_else` 替代。[→ 错误处理基础详解](./10_error_handling_basics.md)

</details>

---

## 二、Option 组合子

### Q4. 以下代码的输出是什么？

```rust
fn main() {
    let a = Some(5);
    let b: Option<i32> = None;

    println!("{:?}", a.map(|x| x * 2));
    println!("{:?}", b.map(|x| x * 2));
    println!("{:?}", a.and_then(|x| Some(x + 1)));
    println!("{:?}", b.unwrap_or(0));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
Some(10)
None
Some(6)
0
```

**解析**：

| 表达式 | 结果 | 说明 |
|:---|:---|:---|
| `Some(5).map(\|x\| x * 2)` | `Some(10)` | 对 `Some` 内值应用函数 |
| `None.map(...)` | `None` | `None` 保持 `None`，函数不执行 |
| `Some(5).and_then(...)` | `Some(6)` | `and_then` 返回 `Option`，可链式组合 |
| `None.unwrap_or(0)` | `0` | `None` 时返回默认值 |

**`Option` 组合子速查**：

| 方法 | `Some(v)` | `None` | 用途 |
|:---|:---|:---|:---|
| `map(f)` | `Some(f(v))` | `None` | 转换值 |
| `and_then(f)` | `f(v)` | `None` | 链式 Option 操作 |
| `filter(p)` | `Some(v)` if `p(v)` | `None` | 条件过滤 |
| `or(other)` | `Some(v)` | `other` | 提供备选 |
| `unwrap_or(def)` | `v` | `def` | 提取值或默认 |
| `unwrap_or_else(f)` | `v` | `f()` | 惰性默认值 |

**知识点**：`Option` 组合子允许在不展开值的情况下进行链式操作，避免嵌套 `match`。[→ 集合类型详解](./08_collections.md)

</details>

---

### Q5. 以下代码能否编译？`if let` 与 `match` 在 Option 处理中的选择

```rust
fn main() {
    let config = Some("debug");

    if let Some(mode) = config {
        println!("Mode: {mode}");
    }

    let count: Option<i32> = None;
    let value = match count {
        Some(n) => n,
        None => 0,
    };
    println!("Count: {value}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出：

```
Mode: debug
Count: 0
```

**解析**：

| 语法 | 适用场景 | 优势 |
|:---|:---|:---|
| `if let Some(x) = opt` | 只关心 `Some`，忽略 `None` | 简洁，避免冗余 `match` arm |
| `let else` | 提前返回/继续 | 减少缩进 |
| `match` | 需要同时处理 `Some` 和 `None` | 穷尽性检查 |

**`let else` 示例**（Rust 1.65+ 稳定）：

```rust,ignore
let Some(mode) = config else {
    println!("No config");
    return;
};
println!("Mode: {mode}");
```

**知识点**：Rust 提供多种 Option 解构语法，选择取决于"需要处理多少种情况"和"是否需要提前返回"。[→ 控制流详解](./07_control_flow.md)

</details>

---

## 三、Panic 与不可恢复错误

### Q6. 以下代码能否编译？`panic!` 与 `Result` 的区别是什么？

```rust
fn main() {
    let v = vec![1, 2, 3];
    let idx = 5;
    println!("{}", v[idx]);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 能编译，但**运行期 panic**

**错误信息**：`index out of bounds: the len is 3 but the index is 5`

**解析**：`Vec` 的索引访问 `v[idx]` 在越界时会 panic。这是 Rust 中"不可恢复错误"的典型场景。

**`panic!` vs `Result` 的哲学**：

| 类型 | 场景 | 处理方式 |
|:---|:---|:---|
| `panic!` | 程序 bug、不变量被违反、不可能发生的情况 | 线程终止，可选 unwind |
| `Result` | 可预期的错误（文件不存在、网络失败） | 显式传播和处理 |

**安全替代**：

```rust,ignore
// 不 panic，返回 Option
if let Some(val) = v.get(idx) {
    println!("{val}");
} else {
    println!("Index out of bounds");
}
```

**知识点**：Rust 区分"可恢复错误"（`Result`）和"不可恢复错误"（`panic`）。选择正确的错误处理策略是健壮程序的基础。[→ Panic 详解](./13_panic_and_abort.md)

</details>

---

### Q7. 以下代码的输出是什么？

```rust
fn divide(a: f64, b: f64) -> Option<f64> {
    if b == 0.0 {
        None
    } else {
        Some(a / b)
    }
}

fn main() {
    let result = divide(10.0, 2.0)
        .map(|x| x * 2.0)
        .filter(|x| *x > 5.0)
        .unwrap_or(0.0);
    println!("{result}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`10`

**解析**：链式组合子执行过程：

1. `divide(10.0, 2.0)` → `Some(5.0)`
2. `.map(|x| x * 2.0)` → `Some(10.0)`
3. `.filter(|x| *x > 5.0)` → `Some(10.0)`（10 > 5，保留）
4. `.unwrap_or(0.0)` → `10.0`

**若 `divide(10.0, 0.0)`**：

1. `divide(...)` → `None`
2. `.map(...)` → `None`（短路）
3. `.filter(...)` → `None`（短路）
4. `.unwrap_or(0.0)` → `0.0`

**知识点**：`Option` 组合子的链式调用是 Rust 函数式编程风格的典型表现，每个操作都是"失败即短路"。[→ 错误处理基础详解](./10_error_handling_basics.md)

</details>

---

## 四、自定义错误

### Q8. 以下代码能否编译？解释 `From` trait 在错误处理中的作用

```rust
#[derive(Debug)]
enum AppError {
    Io(std::io::Error),
    Parse(std::num::ParseIntError),
}

impl From<std::io::Error> for AppError {
    fn from(err: std::io::Error) -> Self {
        AppError::Io(err)
    }
}

impl From<std::num::ParseIntError> for AppError {
    fn from(err: std::num::ParseIntError) -> Self {
        AppError::Parse(err)
    }
}

fn read_config() -> Result<i32, AppError> {
    let content = std::fs::read_to_string("config.txt")?;
    let val: i32 = content.trim().parse()?;
    Ok(val)
}

fn main() {
    println!("{:?}", read_config());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译。

**输出**：`Err(Io(Os { code: 2, kind: NotFound, message: "系统找不到指定的文件。" }))`（Windows）或类似文件不存在错误。

**解析**：

- `AppError` 是**自定义错误枚举（Enum）**，聚合了所有可能的错误类型
- `From<std::io::Error>` 和 `From<std::num::ParseIntError>` 让 `?` 运算符能**自动转换**底层错误为 `AppError`

**`?` 的自动转换机制**：

```rust,ignore
let content = std::fs::read_to_string("config.txt")?;
// 等价于：
let content = match std::fs::read_to_string("config.txt") {
    Ok(v) => v,
    Err(e) => return Err(AppError::from(e)), // 自动调用 From
};
```

**进阶**：Rust 1.81+ 的 `std::error::Error` trait 改进和 `anyhow`/`thiserror` crate 进一步简化了自定义错误。

**知识点**：`From` trait 是实现统一错误类型的关键，`?` 运算符的自动转换能力消除了手动包装错误的大量样板代码。[→ 错误处理进阶](../02_intermediate/04_error_handling.md)

</details>

---

## 五、综合应用

### Q9. 以下代码的输出是什么？

```rust
fn main() {
    let s1 = "42";
    let s2 = "not a number";
    let s3 = "3.14";

    let results = vec![s1, s2, s3]
        .into_iter()
        .map(|s| s.parse::<i32>())
        .collect::<Vec<_>>();

    for (i, r) in results.iter().enumerate() {
        match r {
            Ok(n) => println!("{}: parsed {}", i, n),
            Err(e) => println!("{}: failed - {}", i, e),
        }
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
0: parsed 42
1: failed - invalid digit found in string
2: failed - invalid digit found in string
```

**解析**：

- `s1 = "42"` → `Ok(42)` ✅
- `s2 = "not a number"` → `Err(ParseIntError)` ❌
- `s3 = "3.14"` → `Err(ParseIntError)` ❌（`parse::<i32>()` 不接受小数点）

**`collect` 的妙用**：

```rust,ignore
// 收集为 Vec<Result<i32, _>>
let results: Vec<Result<i32, _>> = vec![s1, s2, s3]
    .into_iter()
    .map(|s| s.parse())
    .collect();

// 或用 Result<Vec<i32>, _> 提前失败
let all_ok: Result<Vec<i32>, _> = vec![s1, s2, s3]
    .into_iter()
    .map(|s| s.parse())
    .collect(); // Result 实现了 FromIterator
```

**知识点**：`Result` 实现了 `FromIterator`，允许 `collect()` 将 `Vec<Result<T, E>>` 转换为 `Result<Vec<T>, E>`（第一个错误即整体失败）。[→ 迭代器（Iterator）详解](LINK_PLACEHOLDER)

</details>

---

### Q10. 以下代码能否编译？解释 `Result` 的 `map` 和 `map_err`

```rust
fn parse_and_scale(s: &str) -> Result<i32, String> {
    s.parse::<i32>()
        .map(|n| n * 10)
        .map_err(|e| format!("Parse failed: {e}"))
}

fn main() {
    println!("{:?}", parse_and_scale("5"));
    println!("{:?}", parse_and_scale("xyz"));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译。

**输出**：

```
Ok(50)
Err("Parse failed: invalid digit found in string")
```

**解析**：

| 方法 | 作用 | 对 `Ok` | 对 `Err` |
|:---|:---|:---|:---|
| `map(f)` | 转换 `Ok` 中的值 | `Ok(f(v))` | 不变 |
| `map_err(f)` | 转换 `Err` 中的错误 | 不变 | `Err(f(e))` |

**执行流程**：

```rust,ignore
s.parse::<i32>()           // "5" → Ok(5), "xyz" → Err(ParseIntError)
    .map(|n| n * 10)       // Ok(5) → Ok(50), Err → 不变
    .map_err(|e| ...)      // Ok → 不变, Err(e) → Err("Parse failed: ...")
```

**常见组合**：

```rust,ignore
// 同时转换 Ok 和 Err
result
    .map(|v| v.process())
    .map_err(|e| Error::from(e))
    .and_then(|v| v.validate())
```

**知识点**：`map` / `map_err` 是 `Result` 的"端点转换"工具，允许在不展开的情况下修改成功值或错误值。[→ 错误处理基础详解](./10_error_handling_basics.md)

</details>

---

## 六、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 错误处理已内化 | 进阶至 [L2 错误处理深度](../02_intermediate/04_error_handling.md) 或 `anyhow`/`thiserror` 生态 |
| 7–9/10 | ✅ 核心概念掌握 | 强化 [L1 错误处理练习](../../exercises/src/error_handling/)，关注错题 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Error Handling Basics](./10_error_handling_basics.md)，完成 rustlings 对应章节 |
| 0–3/10 | 📚 建议重新开始 | 从 [Error Handling Basics](./10_error_handling_basics.md) 逐节阅读，配合 `exercises/src/error_handling/` 示例 |

---

> **对应练习**: [`exercises/src/error_handling/`](../../exercises/src/error_handling/)

---

> **权威来源**: [The Rust Programming Language — Ch9](https://doc.rust-lang.org/book/ch09-00-error-handling.html) · [Rust Reference — Errors](https://doc.rust-lang.org/reference/items/functions.html) · [std::result 文档](https://doc.rust-lang.org/std/result/enum.Result.html)

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文件是 测验：错误处理（试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：错误处理（Error Handling）（试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：在 测验：错误处理（试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：错误处理（Error Handling）（试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>
