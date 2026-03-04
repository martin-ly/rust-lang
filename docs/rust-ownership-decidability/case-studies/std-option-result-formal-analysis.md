# Rust标准库 Option & Result 形式化分析

> **主题**: 可空类型与错误处理的代数结构
>
> **形式化框架**: 代数数据类型 + Monad理论
>
> **参考**: Rust Standard Library; Moggi (1991); Wadler (1992)

---

## 目录

- [Rust标准库 Option \& Result 形式化分析](#rust标准库-option--result-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. `Option<T>` 代数结构](#2-optiont-代数结构)
    - [2.1 类型定义](#21-类型定义)
    - [定义 2.1 (Option类型)](#定义-21-option类型)
    - [定义 2.2 (同构关系)](#定义-22-同构关系)
    - [2.2 Functor与Monad实现](#22-functor与monad实现)
    - [定理 2.1 (Option是Functor)](#定理-21-option是functor)
    - [定理 2.2 (Option是Monad)](#定理-22-option是monad)
  - [3. Result\<T, E\> 错误处理](#3-resultt-e-错误处理)
    - [3.1 错误传播机制](#31-错误传播机制)
    - [定义 3.1 (Result类型)](#定义-31-result类型)
    - [定理 3.1 (Result的Either同构)](#定理-31-result的either同构)
    - [3.2 错误类型转换](#32-错误类型转换)
    - [定理 3.2 (错误类型转换的组合性)](#定理-32-错误类型转换的组合性)
  - [4. ?运算符形式语义](#4-运算符形式语义)
    - [4.1 早期返回机制](#41-早期返回机制)
    - [定义 4.1 (?运算符)](#定义-41-运算符)
    - [定理 4.1 (?运算符类型正确性)](#定理-41-运算符类型正确性)
    - [4.2 与 Try trait 的关系](#42-与-try-trait-的关系)
    - [定义 4.2 (Try trait)](#定义-42-try-trait)
    - [定理 4.2 (Try trait 的通用性)](#定理-42-try-trait-的通用性)
  - [5. 组合子分析](#5-组合子分析)
    - [5.1 map与and\_then](#51-map与and_then)
    - [定理 5.1 (组合子关系)](#定理-51-组合子关系)
    - [定理 5.2 (组合子的幂等性)](#定理-52-组合子的幂等性)
    - [5.2 unwrap\_or与unwrap\_or\_else](#52-unwrap_or与unwrap_or_else)
    - [定理 5.3 (unwrap\_or的正确性)](#定理-53-unwrap_or的正确性)
    - [定理 5.4 (unwrap\_or vs unwrap\_or\_else)](#定理-54-unwrap_or-vs-unwrap_or_else)
  - [6. 零成本抽象证明](#6-零成本抽象证明)
    - [定理 6.1 (Option的零成本)](#定理-61-option的零成本)
    - [定理 6.2 (Result的零成本)](#定理-62-result的零成本)
  - [7. 与异常处理对比](#7-与异常处理对比)
    - [定理 7.1 (错误处理的完备性)](#定理-71-错误处理的完备性)
  - [8. 反例与最佳实践](#8-反例与最佳实践)
    - [反例 8.1 (滥用unwrap)](#反例-81-滥用unwrap)
    - [反例 8.2 (忽略Result)](#反例-82-忽略result)
    - [反例 8.3 (过度嵌套)](#反例-83-过度嵌套)
    - [最佳实践 8.4 (自定义错误类型)](#最佳实践-84-自定义错误类型)
  - [参考文献](#参考文献)

---

## 1. 引言

`Option<T>` 和 `Result<T, E>` 是Rust错误处理的核心，将可能的缺失值和错误显式编码在类型系统中。

**核心特性**:

- **显式性**: 调用者必须处理None/Err情况
- **可组合**: 丰富的组合子(combinators)
- **零成本**: 运行时无额外开销
- **类型安全**: 编译时强制错误处理

---

## 2. `Option<T>` 代数结构

### 2.1 类型定义

### 定义 2.1 (Option类型)

```rust
pub enum Option<T> {
    None,
    Some(T),
}
```

**形式化**:

$$
\text{Option}\langle T \rangle = 1 + T
$$

这是**和类型(Sum Type)**:

- `1` 代表单元类型 `()` (None)
- `T` 代表值的存在 (Some)

### 定义 2.2 (同构关系)

$$
\text{Option}\langle T \rangle \cong \text{Maybe}(T)
$$

对应Haskell的Maybe monad。

### 2.2 Functor与Monad实现

### 定理 2.1 (Option是Functor)

> Option实现了满足Functor定律的`map`操作。

**Functor定律**:

1. **Identity**:
   $$
   \text{map}(\text{id}, x) = x
   $$

2. **Composition**:
   $$
   \text{map}(f \circ g, x) = \text{map}(f, \text{map}(g, x))
   $$

**证明**:

```rust
impl<T> Option<T> {
    pub fn map<U, F>(self, f: F) -> Option<U>
    where F: FnOnce(T) -> U
    {
        match self {
            Some(x) => Some(f(x)),
            None => None,
        }
    }
}
```

**Identity**:

```rust
opt.map(|x| x)
= match opt {
    Some(x) => Some((|x| x)(x)) = Some(x),
    None => None,
}
= opt
```

**Composition**:

```rust
opt.map(g).map(f)
= match (match opt { Some(x) => Some(g(x)), None => None }) {
    Some(y) => Some(f(y)),
    None => None,
}
= match opt {
    Some(x) => Some(f(g(x))),
    None => None,
}
= opt.map(|x| f(g(x)))
```

∎

### 定理 2.2 (Option是Monad)

> Option实现了满足Monad定律的`and_then`操作。

**Monad定律**:

1. **Left Identity**:
   $$
   \text{return}(a) \bind f = f(a)
   $$

2. **Right Identity**:
   $$
   m \bind \text{return} = m
   $$

3. **Associativity**:
   $$
   (m \bind f) \bind g = m \bind (\lambda x. f(x) \bind g)
   $$

**证明**:

```rust
impl<T> Option<T> {
    pub fn and_then<U, F>(self, f: F) -> Option<U>
    where F: FnOnce(T) -> Option<U>
    {
        match self {
            Some(x) => f(x),
            None => None,
        }
    }
}
```

**Left Identity**:

```rust
Some(a).and_then(f) = f(a)  // 定义
```

**Right Identity**:

```rust
opt.and_then(|x| Some(x))
= match opt {
    Some(x) => (|x| Some(x))(x) = Some(x),
    None => None,
}
= opt
```

**Associativity**:

```rust
opt.and_then(f).and_then(g)
= match (match opt { Some(x) => f(x), None => None }) {
    Some(y) => g(y),
    None => None,
}
= match opt {
    Some(x) => match f(x) {
        Some(y) => g(y),
        None => None,
    },
    None => None,
}
= opt.and_then(|x| f(x).and_then(g))
```

∎

---

## 3. Result<T, E> 错误处理

### 3.1 错误传播机制

### 定义 3.1 (Result类型)

```rust
pub enum Result<T, E> {
    Ok(T),
    Err(E),
}
```

**形式化**:

$$
\text{Result}\langle T, E \rangle = T + E
$$

与Option不同，Result携带错误信息。

### 定理 3.1 (Result的Either同构)

> Result<T, E> 与 Either<E, T> 同构。

**证明**:

```rust
// Either定义 (假设)
enum Either<L, R> {
    Left(L),
    Right(R),
}

// 同构映射
fn result_to_either<T, E>(r: Result<T, E>) -> Either<E, T> {
    match r {
        Ok(t) => Either::Right(t),
        Err(e) => Either::Left(e),
    }
}

fn either_to_result<T, E>(e: Either<E, T>) -> Result<T, E> {
    match e {
        Either::Right(t) => Ok(t),
        Either::Left(e) => Err(e),
    }
}
```

这两个函数互为逆映射，构成同构。∎

### 3.2 错误类型转换

### 定理 3.2 (错误类型转换的组合性)

> `map_err` 允许在保持成功值的同时转换错误类型。

**证明**:

```rust
impl<T, E> Result<T, E> {
    pub fn map_err<F, O>(self, op: O) -> Result<T, F>
    where O: FnOnce(E) -> F
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op(e)),
        }
    }
}
```

性质:

- `Ok(t).map_err(f) = Ok(t)` (不变)
- `Err(e).map_err(f) = Err(f(e))` (转换错误)

∎

---

## 4. ?运算符形式语义

### 4.1 早期返回机制

### 定义 4.1 (?运算符)

```rust
// expr? 等价于
match expr {
    Ok(val) => val,
    Err(err) => return Err(From::from(err)),
}
```

### 定理 4.1 (?运算符类型正确性)

> `?` 运算符只在返回类型兼容的函数中使用。

**证明**:

类型检查规则:

```rust
fn foo() -> Result<T, E> {
    let x = may_fail()?;  // 要求 may_fail(): Result<T, E2> 其中 E2: Into<E>
    Ok(x)
}
```

编译器检查:

1. `may_fail()` 返回 `Result<T, E2>`
2. 当前函数返回 `Result<_, E>`
3. `E2` 必须实现 `Into<E>`

如果不满足，编译错误。∎

### 4.2 与 Try trait 的关系

### 定义 4.2 (Try trait)

```rust
trait Try: FromResidual<<Self as Try>::Residual> {
    type Output;
    type Residual;

    fn from_output(output: Self::Output) -> Self;
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}
```

### 定理 4.2 (Try trait 的通用性)

> Try trait 允许 `?` 运算符用于Option、Result和自定义类型。

**实现示例**:

```rust
impl<T> Try for Option<T> {
    type Output = T;
    type Residual = Option<!>;

    fn from_output(output: T) -> Self { Some(output) }
    fn branch(self) -> ControlFlow<Option<!>, T> {
        match self {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }
}
```

**Option与Result互操作**:

```rust
fn mixed() -> Result<T, Error> {
    let opt: Option<T> = ...;
    let x = opt.ok_or(Error::NotFound)?;  // Option -> Result
    Ok(x)
}
```

∎

---

## 5. 组合子分析

### 5.1 map与and_then

### 定理 5.1 (组合子关系)

> `map` 可以用 `and_then` 和 `Some` 表示:
> $$
> \text{map}(f, x) = \text{and_then}(\lambda y. \text{Some}(f(y)), x)
> $$

**证明**:

```rust
opt.and_then(|y| Some(f(y)))
= match opt {
    Some(x) => Some(f(x)),
    None => None,
}
= opt.map(f)
```

∎

### 定理 5.2 (组合子的幂等性)

> `map(id)` 和 `and_then(Some)` 都是幂等的。

**证明**:

```rust
opt.map(|x| x) = opt  // 定理2.1已证

opt.and_then(|x| Some(x))
= match opt {
    Some(x) => Some(x),
    None => None,
}
= opt
```

∎

### 5.2 unwrap_or与unwrap_or_else

### 定理 5.3 (unwrap_or的正确性)

> `unwrap_or` 在None时返回默认值，在Some时返回包含的值。

**证明**:

```rust
impl<T> Option<T> {
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Some(x) => x,
            None => default,
        }
    }
}
```

- `Some(x).unwrap_or(d) = x`
- `None.unwrap_or(d) = d`

∎

### 定理 5.4 (unwrap_or vs unwrap_or_else)

> `unwrap_or_else` 只在需要时计算默认值，更高效。

**对比**:

```rust
// unwrap_or: 总是计算默认值
opt.unwrap_or(expensive_computation())

// unwrap_or_else: 只在None时计算
opt.unwrap_or_else(|| expensive_computation())
```

**复杂度**:

- `unwrap_or`: $O(1) + O(\text{default})$ (总是)
- `unwrap_or_else`: $O(1)$ 或 $O(1) + O(\text{closure})$ (惰性)

∎

---

## 6. 零成本抽象证明

### 定理 6.1 (Option的零成本)

> `Option<T>` 的运行时表示与手动null检查相同，无额外开销。

**证明**:

**表示优化** (Nullable Pointer Optimization):

```rust
// Option<&T> 大小与 &T 相同
size_of::<Option<&T>>() == size_of::<&T>()

// Option<Box<T>> 大小与 Box<T> 相同
size_of::<Option<Box<T>>>() == size_of::<Box<T>>()
```

使用空指针表示 `None`:

```text
Some(&x)  ->  ptr = &x (非空)
None      ->  ptr = null
```

**与C对比**:

```c
// C: 手动null检查
int* maybe_value;
if (maybe_value != NULL) {
    // 使用 *maybe_value
}
```

```rust
// Rust: Option，编译后相同
if let Some(value) = maybe_value {
    // 使用 value
}
```

LLVM优化后生成相同的机器码。∎

### 定理 6.2 (Result的零成本)

> Result<T, E> 使用标签联合(tagged union)表示，开销最小。

**证明**:

**内存布局**:

```text
Result<T, E>
┌─────────────────────────────────────┐
│ discriminant (1字节)  │ padding     │
├─────────────────────────────────────┤
│ T 或 E (对齐到最大对齐要求)           │
└─────────────────────────────────────┘
```

**优化情况**:

当 `E` 是指针类型时:

```rust
Result<(), Box<Error>>
// 可以用空指针表示 Ok(())，与Option优化类似
```

∎

---

## 7. 与异常处理对比

| 特性 | Rust (Option/Result) | C++ (异常) | Java (异常) |
|------|----------------------|------------|-------------|
| **显式性** | ✅ 类型强制 | ❌ 隐式 | ❌ 隐式 |
| **可组合性** | ✅ Monad组合 | ❌ try-catch | ❌ try-catch |
| **零成本** | ✅ 无运行时 | ❌ 有开销 | ❌ 有开销 |
| **文档化** | ✅ 签名说明 | ❌ 注释 | ⚠️ checked异常 |
| **调试** | ✅ 类型错误 | ❌ 运行时 | ⚠️ 堆栈追踪 |
| **性能** | ✅ 预测性好 | ❌ 异常路径慢 | ❌ 异常路径慢 |

### 定理 7.1 (错误处理的完备性)

> Rust的Result系统可以表达所有可恢复错误，不可恢复使用panic。

**分类**:

| 错误类型 | 处理方式 | 示例 |
|----------|----------|------|
| 可恢复错误 | Result | 文件未找到 |
| 可恢复无值 | Option | 缓存未命中 |
| 不可恢复 | panic | 数组越界 |
| 逻辑错误 | 编译错误 | 类型不匹配 |

---

## 8. 反例与最佳实践

### 反例 8.1 (滥用unwrap)

```rust
// 危险: 可能panic
let x = some_option.unwrap();

// 正确做法
if let Some(x) = some_option {
    // 使用x
} else {
    // 处理None
}

// 或提供默认值
let x = some_option.unwrap_or(default);
```

### 反例 8.2 (忽略Result)

```rust
// 危险: 错误被忽略
fs::write("file.txt", data);  // 编译警告!

// 正确做法
fs::write("file.txt", data)?;

// 或显式处理
match fs::write("file.txt", data) {
    Ok(()) => println!("Success"),
    Err(e) => eprintln!("Error: {}", e),
}

// 或显式丢弃
let _ = fs::write("file.txt", data);
```

### 反例 8.3 (过度嵌套)

```rust
// 嵌套过深，难以阅读
let result = opt
    .map(|x| x * 2)
    .and_then(|x| if x > 10 { Some(x) } else { None })
    .map(|x| x + 1)
    .and_then(|x| Some(x.to_string()));

// 使用?运算符更清晰
fn process(opt: Option<i32>) -> Option<String> {
    let x = opt?;
    let x = x * 2;
    if x <= 10 { return None; }
    let x = x + 1;
    Some(x.to_string())
}
```

### 最佳实践 8.4 (自定义错误类型)

```rust
#[derive(Debug, thiserror::Error)]
enum MyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Parse error: {0}")]
    Parse(#[from] std::num::ParseIntError),

    #[error("Invalid configuration")]
    InvalidConfig,
}

fn do_something() -> Result<Data, MyError> {
    let content = fs::read_to_string("config.txt")?;  // io::Error -> MyError
    let value = content.parse()?;                     // ParseIntError -> MyError
    // ...
    Ok(Data { value })
}
```

---

## 参考文献

1. **Rust Standard Library.** (2024). `std::option::Option`, `std::result::Result`. <https://doc.rust-lang.org/std/>

2. **Moggi, E.** (1991). Notions of Computation and Monads. *Information and Computation*, 93(1), 55-92.
   - 关键贡献: Monad在计算理论中的应用
   - 关联: 第2节Monad定律

3. **Wadler, P.** (1992). The Essence of Functional Programming. *POPL*.
   - 关键贡献: Monad用于副作用
   - 关联: 第2节

4. **Peyton Jones, S.** (2001). Tackling the Awkward Squad: Monadic Input/Output in Haskell.
   - 关键贡献: IO Monad实践
   - 关联: 第4节错误处理

5. **Hoare, C. A. R.** (1978). Communicating Sequential Processes.
   - 关键贡献: 进程代数
   - 关联: 第5节组合子

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 12个*
*最后更新: 2026-03-04*
