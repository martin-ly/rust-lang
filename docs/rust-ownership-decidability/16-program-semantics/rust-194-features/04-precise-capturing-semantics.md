# Precise Capturing (+ use<'lt>) 的生命周期语义

## 1. 引言

Precise Capturing（精确捕获）是 Rust 1.94 引入的重要特性，通过 `use<'lt>` 语法允许开发者精确控制哪些生命周期被捕获到不透明类型（`impl Trait`）中。
这是 Rust 生命周期系统的重大改进，提供了更细粒度的生命周期控制。

### 1.1 什么是 Precise Capturing

在传统 Rust 中，`impl Trait` 会捕获所有输入生命周期：

```rust
// 传统方式：捕获所有生命周期
fn foo<'a, 'b>(x: &'a i32, y: &'b i32) -> impl Trait<'a, 'b>;
```

使用 `use<'lt>`，可以精确指定捕获的生命周期：

```rust
// 精确捕获：只捕获 'a
fn bar<'a, 'b>(x: &'a i32, y: &'b i32) -> impl Trait + use<'a>;
```

## 2. 语法定义

### 2.1 精确捕获语法

$$
\begin{aligned}
\text{ImplTrait} &::= \text{impl } \text{TypeParamBound} \\
&\quad | \; \text{impl } \text{TypeParamBound} + \text{use}\langle\text{LifetimeList}\rangle \\
\text{LifetimeList} &::= \epsilon \quad | \quad \rho, \text{LifetimeList}
\end{aligned}
$$

### 2.2 捕获集定义

**捕获集** $\mathcal{C}$ 是生命周期的幂集：

$$
\mathcal{C} \in \mathcal{P}(\text{Lifetime})
$$

**显式捕获**：

$$
\text{use}\langle\rho_1, \dots, \rho_n\rangle \Rightarrow \mathcal{C} = \{\rho_1, \dots, \rho_n\}
$$

**隐式捕获**（默认）：

$$
\text{no use clause} \Rightarrow \mathcal{C} = \text{all\_input\_lifetimes}
$$

### 2.3 返回类型扩展语法

```
ReturnType ::= -> Type
            | -> impl TraitBound + use<Lifetimes>
            | -> impl TraitBound + use<>
```

## 3. 操作语义

### 3.1 捕获集计算

**显式捕获** (CS-Explicit):

$$
\frac{
  \text{return\_type} = \text{impl } B + \text{use}\langle\rho_1, \dots, \rho_n\rangle
}{
  \text{capture\_set}(\text{return\_type}) = \{\rho_1, \dots, \rho_n\}
}
$$

**空捕获** (CS-Empty):

$$
\frac{
  \text{return\_type} = \text{impl } B + \text{use}\langle\rangle
}{
  \text{capture\_set}(\text{return\_type}) = \emptyset
}
$$

**隐式捕获** (CS-Implicit):

$$
\frac{
  \text{return\_type} = \text{impl } B \quad
  \text{no use clause}
}{
  \text{capture\_set}(\text{return\_type}) = \text{free\_lifetimes}(\text{input\_types})
}
$$

### 3.2 生命周期包含关系

**捕获集有效性** (CS-Valid):

$$
\frac{
  \mathcal{C} = \{\rho_1, \dots, \rho_n\} \quad
  \forall i. \rho_i \in \text{input\_lifetimes}
}{
  \vdash \text{use}\langle\mathcal{C}\rangle \text{ valid}
}
$$

### 3.3 闭包捕获语义

**闭包精确捕获** (E-Closure-Precise):

$$
\frac{
  \langle e_i, \sigma \rangle \Downarrow \langle v_i, \sigma_i \rangle \quad
  \mathcal{C} = \text{capture\_set}(\text{return\_type})
}{
  \langle || e, \sigma \rangle \Downarrow
  \langle \text{closure}(\lambda. e, \{v_i \mid \rho_i \in \mathcal{C}\}), \sigma_n \rangle
}
$$

## 4. 类型规则

### 4.1 精确捕获类型规则

**精确捕获推导** (T-Precise-Capture):

$$
\frac{
  \Gamma, \rho_1, \dots, \rho_n \vdash e : \tau \quad
  \tau \text{ implements } B \quad
  \text{free\_lifetimes}(\tau) \cap \text{input\_lifetimes} \subseteq \{\rho_1, \dots, \rho_n\}
}{
  \Gamma \vdash e : \text{impl } B + \text{use}\langle\rho_1, \dots, \rho_n\rangle
}
$$

### 4.2 生命周期检查规则

**捕获生命周期有效性** (T-Capture-Valid):

$$
\frac{
  \text{use}\langle\rho_1, \dots, \rho_n\rangle \in \text{return\_type} \quad
  \forall i. \Gamma \vdash \rho_i : \text{Lifetime} \quad
  \rho_i \in \text{scope}
}{
  \Gamma \vdash \text{return\_type} \text{ well\_formed}
}
$$

### 4.3 与 impl Trait 的交互

**传统 impl Trait** (T-Impl-Trait-Classic):

$$
\frac{
  \Gamma \vdash e : \tau \quad
  \tau \text{ implements } B \quad
  \mathcal{C} = \text{free\_lifetimes}(\Gamma)
}{
  \Gamma \vdash e : \text{impl } B
}
\quad\text{(captures all)}
$$

**精确捕获 impl Trait** (T-Impl-Trait-Precise):

$$
\frac{
  \Gamma \vdash e : \tau \quad
  \tau \text{ implements } B \quad
  \mathcal{C} = \{\rho_1, \dots, \rho_n\}
}{
  \Gamma \vdash e : \text{impl } B + \text{use}\langle\rho_1, \dots, \rho_n\rangle
}
\quad\text{(captures specific)}
$$

### 4.4 闭包类型规则

**精确捕获闭包** (T-Closure-Precise):

$$
\frac{
  \Gamma, x_1 : \tau_1, \dots, x_n : \tau_n \vdash e : \tau \quad
  \mathcal{C} = \text{capture\_set}(\text{closure\_type}) \quad
  \forall i. \text{if } \rho_{x_i} \in \mathcal{C} \text{ then capture } x_i
}{
  \Gamma \vdash |x_1, \dots, x_n| e : \text{impl } Fn(...) \rightarrow \tau + \text{use}\langle\mathcal{C}\rangle
}
$$

## 5. 形式化定义

### 5.1 捕获集

**定义 5.1** (捕获集)：

捕获集 $\mathcal{C}$ 是一个生命周期的集合：

$$
\mathcal{C} \subseteq \text{Lifetime}
$$

对于返回类型 `impl B + use<ρ₁, ..., ρₙ>`，捕获集为：

$$
\mathcal{C}(\text{impl } B + \text{use}\langle\rho_1, \dots, \rho_n\rangle) = \{\rho_1, \dots, \rho_n\}
$$

### 5.2 生命周期依赖

**定义 5.2** (生命周期依赖)：

类型 $\tau$ 依赖于生命周期 $\rho$，记作 $\rho \in \text{depends}(\tau)$：

$$
\text{depends}(\tau) = \begin{cases}
\{\rho\} & \text{if } \tau = \&'\rho T \\
\text{depends}(T) & \text{if } \tau = \text{Box}\langle T \rangle \\
\bigcup_i \text{depends}(\tau_i) & \text{if } \tau = C\langle\tau_1, \dots, \tau_n\rangle \\
\emptyset & \text{otherwise}
\end{cases}
$$

### 5.3 精确捕获条件

**定义 5.3** (精确捕获有效性)：

精确捕获 `use<ρ₁, ..., ρₙ>` 对于表达式 $e$ 是有效的，当且仅当：

$$
\text{valid}(\text{use}\langle\rho_1, \dots, \rho_n\rangle, e) \iff
\text{depends}(\text{type}(e)) \subseteq \{\rho_1, \dots, \rho_n\} \cup \text{global\_lifetimes}
$$

### 5.4 生命周期捕获关系

**定义 5.4** (生命周期捕获关系)：

捕获关系 $\mathcal{K}$ 将返回类型映射到捕获的生命周期集：

$$
\mathcal{K} : \text{ReturnType} \rightarrow \mathcal{P}(\text{Lifetime})
$$

定义：

$$
\mathcal{K}(rt) = \begin{cases}
\{\rho_1, \dots, \rho_n\} & \text{if } rt = \text{impl } B + \text{use}\langle\rho_1, \dots, \rho_n\rangle \\
\text{free\_lifetimes}(\text{input}) & \text{if } rt = \text{impl } B \text{ (no use clause)} \\
\emptyset & \text{if } rt = \text{impl } B + \text{use}\langle\rangle
\end{cases}
$$

## 6. 安全定理

### 6.1 生命周期安全定理

**定理 6.1** (精确捕获生命周期安全)：

如果 $\Gamma \vdash e : \text{impl } B + \text{use}\langle\rho_1, \dots, \rho_n\rangle$，则：

$$
\forall \rho \in \text{depends}(e). \rho \in \{\rho_1, \dots, \rho_n\} \lor \rho = \text{'static}
$$

**证明**：

由类型规则 T-Precise-Capture：

1. 该规则要求 `free_lifetimes(τ) ∩ input_lifetimes ⊆ {ρ₁, ..., ρₙ}`
2. 这意味着只有显式捕获的生命周期可以被返回类型依赖
3. 任何未捕获的生命周期必须在全局范围内有效（如 'static）

因此，返回类型不会依赖于已经过期的生命周期。

### 6.2 捕获完备性定理

**定理 6.2** (捕获完备性)：

如果 $\Gamma \vdash e : \text{impl } B + \text{use}\langle\mathcal{C}\rangle$ 且 $\rho \in \mathcal{C}$，则：

$$
\exists v \in \text{values}(e). \rho \in \text{depends}(v)
$$

即捕获集中每个生命周期确实被返回值的某个组件依赖。

**证明**：

由捕获集的定义，只有在以下情况下生命周期才会被添加到捕获集：

1. 显式出现在 `use<...>` 中
2. 被返回值的类型依赖

因此，捕获的生命周期都是必需的。

### 6.3 子捕获关系

**定理 6.3** (捕获集子类型)：

如果 $\mathcal{C}_1 \subseteq \mathcal{C}_2$，则：

$$
\text{impl } B + \text{use}\langle\mathcal{C}_2\rangle <: \text{impl } B + \text{use}\langle\mathcal{C}_1\rangle
$$

即捕获更多生命周期的类型是捕获更少生命周期的类型的子类型。

**证明**：

捕获更多生命周期意味着返回值可能依赖于更多的输入数据，因此限制更少，更加通用。

### 6.4 空捕获安全

**定理 6.4** (空捕获安全)：

如果 $\Gamma \vdash e : \text{impl } B + \text{use}\langle\rangle$，则：

$$
\text{depends}(e) \subseteq \text{global\_lifetimes}
$$

即返回值只依赖于全局有效的生命周期。

**证明**：

空捕获集 `use<>` 表示不捕获任何输入生命周期。由类型规则，这意味着返回值不能依赖于任何输入生命周期，只能使用全局生命周期（如 'static）。

## 7. Rust 代码示例

### 7.1 基本精确捕获

```rust
// 传统方式：捕获所有生命周期
fn classic_way<'a, 'b>(x: &'a i32, y: &'b i32) -> impl Fn() -> i32 + 'a + 'b {
    move || x + y  // 捕获 'a 和 'b
}

// 精确捕获：只捕获 'a
fn precise_capture<'a, 'b>(x: &'a i32, y: &'b i32) -> impl Fn() -> i32 + use<'a> {
    || *x  // 只使用 x，只捕获 'a
}

fn example() {
    let a = 1;
    let f = {
        let b = 2;
        precise_capture(&a, &b)
        // classic_way(&a, &b)  // 编译错误：b 生命周期不够长
    };
    println!("{}", f());
}
```

### 7.2 空捕获

```rust
// use<> 表示不捕获任何生命周期
fn no_capture<T>(x: T) -> impl FnOnce() -> T + use<> {
    || x  // x 是 owned，不依赖引用生命周期
}

// 等价于
fn also_no_capture<T: 'static>(x: T) -> impl FnOnce() -> T {
    || x
}

fn empty_capture_example() {
    let s = String::from("hello");
    let f = no_capture(s);
    // s 在这里被移动，但 f 仍然有效
    println!("{}", f());
}
```

### 7.3 闭包中的精确捕获

```rust
fn closure_precise_capture<'a, 'b, 'c>(
    a: &'a str,
    b: &'b str,
    c: &'c str
) -> impl Fn() -> String + use<'a, 'b> {
    // 只捕获 'a 和 'b，不捕获 'c
    || format!("{} {}", a, b)
}

fn example() {
    let x = "hello";
    let y = "world";

    let f = {
        let z = "temp";
        closure_precise_capture(x, y, z)
        // z 在这里 drop，但 f 仍然有效，因为 f 没有捕获 'c
    };

    println!("{}", f());
}
```

### 7.4 迭代器返回

```rust
fn filter_by_key<'a, 'b, T: 'a>(
    items: &'a [T],
    key: &'b T::Key,
) -> impl Iterator<Item = &'a T> + use<'a>
where
    T: PartialEq + std::borrow::Borrow<T::Key>,
    T::Key: PartialEq,
{
    items.iter().filter(|item| item.borrow() == key)
}

fn example() {
    let items = vec![1, 2, 3, 2, 4];

    let iter = {
        let key = 2;
        filter_by_key(&items, &key)
        // key 被 drop，但 iter 仍然有效
    };

    for item in iter {
        println!("{}", item);
    }
}
```

### 7.5 异步函数中的精确捕获

```rust
async fn process_data<'a, 'b>(
    data: &'a [u8],
    config: &'b Config,
) -> impl Future<Output = Vec<u8>> + use<'a>
{
    // 只捕获 'a，config 只在调用时使用
    async move {
        // 使用 data
        data.to_vec()
    }
}

struct Config {
    timeout: u64,
}
```

### 7.6 复杂生命周期场景

```rust
struct Parser<'input> {
    source: &'input str,
    position: usize,
}

impl<'input> Parser<'input> {
    // 精确捕获：只捕获 'input
    fn parse_token(&mut self) -> impl Fn() -> Option<&'input str> + use<'input> {
        let start = self.position;
        || {
            // 使用 'input 生命周期
            Some(&self.source[start..])
        }
    }

    // 使用多个生命周期
    fn parse_with_context<'ctx>(
        &mut self,
        ctx: &'ctx Context,
    ) -> impl Fn() -> Result<Token, Error> + use<'input, 'ctx>
    {
        || {
            // 使用 'input 和 'ctx
            Ok(Token::new())
        }
    }
}

struct Context;
struct Token;
struct Error;

impl Token {
    fn new() -> Self { Token }
}
```

### 7.7 trait 中的精确捕获

```rust
trait Processor {
    fn process<'a>(&self, input: &'a str) -> impl Display + use<'a>;
}

struct MyProcessor;

impl Processor for MyProcessor {
    fn process<'a>(&self, input: &'a str) -> impl Display + use<'a> {
        // 只捕获 'a
        input.len()
    }
}
```

## 8. 与其他特性的交互

### 8.1 与生命周期子类型的交互

```rust
fn subtyping_capture<'long: 'short>(
    long_ref: &'long i32,
    short_ref: &'short i32,
) -> impl Fn() -> i32 + use<'short> {
    || *short_ref
}

// 'long 可以转换为 'short
fn example() {
    let x = 42;
    let long_ref: &'static i32 = &x;
    {
        let y = 100;
        let f = subtyping_capture(long_ref, &y);
        // y 被 drop 后 f 无效
    }
}
```

形式化：

$$
\frac{
  \rho_{\text{long}} : \rho_{\text{short}}
}{
  \text{impl } B + \text{use}\langle\rho_{\text{long}}\rangle <: \text{impl } B + \text{use}\langle\rho_{\text{short}}\rangle
}
$$

### 8.2 与闭包捕获的交互

```rust
fn closure_capture_modes() {
    let s = String::from("hello");
    let r = &s;

    // 精确捕获只影响生命周期捕获，不影响值捕获模式
    let f = || {
        println!("{}", r);  // 按引用捕获 r
    };

    let g = move || {
        println!("{}", r);  // 按值捕获 r
    };
}
```

### 8.3 与泛型的交互

```rust
fn generic_precise_capture<'a, T: 'a>(
    value: &'a T,
) -> impl Fn() -> &'a T + use<'a> {
    || value
}

// 在类型参数上使用精确捕获
struct Wrapper<'a, T: 'a> {
    value: &'a T,
}

impl<'a, T: 'a> Wrapper<'a, T> {
    fn get(&self) -> impl Fn() -> &'a T + use<'a> {
        || self.value
    }
}
```

### 8.4 与 Pin 的交互

```rust
use std::pin::Pin;

fn pinned_precise_capture<'a, T>(
    pinned: Pin<&'a mut T>,
) -> impl FnOnce() -> Pin<&'a T> + use<'a> {
    || {
        // 精确捕获 'a，保持 Pin 的保证
        Pin::new(&*pinned)
    }
}
```

## 9. 最佳实践

### 9.1 何时使用精确捕获

```rust
// 1. 当返回值不依赖所有输入生命周期时
fn get_name<'a, 'b>(person: &'a Person, config: &'b Config) -> impl Display + use<'a> {
    &person.name  // 只依赖 'a
}

// 2. 当需要避免生命周期过度约束时
fn transform<'a, 'b, T, F>(
    data: &'a [T],
    f: F,
) -> impl Iterator<Item = T> + use<'a>
where
    F: Fn(&T) -> T,
    T: Clone,
{
    data.iter().map(f)
}

// 3. 当需要更灵活的 API 时
fn create_callback<'a>(target: &'a Target) -> impl Fn() + use<'a> {
    || target.do_something()
}
```

### 9.2 常见陷阱

```rust
// 错误：捕获了不使用的生命周期
// fn bad<'a, 'b>(x: &'a i32, y: &'b i32) -> impl Fn() + use<'b> {
//     || { let _ = x; }  // 使用了 'a 但没有捕获
// }

// 正确：只捕获实际使用的生命周期
fn good<'a, 'b>(x: &'a i32, y: &'b i32) -> impl Fn() + use<'a> {
    || { let _ = x; }
}
```

## 10. 实现考虑

### 10.1 编译器实现

Rust 编译器处理精确捕获的步骤：

1. **解析**：识别 `use<...>` 语法
2. **收集**：确定捕获集
3. **验证**：检查捕获的生命周期确实被使用
4. **类型检查**：验证返回类型只依赖捕获的生命周期
5. **代码生成**：生成适当的闭包/迭代器代码

### 10.2 与现有代码的兼容性

```rust
// 没有 use<> 的代码继续工作（隐式捕获所有）
fn legacy<'a, 'b>(x: &'a i32, y: &'b i32) -> impl Fn() -> i32 {
    move || x + y
}

// 可以逐步迁移到精确捕获
fn modern<'a, 'b>(x: &'a i32, y: &'b i32) -> impl Fn() -> i32 + use<'a, 'b> {
    move || x + y
}
```

## 11. 总结

Precise Capturing (`use<'lt>`) 为 Rust 提供了更精确的生命周期控制能力：

1. **精确控制**：只捕获实际需要使用的生命周期
2. **更灵活的 API**：返回值的生命周期约束更精确
3. **向后兼容**：现有代码无需修改即可继续工作
4. **安全保证**：编译器确保捕获的生命周期确实被使用

通过 `use<'lt>`，开发者可以编写出生命周期约束更精确、API 更灵活的 Rust 代码。
