# Rust 2024 Edition 的新借用规则语义

## 1. 引言

Rust 2024 Edition 引入了多项重要的借用检查器改进，使得 Rust 的借用规则更加精确和灵活。
这些变化旨在减少不必要的编译错误，同时保持 Rust 的核心安全保证。

### 1.1 什么是 Edition

Rust 的 Edition 系统允许语言在不破坏向后兼容的情况下引入重大变化：

```toml
[package]
name = "my-project"
edition = "2024"
```

### 1.2 2024 Edition 的主要变化

1. **更精确的借用分析**：更细粒度的借用跟踪
2. **改进的闭包捕获**：更精确的闭包变量捕获
3. **新的匹配模式**：`ref` 和 `ref mut` 的改进
4. **临时生命周期规则**：临时值生命周期的调整

## 2. 语法定义

### 2.1 扩展的借用表达式

$$
\begin{aligned}
e \in \text{Expr} &::= \dots \\
&\quad | \; \text{borrow}(e, \text{mutability}) \quad \text{(显式借用)} \\
&\quad | \; \text{precise\_borrow}(e, \text{fields}) \quad \text{(精确字段借用)}
\end{aligned}
$$

### 2.2 闭包捕获模式

$$
\begin{aligned}
\text{CaptureMode} &::= \text{ByValue} \quad | \quad \text{ByRef} \\
&\quad | \quad \text{Precise}(\text{Path}) \quad \text{(2024 Edition)}
\end{aligned}
$

### 2.3 新的模式语法

```
Pattern ::= ...
        |  ref? mut? x              -- 变量绑定
        |  & ref? mut? Pattern      -- 引用模式
        |  (Pattern, ..., Pattern)  -- 元组模式
        |  Struct { field: Pattern, ... }  -- 结构体模式
```

## 3. 操作语义

### 3.1 精确借用规则

**精确字段借用** (E-Precise-Borrow):

$$
\frac{
  \langle e, \sigma \rangle \Downarrow \langle \text{struct}\{f_1: v_1, \dots, f_n: v_n\}, \sigma' \rangle
}{
  \langle \text{borrow}(e.f_i), \sigma \rangle \Downarrow
  \langle \&v_i, \sigma'[e \mapsto \text{partially\_borrowed}] \rangle
}
$

### 3.2 改进的闭包捕获

**精确捕获分析** (E-Closure-Precise-2024):

$$
\frac{
  \text{analyze\_body}(e) = \{(x_1, \text{usage}_1), \dots, (x_n, \text{usage}_n)\} \quad
  \forall i. \text{capture\_mode}(x_i, \text{usage}_i) = m_i
}{
  \langle || e, \sigma \rangle \Downarrow
  \langle \text{closure}(\lambda. e, \{(x_i, m_i)\}), \sigma \rangle
}
$

### 3.3 临时生命周期扩展

**临时生命周期 2024** (E-Temp-Lifetime-2024):

$$
\frac{
  \langle e, \sigma \rangle \Downarrow \langle v, \sigma' \rangle \quad
  \text{is\_temporary}(v) \quad
  \text{context\_extends\_lifetime}(\text{ctx})
}{
  \text{lifetime}(v) = \text{extended}(\text{original\_lifetime}(v))
}
$

## 4. 类型规则

### 4.1 精确借用类型规则

**字段级借用** (T-Field-Borrow):

$$
\frac{
  \Gamma \vdash e : S \quad
  S = \text{struct}\{f_1: \tau_1, \dots, f_n: \tau_n\} \quad
  1 \leq i \leq n
}{
  \Gamma \vdash \&e.f_i : \&\tau_i \quad
  \Gamma \vdash e : \text{partially\_borrowed}(f_i)
}
$

**多字段借用** (T-Multi-Field-Borrow):

$$
\frac{
  \Gamma \vdash e : S \quad
  S = \text{struct}\{f_1: \tau_1, \dots, f_n: \tau_n\} \quad
  \forall i \neq j. f_i \text{ disjoint } f_j
}{
  \Gamma \vdash (\&e.f_i, \&e.f_j) : (\&\tau_i, \&\tau_j)
}
$

### 4.2 闭包捕获规则

**最小捕获** (T-Minimal-Capture):

$$
\frac{
  \Gamma \vdash x : \tau \quad
  \text{usage}(x, e) = \text{Read} \quad
  \text{disjoint\_fields}(x, e)
}{
  \Gamma \vdash || e : \text{impl } Fn(...) \text{ captures } x \text{ by ref to field}
}
$

**移动捕获优化** (T-Move-Capture-Opt):

$$
\frac{
  \Gamma \vdash x : \tau \quad
  \text{usage}(x, e) = \text{Write} \quad
  \tau : \text{Copy}
}{
  \Gamma \vdash || e : \text{impl } Fn(...) \text{ captures } x \text{ by copy}
}
$

### 4.3 模式匹配改进

**精确 ref 绑定** (T-Precise-Ref):

$$
\frac{
  \Gamma \vdash e : \tau \quad
  \text{match\_usage}(p, e) = \text{Borrow}
}{
  \Gamma \vdash \text{match } e \{ \text{ref } p \Rightarrow \dots \} : \dots
}
$

### 4.4 借用检查改进

**非词法生命周期 2024** (T-NLL-2024):

$$
\frac{
  \Gamma \vdash \text{borrow}_1 : \&\tau_1 \quad
  \Gamma \vdash \text{borrow}_2 : \&\text{mut } \tau_2 \quad
  \text{usage\_sites}(\text{borrow}_1) \cap \text{usage\_sites}(\text{borrow}_2) = \emptyset
}{
  \Gamma \vdash \{\text{borrow}_1; \text{borrow}_2\} \text{ safe}
}
$

## 5. 形式化定义

### 5.1 借用区域

**定义 5.1** (借用区域)：

借用区域 $\mathcal{B}$ 是一个映射，记录每个位置的借用状态：

$$
\mathcal{B} : \text{Location} \rightarrow \{\text{Free}, \text{Shared}, \text{Mut}\}
$$

### 5.2 精确捕获集

**定义 5.2** (精确捕获)：

精确捕获 $\mathcal{P}$ 是一个二元组：

$$
\mathcal{P} = (\text{base\_var}, \text{projection\_path})
$$

其中 `projection_path` 是字段访问路径：

$$
\text{projection\_path} ::= \epsilon \quad | \quad .f \cdot \text{projection\_path}
$$

### 5.3 借用冲突检测

**定义 5.3** (借用冲突)：

两个借用 $b_1$ 和 $b_2$ 冲突，当：

$$
\text{conflict}(b_1, b_2) \iff
\begin{cases}
\text{true} & \text{if } \text{mut}(b_1) \lor \text{mut}(b_2) \land \text{overlap}(b_1, b_2) \\
\text{false} & \text{otherwise}
\end{cases}
$$

在 2024 Edition 中，`overlap` 的判断更加精确：

$$
\text{overlap}_{2024}(b_1, b_2) = \text{may\_alias}(\text{base}(b_1), \text{base}(b_2)) \land
\text{paths\_intersect}(\text{path}(b_1), \text{path}(b_2))
$$

### 5.4 生命周期区域

**定义 5.4** (生命周期区域)：

生命周期区域 $\mathcal{R}$ 是一个控制流图中的区域：

$$
\mathcal{R} \subseteq \text{BasicBlock}
$$

在 2024 Edition 中，生命周期区域更加精确，基于实际使用而非词法作用域。

## 6. 安全定理

### 6.1 精确借用安全

**定理 6.1** (2024 Edition 精确借用安全)：

如果 $\Gamma \vdash_{2024} e : \tau$，则：

$$
\forall b_1, b_2 \in \text{borrows}(e). \neg\text{conflict}_{2024}(b_1, b_2)
$$

**证明**：

通过对 2024 Edition 借用检查器的分析：

1. **字段级精确性**：借用检查器现在跟踪到字段级别
2. **路径敏感性**：不同字段的借用被视为不相交
3. **非词法分析**：基于实际使用位置而非词法作用域

因此，只要字段不相交，即使来自同一结构体，借用也是安全的。

### 6.2 闭包捕获安全

**定理 6.2** (2024 Edition 闭包捕获安全)：

如果 $\Gamma \vdash_{2024} || e : \text{impl } Fn(...) \rightarrow \tau$，则：

$$
\forall x \in \text{captured}(|| e). \text{valid\_capture}(x, e, \text{mode}(x))
$$

**证明**：

2024 Edition 的闭包捕获分析：

1. **最小化捕获**：只捕获实际使用的字段
2. **最优模式选择**：根据使用情况选择 by-value 或 by-ref
3. **生命周期正确性**：确保捕获的生命周期足够长

### 6.3 临时生命周期安全

**定理 6.3** (2024 Edition 临时生命周期安全)：

如果 $\Gamma \vdash_{2024} e : \tau$ 且 $e$ 包含临时值，则：

$$
\forall t \in \text{temps}(e). \text{lifetime}(t) \supseteq \text{usage\_range}(t)
$$

**证明**：

2024 Edition 扩展了临时值的生命周期：

1. 在 let 语句中，临时值生命周期延长到语句结束
2. 在 match 表达式中，临时值生命周期延长到匹配完成
3. 这防止了悬垂引用而不需要额外的变量绑定

### 6.4 与 2021 Edition 的兼容性

**定理 6.4** (版本兼容性)：

如果 $\Gamma \vdash_{2021} e : \tau$ 是有效的，则：

$$
\Gamma \vdash_{2024} e : \tau \text{ 也是有效的}
$$

**证明**：

2024 Edition 是 2021 Edition 的超集：

1. 所有 2021 Edition 有效的程序在 2024 Edition 中仍然有效
2. 2024 Edition 接受更多之前被拒绝的安全程序
3. 没有引入新的未定义行为

## 7. Rust 代码示例

### 7.1 精确字段借用

```rust
// 2021 Edition: 编译错误
// 2024 Edition: 编译通过
struct Point {
    x: i32,
    y: i32,
}

fn precise_field_borrow() {
    let mut p = Point { x: 1, y: 2 };

    // 同时借用不同字段
    let x = &mut p.x;
    let y = &mut p.y;  // 2021: 错误，p 已经被可变借用

    *x += 1;
    *y += 1;

    println!("Point: ({}, {})", p.x, p.y);
}

// 更复杂的例子
struct Rectangle {
    top_left: Point,
    bottom_right: Point,
}

fn disjoint_field_borrow() {
    let mut rect = Rectangle {
        top_left: Point { x: 0, y: 10 },
        bottom_right: Point { x: 10, y: 0 },
    };

    // 借用不相交的字段
    let tl = &mut rect.top_left;
    let br = &mut rect.bottom_right;  // 2024: OK!

    tl.x += 1;
    br.x -= 1;
}
```

### 7.2 改进的闭包捕获

```rust
// 2024 Edition: 更精确的闭包捕获
fn improved_closure_capture() {
    let mut data = (1, 2);

    // 2021 Edition: 捕获整个 data
    // 2024 Edition: 只捕获实际使用的字段
    let closure = || {
        println!("{}", data.0);  // 只使用 .0
    };

    // 2024 Edition: 可以修改 data.1，因为 closure 没有捕获它
    data.1 = 10;  // 2021: 错误，data 被借用；2024: OK!

    closure();
}

// 另一个例子
fn minimal_capture() {
    struct Data {
        value: i32,
        unused: String,
    }

    let data = Data {
        value: 42,
        unused: String::from("not used"),
    };

    let f = || {
        println!("{}", data.value);  // 只捕获 value
    };

    // 2024 Edition: unused 没有被捕获，可以被移动
    let _ = data.unused;  // 2021: 错误；2024: OK!

    f();
}
```

### 7.3 临时生命周期扩展

```rust
// 2024 Edition: 临时值生命周期扩展
fn temporary_lifetime_extension() {
    // 这个模式在 2024 Edition 中工作
    let slice = &vec![1, 2, 3];  // 2021: 编译错误；2024: OK!
    println!("{:?}", slice);
}

// 更实用的例子
fn match_temporaries() {
    let first = [1, 2, 3]
        .iter()
        .chain(&[4, 5, 6])
        .next();  // 2024: 临时迭代器生命周期足够长

    println!("{:?}", first);
}

// 方法链中的临时值
fn method_chain_temporaries() {
    // 2024 Edition 中，临时值在整条语句中保持有效
    let len = vec![1, 2, 3]
        .iter()
        .map(|x| x * 2)
        .filter(|x| *x > 2)
        .count();

    println!("{}", len);
}
```

### 7.4 改进的匹配模式

```rust
// 2024 Edition: 更好的 ref 模式处理
fn improved_ref_patterns() {
    let mut data = [1, 2, 3, 4, 5];

    // 更灵活的 match 模式
    match &mut data[..] {
        [first, rest @ ..] => {
            *first = 0;  // 修改第一个元素
            println!("Rest: {:?}", rest);  // 借用其余元素
        }
        [] => {}
    }
}

// 结构体模式
fn struct_patterns() {
    struct Item {
        name: String,
        value: i32,
    }

    let item = Item {
        name: String::from("test"),
        value: 42,
    };

    match &item {
        Item { name, .. } => {
            println!("{}", name);  // 只借用 name
        }
    }

    // item.value 仍然可用
    println!("{}", item.value);
}
```

### 7.5 非词法生命周期改进

```rust
// 2024 Edition: 更精确的非词法生命周期
fn nll_improvements() {
    let mut data = vec![1, 2, 3];

    // 借用只在需要时有效
    let ref1 = &data[0];
    println!("{}", ref1);  // ref1 在这里结束

    // 2021 Edition 中可能需要显式 drop
    // drop(ref1);

    // 2024 Edition 自动识别 ref1 不再使用
    data.push(4);  // 可以修改 data

    let ref2 = &data[1];
    println!("{}", ref2);
}

// 更复杂的控制流
fn control_flow_nll() {
    let mut data = vec![1, 2, 3];

    if true {
        let r = &data[0];
        println!("{}", r);
    }  // r 在这里结束

    // 可以安全地修改 data
    data.push(4);
}
```

### 7.6 与泛型的交互

```rust
// 2024 Edition 中的泛型借用
fn generic_borrowing<T>(mut container: Vec<T>) -> impl Iterator<Item = T> {
    // 2024 Edition 更精确地跟踪泛型类型的借用
    container.into_iter()
}

// 生命周期推断改进
fn lifetime_inference<'a, T: 'a>(items: &'a [T]) -> impl Iterator<Item = &'a T> + 'a {
    items.iter()
}

// 关联类型的借用
trait Container {
    type Item;
    fn get(&self) -> &Self::Item;
}

fn use_container<C: Container>(c: &C) -> &C::Item {
    // 2024 Edition 更好地处理关联类型生命周期
    c.get()
}
```

## 8. 2021 vs 2024 Edition 对比

### 8.1 借用检查器差异

```rust
// 示例 1: 字段借用
struct Pair { first: i32, second: i32 }

fn field_borrow_comparison() {
    let mut p = Pair { first: 1, second: 2 };

    let f = &mut p.first;
    let s = &mut p.second;
    // 2021 Edition: 错误 - p 已经被可变借用
    // 2024 Edition: 通过 - f 和 s 借用不相交的字段

    *f += 1;
    *s += 1;
}

// 示例 2: 闭包捕获
fn closure_capture_comparison() {
    let mut data = (1, String::from("hello"));

    let f = || {
        println!("{}", data.0);
    };

    let _ = data.1;  // 移动 String
    // 2021 Edition: 错误 - data 被闭包借用
    // 2024 Edition: 通过 - 闭包只捕获 data.0

    f();
}
```

### 8.2 临时生命周期差异

```rust
fn temporary_lifetime_comparison() {
    // 示例 1: let 语句中的临时值
    let r = &vec![1, 2, 3];
    // 2021 Edition: 编译错误 - 临时值生命周期太短
    // 2024 Edition: 编译通过 - 临时值生命周期延长

    // 示例 2: match 中的临时值
    let first = [1, 2, 3].iter().next();
    // 2021 Edition: 可能需要额外绑定
    // 2024 Edition: 自动处理
}
```

### 8.3 版本迁移指南

| 模式 | 2021 Edition | 2024 Edition |
|------|--------------|--------------|
| 字段级借用 | 受限 | 完全支持 |
| 闭包最小捕获 | 捕获整个变量 | 捕获实际使用的字段 |
| 临时生命周期 | 严格 | 更宽松 |
| 模式匹配 | 基础 | 改进的 ref 处理 |

## 9. 形式化差异分析

### 9.1 借用图差异

**2021 Edition 借用图**：

$$
\mathcal{G}_{2021} = (V, E) \text{ where } V = \text{variables}, E = \text{borrow\_relations}
$$

**2024 Edition 借用图**：

$$
\mathcal{G}_{2024} = (V', E') \text{ where } V' = \text{fields}, E' = \text{field\_level\_borrows}
$$

### 9.2 区域推断差异

**2021 Edition**：

$$
\text{region}_{2021}(b) = \text{lexical\_scope}(b)
$$

**2024 Edition**：

$$
\text{region}_{2024}(b) = \text{usage\_span}(b)
$$

### 9.3 闭包捕获差异

**2021 Edition 捕获**：

$$
\text{capture}_{2021}(x, e) = x \text{ (整个变量)}
$$

**2024 Edition 捕获**：

$$
\text{capture}_{2024}(x, e) = \{(x, p) \mid p \in \text{access\_paths}(x, e)\}
$$

## 10. 实现细节

### 10.1 编译器变化

Rust 2024 Edition 的借用检查器变化：

1. **Polonius 集成**：基于约束的借用检查
2. **字段级跟踪**：精确到字段的借用状态
3. **改进的 NLL**：更精确的非词法生命周期
4. **捕获分析**：AST 级别的精确捕获分析

### 10.2 MIR 表示变化

```rust
// 2021 Edition MIR
_2 = &mut _1;           // 借用整个变量

// 2024 Edition MIR
_2 = &mut (_1.0: i32);  // 只借用字段 0
_3 = &mut (_1.1: i32);  // 可以并发借用字段 1
```

## 11. 总结

Rust 2024 Edition 的借用规则改进使得语言更加灵活和安全：

### 11.1 关键改进

1. **精确字段借用**：可以同时借用同一结构体的不同字段
2. **最小闭包捕获**：闭包只捕获实际使用的部分
3. **临时生命周期扩展**：减少不必要的编译错误
4. **改进的模式匹配**：更灵活的 ref 处理

### 11.2 向后兼容性

- 所有 2021 Edition 代码在 2024 Edition 中仍然有效
- 2024 Edition 接受更多之前被拒绝的安全代码
- 通过 `edition` 标志选择行为

### 11.3 最佳实践

1. 新项目建议使用 2024 Edition
2. 利用精确字段借用简化代码
3. 依靠编译器的最小捕获优化
4. 减少不必要的 `drop()` 调用

这些改进使 Rust 在保持内存安全的同时，提供了更好的开发者体验。
