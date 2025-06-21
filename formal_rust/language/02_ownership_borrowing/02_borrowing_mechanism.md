# 2.3 借用机制的形式化

## 2.3.1 概述

借用（Borrowing）是Rust所有权系统的关键扩展，它允许在不转移所有权的情况下临时访问值。借用机制通过引用（references）实现，分为不可变引用（shared references）和可变引用（mutable references）。本章节将从形式化的角度详细阐述Rust的借用机制，包括其数学基础、形式化定义以及安全性保证。

## 2.3.2 引用的基本概念

### 2.3.2.1 引用类型

Rust中的引用有两种基本类型：

1. 不可变引用（shared reference）：`&T`
2. 可变引用（mutable reference）：`&mut T`

**形式化表示**：

设 $T$ 是任意类型，则：

- $\text{Ref}(T)$ 表示类型 $T$ 的不可变引用类型，即 `&T`
- $\text{MutRef}(T)$ 表示类型 $T$ 的可变引用类型，即 `&mut T`

### 2.3.2.2 借用关系

借用建立了引用与其引用值之间的关系。

**形式化定义**：

设 $\text{borrows}(r, v, t)$ 表示在时间点 $t$，引用 $r$ 借用了值 $v$。

对于不可变引用：
$$\text{immut\_borrows}(r, v, t) \Rightarrow r : \text{Ref}(T) \text{ where } v : T$$

对于可变引用：
$$\text{mut\_borrows}(r, v, t) \Rightarrow r : \text{MutRef}(T) \text{ where } v : T$$

## 2.3.3 借用规则

### 2.3.3.1 基本借用规则

Rust的借用检查器强制执行以下基本规则：

1. 在任意给定时刻，要么有任意数量的不可变引用，要么有一个可变引用
2. 引用必须始终有效（不能有悬垂引用）

**形式化表示**：

设 $\text{Refs}(v, t)$ 表示在时间点 $t$ 借用值 $v$ 的所有引用的集合：

$$\text{Refs}(v, t) = \{r \mid \text{borrows}(r, v, t)\}$$

设 $\text{MutRefs}(v, t)$ 表示在时间点 $t$ 可变借用值 $v$ 的所有引用的集合：

$$\text{MutRefs}(v, t) = \{r \mid \text{mut\_borrows}(r, v, t)\}$$

则借用规则可以形式化为：

$$\forall v, t: |\text{MutRefs}(v, t)| \leq 1$$

$$\forall v, t: |\text{MutRefs}(v, t)| > 0 \Rightarrow |\text{Refs}(v, t)| = |\text{MutRefs}(v, t)|$$

### 2.3.3.2 借用的生命周期

每个引用都有一个生命周期（lifetime），表示引用有效的程序区域。

**形式化定义**：

设 $\text{lifetime}(r) = [t_{\text{start}}, t_{\text{end}}]$ 表示引用 $r$ 的生命周期，从 $t_{\text{start}}$ 开始到 $t_{\text{end}}$ 结束。

则：

$$\forall t \in [t_{\text{start}}, t_{\text{end}}], \exists v \text{ such that } \text{borrows}(r, v, t)$$

并且：

$$\forall t \notin [t_{\text{start}}, t_{\text{end}}], \nexists v \text{ such that } \text{borrows}(r, v, t)$$

## 2.3.4 借用检查器的形式化

### 2.3.4.1 借用检查的基本判断

借用检查器通过跟踪每个值的借用状态来强制执行借用规则。

**形式化表示**：

设 $\Gamma$ 是类型环境，$\Delta$ 是线性资源环境，$\Sigma$ 是借用环境，记录了当前的借用状态。

借用判断的形式为：

$$\Gamma; \Delta; \Sigma \vdash e : T$$

### 2.3.4.2 借用规则的形式化

**不可变借用规则**：

$$\frac{\Gamma; \Delta \vdash x : T \quad \text{no mutable borrows of } x \text{ in } \Sigma}{\Gamma; \Delta; \Sigma \cup \{\text{immut\_borrow}(r, x)\} \vdash \text{\&}x : \text{Ref}(T)}$$

**可变借用规则**：

$$\frac{\Gamma; \Delta \vdash x : T \quad \text{no borrows of } x \text{ in } \Sigma}{\Gamma; \Delta; \Sigma \cup \{\text{mut\_borrow}(r, x)\} \vdash \text{\&mut }x : \text{MutRef}(T)}$$

**解引用规则**：

$$\frac{\Gamma; \Delta; \Sigma \vdash e : \text{Ref}(T)}{\Gamma; \Delta; \Sigma \vdash *e : T}$$

$$\frac{\Gamma; \Delta; \Sigma \vdash e : \text{MutRef}(T)}{\Gamma; \Delta; \Sigma \vdash *e : T}$$

## 2.3.5 借用与所有权的交互

### 2.3.5.1 借用对所有权的限制

当一个值被借用时，其所有者的能力会受到限制：

1. 如果存在不可变借用，所有者不能修改值
2. 如果存在可变借用，所有者不能访问或修改值
3. 在任何借用存在期间，所有者不能转移值的所有权

**形式化表示**：

$$\forall v, t: |\text{Refs}(v, t)| > 0 \Rightarrow \text{owner}_t(v) \text{ cannot modify } v \text{ at time } t$$

$$\forall v, t: |\text{MutRefs}(v, t)| > 0 \Rightarrow \text{owner}_t(v) \text{ cannot access } v \text{ at time } t$$

$$\forall v, t: |\text{Refs}(v, t)| > 0 \Rightarrow \text{ownership of } v \text{ cannot be transferred at time } t$$

### 2.3.5.2 借用的非词法作用域（Non-Lexical Lifetimes, NLL）

Rust的借用检查器使用非词法作用域分析来确定引用的实际生命周期，使得借用的限制仅在必要时有效。

**形式化表示**：

设 $\text{last\_use}(r, t)$ 表示引用 $r$ 在时间点 $t$ 之后不再被使用。则：

$$\text{last\_use}(r, t) \Rightarrow \forall t' > t, \nexists v \text{ such that } \text{borrows}(r, v, t')$$

这允许借用检查器在引用的最后一次使用后立即结束其生命周期，而不必等到词法作用域结束。

## 2.3.6 借用的高级特性

### 2.3.6.1 可变性与排他性

Rust的类型系统将可变性与排他性关联起来：可变引用必须是排他的，而不可变引用可以共享。

**形式化原则**：

1. **可变性需要排他性**：如果一个引用可以修改值，那么它必须是唯一能访问该值的引用
2. **共享需要不可变性**：如果多个引用同时访问一个值，那么它们都必须是不可变的

### 2.3.6.2 内部可变性

内部可变性（interior mutability）是Rust类型系统的一个特性，允许在拥有不可变引用的情况下修改值，通过运行时借用检查确保安全性。

**主要类型**：

1. `Cell<T>`：提供通过值复制的内部可变性
2. `RefCell<T>`：提供运行时借用检查的内部可变性
3. `Mutex<T>`：提供线程安全的内部可变性

**形式化表示**：

对于`RefCell<T>`，我们有：

$$\frac{\Gamma; \Delta; \Sigma \vdash e : \text{Ref}(\text{RefCell}(T))}{\Gamma; \Delta; \Sigma \vdash e.\text{borrow\_mut}() : \text{MutRef}(T)}$$

但这需要在运行时验证：

$$|\text{runtime\_MutRefs}(v, t)| = 0 \text{ and } |\text{runtime\_Refs}(v, t)| = 0$$

## 2.3.7 借用的实际应用

### 2.3.7.1 基本借用示例

```rust
fn main() {
    let mut x = 5;
    let r1 = &x;      // 不可变借用
    let r2 = &x;      // 另一个不可变借用
    println!("{} {}", r1, r2);
    // r1和r2在这里不再使用
    
    let r3 = &mut x;  // 可变借用
    *r3 += 1;
    println!("{}", r3);
    // r3在这里不再使用
    
    x += 1;           // 直接使用x
    println!("{}", x);
}
```

**形式化分析**：

1. 在时间点 $t_1$，创建不可变引用 $r_1$，有 $\text{immut\_borrows}(r_1, x, t_1)$
2. 在时间点 $t_2$，创建不可变引用 $r_2$，有 $\text{immut\_borrows}(r_2, x, t_2)$
3. 在时间点 $t_3$，使用 $r_1$ 和 $r_2$
4. 在时间点 $t_4 > t_3$，$r_1$ 和 $r_2$ 的生命周期结束
5. 在时间点 $t_5 > t_4$，创建可变引用 $r_3$，有 $\text{mut\_borrows}(r_3, x, t_5)$
6. 在时间点 $t_6 > t_5$，修改 $x$ 通过 $r_3$
7. 在时间点 $t_7 > t_6$，$r_3$ 的生命周期结束
8. 在时间点 $t_8 > t_7$，直接修改 $x$

### 2.3.7.2 函数参数中的借用

```rust
fn calculate_length(s: &String) -> usize {
    s.len()
}

fn change_string(s: &mut String) {
    s.push_str(", world");
}

fn main() {
    let mut s = String::from("hello");
    
    let len = calculate_length(&s);
    println!("The length of '{}' is {}.", s, len);
    
    change_string(&mut s);
    println!("Now the string is: {}", s);
}
```

**形式化分析**：

对于`calculate_length`函数：

$$\frac{\Gamma; \Delta \vdash s : \text{String} \quad \text{no mutable borrows of } s \text{ in } \Sigma}{\Gamma; \Delta; \Sigma \cup \{\text{immut\_borrow}(r, s)\} \vdash \text{\&}s : \text{Ref}(\text{String})}$$

对于`change_string`函数：

$$\frac{\Gamma; \Delta \vdash s : \text{String} \quad \text{no borrows of } s \text{ in } \Sigma}{\Gamma; \Delta; \Sigma \cup \{\text{mut\_borrow}(r, s)\} \vdash \text{\&mut }s : \text{MutRef}(\text{String})}$$

## 2.3.8 借用规则的形式化证明

### 2.3.8.1 数据竞争自由定理

**定理**：遵循Rust借用规则的程序不会出现数据竞争。

**证明**：

数据竞争发生的条件是：

1. 两个或更多指针同时访问同一数据
2. 至少有一个指针被用于写入
3. 没有同步机制

假设存在数据竞争，则在某个时间点 $t$，存在两个引用 $r_1$ 和 $r_2$ 同时访问值 $v$，且至少一个是可变引用。

如果 $r_1$ 是可变引用，则 $\text{mut\_borrows}(r_1, v, t)$。根据借用规则，$|\text{MutRefs}(v, t)| = 1$ 且 $|\text{Refs}(v, t)| = 1$，即 $r_2$ 不存在或 $r_2 = r_1$。

如果 $r_1$ 和 $r_2$ 都是不可变引用，则都不能用于写入，不满足数据竞争的条件2。

因此，遵循Rust借用规则的程序不会出现数据竞争。

### 2.3.8.2 引用有效性定理

**定理**：在遵循Rust借用规则的程序中，所有引用在使用时都是有效的。

**证明**：

假设存在引用 $r$ 在时间点 $t$ 被使用，但它指向的值 $v$ 已经无效。

根据借用规则，$r$ 的生命周期为 $[t_{\text{start}}, t_{\text{end}}]$，且 $t \in [t_{\text{start}}, t_{\text{end}}]$。

如果 $v$ 在 $t$ 时无效，则 $v$ 的所有者必须在 $t$ 之前转移了所有权或离开了作用域。

然而，借用规则规定，在任何借用存在期间，所有者不能转移值的所有权，且所有者的作用域必须包含借用的生命周期。

这导致矛盾，因此在遵循Rust借用规则的程序中，所有引用在使用时都是有效的。

## 2.3.9 借用机制的局限性与扩展

### 2.3.9.1 局限性

尽管Rust的借用机制提供了强大的安全保证，但也存在一些局限性：

1. **表达能力限制**：某些数据结构（如图）难以在严格的借用规则下表达
2. **生命周期标注复杂性**：在复杂情况下，可能需要显式的生命周期标注
3. **运行时开销**：内部可变性（如`RefCell`）引入了运行时检查

### 2.3.9.2 扩展机制

Rust提供了几种机制来扩展基本借用模型的表达能力：

1. **内部可变性**：通过`Cell`、`RefCell`、`Mutex`等类型提供
2. **不安全代码**：通过`unsafe`块允许绕过借用检查
3. **生命周期标注**：通过显式标注控制引用的生命周期关系

## 2.3.10 借用与生命周期

### 2.3.10.1 生命周期参数

生命周期参数是Rust类型系统的一部分，用于表示引用的有效期。

**形式化表示**：

设 $\alpha$ 是一个生命周期参数，则：

- $\text{Ref}_{\alpha}(T)$ 表示生命周期为 $\alpha$ 的不可变引用类型，即 `&'a T`
- $\text{MutRef}_{\alpha}(T)$ 表示生命周期为 $\alpha$ 的可变引用类型，即 `&'a mut T`

### 2.3.10.2 生命周期子类型关系

生命周期之间存在子类型关系，表示一个生命周期包含另一个生命周期。

**形式化表示**：

设 $\alpha$ 和 $\beta$ 是两个生命周期参数，如果 $\alpha$ 至少与 $\beta$ 一样长，则 $\alpha : \beta$（$\alpha$ 是 $\beta$ 的子类型）。

这导致了引用类型之间的子类型关系：

$$\frac{\alpha : \beta}{\text{Ref}_{\alpha}(T) : \text{Ref}_{\beta}(T)}$$

$$\frac{\alpha : \beta}{\text{MutRef}_{\alpha}(T) : \text{MutRef}_{\beta}(T)}$$

## 2.3.11 总结

Rust的借用机制是所有权系统的关键扩展，它允许在不转移所有权的情况下临时访问值。本章从形式化的角度详细阐述了借用机制，包括其数学基础、形式化定义以及安全性保证。借用机制与所有权系统共同构成了Rust内存安全和线程安全的基础，使得Rust能够在不依赖垃圾回收的情况下提供强大的安全保证。

## 2.3.12 参考文献

1. Klabnik, S., & Nichols, C. (2019). The Rust Programming Language.
2. Matsakis, N. D., & Klock, F. S. (2014). The Rust Language. Ada Letters, 34(3), 103-104.
3. Jung, R., Jourdan, J. H., Krebbers, R., & Dreyer, D. (2018). RustBelt: Securing the Foundations of the Rust Programming Language.
4. Weiss, A., Patterson, D., Ahmed, A., Appel, A. W., & Morrisett, G. (2019). Reference Mutability for Safe Parallelism.
5. Matsakis, N. D. (2018). Non-lexical lifetimes: Introduction. Rust Blog.
