# 2.2 所有权规则的形式化

## 2.2.1 概述

所有权（Ownership）是Rust语言最核心的特性之一，它为内存安全提供了坚实的基础，同时避免了垃圾回收带来的运行时开销。本章节将从形式化的角度详细阐述Rust的所有权规则，包括其数学基础、形式化定义以及与线性类型理论的关系。

## 2.2.2 所有权的基本规则

### 2.2.2.1 核心规则

Rust的所有权系统基于以下三条基本规则：

1. 每个值都有一个被称为其所有者（owner）的变量
2. 在任意给定时刻，一个值只能有一个所有者
3. 当所有者离开作用域，该值将被丢弃（drop）

**形式化表示**：

设 $\mathcal{V}$ 表示值的集合，$\mathcal{X}$ 表示变量的集合，$\text{owner}: \mathcal{V} \rightarrow \mathcal{X}$ 是一个在任意时刻 $t$ 将值映射到其所有者的函数。则所有权规则可以表示为：

1. $\forall v \in \mathcal{V}, \exists x \in \mathcal{X} \text{ such that } \text{owner}_t(v) = x$
2. $\forall v, v' \in \mathcal{V}, v \neq v' \Rightarrow \text{owner}_t(v) \neq \text{owner}_t(v')$
3. $\forall v \in \mathcal{V}, \text{if } \text{owner}_t(v) \text{ goes out of scope at time } t' > t, \text{then } v \text{ is dropped at time } t'$

### 2.2.2.2 作用域与资源管理

在Rust中，作用域（scope）定义了变量的有效范围。当变量离开作用域时，Rust会自动调用其`drop`函数，释放相关资源。

**形式化定义**：

设 $\text{scope}(x)$ 表示变量 $x$ 的作用域，是程序点的集合。则：

$$\forall v \in \mathcal{V}, \forall p \in \text{Program Points}, p \notin \text{scope}(\text{owner}_t(v)) \Rightarrow v \text{ is not accessible at } p$$

## 2.2.3 所有权转移

### 2.2.3.1 移动语义

Rust默认使用移动（move）语义而非复制（copy）语义。当一个值被赋给另一个变量或传递给函数时，所有权会发生转移。

**形式化表示**：

设 $t_1 < t_2$ 是两个时间点，若在 $t_1$ 时刻有 $\text{owner}_{t_1}(v) = x_1$，且在 $t_2$ 时刻有 $\text{owner}_{t_2}(v) = x_2$ 且 $x_1 \neq x_2$，则称所有权从 $x_1$ 转移到了 $x_2$。

**规则**：

$$\frac{x_1 = \text{owner}_{t_1}(v) \quad x_2 = \text{target of assignment} \quad t_2 > t_1}{\text{owner}_{t_2}(v) = x_2 \quad x_1 \text{ no longer owns any value at } t_2}$$

### 2.2.3.2 复制与克隆

对于实现了`Copy`特质的类型，赋值操作会复制值而非移动。对于其他类型，可以通过显式调用`clone`方法创建深拷贝。

**形式化表示**：

设 $\text{Copy}(T)$ 表示类型 $T$ 实现了`Copy`特质，$v: T$ 表示 $v$ 的类型为 $T$。

对于复制操作：

$$\frac{\text{Copy}(T) \quad v: T \quad \text{owner}_{t_1}(v) = x_1 \quad x_2 = \text{target of assignment} \quad t_2 > t_1}{\exists v' \text{ such that } v' \text{ is a copy of } v \quad \text{owner}_{t_2}(v) = x_1 \quad \text{owner}_{t_2}(v') = x_2}$$

对于克隆操作：

$$\frac{v: T \quad \text{owner}_{t_1}(v) = x_1 \quad v' = \text{clone}(v) \quad t_2 > t_1}{\text{owner}_{t_2}(v) = x_1 \quad \text{owner}_{t_2}(v') = x_2}$$

## 2.2.4 所有权与线性类型

### 2.2.4.1 线性类型系统

Rust的所有权系统可以通过线性类型理论进行形式化。在线性类型系统中，每个值必须精确地使用一次，这与Rust的所有权规则高度一致。

**形式化对应**：

设 $\Gamma$ 是类型环境，$\Delta$ 是线性资源环境。则：

$$\frac{\Gamma \vdash e_1 : T_1 \multimap T_2 \quad \Gamma; \Delta_1 \vdash e_2 : T_1}{\Gamma; \Delta_1 \vdash e_1 \; e_2 : T_2}$$

其中 $\multimap$ 是线性函数类型构造器，表示函数在执行过程中会消耗其参数。

### 2.2.4.2 仿射类型系统

实际上，Rust的所有权系统更接近于仿射类型系统，允许值被使用零次或一次，但不能多于一次。

**形式化表示**：

在仿射类型系统中，我们有弱化规则（weakening）：

$$\frac{\Gamma; \Delta \vdash e : T}{\Gamma; \Delta, x : S \vdash e : T}$$

这允许资源被丢弃而不使用，对应于Rust中变量可以声明但不使用的情况（尽管会产生编译器警告）。

## 2.2.5 所有权与类型系统

### 2.2.5.1 所有权类型判断

Rust的类型系统将所有权信息编码到类型判断中。

**形式化表示**：

$$\Gamma; \Delta \vdash e : T$$

其中：
- $\Gamma$ 是共享（非线性）环境，包含引用类型
- $\Delta$ 是线性环境，包含拥有所有权的值
- $e$ 是表达式
- $T$ 是类型

### 2.2.5.2 移动检查

Rust编译器会追踪值的移动，并防止使用已移动的值。

**形式化规则**：

$$\frac{\Delta(x) = T \quad \text{moved}(x) = \text{false}}{\Gamma; \Delta \vdash x : T}$$

$$\frac{\Delta(x) = T \quad \text{moved}(x) = \text{true}}{\Gamma; \Delta \vdash x : \text{ERROR}}$$

## 2.2.6 所有权与内存模型

### 2.2.6.1 栈与堆

Rust的所有权系统与其内存模型密切相关：

- 栈上分配的值：大小固定，生命周期与所有者绑定
- 堆上分配的值：大小可变，通过`Box`、`Vec`等智能指针管理

**形式化表示**：

设 $\text{Mem} = \text{Stack} \cup \text{Heap}$ 表示内存空间，$\text{alloc} : \mathcal{V} \rightarrow \text{Mem}$ 表示值的分配位置。

对于栈分配：

$$\frac{v : T \quad \text{size}(T) \text{ is known at compile time}}{\text{alloc}(v) \in \text{Stack}}$$

对于堆分配：

$$\frac{v : \text{Box}<T>}{\exists v' : T \text{ such that } \text{alloc}(v') \in \text{Heap} \text{ and } v \text{ owns } v'}$$

### 2.2.6.2 RAII模式

Rust采用RAII（Resource Acquisition Is Initialization）模式，资源的获取与对象初始化绑定，资源的释放与对象销毁绑定。

**形式化表示**：

设 $\text{acquire}(r)$ 表示获取资源 $r$，$\text{release}(r)$ 表示释放资源 $r$。则：

$$\frac{x \text{ is initialized with resource } r}{\text{acquire}(r) \text{ is called}}$$

$$\frac{x \text{ goes out of scope and owns resource } r}{\text{release}(r) \text{ is called via } \text{drop}(x)}$$

## 2.2.7 所有权规则的实际应用

### 2.2.7.1 基本示例

```rust
fn main() {
    let s1 = String::from("hello"); // s1 owns the string
    let s2 = s1;                    // ownership moves to s2
    // println!("{}", s1);          // Error: s1 no longer owns the string
    println!("{}", s2);             // OK: s2 owns the string
}
```

**形式化分析**：

1. 在时间点 $t_1$，创建字符串值 $v$，有 $\text{owner}_{t_1}(v) = \text{s1}$
2. 在时间点 $t_2 > t_1$，所有权转移，有 $\text{owner}_{t_2}(v) = \text{s2}$
3. 在 $t_2$ 之后，$\text{s1}$ 不再拥有任何值，使用 $\text{s1}$ 会导致编译错误

### 2.2.7.2 函数参数与返回值

```rust
fn take_ownership(s: String) {
    println!("{}", s);
} // s goes out of scope and is dropped

fn gives_ownership() -> String {
    let s = String::from("hello");
    s // ownership of s is moved to the calling function
}

fn main() {
    let s1 = String::from("hello");
    take_ownership(s1); // s1's ownership is moved to the function
    // println!("{}", s1); // Error: s1 no longer owns the string
    
    let s2 = gives_ownership(); // s2 takes ownership of the returned string
    println!("{}", s2); // OK: s2 owns the string
}
```

**形式化分析**：

对于`take_ownership`函数：

$$\frac{\text{owner}_{t_1}(v) = \text{s1} \quad \text{s is parameter of take_ownership}}{\text{owner}_{t_2}(v) = \text{s} \quad \text{s1 no longer owns any value}}$$

对于`gives_ownership`函数：

$$\frac{\text{owner}_{t_3}(v') = \text{s} \quad \text{s2 = result of gives_ownership()}}{\text{owner}_{t_4}(v') = \text{s2} \quad \text{s no longer owns any value}}$$

## 2.2.8 所有权规则的形式化证明

### 2.2.8.1 内存安全性定理

**定理**：遵循Rust所有权规则的程序不会出现悬垂引用（dangling references）。

**证明**：

假设存在悬垂引用，即在时间点 $t$ 存在引用 $r$ 指向值 $v$，但 $v$ 已被释放。

由于 $v$ 被释放，根据规则3，其所有者 $x = \text{owner}_{t'}(v)$ 在某个时间点 $t' < t$ 离开了作用域。

然而，要创建指向 $v$ 的引用 $r$，必须通过借用操作（将在下一章详细讨论），这要求 $v$ 的所有者在引用有效期内保持有效。

这导致矛盾，因为我们假设 $r$ 在时间点 $t$ 有效，但 $v$ 的所有者已在 $t' < t$ 离开作用域。

因此，遵循Rust所有权规则的程序不会出现悬垂引用。

### 2.2.8.2 资源泄漏预防定理

**定理**：遵循Rust所有权规则的程序不会出现资源泄漏（除非使用`std::mem::forget`或循环引用）。

**证明草图**：

1. 假设值 $v$ 关联了资源 $r$
2. 根据所有权规则3，当 $v$ 的所有者离开作用域时，$v$ 会被丢弃
3. 根据RAII模式，当 $v$ 被丢弃时，资源 $r$ 会被释放
4. 由于每个值都有唯一的所有者，且所有者最终会离开作用域，所以每个资源最终都会被释放

例外情况：
- 使用`std::mem::forget`显式阻止值被丢弃
- 创建循环引用（需要使用`Rc`/`Arc`和`RefCell`/`Mutex`）

## 2.2.9 所有权系统的局限性与扩展

### 2.2.9.1 局限性

尽管Rust的所有权系统提供了强大的安全保证，但也存在一些局限性：

1. **表达能力限制**：某些数据结构（如图）难以在严格的所有权模型下表达
2. **学习曲线**：所有权和借用规则增加了语言的学习难度
3. **代码冗长**：有时需要显式处理所有权转移，增加代码复杂性

### 2.2.9.2 扩展机制

Rust提供了几种机制来扩展基本所有权模型的表达能力：

1. **引用计数**：`Rc`和`Arc`允许多重所有权
2. **内部可变性**：`RefCell`和`Mutex`允许在不可变引用的情况下修改值
3. **不安全代码**：`unsafe`块允许绕过所有权检查，但需要程序员保证安全性

**形式化表示**：

对于引用计数：

$$\frac{v : \text{Rc}<T> \quad \text{count}(v) > 0}{\exists x_1, x_2, \ldots, x_n \text{ such that each } x_i \text{ has a shared ownership of } v}$$

## 2.2.10 总结

Rust的所有权系统是一种强大的内存管理机制，它通过静态类型系统在编译时强制执行资源安全。本章从形式化的角度详细阐述了所有权规则，包括其数学基础、形式化定义以及与线性类型理论的关系。所有权系统为Rust提供了内存安全和线程安全保证，同时避免了垃圾回收带来的运行时开销，是Rust最具特色和价值的设计之一。

## 2.2.11 参考文献

1. Matsakis, N. D., & Klock, F. S. (2014). The Rust Language. Ada Letters, 34(3), 103-104.
2. Klabnik, S., & Nichols, C. (2019). The Rust Programming Language.
3. Wadler, P. (1990). Linear Types Can Change the World!
4. Walker, D. (2005). Substructural Type Systems. In Advanced Topics in Types and Programming Languages.
5. Jung, R., Jourdan, J. H., Krebbers, R., & Dreyer, D. (2018). RustBelt: Securing the Foundations of the Rust Programming Language. 