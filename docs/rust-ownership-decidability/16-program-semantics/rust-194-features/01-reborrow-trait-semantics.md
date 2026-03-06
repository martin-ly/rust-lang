# Reborrow Trait 的完整形式化语义

## 1. 引言

Reborrow Trait 是 Rust 类型系统中一个核心但隐式的机制，它允许可变引用 `&mut T` 在不放弃所有权的情况下创建临时只读引用 `&T`。
这种机制是 Rust 实现灵活借用模式的基础，使得代码能够在保持所有权不变的同时临时共享数据访问。

在 Rust 1.94 中，Reborrow Trait 的行为得到了更精确的定义，特别是在处理生命周期和借用检查器的交互方面。

### 1.1 什么是 Reborrow

Reborrow 本质上是一种**引用的转换操作**：

```rust
let mut x = 5;
let r_mut: &mut i32 = &mut x;
let r_shared: &i32 = &*r_mut;  // 这就是 reborrow
```

从形式化角度看，Reborrow 关系可以表示为：

$$
\text{Reborrow} : \&'\rho_1 \text{ mut } T \rightarrow \&'\rho_2 T
$$

其中 $\rho_2 \sqsubseteq \rho_1$，即新引用的生命周期必须小于或等于原引用的生命周期。

## 2. 语法定义

### 2.1 Reborrow 操作的语法

Reborrow 操作在 Rust 中有多种表现形式：

$$
\begin{aligned}
e \in \text{Expr} &::= \dots \\
&\quad | \; \&*e \quad \text{(显式 reborrow)} \\
&\quad | \; \text{reborrow}(e) \quad \text{(形式化表示)} \\
&\quad | \; e \text{ as } \&T \quad \text{(类型转换)} \\
&\quad | \; \text{match } e \{ \text{ref } x \Rightarrow \dots \} \quad \text{(模式匹配 reborrow)}
\end{aligned}
$$

### 2.2 类型语法扩展

```
τ ::= T                    -- 基本类型
  | &ρ mut τ             -- 可变引用
  | &ρ τ                 -- 不可变引用
  | Reborrow(τ₁, τ₂)     -- Reborrow 关系类型
```

其中 `Reborrow(&'a mut T, &'b T)` 表示从 `'a mut T` 到 `'b T` 的有效 reborrow。

## 3. 操作语义

### 3.1 大步操作语义 (Big-Step Semantics)

**基本 Reborrow 规则** (EB-Reborrow):

$$
\frac{
  \langle e, \sigma \rangle \Downarrow \langle \&'\rho_1 \text{ mut } v, \sigma' \rangle \quad
  \rho_2 \sqsubseteq \rho_1 \quad
  \text{valid}(\sigma', \&'\rho_1 \text{ mut } v)
}{
  \langle \&*e, \sigma \rangle \Downarrow \langle \&'\rho_2 v, \sigma' \rangle
}
$$

**含义**：如果表达式 $e$ 求值为一个指向值 $v$ 的可变引用，且新生命周期 $\rho_2$ 是原生命周期 $\rho_1$ 的子生命周期，则 reborrow 操作产生一个指向同一值 $v$ 的只读引用。

### 3.2 小步操作语义 (Small-Step Semantics)

**Reborrow 规约规则** (S-Reborrow):

$$
\frac{
  e \rightarrow e'
}{
  \&*e \rightarrow \&*e'
}
\quad\text{(S-Reborrow-Step)}
$$

$$
\frac{
  \text{valid}(\sigma, \&'\rho_1 \text{ mut } v) \quad
  \rho_2 \sqsubseteq \rho_1
}{
  \langle \&*(\&'\rho_1 \text{ mut } v), \sigma \rangle \rightarrow \langle \&'\rho_2 v, \sigma \rangle
}
\quad\text{(S-Reborrow-Value)}
$$

### 3.3 存储语义

Reborrow 操作对存储的影响：

$$
\frac{
  \sigma(x) = \langle \&'\rho_1 \text{ mut } v, \text{Mut} \rangle
}{
  \sigma' = \sigma[x \mapsto \langle \&'\rho_2 v, \text{Imm} \rangle]
}
\quad\text{(Reborrow-Store-Update)}
$$

其中 `Mut` 表示可变访问，`Imm` 表示不可变访问。

## 4. 类型规则

### 4.1 Reborrow 类型推导规则

**Reborrow 推导规则** (T-Reborrow):

$$
\frac{
  \Gamma \vdash e : \&'\rho_1 \text{ mut } T \quad
  \rho_2 \sqsubseteq \rho_1 \quad
  \Gamma \vdash \rho_2 : \text{Lifetime}
}{
  \Gamma \vdash \&*e : \&'\rho_2 T
}
$$

**前提条件**：

1. 表达式 $e$ 具有类型 `&'ρ₁ mut T`
2. 生命周期 $\rho_2$ 是 $\rho_1$ 的子生命周期
3. $\rho_2$ 是一个有效的生命周期

### 4.2 生命周期包含关系

$$
\frac{
  \rho_1 \text{ 在作用域内} \quad
  \rho_2 \text{ 嵌套于 } \rho_1
}{
  \Gamma \vdash \rho_2 \sqsubseteq \rho_1
}
\quad\text{(L-Sub)}
$$

### 4.3 借用检查规则

**借用有效性规则** (B-Reborrow):

$$
\frac{
  \text{borrow\_set}(\Gamma, x) = \{b_1, \dots, b_n\} \quad
  \forall i. \text{compatible}(b_i, \&'\rho_2 T) \quad
  \text{no\_active\_mut}(\Gamma, x, \rho_2)
}{
  \Gamma \vdash \&*x \text{ safe}
}
$$

其中 `no_active_mut` 确保在 reborrow 期间没有活跃的可变借用。

### 4.4 多重 Reborrow 规则

$$
\frac{
  \Gamma \vdash e : \&'\rho_1 \text{ mut } \&'\rho_2 \text{ mut } T \quad
  \rho_3 \sqsubseteq \rho_2
}{
  \Gamma \vdash \&*\&*e : \&'\rho_3 T
}
\quad\text{(T-Reborrow-Nested)}
$$

## 5. 形式化定义

### 5.1 Reborrow 关系的数学定义

**定义 5.1** (Reborrow 关系)：

对于类型 $T$ 和生命周期 $\rho_1, \rho_2$，Reborrow 关系 $\mathcal{R}$ 定义为：

$$
\mathcal{R}(T, \rho_1, \rho_2) \subseteq \&'\rho_1 \text{ mut } T \times \&'\rho_2 T
$$

其中 $(r_{\text{mut}}, r_{\text{shared}}) \in \mathcal{R}(T, \rho_1, \rho_2)$ 当且仅当：

1. $\text{target}(r_{\text{mut}}) = \text{target}(r_{\text{shared}})$
2. $\rho_2 \sqsubseteq \rho_1$
3. $\forall t \in \rho_2. \text{valid}(r_{\text{mut}}, t)$

### 5.2 引用有效性

**定义 5.2** (引用有效性)：

引用 $r$ 在时间 $t$ 有效，记作 $\text{valid}(r, t)$，当且仅当：

$$
\text{valid}(\&'\rho \tau, t) \iff t \in \rho \land \text{alive}(\text{target}(r), t)
$$

### 5.3 生命周期包含

**定义 5.3** (生命周期包含)：

生命周期 $\rho_1$ 包含 $\rho_2$，记作 $\rho_2 \sqsubseteq \rho_1$，定义为：

$$
\rho_2 \sqsubseteq \rho_1 \iff \forall t. \, t \in \rho_2 \rightarrow t \in \rho_1
$$

### 5.4 借用兼容性

**定义 5.4** (借用兼容性)：

两个借用 $b_1$ 和 $b_2$ 是兼容的，记作 $\text{compatible}(b_1, b_2)$，当且仅当：

$$
\text{compatible}(b_1, b_2) \iff
\begin{cases}
\text{true} & \text{if } \text{mut}(b_1) = \text{false} \land \text{mut}(b_2) = \text{false} \\
\text{disjoint}(b_1, b_2) & \text{otherwise}
\end{cases}
$$

## 6. 安全定理

### 6.1 Reborrow 保持性定理

**定理 6.1** (Reborrow 保持所有权安全)：

如果 $\Gamma \vdash e : \&'\rho_1 \text{ mut } T$ 且 $\Gamma \vdash \&*e : \&'\rho_2 T$，那么：

$$
\forall t \in \rho_2. \text{safe\_access}(\text{target}(e), t, \text{Read})
$$

**证明**：

由类型规则 (T-Reborrow)，我们知道：

1. $\rho_2 \sqsubseteq \rho_1$
2. $e$ 是有效的可变引用

对于任意 $t \in \rho_2$：

- 由于 $\rho_2 \sqsubseteq \rho_1$，有 $t \in \rho_1$
- 由于 $e : \&'\rho_1 \text{ mut } T$，在时间 $t$ 时目标值是有效的
- reborrow 产生只读引用，因此只能进行读取访问
- 根据借用检查规则，reborrow 期间没有其他活跃的可变借用

因此，访问是安全的。

### 6.2 生命周期安全性定理

**定理 6.2** (Reborrow 生命周期安全)：

如果 $(r_{\text{mut}}, r_{\text{shared}}) \in \mathcal{R}(T, \rho_1, \rho_2)$，则：

$$
\text{lifetime}(r_{\text{shared}}) \subseteq \text{lifetime}(r_{\text{mut}})
$$

**证明**：

直接由 Reborrow 关系的定义 5.1 得出，其中条件 2 要求 $\rho_2 \sqsubseteq \rho_1$。

### 6.3 别名安全定理

**定理 6.3** (Reborrow 别名安全)：

如果 $r_{\text{shared}}$ 是通过 reborrow 从 $r_{\text{mut}}$ 创建的，那么：

$$
\forall r'. \text{alias}(r', r_{\text{shared}}) \rightarrow \neg\text{mut}(r')
$$

即所有与 reborrow 结果别名的引用都是不可变的。

**证明**：

由借用检查器保证：

1. 创建 $r_{\text{shared}}$ 时，$r_{\text{mut}}$ 被冻结
2. 在 $r_{\text{shared}}$ 的生命周期内，$r_{\text{mut}}$ 不能被使用
3. 任何其他可变引用都与 $r_{\text{mut}}$ 不相交（由借用规则保证）

因此不存在可变别名。

### 6.4 引用唯一性定理

**定理 6.4** (可变引用唯一性保持)：

在任何程序点，对于任意内存位置 $l$，最多只有一个活跃的可变引用指向 $l$。

**证明**：

通过对程序执行的结构归纳：

- **基础情况**：初始状态没有引用，性质成立
- **归纳步骤**：
  - 创建可变引用：借用检查器确保没有其他活跃引用
  - 创建共享引用：允许，不影响唯一性
  - Reborrow 操作：冻结原可变引用，创建共享引用，保持唯一性

## 7. Rust 代码示例

### 7.1 基本 Reborrow 示例

```rust
fn basic_reborrow() {
    let mut data = vec![1, 2, 3];

    // 创建可变引用
    let r_mut: &mut Vec<i32> = &mut data;

    // Reborrow: 从 &mut T 创建 &T
    let r_shared: &Vec<i32> = &*r_mut;

    // 现在可以使用 r_shared 进行只读访问
    println!("Length: {}", r_shared.len());
    println!("First: {}", r_shared[0]);

    // r_mut 在这里被冻结，不能使用
    // r_mut.push(4);  // 编译错误！

    // r_shared 生命周期结束后，r_mut 重新可用
    drop(r_shared);
    r_mut.push(4);  // OK
}
```

### 7.2 函数参数中的 Reborrow

```rust
fn process_data(data: &mut Vec<i32>) {
    // 隐式 reborrow: &mut T → &T
    print_length(data);  // 等价于 print_length(&*data)

    // 原可变引用仍然可用
    data.push(42);
}

fn print_length(data: &Vec<i32>) {
    println!("Length: {}", data.len());
}
```

### 7.3 嵌套 Reborrow

```rust
fn nested_reborrow() {
    let mut x = 10;
    let mut r1: &mut i32 = &mut x;
    let r2: &&mut i32 = &r1;

    // 嵌套 reborrow
    let r3: &i32 = &**r2;
    println!("Value: {}", r3);
}
```

### 7.4 模式匹配中的 Reborrow

```rust
fn match_reborrow(opt: &mut Option<i32>) {
    match opt {
        Some(ref val) => {
            // val 是 &i32，通过 reborrow 获得
            println!("Value: {}", val);
        }
        None => {}
    }

    // opt 仍然可变
    *opt = Some(42);
}
```

### 7.5 生命周期标注示例

```rust
struct Buffer<'a> {
    data: &'a mut [u8],
}

impl<'a> Buffer<'a> {
    // 返回 reborrow 的共享引用
    fn as_slice(&mut self) -> &[u8] {
        &*self.data  // 显式 reborrow
    }

    // 返回带生命周期的 reborrow
    fn get_range<'b>(&'b mut self, start: usize, end: usize) -> &'b [u8] {
        &self.data[start..end]  // 隐式 reborrow
    }
}
```

### 7.6 泛型中的 Reborrow

```rust
trait Reborrow<'a, T: ?Sized> {
    type Output;
    fn reborrow(&'a mut self) -> Self::Output;
}

impl<'a, T> Reborrow<'a, T> for &'a mut T {
    type Output = &'a T;
    fn reborrow(&'a mut self) -> &'a T {
        &**self
    }
}
```

## 8. 与其他特性的交互

### 8.1 与 Auto Trait 的交互

Reborrow 操作保持 Auto Trait 的一致性：

```rust
fn auto_trait_reborrow<T: Send>(r: &mut T) -> &T {
    r  // 隐式 reborrow，Send trait 保持
}
```

形式化：

$$
\frac{
  T : \text{Trait} \in \text{AutoTraits}
}{
  \&'\rho T : \text{Trait} \rightarrow \&'\rho \text{ mut } T : \text{Trait}
}
$$

### 8.2 与 impl Trait 的交互

```rust
fn get_iter(data: &mut Vec<i32>) -> impl Iterator<Item = &i32> {
    data.iter()  // 隐式 reborrow
}
```

### 8.3 与闭包捕获的交互

```rust
fn closure_reborrow() {
    let mut data = vec![1, 2, 3];

    let closure = || {
        // 闭包隐式 reborrow
        let len = data.len();  // &data
        println!("{}", len);
    };

    closure();
    data.push(4);  // 仍然可变
}
```

### 8.4 与 Pin 的交互

```rust
use std::pin::Pin;

fn pin_reborrow<T>(pinned: Pin<&mut T>) -> Pin<&T> {
    Pin::new(&*pinned)  // 保持 pinning 保证的 reborrow
}
```

形式化：

$$
\frac{
  \text{Pin}(\&'\rho_1 \text{ mut } T) \quad
  \rho_2 \sqsubseteq \rho_1
}{
  \text{Pin}(\&'\rho_2 T)
}
$$

## 9. 实现细节

### 9.1 编译器中的 Reborrow

在 Rust 编译器中，Reborrow 是通过以下方式实现的：

1. **类型检查阶段**：`rustc_typeck` 识别 reborrow 模式
2. **借用检查阶段**：`rustc_borrowck` 验证 reborrow 的安全性
3. **MIR 生成**：reborrow 被转换为适当的借用操作

### 9.2 MIR 表示

```
bb0: {
    _2 = &mut _1;           // 创建可变引用
    _3 = &(*_2);            // reborrow
    _4 = _3;                // 使用 reborrow 结果
}
```

## 10. 总结

Reborrow Trait 是 Rust 借用检查器的核心机制之一，它通过允许可变引用临时降级为共享引用，实现了灵活而安全的内存访问模式。本文提供的形式化语义精确描述了 reborrow 操作的类型规则、操作语义和安全保证，为理解和验证 Rust 程序的正确性提供了理论基础。

关键要点：

1. Reborrow 关系 $\&'\rho_1 \text{ mut } T \rightarrow \&'\rho_2 T$ 要求 $\rho_2 \sqsubseteq \rho_1$
2. 安全定理保证 reborrow 保持所有权安全和别名安全
3. Reborrow 与 Rust 的其他特性（Auto Trait、Pin、闭包等）良好协作
