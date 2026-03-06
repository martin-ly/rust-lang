# Const Generics 的依赖类型语义

## 1. 引言

Const Generics（常量泛型）是 Rust 类型系统的强大扩展，它允许常量值作为类型参数。
这使得类型系统能够表达依赖于编译时常量的类型，如 `[T; N]` 数组类型，其中 `N` 是一个常量整数。

从类型理论角度看，Const Generics 引入了**依赖类型（Dependent Types）**的元素，允许类型依赖于值。

### 1.1 什么是 Const Generics

```rust
// N 是一个 const generic 参数
struct Array<T, const N: usize> {
    data: [T; N],
}

// 使用
let arr: Array<i32, 5> = Array { data: [1, 2, 3, 4, 5] };
```

## 2. 语法定义

### 2.1 扩展的类型语法

$$
\begin{aligned}
\tau \in \text{Type} &::= T \quad \text{(类型变量)} \\
&\quad | \; C\langle\tau_1, \dots, \tau_n\rangle \quad \text{(类型构造器)} \\
&\quad | \; \text{Array}(\tau, n) \quad \text{(数组类型)} \\
&\quad | \; \text{ConstApp}(\tau, c) \quad \text{(常量应用)} \\
&\quad | \; \forall \langle\text{const } X: K\rangle. \tau \quad \text{(常量量化)}
\end{aligned}
$$

### 2.2 常量表达式语法

$$
\begin{aligned}
c \in \text{ConstExp} &::= n \quad \text{(整数常量)} \\
&\quad | \; X \quad \text{(常量变量)} \\
&\quad | \; c_1 + c_2 \quad \text{(加法)} \\
&\quad | \; c_1 - c_2 \quad \text{(减法)} \\
&\quad | \; c_1 * c_2 \quad \text{(乘法)} \\
&\quad | \; c_1 / c_2 \quad \text{(除法)} \\
&\quad | \; f(c_1, \dots, c_n) \quad \text{(const fn 应用)}
\end{aligned}
$$

### 2.3 常量种类 (Const Kind)

$$
\begin{aligned}
K \in \text{ConstKind} &::= \text{usize} \\
&\quad | \; \text{isize} \\
&\quad | \; \text{bool} \\
&\quad | \; \text{char} \\
&\quad | \; \text{Type}
\end{aligned}
$

## 3. 操作语义

### 3.1 常量表达式求值

**常量求值规则** (CE-Eval):

$$
\frac{
  \text{eval}(c) = n \quad
  n \text{ 是编译时常量}
}{
  \vdash c \Downarrow n
}
$$

**具体求值规则**：

$$
\frac{
  \vdash c_1 \Downarrow n_1 \quad
  \vdash c_2 \Downarrow n_2
}{
  \vdash c_1 + c_2 \Downarrow n_1 + n_2
}
\quad\text{(CE-Add)}
$$

$$
\frac{
  \vdash c_1 \Downarrow n_1 \quad
  \vdash c_2 \Downarrow n_2 \quad
  n_2 \neq 0
}{
  \vdash c_1 / c_2 \Downarrow n_1 / n_2
}
\quad\text{(CE-Div)}
$$

### 3.2 数组构造语义

**数组构造** (E-Array-New):

$$
\frac{
  \vdash n : \text{usize} \quad
  \forall i \in 0..n. \langle e_i, \sigma \rangle \Downarrow \langle v_i, \sigma_i \rangle
}{
  \langle [e_0, \dots, e_{n-1}], \sigma \rangle \Downarrow
  \langle \text{Array}_n(v_0, \dots, v_{n-1}), \sigma_n \rangle
}
$$

### 3.3 数组访问语义

**数组索引** (E-Array-Index):

$$
\frac{
  \langle e, \sigma \rangle \Downarrow \langle \text{Array}_n(v_0, \dots, v_{n-1}), \sigma' \rangle \quad
  \langle i, \sigma' \rangle \Downarrow \langle k, \sigma'' \rangle \quad
  0 \leq k < n
}{
  \langle e[i], \sigma \rangle \Downarrow \langle v_k, \sigma'' \rangle
}
$$

**边界检查失败** (E-Array-Index-Bound):

$$
\frac{
  \langle e, \sigma \rangle \Downarrow \langle \text{Array}_n(\dots), \sigma' \rangle \quad
  \langle i, \sigma' \rangle \Downarrow \langle k, \sigma'' \rangle \quad
  k \geq n \lor k < 0
}{
  \langle e[i], \sigma \rangle \Downarrow \langle \text{panic}, \sigma'' \rangle
}
$$

## 4. 类型规则

### 4.1 常量泛型声明

**常量泛型参数** (T-Const-Param):

$$
\frac{
  \Gamma, X : K \vdash \tau : \text{Type}
}{
  \Gamma \vdash \forall \langle\text{const } X : K\rangle. \tau : \text{Type}
}
$$

### 4.2 数组类型规则

**数组类型形成** (T-Array-Form):

$$
\frac{
  \Gamma \vdash \tau : \text{Type} \quad
  \Gamma \vdash n : \text{usize} \quad
  \text{const}(n)
}{
  \Gamma \vdash [\tau; n] : \text{Type}
}
$$

**数组构造** (T-Array-Cons):

$$
\frac{
  \Gamma \vdash e_i : \tau \quad
  \forall i \in 0..n
}{
  \Gamma \vdash [e_0, \dots, e_{n-1}] : [\tau; n]
}
$$

**重复数组构造** (T-Array-Repeat):

$$
\frac{
  \Gamma \vdash e : \tau \quad
  \Gamma \vdash n : \text{usize} \quad
  \text{const}(n)
}{
  \Gamma \vdash [e; n] : [\tau; n]
}
$$

### 4.3 类型应用规则

**常量类型应用** (T-Const-App):

$$
\frac{
  \Gamma \vdash \tau : \forall \langle\text{const } X : K\rangle. \tau' \quad
  \Gamma \vdash c : K \quad
  \text{const}(c)
}{
  \Gamma \vdash \tau\langle c \rangle : [c/X]\tau'
}
$$

### 4.4 类型等价规则

**结构等价** (TE-Struct):

$$
\frac{
  \Gamma \vdash \tau_1 \equiv \tau_2 \quad
  \Gamma \vdash c_1 \equiv c_2 : K
}{
  \Gamma \vdash \text{Array}(\tau_1, c_1) \equiv \text{Array}(\tau_2, c_2)
}
$$

**常量表达式等价** (TE-Const):

$$
\frac{
  \text{eval}(c_1) = \text{eval}(c_2)
}{
  \Gamma \vdash c_1 \equiv c_2 : K
}
$$

## 5. 形式化定义

### 5.1 常量求值函数

**定义 5.1** (常量求值)：

常量求值函数 $\text{eval} : \text{ConstExp} \rightarrow \text{Value}$ 定义为：

$$
\text{eval}(c) = \begin{cases}
n & \text{if } c = n \\
\text{eval}(c_1) + \text{eval}(c_2) & \text{if } c = c_1 + c_2 \\
\text{eval}(c_1) - \text{eval}(c_2) & \text{if } c = c_1 - c_2 \\
\text{eval}(c_1) \times \text{eval}(c_2) & \text{if } c = c_1 * c_2 \\
\text{eval}(c_1) \div \text{eval}(c_2) & \text{if } c = c_1 / c_2, \text{eval}(c_2) \neq 0 \\
\text{const\_fn}(\text{eval}(c_1), \dots, \text{eval}(c_n)) & \text{if } c = f(c_1, \dots, c_n)
\end{cases}
$$

### 5.2 类型等价

**定义 5.2** (类型等价)：

两个类型 $\tau_1$ 和 $\tau_2$ 等价，记作 $\tau_1 \equiv \tau_2$，当且仅当：

$$
\tau_1 \equiv \tau_2 \iff
\begin{cases}
\text{true} & \text{if } \tau_1 = \tau_2 = T \\
\tau_1' \equiv \tau_2' \land c_1 \equiv c_2 & \text{if } \tau_1 = \text{Array}(\tau_1', c_1), \tau_2 = \text{Array}(\tau_2', c_2) \\
\tau_1'[c_1/X] \equiv \tau_2'[c_2/X] & \text{if } \tau_1 = (\forall X. \tau_1')\langle c_1 \rangle, \tau_2 = (\forall X. \tau_2')\langle c_2 \rangle \\
\text{false} & \text{otherwise}
\end{cases}
$$

### 5.3 常量表达式等价

**定义 5.3** (常量表达式等价)：

两个常量表达式 $c_1$ 和 $c_2$ 等价，记作 $c_1 \equiv c_2$，当且仅当：

$$
c_1 \equiv c_2 \iff \text{eval}(c_1) = \text{eval}(c_2)
$$

### 5.4 常量上下文

**定义 5.4** (常量上下文)：

常量上下文 $\Theta$ 是一个映射，记录常量变量的值：

$$
\Theta : \text{ConstVar} \rightarrow \text{Value}
$$

在常量上下文中，$\Theta \vdash c \equiv c'$ 表示在 $\Theta$ 下 $c$ 和 $c'$ 等价。

## 6. 安全定理

### 6.1 类型安全定理

**定理 6.1** (Const Generics 类型安全)：

如果 $\Gamma \vdash e : \tau$ 且 $\langle e, \sigma \rangle \Downarrow \langle v, \sigma' \rangle$，则：

$$
\exists \tau'. \Gamma \vdash v : \tau' \land \tau' <: \tau
$$

**证明**：通过对推导结构的归纳。

**基本情况**：
- 常量表达式：直接由求值规则得出

**归纳步骤**：
- 数组构造：由 T-Array-Cons 和归纳假设，每个元素类型正确
- 数组索引：由 T-Array-Index 和边界检查保证安全

### 6.2 数组边界安全

**定理 6.2** (数组访问边界安全)：

如果 $\Gamma \vdash e : [\tau; n]$ 且 $\Gamma \vdash i : \text{usize}$，则运行时求值 $e[i]$ 不会越界，当：

$$
\text{eval}(i) < n
$$

如果条件不满足，程序将安全地 panic 而不是造成未定义行为。

**证明**：

由 E-Array-Index 和 E-Array-Index-Bound 规则：
- 如果 $0 \leq k < n$，正常返回 $v_k$
- 否则触发 panic

这保证了不会出现缓冲区溢出。

### 6.3 常量求值终止性

**定理 6.3** (常量求值终止)：

对于任意常量表达式 $c$，求值过程 $\text{eval}(c)$ 必然终止。

**证明**：

通过对 $c$ 的结构归纳：
- 基础值（整数）：立即返回
- 复合表达式：递归求值子表达式，每个子表达式根据归纳假设终止
- Const fn 调用：由 const fn 的求值限制（无循环、无递归）保证终止

### 6.4 类型等价一致性

**定理 6.4** (类型等价的一致性)：

类型等价关系 $\equiv$ 是等价关系：

1. **自反性**：$\forall \tau. \tau \equiv \tau$
2. **对称性**：$\forall \tau_1, \tau_2. \tau_1 \equiv \tau_2 \rightarrow \tau_2 \equiv \tau_1$
3. **传递性**：$\forall \tau_1, \tau_2, \tau_3. \tau_1 \equiv \tau_2 \land \tau_2 \equiv \tau_3 \rightarrow \tau_1 \equiv \tau_3$

**证明**：

直接由定义 5.2 得出，因为等价基于结构递归和常量求值的等式关系。

## 7. Rust 代码示例

### 7.1 基本 Const Generic 类型

```rust
// 定义带有 const generic 的结构体
struct PointND<T, const N: usize> {
    coords: [T; N],
}

impl<T: Copy + Default, const N: usize> PointND<T, N> {
    fn new() -> Self {
        Self {
            coords: [T::default(); N],
        }
    }

    fn get(&self, index: usize) -> Option<&T> {
        self.coords.get(index)
    }

    fn dimension(&self) -> usize {
        N  // 常量泛型参数可以直接使用
    }
}

fn basic_usage() {
    let p2: PointND<f64, 2> = PointND::new();
    let p3: PointND<f64, 3> = PointND::new();

    println!("2D point dimension: {}", p2.dimension());
    println!("3D point dimension: {}", p3.dimension());
}
```

### 7.2 数组类型操作

```rust
fn array_operations<const N: usize>(arr: [i32; N]) -> i32 {
    // N 是编译时常量
    let mut sum = 0;
    for i in 0..N {
        sum += arr[i];
    }
    sum
}

fn array_type_equivalence() {
    // 以下类型等价
    let a: [i32; 3] = [1, 2, 3];
    let b: [i32; 1 + 2] = [1, 2, 3];
    let c: [i32; 6 / 2] = [1, 2, 3];

    // 这些数组类型在编译时被认为是等价的
    fn process<const N: usize>(arr: [i32; N]) {}

    process(a);
    process(b);
    process(c);
}
```

### 7.3 类型级别的常量计算

```rust
// 在类型级别进行计算
struct Matrix<T, const ROWS: usize, const COLS: usize> {
    data: [[T; COLS]; ROWS],
}

impl<T: Copy + Default, const R: usize, const C: usize> Matrix<T, R, C> {
    fn new() -> Self {
        Self {
            data: [[T::default(); C]; R],
        }
    }

    fn transpose(self) -> Matrix<T, C, R> {
        let mut result = Matrix::new();
        for i in 0..R {
            for j in 0..C {
                result.data[j][i] = self.data[i][j];
            }
        }
        result
    }

    fn flatten(self) -> [T; R * C] {
        let mut result = [T::default(); R * C];
        let mut idx = 0;
        for i in 0..R {
            for j in 0..C {
                result[idx] = self.data[i][j];
                idx += 1;
            }
        }
        result
    }
}
```

### 7.4 Const Generic 约束

```rust
// 基于 const generic 的 trait 实现
trait SizedArray {
    const SIZE: usize;
}

impl<T, const N: usize> SizedArray for [T; N] {
    const SIZE: usize = N;
}

// 使用 where 约束 const generic
fn process_fixed_size<T, const N: usize>(arr: [T; N]) -> [T; N]
where
    T: Copy,
    [T; N]: SizedArray,
{
    arr
}
```

### 7.5 Const 表达式求值

```rust
// const fn 与 const generic 结合
const fn pow2(n: usize) -> usize {
    1 << n
}

const fn factorial(n: usize) -> usize {
    let mut result = 1;
    let mut i = 1;
    while i <= n {
        result *= i;
        i += 1;
    }
    result
}

// 在类型中使用 const 表达式
struct Buffer<const SIZE: usize>;

impl Buffer<1024> {
    fn name() -> &'static str {
        "1KB buffer"
    }
}

impl Buffer<{ 1024 * 1024 }> {
    fn name() -> &'static str {
        "1MB buffer"
    }
}

fn const_eval_example() {
    type PowerOfTwo<const N: usize> = Buffer<{ pow2(N) }>;

    let _: PowerOfTwo<10>;  // 大小为 1024 的 buffer
}
```

### 7.6 数组长度泛型

```rust
// 处理不同长度的数组
fn concatenate<T: Copy, const N: usize, const M: usize>(
    a: [T; N],
    b: [T; M]
) -> [T; N + M] {
    let mut result = unsafe { std::mem::zeroed() };

    for i in 0..N {
        result[i] = a[i];
    }
    for i in 0..M {
        result[N + i] = b[i];
    }

    result
}

fn split<T: Copy, const N: usize, const M: usize>(
    arr: [T; N + M]
) -> ([T; N], [T; M]) {
    let mut first = unsafe { std::mem::zeroed() };
    let mut second = unsafe { std::mem::zeroed() };

    for i in 0..N {
        first[i] = arr[i];
    }
    for i in 0..M {
        second[i] = arr[N + i];
    }

    (first, second)
}
```

### 7.7 泛型特化

```rust
// 基于 const generic 的特化
trait Process {
    fn process(&self);
}

impl<T> Process for [T; 0] {
    fn process(&self) {
        println!("Empty array");
    }
}

impl<T: std::fmt::Display> Process for [T; 1] {
    fn process(&self) {
        println!("Single element: {}", self[0]);
    }
}

impl<T: std::fmt::Display> Process for [T; 2] {
    fn process(&self) {
        println!("Two elements: {}, {}", self[0], self[1]);
    }
}

// 通用实现
impl<T: std::fmt::Display, const N: usize> Process for [T; N] {
    default fn process(&self) {
        println!("Array with {} elements", N);
    }
}
```

## 8. 依赖类型限制

### 8.1 Rust 的限制

Rust 的 Const Generics 是受限的依赖类型：

```rust
// 允许的：常量整数作为类型参数
struct Array<T, const N: usize>([T; N]);

// 不允许的：依赖类型的完全表达
// struct Dependent<T, const P: fn(T) -> bool>(T);  // 不行

// 允许的：const bool
struct Flagged<T, const FLAG: bool> {
    data: T,
    // 不能在类型级别根据 FLAG 改变结构
}
```

### 8.2 与完全依赖类型的比较

| 特性 | Rust Const Generics | 完全依赖类型 (如 Idris) |
|------|---------------------|------------------------|
| 值依赖 | 有限的 | 完全的 |
| 类型由值决定 | 部分支持 | 完全支持 |
| 证明携带 | 无 | 有 |
| 编译时求值 | 是 | 是 |

## 9. 与其他特性的交互

### 9.1 与生命周期

```rust
struct BorrowedArray<'a, T, const N: usize> {
    data: &'a [T; N],
}

impl<'a, T, const N: usize> BorrowedArray<'a, T, N> {
    fn get(&self, idx: usize) -> Option<&'a T> {
        self.data.get(idx)
    }
}
```

### 9.2 与 Trait Bound

```rust
use std::ops::Add;

fn sum_array<T, const N: usize>(arr: [T; N]) -> T
where
    T: Add<Output = T> + Default + Copy,
{
    let mut sum = T::default();
    for i in 0..N {
        sum = sum + arr[i];
    }
    sum
}
```

### 9.3 与 impl Trait

```rust
fn create_array<T: Default + Copy, const N: usize>() -> impl ExactSizeIterator<Item = T> {
    [T::default(); N].into_iter()
}
```

## 10. 实现细节

### 10.1 编译时求值

Rust 编译器在以下阶段处理 const generics：

1. **解析**：识别 const generic 参数
2. **类型检查**：验证 const 表达式类型
3. **求值**：在编译时求值 const 表达式
4. **单态化**：为每个不同的 const 值生成具体代码

### 10.2 单态化爆炸问题

```rust
// 这可能导致代码膨胀
fn foo<const N: usize>() {}

// 调用
foo::<1>();
foo::<2>();
foo::<3>();
// ... 每个不同的 N 生成一个实例
```

## 11. 总结

Const Generics 为 Rust 引入了依赖类型的元素，允许类型依赖于编译时常量。关键结论：

1. **类型等价**：`Array<T, 3> ≡ Array<T, 1+2> ≡ Array<T, 6/2>`
2. **安全保证**：数组访问通过 const generic 保证边界安全
3. **受限依赖**：Rust 的依赖类型比完全依赖类型系统更受限但更高效
4. **编译时求值**：const 表达式在编译时求值，无运行时开销

Const Generics 使得 Rust 能够表达更精确的类型约束，同时保持零成本抽象。
