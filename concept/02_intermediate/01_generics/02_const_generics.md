> **内容分级**: [进阶级]

# Const Generics（常量泛型）：值作为类型参数

> **EN**: Const Generics — Values as Type Parameters
> **Summary**: Const generics allow types, functions, and impls to be parameterized by compile-time constant values (e.g. `<const N: usize>`), making fixed-size arrays `[T; N]` and similar value-indexed abstractions expressible without macros or type-level encodings. This page is the canonical reference for their motivation, syntax, the stable boundary of `min_const_generics` versus the nightly `generic_const_exprs`/`adt_const_params` in Rust 1.97.0, monomorphization semantics, and the decision boundary against macros and type-level naturals.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L2-L3
> **受众**: [进阶]
> **权威来源**: 本文件为 `concept/` 权威页。const generics 的**语法、stable 边界与判定规则**统一收敛于本页；[泛型系统总览](01_generics.md) 保留泛型参数空间的整体介绍，[类型级编程](03_type_level_programming.md) 保留 Peano/typenum 等编码技术，均通过链接指向本页。
>
> **层次定位**: L2 进阶概念 / 泛型子域 — 类型参数（type parameter）与值参数（value parameter）的交叉
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×App — 应用常量参数消除数组大小的抽象泄漏
> **前置概念**: [Generics](01_generics.md) · [Traits](../00_traits/01_traits.md) · [Type System](../../01_foundation/02_type_system/01_type_system.md)
> **后置概念**: [Type-Level Programming](03_type_level_programming.md) · [const Trait Impl（预览）](../../07_future/03_preview_features/06_const_trait_impl_preview.md) · [Const Eval](../../01_foundation/04_control_flow/03_statements_and_expressions.md)

---

> **主要来源**: [Rust Reference — Generic Parameters](https://doc.rust-lang.org/reference/items/generics.html) ·
> [RFC 2000 — Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html) ·
> [rust-lang blog — Const Generics MVP Hits Beta (1.51)](https://blog.rust-lang.org/2021/02/26/const-generics-mvp-beta.html) ·
> [Tracking Issue #74878 — min_const_generics](https://github.com/rust-lang/rust/issues/74878) ·
> [Tracking Issue #76560 — generic_const_exprs](https://github.com/rust-lang/rust/issues/76560)

## 📑 目录

- [Const Generics（常量泛型）：值作为类型参数](#const-generics常量泛型值作为类型参数)
  - [📑 目录](#-目录)
  - [一、动机：`[T; N]` 的抽象困境](#一动机t-n-的抽象困境)
  - [二、语法与允许的标量类型边界](#二语法与允许的标量类型边界)
  - [三、stable 边界：min\_const\_generics vs generic\_const\_exprs](#三stable-边界min_const_generics-vs-generic_const_exprs)
  - [四、关联常量（Associated Const）与 const 参数的关系](#四关联常量associated-const与-const-参数的关系)
  - [五、单态化与编译期求值：推理链](#五单态化与编译期求值推理链)
  - [六、实质示例](#六实质示例)
    - [6.1 固定大小环形缓冲区](#61-固定大小环形缓冲区)
    - [6.2 维度泛型矩阵](#62-维度泛型矩阵)
  - [七、反例：stable 边界上的编译期拒绝](#七反例stable-边界上的编译期拒绝)
    - [反例 1：const 参数参与运算（generic\_const\_exprs）](#反例-1const-参数参与运算generic_const_exprs)
    - [反例 2：在泛型上下文中用 const 参数构造依赖类型](#反例-2在泛型上下文中用-const-参数构造依赖类型)
    - [反例 3：非法的 const 参数类型](#反例-3非法的-const-参数类型)
  - [八、判定表：const generics vs 宏 vs 类型级自然数](#八判定表const-generics-vs-宏-vs-类型级自然数)
  - [九、与既有内容的关系声明](#九与既有内容的关系声明)
  - [相关概念](#相关概念)
  - [十、来源与延伸阅读](#十来源与延伸阅读)

---

## 一、动机：`[T; N]` 的抽象困境

Rust 的数组（array）类型 `[T; N]` 把**长度编码在类型里**：`[u8; 4]` 与 `[u8; 8]` 是不同的类型。这带来零成本（Zero-Cost Abstraction）的栈上定长存储，但在 const generics 之前（Rust < 1.51），泛型代码无法对"任意长度 N"抽象：

```rust
// 历史困境（1.51 之前）：只能手写 impl，或退化为 slice
trait Reverse { fn reverse(&mut self); }

impl Reverse for [u8; 4] { fn reverse(&mut self) { self.reverse(); } } // 同名方法冲突…
impl Reverse for [u8; 8] { fn reverse(&mut self) { todo!() } }
// …想覆盖到 32？宏展开或 32 份手写 impl —— 抽象泄漏
```

const generics 把"值"提升为泛型参数，一次定义覆盖所有长度：

```rust
use std::fmt::Debug;

/// 对任意长度 N 一次实现
fn print_array<T: Debug, const N: usize>(a: &[T; N]) {
    println!("[{N} elements] {a:?}");
}

fn motivation_demo() {
    print_array(&[1, 2, 3]);          // N = 3，编译期推断
    print_array(&[0u8; 64]);          // N = 64
    // 类型层面：[i32; 3] 与 [i32; 4] 仍是不同类型 ⟹ 无运行时开销、无长度检查
}
```

核心收益：

1. **数组抽象**：`[T; N]` 泛型化，告别宏批量生成 impl（std 自身曾用宏为 0..=32 长度实现 `Debug`/`PartialEq` 等 trait）；
2. **维度即类型**：矩阵、SIMD 通道数、页大小等"值级不变量"进入类型系统，编译期拒绝维度不匹配；
3. **零成本**：const 参数在单态化（Monomorphization）时被替换为字面常量，生成代码与手写定长版本逐指令相同。

## 二、语法与允许的标量类型边界

**声明位置**：const 参数以 `const NAME: TYPE` 形式出现在泛型参数列表中，与类型参数、生命周期（Lifetimes）参数并列：

```rust
struct FixedVec<T, const N: usize> { data: [T; N] }

fn fill<T: Copy, const N: usize>(v: T) -> [T; N] { [v; N] }

impl<T, const N: usize> FixedVec<T, N> {
    const LEN: usize = N;            // const 参数可参与常量表达式
}
```

**使用位置（stable 允许的形态）**：

| 位置 | 示例 | 说明 |
|:---|:---|:---|
| 数组长度 | `[T; N]` | 最主要的消费点 |
| 常量表达式中的独立参数 | `N`、`N * 8`（见 §3 边界） | 传给其他 const 上下文 |
| 关联常量初始化 | `const LEN: usize = N;` | 见 §4 |
| where 子句相等约束 | `where [T; N]: Sized` | 用于约束推导，见 §7 反例 2 |
| 默认值 | `struct B<T, const N: usize = 16>` | 与类型参数默认值规则一致 |

**允许的标量类型（Rust 1.97.0 stable）**——这是 RFC 2000 划定的硬边界：

```rust
fn integer_types<const A: u8, const B: i32, const C: usize, const D: isize>() {}
fn bool_and_char<const FLAG: bool, const CH: char>() {}
// fn no_floats<const X: f64>() {}       // ❌ 编译错误：f64 不允许作为 const 参数类型
// fn no_strs<const S: &str>() {}        // ❌ 编译错误：&str 不允许
// fn no_structs<const S: MyStruct>() {} // ❌ 需每日构建版 adt_const_params
```

允许：`u8 u16 u32 u64 u128 usize` / `i8 i16 i32 i64 i128 isize` / `bool` / `char`，共 14 种整数 + `bool` + `char`。

禁止（stable）：浮点（无结构相等性（structural equality），`0.0 == -0.0` 等问题）、`&str`、引用、以及任何 ADT（struct/enum）。ADT 作为 const 参数由 `adt_const_params`（特性门，截至 1.97.0 仍未稳定）解锁，要求类型派生 `PartialEq + Eq + StructuralPartialEq + StructuralEq`。

**排序规则**：const 参数可以在类型参数之后声明；调用时按位置或推断提供：

```rust
fn ordering_demo() {
    let a = fill::<i32, 4>(7);   // 显式 turbofish：类型参数在前，const 参数在后
    let b: [i32; 3] = fill(9);   // 全部由上下文推断
    assert_eq!(a.len(), 4);
    assert_eq!(b, [9, 9, 9]);
}
```

## 三、stable 边界：min_const_generics vs generic_const_exprs

这是本页最重要的实践判据。const generics 分两层落地：

| 特性 | 状态（1.97.0） | 能力 |
|:---|:---|:---|
| `min_const_generics` | ✅ stable（1.51，2021-03） | const 参数**独立**出现在数组长度等位置：`[T; N]`、`[0u8; N]` |
| `generic_const_exprs` | ⚠️ 仅每日构建版 | const 参数参与**运算**的常量表达式：`[T; N + 1]`、`[T; N * M]`、where `[(); N - 1]:` |
| `adt_const_params` | ⚠️ 仅每日构建版 | struct/enum/`&'static str` 等作为 const 参数类型 |

**min_const_generics 的精确边界**（stable 可做 / 不可做）：

```rust
// ✅ stable：const 参数"原样"使用
fn ok_identity<T, const N: usize>(a: [T; N]) -> [T; N] { a }

// ✅ stable：常量算术出现在"非泛型依赖"位置
fn ok_literal() -> [u8; 2 + 3] { [0; 5] } // 2+3 不含泛型参数，普通 const eval

// ❌ stable 拒绝：const 参数参与运算（generic_const_exprs 领域）
// fn grow<T, const N: usize>(a: [T; N]) -> [T; N + 1] { todo!() }
//   error: generic parameters may not be used in const operations
// fn pair<T, const N: usize, const M: usize>() -> [T; N * M] { todo!() }
//   同上
```

边界规则一句话：**只要常量表达式中出现了 const 泛型参数的运算（而非原样引用），就需要每日构建版的 `generic_const_exprs`**。原因是 `[T; N + 1]` 这类类型在求值前无法判定相等性（`N + 1 == M + 1 ⟺ N == M`？对抽象 N、M 不可判定），会冲击类型检查的可判定性（Decidability）——这正是 RFC 2000 把 MVP 限制为"独立参数"的理论动机。

每日构建版上的对应形态（仅供认知，1.97.0 stable 不可用）：

```rust
// 需启用实验特性门 generic_const_exprs —— 仅每日构建版
// fn grow<T: Copy + Default, const N: usize>(a: [T; N]) -> [T; N + 1]
// where
//     [(); N + 1]:,   // 必需的 "where 证明"：承诺 N+1 可求值
// {
//     let mut out = [T::default(); N + 1];
//     out[..N].copy_from_slice(&a);
//     out
// }
```

`where [(); N + 1]:` 这类约束的读法："`[(); N + 1]` 是良构类型" ⟺ "`N + 1` 可作为数组长度求值"。它把"该常量表达式对所有实例化都可求值"变成显式的 trait 风格证明义务。

## 四、关联常量（Associated Const）与 const 参数的关系

二者正交互补：**const 参数从外部注入值，关联常量从实现内部暴露值**。

```rust
trait Bytes {
    const SIZE: usize;                    // 关联常量：由实现者定义
    fn as_bytes(&self) -> Vec<u8>;        // 长度运行时可知；Self::SIZE 直接用作
}                                         // 数组长度需每日构建版（见下方边界）

// 组合用法：关联常量作为 const 参数的"实参"——stable 合法
fn zero_buf<T: Bytes, const N: usize>() -> [u8; N] { [0; N] }

struct Header;
impl Bytes for Header {
    const SIZE: usize = 24;
    fn as_bytes(&self) -> Vec<u8> { vec![0u8; Self::SIZE] }
    // impl 内部 Self::SIZE 是具体值 24，[0u8; 24] 可直接写；
    // 受限的是 trait 签名中写 fn as_bytes(&self) -> [u8; Self::SIZE]
}

fn assoc_const_as_argument() {
    let b = zero_buf::<Header, 24>();
    assert_eq!(b.len(), Header::SIZE); // 关联常量 ⟹ 调用点的 const 实参
}
```

> **边界警告（1.97.0 stable）**：在 trait 签名或泛型函数中把关联常量投影用作数组长度——
> `fn as_bytes(&self) -> [u8; Self::SIZE]`——会被拒绝：
> `error: generic parameters may not be used in const operations (cannot perform const operation using Self)`，
> 需启用实验特性门 `generic_const_exprs`。stable 上让关联常量"影响类型"的唯一路径是
> 在调用点把它作为 const 实参显式传入（如上 `zero_buf::<Header, 24>`）。

关系总结：

| | const 泛型参数 `<const N: usize>` | 关联常量 `const N: usize;` |
|:---|:---|:---|
| 值的来源 | 调用点提供 | impl 内部定义 |
| 参与类型相等性 | 是（`Foo<3> ≠ Foo<4>`） | 否（同一 trait 的不同 impl 是不同类型） |
| 典型用途 | 数组长度、维度 | 每实现固有常量（`u32::BITS`、页大小） |
| 组合模式 | `zero_buf::<Header, 24>()`（调用点传具体值） | `impl Bytes for T { const SIZE = … }` |

## 五、单态化与编译期求值：推理链

const 参数不是"类型"，是"**编译期已知的值**"，其语义由三条规则完全刻画：

```text
规则 1（类型同一性）: 两个泛型实例类型相同 ⟺ 所有参数（类型+const）逐一相等
                    Foo<i32, 3> 与 Foo<i32, 4> 是完全不同的类型
规则 2（单态化）:     每个 (类型参数, const 参数) 的具体组合生成一份独立机器码
                    ⟹ 二进制体积随实例数增长（与类型参数单态化同理）
规则 3（求值时机）:   const 实参必须是"具体常量"（字面量、const 项、或
                    外层 const 参数的原样传递）；含外层 const 参数的运算
                    在单态化后才能求值 ⟹ stable 直接拒绝（§3）
```

求值推理链示例：

```text
调用 fill::<i32, 4>(7)
  ⟹ 单态化点收集实参 (T=i32, N=4)
  ⟹ 将函数体中 N 替换为 4（const 参数替换）
  ⟹ [7; 4] 是普通数组表达式，codegen 为 16 字节栈初始化
  ⟹ 类型签名实例化为 fn(i32) -> [i32; 4]
结论: 生成的代码与手写 fn fill4(v: i32) -> [i32; 4] { [v; 4] } 等价
```

这也意味着**递归类型定义必须小心**：`struct Cons<T, const N: usize>(T, Cons<T, { N - 1 }>)` 无法终止（且 `N - 1` 本身需要 generic_const_exprs）——类型级递归的终止性没有保证，这是类型级自然数方案（§8）仍需存在的原因之一。

## 六、实质示例

「实质示例」部分包含固定大小环形缓冲区 与 维度泛型矩阵 两条主线，本节依次说明。

### 6.1 固定大小环形缓冲区

```rust
/// 栈上定长环形缓冲区：容量编码在类型里，零堆分配
struct RingBuffer<T: Copy + Default, const N: usize> {
    data: [T; N],
    head: usize,
    len: usize,
}

impl<T: Copy + Default, const N: usize> RingBuffer<T, N> {
    const CAPACITY: usize = N;

    fn new() -> Self {
        Self { data: [T::default(); N], head: 0, len: 0 }
    }

    /// 满时覆盖最旧元素并返回它
    fn push(&mut self, v: T) -> Option<T> {
        let idx = (self.head + self.len) % N;
        if self.len == N {
            let old = self.data[self.head];
            self.data[self.head] = v;
            self.head = (self.head + 1) % N;
            return Some(old);
        }
        self.data[idx] = v;
        self.len += 1;
        None
    }

    fn pop(&mut self) -> Option<T> {
        if self.len == 0 { return None; }
        let v = self.data[self.head];
        self.head = (self.head + 1) % N;
        self.len -= 1;
        Some(v)
    }

    fn len(&self) -> usize { self.len }
}

fn ring_buffer_demo() {
    let mut rb = RingBuffer::<u32, 3>::new();
    assert_eq!(RingBuffer::<u32, 3>::CAPACITY, 3);
    assert_eq!(rb.push(1), None);
    assert_eq!(rb.push(2), None);
    assert_eq!(rb.push(3), None);
    assert_eq!(rb.push(4), Some(1));  // 容量 3 编译期固定，溢出语义明确
    assert_eq!(rb.len(), 3);
    assert_eq!(rb.pop(), Some(2));
    // let other = RingBuffer::<u32, 4>::new();
    // rb = other;                    // 编译错误：RingBuffer<u32, 3> ≠ RingBuffer<u32, 4>
}
```

### 6.2 维度泛型矩阵

维度进入类型 ⟹ 形状错误在编译期暴露，乘法只写一次覆盖所有形状：

```rust
use std::ops::Mul;

/// R×C 矩阵，行主序
struct Matrix<const R: usize, const C: usize> {
    data: [[f64; C]; R],
}

impl<const R: usize, const C: usize> Matrix<R, C> {
    fn zeros() -> Self { Self { data: [[0.0; C]; R] } }
}

/// 方阵专属方法：只对 Matrix<N, N> 存在
impl<const N: usize> Matrix<N, N> {
    fn identity() -> Self {
        let mut m = Self::zeros();
        for (i, row) in m.data.iter_mut().enumerate() {
            row[i] = 1.0;
        }
        m
    }
}

/// 乘法：(R×C) · (C×K) = (R×K)
/// 维度匹配由类型系统强制——C 在两个参数中必须相同
impl<const R: usize, const C: usize, const K: usize> Mul<Matrix<C, K>> for Matrix<R, C> {
    type Output = Matrix<R, K>;

    fn mul(self, rhs: Matrix<C, K>) -> Matrix<R, K> {
        let mut out = Matrix::<R, K>::zeros();
        for r in 0..R {
            for k in 0..K {
                for c in 0..C {
                    out.data[r][k] += self.data[r][c] * rhs.data[c][k];
                }
            }
        }
        out
    }
}

fn matrix_demo() {
    let a = Matrix::<2, 3> { data: [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]] };
    let i3 = Matrix::<3, 3>::identity();
    let r = a * i3;                       // Matrix<2, 3> —— 形状自动推导
    assert!((r.data[1][2] - 6.0).abs() < 1e-12);
    // let bad = r * Matrix::<2, 2>::identity(); // 编译错误：3 ≠ 2，维度不匹配
    let id4 = Matrix::<4, 4>::identity();       // 方阵方法对 4×4 可用
    assert!((id4.data[3][3] - 1.0).abs() < 1e-12);
}
```

两个示例共同展示：**长度/维度是类型的组成部分**（规则 1），方法是**按形状条件化存在**的（`identity` 仅方阵），全部检查发生在编译期，生成代码与手写定长版本等价（规则 2、3）。

## 七、反例：stable 边界上的编译期拒绝

本节将「反例：stable 边界上的编译期拒绝」分解为若干主题：反例 1：const 参数参与运算（generic_const_exp…、反例 2：在泛型上下文中用 const 参数构造依赖类型与反例 3：非法的 const 参数类型。

### 反例 1：const 参数参与运算（generic_const_exprs）

```rust
// ❌ stable 编译错误
// fn concat<T: Copy, const N: usize, const M: usize>(a: [T; N], b: [T; M]) -> [T; N + M] {
//     let mut out = [a[0]; N + M];   // error: generic parameters may not be used
//     out[..N].copy_from_slice(&a);  //        in const operations
//     out[N..].copy_from_slice(&b);
//     out
// }
```

**stable 绕行方案**：把运算结果作为额外 const 参数传入，由调用点做算术：

```rust
/// stable 版 concat：结果长度作为独立参数，调用点保证 K == N + M
fn concat_stable<T: Copy, const N: usize, const M: usize, const K: usize>(
    a: [T; N],
    b: [T; M],
) -> [T; K] {
    assert_eq!(N + M, K, "K must equal N + M"); // 运行时断言（debug 期可捕获）
    let mut out = [a[0]; K];
    out[..N].copy_from_slice(&a);
    out[N..].copy_from_slice(&b);
    out
}

fn concat_demo() {
    let c = concat_stable([1, 2], [3, 4, 5]);   // N=2, M=3, K=5 全推断
    assert_eq!(c, [1, 2, 3, 4, 5]);
}
```

代价：相等性 `K == N + M` 从编译期降级为运行期断言。要恢复编译期保证，可配合 §8 的类型级自然数，或等待 `generic_const_exprs` 稳定。

### 反例 2：在泛型上下文中用 const 参数构造依赖类型

```rust
// ❌ stable 编译错误：where 子句中同样禁止参数运算
// trait Splitable<const N: usize> {
//     fn split(self) -> ([u8; N / 2], [u8; N - N / 2]);  // N/2 是参数运算
// }

// ✅ stable 合法形态：参数只"原样"传递
trait ArrayExt<T, const N: usize> {
    fn first_chunk(&self) -> &[T];
}

impl<T, const N: usize> ArrayExt<T, N> for [T; N] {
    fn first_chunk(&self) -> &[T] { &self[..N.min(self.len())] }
}
```

### 反例 3：非法的 const 参数类型

```rust
// ❌ 编译错误：float 不是允许的 const 参数类型
// struct Scaled<T, const SCALE: f64>(T);
//   error: `f64` is forbidden as the type of a const generic parameter

// ✅ 绕行：用有理数编码（分子/分母两个整数参数）
struct Scaled<T, const NUM: u64, const DEN: u64>(T);

fn scaled_demo() {
    let half = Scaled::<i32, 1, 2>(10); // 表示 10 × 1/2
    assert_eq!(half.0 * 1 / 2, 5);
}
```

## 八、判定表：const generics vs 宏 vs 类型级自然数

| 场景 | 首选方案 | 理由 |
|:---|:---|:---|
| 定长数组抽象（`[T; N]`）、缓冲区容量 | **const generics** | 正是设计目标；零成本、错误信息清晰 |
| 矩阵/张量维度、SIMD 通道数 | **const generics** | 维度相等性由类型系统强制；乘法类 API 一次定义 |
| 需要在常量表达式中做算术（`N+1`、`N*M`、`N/2`）且必须编译期保证 | **类型级自然数**（typenum 风格，见 [03_type_level_programming.md](03_type_level_programming.md)） | `generic_const_exprs` 未稳定；`UAdd<UN>` 等 trait 运算在 stable 可用，但错误信息晦涩、编译慢 |
| 一次性为有限几个长度生成 impl（如 N=4,8,16,32） | **宏（Macro）**（`macro_rules!` 批量展开） | 比 typenum 简单；无泛型参数开销；适合封闭的小集合 |
| 维度组合爆炸、运算复杂（张量收缩、广播规则） | **typenum / 类型级编程** | const generics 当前表达力不足；接受编译时间与错误信息代价 |
| 值仅在运行期知道 | 都不是——用 `Vec<T>` / slice | const 参数必须编译期可知（规则 3） |

决策一句话：**值编译期已知且只需"原样传递" ⟹ const generics；需要编译期算术 ⟹ stable 上加参数绕行或上 typenum；长度集合小而封闭 ⟹ 宏更省事。**

## 九、与既有内容的关系声明

按 AGENTS.md §2 Canonical 规则，const generics 的语法、stable/每日构建版 边界与判定规则以本页为唯一权威来源：

| 文件 | 保留内容 | 与本页关系 |
|:---|:---|:---|
| [01_generics.md](01_generics.md) | 泛型参数空间总览（类型/生命周期/const/关联类型）、单态化全景 | 引用本页作为 const 参数的深度权威页 |
| [03_type_level_programming.md](03_type_level_programming.md) | Peano 数、typenum、HList、类型级计算编码 | const generics 表达力不足时的替代方案，边界对照指向本页 §8 |
| [11_const_trait_impl_preview.md](../../07_future/03_preview_features/06_const_trait_impl_preview.md) | `const trait`/`const fn` 在 trait 上下文的效果（const 计算的另一轴） | 互补：const generics 是"值级参数"，const trait 是"效果级参数" |

## 相关概念

- **上层概念**: [Generics](01_generics.md) · [Traits](../00_traits/01_traits.md) · [Type System](../../01_foundation/02_type_system/01_type_system.md)
- **下层概念**: [Type-Level Programming](03_type_level_programming.md) · [const Trait Impl（预览）](../../07_future/03_preview_features/06_const_trait_impl_preview.md) · [Const Eval](../../01_foundation/04_control_flow/03_statements_and_expressions.md)

## 十、来源与延伸阅读

- [Rust Reference — Generic Parameters](https://doc.rust-lang.org/reference/items/generics.html)：const 参数的规范语法与约束
- [RFC 2000 — Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)：设计动机、MVP 边界、相等性与可判定性论证
- [rust-lang blog — Const Generics MVP Hits Beta](https://blog.rust-lang.org/2021/02/26/const-generics-mvp-beta.html)：1.51 稳定公告与 min_const_generics 边界示例
- [Tracking Issue #74878 — min_const_generics](https://github.com/rust-lang/rust/issues/74878)（已稳定）
- [Tracking Issue #76560 — generic_const_exprs](https://github.com/rust-lang/rust/issues/76560)：截至 Rust 1.97.0 仍未稳定，关注其稳定化进展
- [Tracking Issue #95174 — adt_const_params](https://github.com/rust-lang/rust/issues/95174)：ADT 作为 const 参数类型的进展
- [Jung, Jourdan, Krebbers & Dreyer: RustBelt — Securing the Foundations of the Rust Programming Language（POPL 2018）](https://plv.mpi-sws.org/rustbelt/)（P1 学术：Rust 类型系统形式化基线，2026-07-12 验证 HTTP 200）

**文档版本**: 1.0
**最后更新**: 2026-07-12
