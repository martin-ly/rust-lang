# CoerceShared Trait 的完整形式化语义

## 1. 引言

CoerceShared Trait 是 Rust 类型系统中负责**类型强制转换（type coercion）**的核心机制。
它定义了在哪些情况下，一个类型的值可以被隐式地转换为另一个类型，特别是在涉及引用转换时。
理解 CoerceShared 的形式化语义对于分析 Rust 程序的类型安全至关重要。

### 1.1 什么是 CoerceShared

CoerceShared 表示从更特定的引用类型到更通用引用类型的**隐式转换**：

```rust
let mut x = 5;
let r_mut: &mut i32 = &mut x;
let r_shared: &i32 = r_mut;  // 隐式 CoerceShared: &mut T → &T
```

### 1.2 安全边界

Rust 区分两种强制转换：

- **Safe coercion**: 编译器自动执行的转换，保证内存安全
- **Unsafe conversion**: 需要 `unsafe` 块的手动转换

## 2. 语法定义

### 2.1 强制转换表达式

$$
\begin{aligned}
e \in \text{Expr} &::= \dots \\
&\quad | \; e : \tau \quad \text{(带类型标注)} \\
&\quad | \; e \text{ as } \tau \quad \text{(显式转换)} \\
&\quad | \; \text{coerce}(e, \tau_1, \tau_2) \quad \text{(形式化强制)}
\end{aligned}
$$

### 2.2 强制转换类型语法

```
Coercion ::= Unsize(τ₁, τ₂)        -- 非大小类型转换
          | MutToImm(&ρ mut τ, &ρ τ)  -- 可变到不可变
          | RefToRaw(&τ, *const τ)    -- 引用到裸指针
          | BoxToRef(Box<τ>, &τ)      -- Box 到引用
          | Deref(τ₁, τ₂)             -- 解引用强制
```

## 3. 操作语义

### 3.1 大步操作语义

**可变到不可变引用强制** (EB-MutToImm):

$$
\frac{
  \langle e, \sigma \rangle \Downarrow \langle \&'\rho \text{ mut } v, \sigma' \rangle \quad
  \text{valid}(\sigma', \&'\rho \text{ mut } v)
}{
  \langle \text{coerce}(e, \&'\rho \text{ mut } T, \&'\rho T), \sigma \rangle \Downarrow
  \langle \&'\rho v, \sigma' \rangle
}
$$

**引用到裸指针强制** (EB-RefToRaw):

$$
\frac{
  \langle e, \sigma \rangle \Downarrow \langle \&'\rho v, \sigma' \rangle \quad
  \text{valid}(\sigma', \&'\rho v)
}{
  \langle e \text{ as } *\text{const } T, \sigma \rangle \Downarrow
  \langle *\text{const } v, \sigma' \rangle
}
\quad\text{(unsafe)}
$$

**Box 到引用强制** (EB-BoxToRef):

$$
\frac{
  \langle e, \sigma \rangle \Downarrow \langle \text{Box}(v), \sigma' \rangle
}{
  \langle \text{coerce}(e, \text{Box}\langle T \rangle, \&T), \sigma \rangle \Downarrow
  \langle \&v, \sigma' \rangle
}
$$

### 3.2 小步操作语义

**强制转换步骤规则** (S-Coerce-Step):

$$
\frac{
  e \rightarrow e'
}{
  \text{coerce}(e, \tau_1, \tau_2) \rightarrow \text{coerce}(e', \tau_1, \tau_2)
}
$$

**强制转换值规则** (S-Coerce-Value):

$$
\frac{
  \text{coerce\_valid}(v, \tau_1, \tau_2)
}{
  \text{coerce}(v, \tau_1, \tau_2) \rightarrow v'
}
$$

其中 $v'$ 是转换后的值。

### 3.3 强制转换有效性

$$
\text{coerce\_valid}(v, \tau_1, \tau_2) \iff
\begin{cases}
\text{true} & \text{if } \tau_1 = \&'\rho \text{ mut } T, \tau_2 = \&'\rho T \\
\text{true} & \text{if } \tau_1 = \text{Box}\langle T \rangle, \tau_2 = \&T \\
\text{unsafe} & \text{if } \tau_1 = \&T, \tau_2 = *\text{const } T \\
\text{unsafe} & \text{if } \tau_1 = \&\text{mut } T, \tau_2 = *\text{mut } T \\
\text{false} & \text{otherwise}
\end{cases}
$$

## 4. 类型规则

### 4.1 子类型关系

**子类型规则** (T-Sub):

$$
\frac{
  \Gamma \vdash e : \tau_1 \quad
  \Gamma \vdash \tau_1 <: \tau_2
}{
  \Gamma \vdash e : \tau_2
}
$$

### 4.2 引用强制规则

**可变到不可变** (T-MutToImm):

$$
\frac{
  \Gamma \vdash e : \&'\rho \text{ mut } T
}{
  \Gamma \vdash e : \&'\rho T
}
$$

**引用到裸指针** (T-RefToRaw):

$$
\frac{
  \Gamma \vdash e : \&'\rho T \quad
  \text{unsafe\_context}(\Gamma)
}{
  \Gamma \vdash e \text{ as } *\text{const } T : *\text{const } T
}
$$

**可变引用到可变裸指针** (T-MutRefToRawMut):

$$
\frac{
  \Gamma \vdash e : \&'\rho \text{ mut } T \quad
  \text{unsafe\_context}(\Gamma)
}{
  \Gamma \vdash e \text{ as } *\text{mut } T : *\text{mut } T
}
$$

### 4.3 Box 强制规则

**Box 到共享引用** (T-BoxToRef):

$$
\frac{
  \Gamma \vdash e : \text{Box}\langle T \rangle
}{
  \Gamma \vdash \&*e : \&T
}
$$

**Box 到可变引用** (T-BoxToMutRef):

$$
\frac{
  \Gamma \vdash e : \text{Box}\langle T \rangle
}{
  \Gamma \vdash \&\text{mut } *e : \&\text{mut } T
}
$$

### 4.4 数组到切片强制

**数组到切片** (T-ArrayToSlice):

$$
\frac{
  \Gamma \vdash e : [T; n] \quad
  n \geq 0
}{
  \Gamma \vdash \&e : \&[T]
}
$$

### 4.5 函数指针强制

**函数到函数指针** (T-FnToPtr):

$$
\frac{
  \Gamma \vdash f : \text{fn}(\tau_1, \dots, \tau_n) \rightarrow \tau
}{
  \Gamma \vdash f : \text{fn\_ptr}(\tau_1, \dots, \tau_n) \rightarrow \tau
}
$$

## 5. 形式化定义

### 5.1 CoerceShared 关系

**定义 5.1** (CoerceShared 关系)：

CoerceShared 关系 $\mathcal{C}$ 是类型对上的二元关系：

$$
\mathcal{C} \subseteq \text{Type} \times \text{Type}
$$

其中 $(\tau_1, \tau_2) \in \mathcal{C}$ 表示 $\tau_1$ 可以强制转换为 $\tau_2$。

### 5.2 强制转换闭包

**定义 5.2** (强制转换闭包)：

强制转换闭包 $\mathcal{C}^*$ 是 $\mathcal{C}$ 的自反传递闭包：

$$
\mathcal{C}^* = \{(\tau, \tau) \mid \tau \in \text{Type}\} \cup
               \{(\tau_1, \tau_3) \mid \exists \tau_2. (\tau_1, \tau_2) \in \mathcal{C} \land (\tau_2, \tau_3) \in \mathcal{C}^*\}
$$

### 5.3 安全强制转换

**定义 5.3** (安全强制转换)：

安全强制转换 $\mathcal{C}_{\text{safe}}$ 是 $\mathcal{C}$ 的子集：

$$
\mathcal{C}_{\text{safe}} = \{(\tau_1, \tau_2) \in \mathcal{C} \mid \text{safe}(\tau_1, \tau_2)\}
$$

其中：

$$
\text{safe}(\tau_1, \tau_2) \iff
\begin{cases}
\text{true} & \text{if } \tau_1 = \&'\rho \text{ mut } T, \tau_2 = \&'\rho T \\
\text{true} & \text{if } \tau_1 = \text{Box}\langle T \rangle, \tau_2 = \&T \\
\text{true} & \text{if } \tau_1 = [T; n], \tau_2 = [T] \\
\text{true} & \text{if } \tau_1 <: \tau_2 \text{ (子类型)} \\
\text{false} & \text{if } \tau_1 = \&T, \tau_2 = *\text{const } T \\
\text{false} & \text{otherwise}
\end{cases}
$$

### 5.4 类型一致性

**定义 5.4** (强制转换一致性)：

强制转换是一致的，如果：

$$
\forall (\tau_1, \tau_2) \in \mathcal{C}_{\text{safe}}. \forall v : \tau_1. \text{safe\_value}(\text{coerce}(v), \tau_2)
$$

## 6. 安全定理

### 6.1 安全强制保持性

**定理 6.1** (安全强制保持类型安全)：

如果 $(\tau_1, \tau_2) \in \mathcal{C}_{\text{safe}}$ 且 $\Gamma \vdash e : \tau_1$，则：

$$
\Gamma \vdash \text{coerce}(e, \tau_1, \tau_2) : \tau_2 \land
\text{preserves\_safety}(e, \text{coerce}(e, \tau_1, \tau_2))
$$

**证明**：

根据 $\mathcal{C}_{\text{safe}}$ 的定义分类讨论：

**情况 1**：$\tau_1 = \&'\rho \text{ mut } T$, $\tau_2 = \&'\rho T$

- 强制转换将可变引用转为不可变引用
- 不可变引用只允许读取，不允许写入
- 原可变引用在转换结果被使用时被冻结
- 因此安全性得到保持

**情况 2**：$\tau_1 = \text{Box}\langle T \rangle$, $\tau_2 = \&T$

- Box 提供堆分配值的所有权
- 转换为引用后，Box 仍然负责内存管理
- 引用的生命周期受 Box 生命周期限制
- 因此安全性得到保持

**情况 3**：数组到切片

- 数组大小在编译时已知
- 切片是 (指针, 长度) 对
- 转换保持对相同内存区域的引用
- 边界检查在运行时通过切片长度保证

### 6.2 不安全强制定理

**定理 6.2** (不安全强制需要显式标记)：

如果 $(\tau_1, \tau_2) \in \mathcal{C} \setminus \mathcal{C}_{\text{safe}}$，则强制转换只能在 `unsafe` 上下文中进行。

**证明**：

不安全强制包括：

- 引用到裸指针：失去生命周期检查
- 可变裸指针转换：失去别名唯一性保证

这些转换可能破坏 Rust 的安全保证，因此需要程序员显式承担责任。

### 6.3 强制转换组合性

**定理 6.3** (安全强制的组合)：

如果 $(\tau_1, \tau_2) \in \mathcal{C}_{\text{safe}}$ 且 $(\tau_2, \tau_3) \in \mathcal{C}_{\text{safe}}$，则：

$$
(\tau_1, \tau_3) \in \mathcal{C}_{\text{safe}} \land
\text{coerce}(\text{coerce}(v, \tau_1, \tau_2), \tau_2, \tau_3) =
\text{coerce}(v, \tau_1, \tau_3)
$$

### 6.4 引用转换的别名安全

**定理 6.4** (强制转换的别名安全)：

对于任意有效的强制转换 $(\&'\rho_1 \text{ mut } T, \&'\rho_2 T) \in \mathcal{C}$：

$$
\rho_2 = \rho_1 \rightarrow
\forall t \in \rho_2. \text{no\_mut\_alias}(\text{target}(v), t)
$$

## 7. Rust 代码示例

### 7.1 基本强制转换

```rust
fn basic_coercions() {
    // &mut T → &T (safe)
    let mut x = 5;
    let r_mut: &mut i32 = &mut x;
    let r_shared: &i32 = r_mut;  // 隐式 CoerceShared
    println!("{}", r_shared);

    // 注意：r_mut 在 r_shared 生命周期内被冻结
    // r_mut = 6;  // 编译错误！
}
```

### 7.2 Box 到引用强制

```rust
fn box_to_ref() {
    let b = Box::new(vec![1, 2, 3]);

    // Box<Vec<i32>> → &Vec<i32> (safe)
    let r: &Vec<i32> = &b;
    println!("Length: {}", r.len());

    // Box<T> → &mut T
    let mut b2 = Box::new(42);
    let r_mut: &mut i32 = &mut *b2;
    *r_mut = 100;
    println!("{}", b2);
}
```

### 7.3 数组到切片强制

```rust
fn array_to_slice() {
    let arr: [i32; 5] = [1, 2, 3, 4, 5];

    // [i32; 5] → &[i32] (safe)
    let slice: &[i32] = &arr;
    println!("Slice length: {}", slice.len());

    // 数组引用强制
    process_slice(&arr);  // 自动转换
}

fn process_slice(s: &[i32]) {
    for x in s {
        println!("{}", x);
    }
}
```

### 7.4 引用到裸指针转换 (unsafe)

```rust
fn ref_to_raw_pointer() {
    let x = 42;
    let r: &i32 = &x;

    // &T → *const T (unsafe)
    let raw_const: *const i32 = r as *const i32;

    unsafe {
        println!("Dereferenced: {}", *raw_const);
    }
}

fn mut_ref_to_raw_pointer() {
    let mut x = 42;
    let r_mut: &mut i32 = &mut x;

    // &mut T → *mut T (unsafe)
    let raw_mut: *mut i32 = r_mut as *mut i32;

    unsafe {
        *raw_mut = 100;
    }
    println!("{}", x);
}
```

### 7.5 函数指针强制

```rust
fn fn_to_fn_ptr() {
    fn add_one(x: i32) -> i32 {
        x + 1
    }

    // fn item → fn pointer
    let f: fn(i32) -> i32 = add_one;
    println!("{}", f(5));
}
```

### 7.6 自定义类型的强制转换

```rust
use std::ops::Deref;

struct MyBox<T>(T);

impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

fn custom_deref_coercion() {
    let my_box = MyBox(String::from("hello"));

    // MyBox<String> → &String → &str (通过 Deref 强制)
    let s: &str = &my_box;
    println!("{}", s);
}
```

### 7.7 生命周期强制

```rust
fn lifetime_coercion<'a, 'b>(r: &'a &'b str) -> &'a str
where
    'b: 'a,  // 'b outlives 'a
{
    *r  // &'a &'b str → &'a str
}

fn static_lifetime() {
    let s: &'static str = "hello";
    let r: &str = s;  // &'static str → &str (lifetime缩短)
}
```

### 7.8 复合强制

```rust
fn compound_coercions() {
    let mut arr = [1, 2, 3, 4, 5];

    // &mut [i32; 5] → &mut [i32] → &[i32]
    let slice: &[i32] = &mut arr;

    // Box<[i32; 5]> → Box<[i32]>
    let boxed_arr = Box::new([1, 2, 3]);
    let boxed_slice: Box<[i32]> = boxed_arr;
}
```

## 8. 安全边界分析

### 8.1 Safe Coercions 总结

| 从类型 | 到类型 | 安全性 | 条件 |
|--------|--------|--------|------|
| `&mut T` | `&T` | Safe | 同生命周期 |
| `Box<T>` | `&T` | Safe | 临时借用 |
| `Box<T>` | `&mut T` | Safe | 临时可变借用 |
| `[T; N]` | `[T]` | Safe | 自动 |
| `fn item` | `fn pointer` | Safe | 自动 |
| `&T` | `*const T` | Unsafe | 需 unsafe |
| `&mut T` | `*mut T` | Unsafe | 需 unsafe |

### 8.2 为什么某些转换是 Unsafe

```rust
// 引用到裸指针转换失去安全保障
fn why_unsafe() {
    let x = 42;
    let r: &i32 = &x;
    let raw: *const i32 = r as *const i32;

    // 以下代码是 UB (未定义行为) 但编译器无法检测
    unsafe {
        // 可以伪造指针
        let fake: *const i32 = (0x1234 as usize + 0) as *const i32;
        // 可以创建悬空指针
        let dangling = create_dangling();
    }
}

fn create_dangling() -> *const i32 {
    let x = 42;
    &x as *const i32  // x 在函数返回后被释放
}
```

### 8.3 Unsize 强制

```rust
// 非大小类型强制 (Unsize coercion)
trait Trait {}
struct Impl;
impl Trait for Impl {}

fn unsized_coercion() {
    let obj: Box<dyn Trait> = Box::new(Impl);
    // Impl → dyn Trait (unsize coercion)
}
```

## 9. 与其他特性的交互

### 9.1 与泛型的交互

```rust
fn generic_coercion<T>(mut v: Vec<T>) -> &[T] {
    &v  // Vec<T> → &[T] 通过 Deref
}

fn trait_bound_coercion<T: AsRef<str>>(t: T) -> &str {
    t.as_ref()
}
```

### 9.2 与生命周期子类型的交互

```rust
fn lifetime_subtyping<'a, 'b: 'a>(x: &'b i32) -> &'a i32 {
    x  // &'b i32 → &'a i32 (子类型强制)
}
```

形式化：

$$
\frac{
  \Gamma \vdash e : \&'\rho_2 T \quad
  \rho_2 : \rho_1
}{
  \Gamma \vdash e : \&'\rho_1 T
}
$$

### 9.3 与模式匹配的交互

```rust
fn pattern_coercion() {
    let arr: [i32; 3] = [1, 2, 3];

    // 模式中的强制转换
    match &arr {
        slice => println!("Slice: {:?}", slice),  // &[i32; 3] → &[i32]
    }
}
```

## 10. 实现考虑

### 10.1 编译器实现

Rust 编译器在以下阶段处理强制转换：

1. **类型检查** (`rustc_typeck`): 识别需要强制转换的位置
2. **类型推断**: 确定目标类型
3. **借用检查**: 验证强制转换的安全性
4. **代码生成**: 生成实际的转换代码

### 10.2 强制转换点

强制转换发生在以下位置：

- 赋值：\[let x: T = expr;\]
- 函数参数传递
- 函数返回值
- 结构体字段初始化

## 11. 总结

CoerceShared Trait 定义了 Rust 中类型安全强制转换的边界。关键结论：

1. **Safe 强制转换**：`&mut T → &T`、`Box<T> → &T`、数组到切片等，编译器自动执行
2. **Unsafe 强制转换**：引用到裸指针，需要显式 `unsafe` 标记
3. **类型保持性**：安全强制保持内存安全和类型安全
4. **组合性**：安全强制可以安全地组合

理解这些规则对于编写安全和高效的 Rust 代码至关重要。
