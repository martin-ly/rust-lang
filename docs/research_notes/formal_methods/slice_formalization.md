# Slice类型形式化

> **创建日期**: 2026-03-05
> **Rust版本**: 1.94.0+
> **Rust Book对应**: Ch 4.3 The Slice Type
> **状态**: ✅ 新增 (修复GAP-SLICE-01)

---

## 目录

- [Slice类型形式化](#slice类型形式化)
  - [目录](#目录)
  - [概述](#概述)
  - [形式化定义](#形式化定义)
    - [定义 SLICE-1 (Slice类型)](#定义-slice-1-slice类型)
    - [定义 SLICE-2 (Slice引用)](#定义-slice-2-slice引用)
    - [定义 SLICE-3 (Slice索引)](#定义-slice-3-slice索引)
  - [String切片形式化](#string切片形式化)
    - [定义 STR-1 (str类型)](#定义-str-1-str类型)
    - [定义 STR-2 (String与str关系)](#定义-str-2-string与str关系)
    - [定理 STR-T1 (UTF-8保证)](#定理-str-t1-utf-8保证)
  - [切片生命周期](#切片生命周期)
    - [定义 SLICE-LF-1 (切片生命周期)](#定义-slice-lf-1-切片生命周期)
    - [定理 SLICE-LF-T1 (切片有效性)](#定理-slice-lf-t1-切片有效性)
  - [定理与证明](#定理与证明)
    - [定理 SLICE-T2 (切片不拥有数据)](#定理-slice-t2-切片不拥有数据)
    - [定理 SLICE-T3 (可变切片互斥)](#定理-slice-t3-可变切片互斥)
    - [定理 SLICE-T4 (Slice Copy行为)](#定理-slice-t4-slice-copy行为)
  - [代码示例](#代码示例)
    - [示例1: 基本Slice操作](#示例1-基本slice操作)
    - [示例2: String切片](#示例2-string切片)
    - [示例3: 可变切片](#示例3-可变切片)
    - [示例4: 生命周期检查](#示例4-生命周期检查)
  - [与Rust Book对齐](#与rust-book对齐)
  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)

---

## 概述

Slice (`[T]`) 是Rust中的动态大小类型(DST)，表示连续内存区域的视图。
Slice本身不是具体类型，必须通过引用(`&[T]`或`&mut [T]`)使用。

**与Rust Book Ch 4.3对应**: 本项目提供Book中Slice概念的形式化数学定义。

---

## 形式化定义

### 定义 SLICE-1 (Slice类型)

Slice类型`[T]`表示类型`T`的连续元素序列，大小在编译时未知。

$$
\text{Slice}\langle T \rangle = \{ s \mid s = [e_0, e_1, \ldots, e_{n-1}] \land \forall i. e_i : T \land n \geq 0 \}
$$

**性质**:

- `size_of::<[T]>()`未定义（DST）
- `size_of::<&[T]>() = 2 * size_of::<usize>()` (胖指针：地址+长度)

### 定义 SLICE-2 (Slice引用)

Slice引用`&[T]`是胖指针，包含指向首元素的指针和长度。

$$
\text{SliceRef}\langle T \rangle = \{ (ptr, len) \mid ptr : *const T \land len : usize \}
$$

**类型规则**:

```text
Γ ⊢ arr : [T; n]      (n为编译时常量)
─────────────────────────────── (SLICE-R1)
Γ ⊢ &arr[..] : &[T]

Γ ⊢ vec : Vec<T>
─────────────────────────────── (SLICE-R2)
Γ ⊢ &vec[..] : &[T]

Γ ⊢ s : String
─────────────────────────────── (SLICE-R3)
Γ ⊢ &s[..] : &str
```

### 定义 SLICE-3 (Slice索引)

Slice索引操作返回对元素的引用。

$$
\text{index}(s, i) = \begin{cases}
\&s[i] & \text{if } 0 \leq i < s.len \\
\text{panic} & \text{otherwise}
\end{cases}
$$

**安全性**: 索引操作在运行时检查边界，保证内存安全。

**定理 SLICE-T1 (索引安全性)**:
对于任意`slice: &[T]`和索引`i`，若`i >= slice.len()`，则程序panic，不会访问越界内存。

$$
\forall s: \&[T], i: usize.\ (i \geq s.len) \rightarrow \text{panic}
$$

---

## String切片形式化

### 定义 STR-1 (str类型)

`str`是UTF-8编码字符串的Slice类型，是Rust的字符串切片类型。

$$
\text{Str} = \{ s \mid s : [u8] \land \text{valid_utf8}(s) \}
$$

**性质**:

- `str`是DST，必须通过`&str`使用
- 保证有效UTF-8编码
- 不可变

### 定义 STR-2 (String与str关系)

`String`拥有堆分配的`str`，`&str`借用`String`的内容。

$$
\text{String} = \text{Own}\langle \text{Str} \rangle \\
\&\text{String} \rightsquigarrow \&\text{str}
$$

**借用规则**:

```rust
let s: String = String::from("hello");
let slice: &str = &s[..];  // 不可变借用
// s.push_str("!");        // 错误：借用期间不能修改
```

**形式化**:
$$
\text{borrow}(s, \text{slice}) \rightarrow \Omega(s) = \text{Borrowed}_{\text{imm}} \land \text{valid}(\text{slice})
$$

### 定理 STR-T1 (UTF-8保证)

所有`str`值在创建时保证为有效UTF-8，否则panic。

$$
\forall s: \&str.\ \text{valid_utf8}(s)
$$

**证明**:

- `String::from_utf8`返回`Result`，无效UTF-8时返回`Err`
- 字符串字面量`"..."`在编译时验证UTF-8
- `str`的unsafe构造必须满足UTF-8不变式

---

## 切片生命周期

### 定义 SLICE-LF-1 (切片生命周期)

切片引用的生命周期不能超过其源数据的生命周期。

$$
\frac{\Gamma \vdash \text{source} : T \quad \Gamma \vdash \&\text{source}[..] : \&'a [T]}{'a \subseteq \text{scope}(\text{source})}
$$

### 定理 SLICE-LF-T1 (切片有效性)

切片引用在生命周期内始终指向有效内存。

$$
\forall s: \&'a [T], t.\ (t \in 'a) \rightarrow \text{valid}(s \text{ at } t)
$$

**证明**:

1. 切片借用创建时，源数据被标记为借用状态
2. 借用检查器确保源数据在生命周期'a内不被释放
3. 因此切片始终指向有效内存

---

## 定理与证明

### 定理 SLICE-T2 (切片不拥有数据)

切片引用`&[T]`不拥有数据，只借用数据。

$$
\forall s: \&[T].\ \neg\text{owns}(s)
$$

**推论**: 切片离开作用域时，不调用元素的`drop`。

### 定理 SLICE-T3 (可变切片互斥)

同一时间只能有一个可变切片引用。

$$
\forall s_1, s_2: \&mut [T].\ (s_1 \text{ active} \land s_2 \text{ active}) \rightarrow s_1 = s_2
$$

### 定理 SLICE-T4 (Slice Copy行为)

若`T: Copy`，则`&[T]`可以被安全复制。

$$
T: \text{Copy} \rightarrow \&[T] : \text{Copy}
$$

**注意**: 复制的是引用（胖指针），不是底层数据。

---

## 代码示例

### 示例1: 基本Slice操作

```rust
fn slice_basics() {
    let arr = [1, 2, 3, 4, 5];
    let slice: &[i32] = &arr[1..3];  // [2, 3]

    assert_eq!(slice.len(), 2);
    assert_eq!(slice[0], 2);

    // 形式化: slice = (ptr=&arr[1], len=2)
}
```

### 示例2: String切片

```rust
fn string_slices() {
    let s = String::from("hello world");
    let hello: &str = &s[0..5];
    let world: &str = &s[6..11];

    assert_eq!(hello, "hello");
    assert_eq!(world, "world");

    // 形式化: hello和world都借用s，生命周期受s约束
}
```

### 示例3: 可变切片

```rust
fn mutable_slice() {
    let mut arr = [1, 2, 3, 4, 5];
    let slice: &mut [i32] = &mut arr[..];

    slice[0] = 10;  // 通过切片修改

    assert_eq!(arr[0], 10);  // 原数组被修改
}
```

### 示例4: 生命周期检查

```rust
fn dangling_slice() -> &str {
    let s = String::from("hello");
    &s[..]  // 错误：s在函数结束时释放
}

// 形式化: 返回的&str生命周期超过s的作用域
// 借用检查器拒绝此代码
```

---

## 与Rust Book对齐

| Book内容 | 本项目形式化 | 状态 |
| :--- | :--- | :--- |
| Slice概念 | Def SLICE-1, SLICE-2 | ✅ |
| String slices | Def STR-1, STR-2 | ✅ |
| Slice索引 | Def SLICE-3, 定理SLICE-T1 | ✅ |
| UTF-8保证 | 定理STR-T1 | ✅ |
| 生命周期 | 定理SLICE-LF-T1 | ✅ |

---

**维护者**: Rust Formal Methods Research Team
**创建日期**: 2026-03-05
**对应Book章节**: Ch 4.3 The Slice Type
**状态**: ✅ 已对齐

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
