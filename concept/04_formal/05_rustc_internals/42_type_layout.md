# 类型布局（Type Layout）

> **EN**: Type Layout
> **Summary**: Rust 类型布局的规范保证：size、alignment、字段偏移；`repr` 属性对结构体（Struct）、枚举（Enum）、联合体布局的影响；ZST 与 DST。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Type System](../../01_foundation/02_type_system/04_type_system.md) · [Special Types and Traits](41_special_types_and_traits.md) · [Memory Model](../../03_advanced/02_unsafe/29_memory_model.md)
> **后置概念**: [Behavior Considered Undefined](../01_ownership_logic/37_behavior_considered_undefined.md) · [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) · [FFI Advanced](../../03_advanced/04_ffi/09_ffi_advanced.md)
> **定理链**: Type → Size/Align/Offset → Repr → ABI
> **主要来源**: [Rust Reference — Type Layout](https://doc.rust-lang.org/reference/type-layout.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/) · [System V AMD64 ABI](https://gitlab.com/x86-psABIs/x86-64-ABI) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

>
> **来源**: [Rust Reference — Type Layout](https://doc.rust-lang.org/reference/type-layout.html)

---

---

## 认知路径

> **认知路径**: 本节从 "类型布局（Type Layout）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 类型布局（Type Layout） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 类型布局（Type Layout） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与类型布局（Type Layout）的适用边界。
5. **迁移应用**: 将 类型布局（Type Layout） 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "类型布局（Type Layout） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 类型布局（Type Layout） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 类型布局（Type Layout） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 类型布局（Type Layout） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 类型布局（Type Layout） 具有语言特有的形态。

## 一、什么是类型布局

**类型布局（type layout）** 指类型的：

- **大小（size）**: 类型在内存中占用的字节数。
- **对齐（alignment）**: 类型必须存放的内存地址的倍数。
- **字段相对偏移（offsets）**: 复合类型中各字段相对于起始地址的位置。
- **枚举（Enum） discriminant 布局**: 枚举如何存储和解释其判别值。

Rust 只保证稳定的布局规则，具体细节可能随编译版本变化。

---

## 二、Size 与 Alignment

- 类型大小可通过 `std::mem::size_of<T>()` 获取。
- 对齐要求可通过 `std::mem::align_of<T>()` 获取。
- 大小始终是对齐的倍数。
- 即使两个类型布局相同，它们在函数调用 ABI 中仍可能不同。

---

## 三、`repr` 属性

Rust 允许通过属性控制类型的内存布局。

### `#[repr(C)]`

使类型布局与 C 兼容，便于 FFI：

- 结构体（Struct）字段按声明顺序排列。
- 枚举（Enum） discriminant 类型默认为 `isize`，但可指定（如 `#[repr(C, u8)]`）。

```rust
#[repr(C)]
struct Point {
    x: f64,
    y: f64,
}
```

### `#[repr(transparent)]`

用于单字段结构体（Struct）或枚举（Enum），要求其布局与内部字段完全相同。常用于 newtype 包装器。

```rust
#[repr(transparent)]
struct UserId(u64);
```

### `#[repr(packed)]`

移除字段间的 padding，按 1 字节对齐。访问未对齐字段是 unsafe。

```rust
#[repr(packed)]
struct Packed {
    a: u8,
    b: u32, // 可能未对齐
}
```

### `#[repr(align(n))]`

强制类型的对齐要求至少为 `n` 字节。

```rust
#[repr(align(64))]
struct AlignedBuffer([u8; 64]);
```

---

## 四、零大小类型（ZST）

**Zero-sized types（ZST）** 大小为 0，对齐为 1（除非另有指定）。

常见 ZST：

- `()`
- 空数组 `[]`
- 只包含 ZST 字段的结构体（Struct）
- `PhantomData<T>`

ZST 不占用运行时（Runtime）内存，但参与类型系统（Type System）和泛型（Generics）单态化（Monomorphization）。

---

## 五、动态大小类型（DST）

**Dynamically sized types（DST）** 的大小在编译期未知，需要指针 + metadata。

常见 DST：

- `[T]`
- `str`
- `dyn Trait`

`Sized` trait 表示类型大小在编译期已知。`?Sized` 可放宽该约束。

---

## 六、枚举 Discriminant

- 默认枚举（Enum） discriminant 布局由编译器决定。
- 使用 `#[repr(u8)]`、`#[repr(i32)]` 等可指定 discriminant 类型。
- `#[repr(C)]` 枚举的 discriminant 类型与 C 兼容。

---

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Special Types and Traits](41_special_types_and_traits.md) | `Sized`、`PhantomData` 与布局相关 |
| [FFI Advanced](../../03_advanced/04_ffi/09_ffi_advanced.md) | `repr(C)` 用于跨语言 ABI 兼容 |
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | 访问未对齐字段、布局假设需要 unsafe |
| [Behavior Considered Undefined](../01_ownership_logic/37_behavior_considered_undefined.md) | 错误假设布局可能导致 UB |
