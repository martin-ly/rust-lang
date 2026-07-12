# 类型布局（Type Layout）

> **EN**: Type Layout
> **Summary**: Rust 类型布局的规范保证：size、alignment、字段偏移；`repr` 属性对结构体（Struct）、枚举（Enum）、联合体布局的影响；ZST 与 DST。
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位声明**: 本页为 Rust Reference 对应章节的**规范摘译与注解**（规范条文摘译 + 示例 + 交叉引用），非形式化推导或机器验证证明；形式化理论内容见 [类型语义](../00_type_theory/06_type_semantics.md)。依据 [A/S/P 标记规范](../../00_meta/03_audit/02_asp_marking_guide.md) §3.4，L4 形式化层同时容纳 S（Specification）规范分析类内容，故本页保留于 L4，Bloom 层级维持与内容相符的标注（理解/分析层的规范内容）。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Type System](../../01_foundation/02_type_system/01_type_system.md) · [Special Types and Traits](07_special_types_and_traits.md) · [Memory Model](../../03_advanced/02_unsafe/06_memory_model.md)
> **后置概念**: [Behavior Considered Undefined](../01_ownership_logic/06_behavior_considered_undefined.md) · [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) · [FFI Advanced](../../03_advanced/04_ffi/02_ffi_advanced.md)
> **定理链**: Type → Size/Align/Offset → Repr → ABI
> **主要来源**: [Rust Reference — Type Layout](https://doc.rust-lang.org/reference/type-layout.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/) · [System V AMD64 ABI](https://gitlab.com/x86-psABIs/x86-64-ABI) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

>
> **来源**: [Rust Reference — Type Layout](https://doc.rust-lang.org/reference/type-layout.html)

---

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
- `#[repr(C)]` 枚举（Enum）的 discriminant 类型与 C 兼容。

---

## 七、相关概念

| 概念 | 关系 |
|:---|:---|
| [Special Types and Traits](07_special_types_and_traits.md) | `Sized`、`PhantomData` 与布局相关 |
| [FFI Advanced](../../03_advanced/04_ffi/02_ffi_advanced.md) | `repr(C)` 用于跨语言 ABI 兼容 |
| [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) | 访问未对齐字段、布局假设需要 unsafe |
| [Behavior Considered Undefined](../01_ownership_logic/06_behavior_considered_undefined.md) | 错误假设布局可能导致 UB |

---

> **权威来源**: [Rust Reference — Type Layout](https://doc.rust-lang.org/reference/type-layout.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/) · [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.0
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/nix — 生态权威 API 文档](https://docs.rs/nix) · [docs.rs/bytemuck — 生态权威 API 文档](https://docs.rs/bytemuck)
