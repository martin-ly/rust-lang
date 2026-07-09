# 泛型编译器行为：单态化、分发与类型擦除

> **EN**: Generics Compiler Behavior
> **Summary**: Rust 泛型代码的编译行为：单态化、静态分发与动态分发、类型擦除、胖指针与 VTable，以及性能权衡。 How Rust compiles generic code: monomorphization, static vs dynamic dispatch, type erasure, fat pointers, vtables, and performance trade-offs.
>
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S** — Structure
> **双维定位**: S×Eva — 结构评价
> **前置概念**: [Generics](../../02_intermediate/01_generics/02_generics.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) · [Type System](../../01_foundation/02_type_system/04_type_system.md)
> **后置概念**: [Rustc Trait Solver](26_trait_solver_in_rustc.md) · [Type Layout](42_type_layout.md)
> **定理链**: Generic Function → Monomorphization → Static Dispatch / Dynamic Dispatch
> **本节关键术语**: 单态化 (Monomorphization) · 静态分发 (Static Dispatch) · 动态分发 (Dynamic Dispatch) · 类型擦除 (Type Erasure) · Fat Pointer · VTable — [完整对照表](../../00_meta/01_terminology/terminology_glossary.md)

---

> **来源**: [Rust Reference — Generics](https://doc.rust-lang.org/reference/items/generics.html) · [Rust Reference — Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html) · [Rustonomicon — Trait Objects](https://doc.rust-lang.org/nomicon/trait-objects.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

## 认知路径

> **认知路径**: 本节从 "泛型编译器行为：单态化、分发与类型擦除" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么泛型编译器行为在 Rust 中值得关注？它直接决定二进制大小、运行时性能和编译时间，是零成本抽象的核心。
2. **概念建立**: 掌握单态化、静态分发、动态分发、类型擦除、胖指针和 VTable 的核心机制。
3. **机制推理**: 通过 ⟹ 定理链将泛型函数、类型参数、实例化和分发方式串联起来。
4. **边界辨析**: 借助反命题/反例理解单态化膨胀和动态分发开销的适用边界。
5. **迁移应用**: 将泛型编译器行为与 trait solver、类型布局和 unsafe 代码链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "泛型在所有场景下都零成本" ⟹ 不成立。单态化会导致代码体积膨胀和编译时间增加。

> **反命题 2**: "动态分发总是比静态分发慢" ⟹ 不成立。在特定场景下，`dyn Trait` 可以减少缓存失效和代码体积，反而提升整体性能。

> **反命题 3**: "单态化代码可以直接等价替换为 trait object" ⟹ 不成立。trait object 有对象安全限制，且丢失类型信息。

## 一、单态化 Monomorphization

Rust 泛型在编译期为每个具体类型生成一份专用代码，称为**单态化**。

```rust
fn identity<T>(x: T) -> T { x }

fn main() {
    identity(5i32);     // 生成 identity_i32
    identity(3.14f64);  // 生成 identity_f64
}
```

### 优势与代价

| 优势 | 代价 |
|:---|:---|
| 零运行时开销 | 代码体积膨胀（code bloat） |
| 可内联优化 | 编译时间增加 |
| 类型错误在编译期捕获 | 跨 crate 边界重复实例化 |

## 二、静态分发 vs 动态分发

| 特性 | 静态分发 `impl Trait` / 泛型 | 动态分发 `dyn Trait` |
|:---|:---|:---|
| 调用方式 | 直接调用，可内联 | 通过 VTable 间接调用 |
| 性能 | 高（零开销） | 低（间接跳转 + 无法内联） |
| 代码体积 | 可能膨胀 | 固定 |
| 同质集合 | 不便（每个元素类型不同） | 方便（`Vec<Box<dyn Trait>>`） |
| 类型信息 | 保留完整类型 | 擦除为 trait 对象 |

```rust
fn static_dispatch<T: Debug>(x: T) { println!("{:?}", x); }
fn dynamic_dispatch(x: &dyn Debug) { println!("{:?}", x); }
```

## 三、类型擦除与 Fat Pointer

`dyn Trait` 使用**胖指针（fat pointer）**：数据指针 + VTable 指针。

```rust
let obj: &dyn Trait = &value;
// 内存布局: [data_ptr, vtable_ptr]
```

### VTable 结构

VTable 存储 trait 方法地址、析构函数、大小与对齐信息。

```text
VTable for dyn Trait:
+------------------+
| drop_in_place    |
+------------------+
| size             |
+------------------+
| align            |
+------------------+
| method_1         |
+------------------+
| method_2         |
+------------------+
| ...              |
+------------------+
```

## 四、对象安全

只有满足对象安全条件的 trait 才能用作 trait object：

| 条件 | 说明 |
|:---|:---|
| 返回值不能为 `Self` | `fn clone(&self) -> Self` 不满足 |
| 没有泛型方法 | `fn foo<T>(&self, x: T)` 不满足 |
| 关联类型必须被约束 | 不能被调用者任意选择 |
| `Sized` 不是 supertrait | 或显式标记 `Self: ?Sized` |

## 五、性能权衡与最佳实践

| 目标 | 推荐方案 | 原因 |
|:---|:---|:---|
| 最大化运行时性能 | 泛型 / `impl Trait` | 可内联、零开销 |
| 最小化二进制体积 | `dyn Trait` | 一份代码处理所有类型 |
| 同质集合 | 泛型 `Vec<T>` | 连续存储 |
| 异质集合 | `Vec<Box<dyn Trait>>` | 统一接口 |
| 减少编译时间 | 非泛型入口 + 内部泛型包装 | 降低单态化点 |

```rust
// 减少膨胀：公共非泛型入口 + 小型泛型包装
pub fn process_value(value: &dyn MyTrait) {
    // 非泛型主体
}
```

## 六、`impl Trait` 返回类型

`impl Trait` 在返回位置提供抽象同时保留静态分发：

```rust
fn make_iter() -> impl Iterator<Item = i32> {
    (0..10).map(|x| x * 2)
}
```

与 `dyn Trait` 的区别：调用者不知道具体类型，但编译器可以内联和优化。

## 七、单态化与编译时间

单态化在 crate 边界会导致重复编译：泛型函数在定义 crate 中不生成机器码，在每个使用 crate 中单独实例化。对于大型泛型库，可以考虑：

- 提供非泛型 API 入口。
- 将泛型包装为内部 trait object。
- 使用 `-C prefer-dynamic`（较少用）。

## 八、与 Unsafe 的交互

`dyn Trait` 的 VTable 布局、`Any::downcast_ref` 的类型擦除与恢复，以及 `core::raw_vtable` 等底层操作都涉及 unsafe 语义。详见 [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md)。

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Rustc Trait Solver](26_trait_solver_in_rustc.md) | 泛型约束求解 |
| [Type Layout](42_type_layout.md) | 单态化后类型布局 |
| [Application Binary Interface](38_application_binary_interface.md) | trait object 的 ABI |
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | VTable 和类型擦除涉及 unsafe |

---

> **权威来源**: [Rust Reference — Generics](https://doc.rust-lang.org/reference/items/generics.html) · [Rust Reference — Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html) · [Rustonomicon — Trait Objects](https://doc.rust-lang.org/nomicon/trait-objects.html)
> **内容分级**: [专家级]
