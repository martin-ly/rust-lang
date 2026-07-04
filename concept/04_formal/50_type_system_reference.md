# 类型系统参考（Type System Reference）

> **EN**: Type System Reference
> **Summary**: Rust Reference 对类型系统的完整规范：各类型子类、动态大小类型、内部可变性、子类型与变型、trait/lifetime 约束、类型强制转换、发散类型、生命周期（Lifetimes）省略。 Complete Rust Reference specification of the type system: subtypes, variances, trait/lifetime bounds, coercions, diverging types, and lifetime elision.
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Type System](../01_foundation/04_type_system.md) · [Type Layout](42_type_layout.md) · [Variables](../03_advanced/33_variables.md)
> **后置概念**: [Subtyping and Variance](06_subtype_variance.md) · [Behavior Considered Undefined](37_behavior_considered_undefined.md) · [Application Binary Interface](38_application_binary_interface.md)
> **定理链**: Type → Kind → Size/Align → Lifetime → Trait Bounds
>
> **来源**: [Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Cardelli & Wegner — On Understanding Types](https://doi.org/10.1145/6041.6042) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---


---

## 认知路径

> **认知路径**: 本节从 "类型系统参考（Type System Reference）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 类型系统参考（Type System Reference） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 类型系统参考（Type System Reference） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与类型系统参考（Type System Reference）的适用边界。
5. **迁移应用**: 将 类型系统参考（Type System Reference） 与前置/后置概念链接，形成跨层知识网络。


---

## 反命题决策树

> **反命题 1**: "类型系统参考（Type System Reference） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 类型系统参考（Type System Reference） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 类型系统参考（Type System Reference） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 类型系统参考（Type System Reference） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 类型系统参考（Type System Reference） 具有语言特有的形态。


## 一、类型分类

Rust 类型可分为：

| 类别 | 示例 | 说明 |
|:---|:---|:---|
| 原始类型 | `bool`, `i32`, `u64`, `f64`, `char` | 标量，大小固定 |
| 复合类型 | tuple、array、struct、enum、union | 由多个值组合 |
| 函数类型 | `fn(i32) -> i32` | 函数指针 |
| 指针类型 | `&T`, `&mut T`, `*const T`, `*mut T`, `Box<T>` | 引用（Reference）与裸指针 |
| Trait 对象 | `dyn Trait` | 动态分发 |
| `impl Trait` | `impl Iterator` | 抽象具体类型 |
| 类型参数 | `T`, `'a`, `const N: usize` | 泛型（Generics）参数 |
| Never 类型 | `!` | 发散类型 |
| Inferred 类型 | `_` | 类型推断（Type Inference）占位 |

## 二、动态大小类型（DST）

DST 在编译期大小未知，必须置于指针之后：

- `dyn Trait`
- `[T]`
- `str`

通过 `&dyn Trait`、`&[T]`、`&str`、`Box<dyn Trait>` 等 fat pointer 使用。

详见 [Type System Advanced](../02_intermediate/20_type_system_advanced.md)。

## 三、内部可变性

内部可变性允许在不可变引用（Mutable Reference）后修改数据：

| 类型 | 适用场景 |
|:---|:---|
| `Cell<T>` | 单线程，只要求 `Copy` |
| `RefCell<T>` | 单线程，运行时（Runtime）借用（Borrowing）检查 |
| `Mutex<T>` | 多线程，互斥 |
| `RwLock<T>` | 多线程，读写锁 |
| `Atomic*` | 多线程，原子操作（Atomic Operations） |

## 四、子类型与变型

- 生命周期（Lifetimes）具有子类型关系：`'static: 'a`。
- 变型描述类型构造器对子类型的保留方式：协变、逆变、不变。

详见 [Subtyping and Variance](06_subtype_variance.md)。

## 五、Trait 与 Lifetime Bounds

类型参数可受约束：

```rust
fn foo<T: Clone + Send + 'a>(x: T) {}
```

- Trait bound：`T: Trait`
- Lifetime bound：`T: 'a`
- Higher-ranked trait bound (HRTB)：`for<'a> T: Trait<'a>`

## 六、类型强制转换

Rust 在特定位置自动执行类型强制（coercion）：

| 强制 | 示例 |
|:---|:---|
| 解引用（Reference） | `&String` → `&str` |
| 数组转切片（Slice） | `[T; N]` → `[T]` |
| 子类型 | `&'static str` → `&'a str` |
| Trait 对象 | `&T` → `&dyn Trait` |
| 函数项转指针 | `fn item` → `fn pointer` |

## 七、生命周期省略

函数签名中生命周期可省略，编译器按三条规则推导：

1. 每个 elided 输入参数获得独立生命周期。
2. 若只有一个输入生命周期，所有输出生命周期与之相同。
3. 若 `&self` 或 `&mut self` 存在，其生命周期赋给所有输出生命周期。

---

> **权威来源**: [Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html) · [Rust Reference — Dynamically Sized Types](https://doc.rust-lang.org/reference/dynamically-sized-types.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
