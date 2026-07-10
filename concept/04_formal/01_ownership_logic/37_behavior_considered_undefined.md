> **内容分级**: [研究级]
>
# 未定义行为清单（Behavior Considered Undefined）

> **EN**: Behavior Considered Undefined
> **Summary**: Rust Reference 明确列出的未定义行为（UB）清单，覆盖数据竞争、指针别名、无效值、运行时假设等核心安全契约边界。 Rust Reference list of undefined behaviors, covering data races, pointer aliasing, invalid values, and runtime assumptions.
>
> **受众**: [专家]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) · [Atomics and Memory Ordering](../../03_advanced/00_concurrency/11_atomics_and_memory_ordering.md) · [Pointer Aliasing](03_ownership_formal.md)
> **后置概念**: [Miri](../04_model_checking/31_miri.md) · [Tree Borrows](36_tree_borrows_deep_dive.md) · [Inline Assembly](../../03_advanced/05_inline_assembly/13_inline_assembly.md)
> **定理链**: Unsafe Contract → UB 清单 → Soundness
> **主要来源**: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [LLVM — Undefined Behavior](https://llvm.org/docs/UndefinedBehavior.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [Rust Reference — The unsafe keyword](https://doc.rust-lang.org/reference/unsafe-keyword.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)

---

---

## 认知路径

> **认知路径**: 本节从 "未定义行为清单（Behavior Considered Un" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 未定义行为清单（Behavior Considered Un 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 未定义行为清单（Behavior Considered Un 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与未定义行为清单（Behavior Considered Un的适用边界。
5. **迁移应用**: 将 未定义行为清单（Behavior Considered Un 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "未定义行为清单（Behavior Considered Un 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 未定义行为清单（Behavior Considered Un 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 未定义行为清单（Behavior Considered Un 规则被违反的直接信号。

> **反命题 3**: "其他语言对 未定义行为清单（Behavior Considered Un 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 未定义行为清单（Behavior Considered Un 具有语言特有的形态。

## 一、核心原则

`unsafe` 关键字**不**改变“Rust 程序永远不得导致未定义行为”这一事实。它只是将避免 UB 的责任从编译器转移到了程序员。 (Source: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html))

- **Sound（健全）**: 任何 safe 代码与某段 unsafe 代码交互时都不会触发 UB。
- **Unsound（不健全）**: safe 代码可以错误使用该 unsafe 代码并触发 UB。

(Soundness 定义见 [Rustonomicon — Soundness](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html))

> **警告**: 下列清单**非穷尽**，未来可能增减。目前 Rust 尚未对 unsafe 代码建立完整的形式化语义模型。

---

## 二、UB 清单

### 1. 数据竞争（Data races）

多个线程同时访问同一内存位置，且至少一个是写操作，没有同步。 (Source: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html))

### 2. 访问悬垂或基于未对齐指针的 place

- **悬垂指针（dangling pointer）**: 指针指向的内存已不属于同一生存期内的分配。
- **未对齐指针（misaligned pointer）**: 解引用（Reference）时指针未满足类型的对齐要求。

> 零大小类型（ZST）的指针永远不会悬垂，即使它是空指针。

### 3. 越界 place projection

字段访问、元组索引、数组/切片（Slice）索引运算导致指针算术越界。

### 4. 破坏指针别名规则

- `&T` 指向的内存在其存活期间不可被修改（`UnsafeCell<U>` 内部除外）。
- `&mut T` 指向的内存不可被任何非派生自该引用（Reference）的指针读写，且同一时间内不可存在其他引用。
- `Box<T>` 在别名规则中等价于 `&'static mut T`。

### 5. 修改不可变字节

- `const` 提升表达式可达的字节。
- `static` / `const` 初始化器中生命周期（Lifetimes）被延长到 `'static` 的借用（Borrowing）可达的字节。
- 不可变绑定或不可变 `static` 拥有的字节（`UnsafeCell<U>` 内部除外）。
- 共享引用（Reference）（以及通过 `Box`、复合类型字段传递的引用）可达的字节。

### 6. 调用编译器内建产生 UB

例如错误使用 `std::intrinsics` 中的某些内建函数。

### 7. 在当前平台不支持的特性上执行代码

使用 `target_feature` 启用当前 CPU 不支持的指令集，除非平台文档明确说明安全。

### 8. 错误调用约定或错误展开

- 调用函数的 ABI 不匹配。
- 跨过一个不允许展开的栈帧进行 unwind（例如将 `"C-unwind"` 函数当作 `"C"` 调用或转换函数指针）。

### 9. 产生无效值（Invalid values）

只要值被赋值、读取、传递、返回，即视为“产生”该值。以下值为无效：

| 类型 | 有效值要求 |
|:---|:---|
| `bool` | 只能是 `0` (`false`) 或 `1` (`true`) |
| `fn` 指针 | 必须非空 |
| `char` | 不能是 surrogate (`0xD800..=0xDFFF`)，且 ≤ `char::MAX` |
| `!` | 永远不存在 |
| 整数/浮点/原始指针（Raw Pointer） | 必须已初始化 |
| `str` | 与 `[u8]` 相同，必须已初始化 |
| `enum` | 必须有合法 discriminant，且对应变体字段有效 |
| `struct` / tuple / array | 所有字段/元素有效 |
| `union` | 细节尚未确定；safe 代码可构造的值一定有效 |
| 引用（Reference） / `Box<T>` | 对齐、非空、不悬垂、指向有效值 |
| 宽引用（Reference）/Box/裸指针 metadata | 必须与 unsized tail 类型匹配（vtable 或有效 slice 长度） |
| 自定义有效范围类型 | 如 `NonNull<T>`、`NonZero<T>`，必须落在允许范围内 |

### 10. 错误使用内联汇编

参见 [Inline Assembly](../../03_advanced/05_inline_assembly/13_inline_assembly.md) 的安全规则。

### 11. 违反 Rust 运行时假设

- 当前大多数运行时（Runtime）假设未显式文档化。
- unwind 相关假设参见 panic 文档。
- 运行时（Runtime）期望 Rust 栈帧在局部变量析构完成前不会被释放；`longjmp` 等 C 函数可能违反该假设。

---

## 三、悬垂指针与未对齐指针细节

### 悬垂指针

引用（Reference）或指针若指向的字节不全部属于同一生存期内的分配，则为悬垂。ZST 指针例外。

### 未对齐指针

place 基于未对齐指针，当且仅当对该 place 进行 load/store 时构成 UB。使用 `&raw const` / `&raw mut` 创建裸指针是允许的，但 `&` / `&mut` 要求字段类型对齐。

---

## 四、const 上下文中的额外要求

在 const 求值中，纯整数数据不能携带 provenance；持有指针数据的值必须要么无 provenance，要么所有字节是同一原始指针（Raw Pointer）的正确顺序片段。

因此，在 const 上下文中将带 provenance 的指针转译为整数是 UB。

---

## 五、与其他语言的 UB 交互

未定义行为影响**整个程序**。调用 C 代码产生 UB 意味着整个 Rust 程序包含 UB；反之亦然。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | UB 清单是 unsafe 契约的反向边界 |
| [Miri](../04_model_checking/31_miri.md) | Miri 用于在运行时（Runtime）检测部分 UB |
| [Tree Borrows](36_tree_borrows_deep_dive.md) | 指针别名规则的形式化模型 |
| [Inline Assembly](../../03_advanced/05_inline_assembly/13_inline_assembly.md) | 内联汇编有独立的正确性规则 |
| [Application Binary Interface](../05_rustc_internals/38_application_binary_interface.md) | ABI 错误调用可触发 UB |

---

> **权威来源**: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference — The unsafe keyword](https://doc.rust-lang.org/reference/unsafe-keyword.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) · [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)
