> **内容分级**: [研究级]
>
# 未定义行为清单（Behavior Considered Undefined）

> **EN**: Behavior Considered Undefined
> **Summary**: Rust Reference 明确列出的未定义行为（UB）清单，覆盖数据竞争、指针别名、无效值、运行时假设等核心安全契约边界。 Rust Reference list of undefined behaviors, covering data races, pointer aliasing, invalid values, and runtime assumptions.
>
> **受众**: [专家]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [Atomics and Memory Ordering](../03_advanced/11_atomics_and_memory_ordering.md) · [Pointer Aliasing](../04_formal/03_ownership_formal.md)
> **后置概念**: [Miri](31_miri.md) · [Tree Borrows](36_tree_borrows_deep_dive.md) · [Inline Assembly](../03_advanced/13_inline_assembly.md)
> **定理链**: Unsafe Contract → UB 清单 → Soundness
> **主要来源**: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [LLVM — Undefined Behavior](https://llvm.org/docs/UndefinedBehavior.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [Rust Reference — The unsafe keyword](https://doc.rust-lang.org/reference/unsafe-keyword.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/)

---

## 一、核心原则

`unsafe` 关键字**不**改变“Rust 程序永远不得导致未定义行为”这一事实。它只是将避免 UB 的责任从编译器转移到了程序员。

- **Sound（健全）**: 任何 safe 代码与某段 unsafe 代码交互时都不会触发 UB。
- **Unsound（不健全）**: safe 代码可以错误使用该 unsafe 代码并触发 UB。

> **警告**: 下列清单**非穷尽**，未来可能增减。目前 Rust 尚未对 unsafe 代码建立完整的形式化语义模型。

---

## 二、UB 清单

### 1. 数据竞争（Data races）

多个线程同时访问同一内存位置，且至少一个是写操作，没有同步。

### 2. 访问悬垂或基于未对齐指针的 place

- **悬垂指针（dangling pointer）**: 指针指向的内存已不属于同一生存期内的分配。
- **未对齐指针（misaligned pointer）**: 解引用时指针未满足类型的对齐要求。

> 零大小类型（ZST）的指针永远不会悬垂，即使它是空指针。

### 3. 越界 place projection

字段访问、元组索引、数组/切片索引运算导致指针算术越界。

### 4. 破坏指针别名规则

- `&T` 指向的内存在其存活期间不可被修改（`UnsafeCell<U>` 内部除外）。
- `&mut T` 指向的内存不可被任何非派生自该引用的指针读写，且同一时间内不可存在其他引用。
- `Box<T>` 在别名规则中等价于 `&'static mut T`。

### 5. 修改不可变字节

- `const` 提升表达式可达的字节。
- `static` / `const` 初始化器中生命周期被延长到 `'static` 的借用可达的字节。
- 不可变绑定或不可变 `static` 拥有的字节（`UnsafeCell<U>` 内部除外）。
- 共享引用（以及通过 `Box`、复合类型字段传递的引用）可达的字节。

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
| 整数/浮点/原始指针 | 必须已初始化 |
| `str` | 与 `[u8]` 相同，必须已初始化 |
| `enum` | 必须有合法 discriminant，且对应变体字段有效 |
| `struct` / tuple / array | 所有字段/元素有效 |
| `union` | 细节尚未确定；safe 代码可构造的值一定有效 |
| 引用 / `Box<T>` | 对齐、非空、不悬垂、指向有效值 |
| 宽引用/Box/裸指针 metadata | 必须与 unsized tail 类型匹配（vtable 或有效 slice 长度） |
| 自定义有效范围类型 | 如 `NonNull<T>`、`NonZero<T>`，必须落在允许范围内 |

### 10. 错误使用内联汇编

参见 [Inline Assembly](../03_advanced/13_inline_assembly.md) 的安全规则。

### 11. 违反 Rust 运行时假设

- 当前大多数运行时假设未显式文档化。
- unwind 相关假设参见 panic 文档。
- 运行时期望 Rust 栈帧在局部变量析构完成前不会被释放；`longjmp` 等 C 函数可能违反该假设。

---

## 三、悬垂指针与未对齐指针细节

### 悬垂指针

引用或指针若指向的字节不全部属于同一生存期内的分配，则为悬垂。ZST 指针例外。

### 未对齐指针

place 基于未对齐指针，当且仅当对该 place 进行 load/store 时构成 UB。使用 `&raw const` / `&raw mut` 创建裸指针是允许的，但 `&` / `&mut` 要求字段类型对齐。

---

## 四、const 上下文中的额外要求

在 const 求值中，纯整数数据不能携带 provenance；持有指针数据的值必须要么无 provenance，要么所有字节是同一原始指针的正确顺序片段。

因此，在 const 上下文中将带 provenance 的指针转译为整数是 UB。

---

## 五、与其他语言的 UB 交互

未定义行为影响**整个程序**。调用 C 代码产生 UB 意味着整个 Rust 程序包含 UB；反之亦然。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Unsafe Rust](../03_advanced/03_unsafe.md) | UB 清单是 unsafe 契约的反向边界 |
| [Miri](31_miri.md) | Miri 用于在运行时检测部分 UB |
| [Tree Borrows](36_tree_borrows_deep_dive.md) | 指针别名规则的形式化模型 |
| [Inline Assembly](../03_advanced/13_inline_assembly.md) | 内联汇编有独立的正确性规则 |
| [Application Binary Interface](38_application_binary_interface.md) | ABI 错误调用可触发 UB |
