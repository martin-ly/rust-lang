> **内容分级**: [参考级]
>
# 测验：C/C++ → Rust 基础知识对比
>
> **EN**: Quiz: C/C++ to Rust Foundations
> **Summary**: Embedded quiz for the C/C++ engineering-layer comparison files: RTTI, macros, exception safety, construction, friend, move semantics, and value/reference semantics.
>
> **受众**: [进阶]
> **层级**: L2 进阶概念
> **A/S/P 标记**: S — Structure
> **双维定位**: C×Eva
> **前置概念**:
>
> [RTTI](../04_types_and_conversions/25_rtti_and_dynamic_typing.md) ·
> [Preprocessor vs Macros](../06_macros_and_metaprogramming/26_c_preprocessor_vs_rust_macros.md) ·
> [Exception Safety](../03_error_handling/27_exception_safety_rust_cpp.md) ·
> [Construction](../00_traits/28_construction_and_initialization.md) ·
> [Friend vs Privacy](../05_modules_and_visibility/29_friend_vs_module_privacy.md) ·
> [Move Semantics](../../01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md) ·
> [Value vs Reference Semantics](../../01_foundation/03_values_and_references/19_value_vs_reference_semantics.md)
>
> **后置概念**: N/A
> **主要来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/) · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
---

> **Bloom 层级**: 理解 → 应用 → 分析

---

---

> **过渡**: 从 测验 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 测验 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 测验 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **反向推理 1**: 如果程序在 测验 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 测验 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 认知路径

> **认知路径**: 本节从 "测验" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 测验 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 测验 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与测验的适用边界。
5. **迁移应用**: 将 测验 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "测验 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 测验 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 测验 规则被违反的直接信号。

> **反命题 3**: "其他语言对 测验 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 测验 具有语言特有的形态。

## 一、RTTI 与动态类型识别

### 问题 1：C++ `dynamic_cast` 和 Rust `Any::downcast_ref` 的核心语义差异是什么？

- A. C++ 基于子类型关系，Rust 基于类型相等
- B. C++ 基于类型相等，Rust 基于子类型关系
- C. 两者都基于子类型关系
- D. 两者都基于类型相等

<details>
<summary>✅ 答案与解析</summary>

**答案：A**

C++ `dynamic_cast<T>(p)` 检查对象的动态类型是否是 `T` 的子类型；Rust `Any::downcast_ref::<T>()` 检查擦除前的类型是否与 `T` 完全相同。Rust 不支持子类型向下转换。

</details>

---

## 二、C 预处理器 vs Rust 宏

### 问题 2：C 预处理器 `#define SQUARE(x) ((x) * (x))` 与 Rust `macro_rules! square { ($x:expr) => { $x * $x } }` 的本质区别是什么？

- A. C 宏（Macro）在文本层面替换，Rust 宏在语法树层面操作
- B. C 宏（Macro）在语法树层面操作，Rust 宏在文本层面替换
- C. 两者都在文本层面替换
- D. 两者都在语法树层面操作

<details>
<summary>✅ 答案与解析</summary>

**答案：A**

C 预处理器做纯文本替换，不感知语法、类型和作用域；Rust `macro_rules!` 操作 token 树，展开后进入 AST 解析和类型检查，且具有卫生性。

</details>

---

## 三、异常安全

### 问题 3：C++ 析构函数中抛出异常会发生什么？

- A. 异常被静默忽略
- B. 调用 `std::terminate`
- C. 异常正常传播
- D. 程序进入未定义行为，但不一定终止

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

C++ 中，析构函数抛出异常（在栈展开过程中）会导致 `std::terminate`。因此析构函数通常必须标记为 `noexcept`。Rust 的 `Drop::drop` 签名不允许返回错误，从类型层面消除了这类问题。

</details>

---

## 四、构造与初始化

### 问题 4：Rust 中如何为一个类型提供"默认构造函数"的等价物？

- A. 定义一个名为 `new` 的构造函数
- B. 实现 `Default` trait
- C. 定义 `__init__` 方法
- D. 使用 `const fn` 作为构造函数

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

Rust 没有构造函数语言特性。`Default::default()` 是零参数构造的约定等价物。`new` 只是普通关联函数，`const fn` 用于编译期构造。

</details>

---

## 五、友元 vs 模块可见性

### 问题 5：Rust 中哪个可见性修饰符最接近 C++ `friend` 的"同一 crate 内亲密协作"场景？

- A. `pub`
- B. `pub(crate)`
- C. `pub(super)`
- D. `pub(in path)`

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

`pub(crate)` 允许整个 crate 访问，最接近 C++ 中把某个类声明为 `friend` 以实现 crate/模块（Module）内协作的场景，但 Rust 的方式不破坏封装边界。

</details>

---

## 六、Move 语义

### 问题 6：执行 `let s2 = s1;` 后，下面哪项对 Rust `String` 的描述是正确的？

- A. `s1` 和 `s2` 都指向同一个堆缓冲区
- B. `s1` 的内容被深拷贝到 `s2`
- C. 堆缓冲区的所有权（Ownership）从 `s1` 转移到 `s2`，`s1` 不能再使用
- D. `s1` 变为空字符串，`s2` 拥有原内容

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

Rust 的 move 是所有权（Ownership）转移。对于 `String`，转移的是指向堆缓冲区的指针/长度/容量，`s1` 在编译期被标记为无效，后续访问会被编译器拒绝。

</details>

---

## 七、值语义 vs 引用语义

### 问题 7：Python 中 `a = [1, 2, 3]; b = a; b[0] = 99` 后 `a` 的值是什么？在 Rust 中要达到相同效果应该怎么做？

- A. Python 中 `a` 不变；Rust 中 `let b = a;`
- B. Python 中 `a` 变为 `[99, 2, 3]`；Rust 中 `let b = &mut a;`
- C. Python 中 `a` 不变；Rust 中 `let b = &mut a;`
- D. Python 中 `a` 变为 `[99, 2, 3]`；Rust 中 `let b = a;`

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

Python 列表是引用（Reference）语义，`b = a` 让 `b` 和 `a` 指向同一对象。在 Rust 中，要使 `b` 修改影响 `a`，需要显式可变借用（Mutable Borrow） `let b = &mut a;`。

</details>

---

## 八、综合应用

### 问题 8：一个 C++ 类管理动态内存，应遵循 Rule of Three/Five/Zero。在 Rust 中，下面哪个描述最准确？

- A. 必须手动实现 `Drop`、`Clone`、`Copy` 三个 trait
- B. 只要字段实现了正确的 trait，复合类型自动获得对应能力
- C. Rust 没有对应机制，必须写 `unsafe` 代码
- D. 需要使用 `Box<T>` 包装所有字段

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

Rust 中复合类型的 `Drop`/`Clone`/`Copy` 行为由字段自动推导。如果字段是 `Vec<T>` 等已正确实现这些 trait 的类型，外层类型不需要手动实现。这与 C++ 的 Rule of Zero 对应，但由类型系统（Type System）强制执行。

</details>

---

> **Checklist**: 已覆盖 RTTI / 宏（Macro） / 异常安全 / 构造 / 友元 / Move / 值引用（Reference）语义 / 综合应用，共 8 题。
