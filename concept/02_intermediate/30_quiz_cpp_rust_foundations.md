# 测验：C/C++ → Rust 基础知识对比
>
> **EN**: Quiz: C/C++ to Rust Foundations
> **Summary**: Embedded quiz for the C/C++ engineering-layer comparison files: RTTI, macros, exception safety, construction, friend, move semantics, and value/reference semantics.
>
> **受众**: [进阶]
> **层级**: L2 进阶概念
> **A/S/P 标记**: S — Structure
> **双维定位**: C×Eva
> **前置概念**: [RTTI](25_rtti_and_dynamic_typing.md) · [Preprocessor vs Macros](26_c_preprocessor_vs_rust_macros.md) · [Exception Safety](27_exception_safety_rust_cpp.md) · [Construction](28_construction_and_initialization.md) · [Friend vs Privacy](29_friend_vs_module_privacy.md) · [Move Semantics](../01_foundation/23_move_semantics.md) · [Value vs Reference Semantics](../01_foundation/19_value_vs_reference_semantics.md)
> **后置概念**: N/A
---

> **Bloom 层级**: 理解 → 应用 → 分析

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

- A. C 宏在文本层面替换，Rust 宏在语法树层面操作
- B. C 宏在语法树层面操作，Rust 宏在文本层面替换
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

`pub(crate)` 允许整个 crate 访问，最接近 C++ 中把某个类声明为 `friend` 以实现 crate/模块内协作的场景，但 Rust 的方式不破坏封装边界。

</details>

---

## 六、Move 语义

### 问题 6：执行 `let s2 = s1;` 后，下面哪项对 Rust `String` 的描述是正确的？

- A. `s1` 和 `s2` 都指向同一个堆缓冲区
- B. `s1` 的内容被深拷贝到 `s2`
- C. 堆缓冲区的所有权从 `s1` 转移到 `s2`，`s1` 不能再使用
- D. `s1` 变为空字符串，`s2` 拥有原内容

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

Rust 的 move 是所有权转移。对于 `String`，转移的是指向堆缓冲区的指针/长度/容量，`s1` 在编译期被标记为无效，后续访问会被编译器拒绝。

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

Python 列表是引用语义，`b = a` 让 `b` 和 `a` 指向同一对象。在 Rust 中，要使 `b` 修改影响 `a`，需要显式可变借用 `let b = &mut a;`。

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

Rust 中复合类型的 `Drop`/`Clone`/`Copy` 行为由字段自动推导。如果字段是 `Vec<T>` 等已正确实现这些 trait 的类型，外层类型不需要手动实现。这与 C++ 的 Rule of Zero 对应，但由类型系统强制执行。

</details>

---

> **Checklist**: 已覆盖 RTTI / 宏 / 异常安全 / 构造 / 友元 / Move / 值引用语义 / 综合应用，共 8 题。
