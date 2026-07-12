> **内容分级**: [参考级]
>
# 测验：C/C++ → Rust 基础知识对比
>
> **EN**: Quiz: C/C++ to Rust Foundations
> **Summary**: Embedded quiz for the C/C++ engineering-layer comparison files: RTTI, macros, exception safety, construction, friend, move semantics, and value/reference semantics.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [进阶]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L2 进阶概念
> **A/S/P 标记**: S — Structure
> **双维定位**: C×Eva
> **前置概念**:
>
> [RTTI](../04_types_and_conversions/05_rtti_and_dynamic_typing.md) ·
> [Preprocessor vs Macros](../06_macros_and_metaprogramming/05_c_preprocessor_vs_rust_macros.md) ·
> [Exception Safety](../03_error_handling/04_exception_safety_rust_cpp.md) ·
> [Construction](../00_traits/05_construction_and_initialization.md) ·
> [Friend vs Privacy](../05_modules_and_visibility/02_friend_vs_module_privacy.md) ·
> [Move Semantics](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) ·
> [Value vs Reference Semantics](../../01_foundation/03_values_and_references/02_value_vs_reference_semantics.md)
>
> **后置概念**: N/A
> **主要来源**:
> [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) ·
> [TRPL](https://doc.rust-lang.org/book/title-page.html) ·
> [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html) ·
> [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) ·
> [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) ·
> [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) ·
> [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) ·
> [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
---

> **Bloom 层级**: L2-L4
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题（能否编译 / 输出分析，本测验特色）+ 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`） 的 .md 落地形态组织，不引入 TOML 插件）

---

## 一、RTTI 与动态类型识别

本节聚焦「RTTI 与动态类型识别」，核心内容为问题 1：C++ `dynamic_cast` 和 Rust `Any…。

### 问题 1：🟡 C++ `dynamic_cast` 和 Rust `Any::downcast_ref` 的核心语义差异是什么？

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

本节聚焦「C 预处理器 vs Rust 宏」，核心内容为问题 2：C 预处理器 `#define SQUARE(x) ((x)…。

### 问题 2：🟡 C 预处理器 `#define SQUARE(x) ((x) * (x))` 与 Rust `macro_rules! square { ($x:expr) => { $x * $x } }` 的本质区别是什么？

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

「异常安全」部分的核心主题是问题 3：C++ 析构函数中抛出异常会发生什么？，本节展开说明。

### 问题 3：🔴 C++ 析构函数中抛出异常会发生什么？

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

「构造与初始化」部分的核心主题是问题 4：Rust 中如何为一个类型提供"默认构造函数"的等价物？，本节展开说明。

### 问题 4：🟢 Rust 中如何为一个类型提供"默认构造函数"的等价物？

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

本节聚焦「友元 vs 模块可见性」，核心内容为问题 5：Rust 中哪个可见性修饰符最接近 C++ `friend`…。

### 问题 5：🟡 Rust 中哪个可见性修饰符最接近 C++ `friend` 的"同一 crate 内亲密协作"场景？

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

本节专门讨论「Move 语义」下的问题 6：执行 `let s2 = s1;` 后，下面哪项对 Rust…。

### 问题 6：🟢 执行 `let s2 = s1;` 后，下面哪项对 Rust `String` 的描述是正确的？

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

本节专门讨论「值语义 vs 引用语义」下的问题 7：Python 中 `a = [1, 2, 3]; b = a…。

### 问题 7：🟡 Python 中 `a = [1, 2, 3]; b = a; b[0] = 99` 后 `a` 的值是什么？在 Rust 中要达到相同效果应该怎么做？

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

本节聚焦「综合应用」，核心内容为问题 8：一个 C++ 类管理动态内存，应遵循 Rule of Thr…。

### 问题 8：🔴 一个 C++ 类管理动态内存，应遵循 Rule of Three/Five/Zero。在 Rust 中，下面哪个描述最准确？

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

---

## 九、规范题型补充：单选 · 多选 · 判断

> 本节按四级题型规范补充单选、多选与判断题，知识点与
> [Exception Safety](../03_error_handling/04_exception_safety_rust_cpp.md)、
> [Move Semantics](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md)、
> [Preprocessor vs Macros](../06_macros_and_metaprogramming/05_c_preprocessor_vs_rust_macros.md) 权威页一致；
> 干扰项针对常见误解设计。

### 问题 9：🟡【单选】C++ 异常与 Rust panic 的关键设计区别是什么？

- A. 两者机制与定位完全相同
- B. C++ 异常用于常规错误处理、可被任意 `catch`；Rust panic 定位不可恢复错误，常规错误用 `Result` 显式传递
- C. Rust 的 panic 可以被静默忽略而不产生任何后果
- D. C++ 没有异常机制

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：两语言把"可恢复错误"放在不同位置：C++ 主流用异常（控制流隐式跳转），Rust 用 `Result` 值（控制流显式、类型系统强制处理）；panic 对应的是 C++ 中"违反前置条件/逻辑错误"的场景。C 错：默认 `unwind` 策略下未被捕获的 panic 终止当前线程，进程级 `panic = "abort"` 则直接中止——没有"静默忽略"。

</details>

---

### 问题 10：🟡【单选】Rust 的 `Drop` trait 与 C++ 析构函数的关系，下列哪项最准确？

- A. Rust 没有析构机制，堆内存靠泄漏回收
- B. `Drop::drop` 在值离开作用域时自动调用，与 C++ RAII 析构对应，同样保证确定性资源释放
- C. 必须手动调用 `x.drop()` 才会释放资源
- D. `Drop::drop` 可以返回 `Result` 报告释放失败

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：Rust 继承 RAII：所有者离开作用域即确定性 drop，无需 GC 也无 finally。C 有教学价值：`std::mem::drop(x)` 是**提前消耗所有权**（随后 x 不可再用），不是"调用析构方法后继续使用"——直接写 `x.drop()` 会被编译器拒绝（explicit destructor calls not allowed）。D 错：`drop(&mut self)` 无返回值，释放失败只能 panic 或记录。

</details>

---

### 问题 11：🔴【多选】下列 C/C++ 中常见的未定义行为（UB），哪些在 Rust 的**安全子集**中被编译期静态阻止？（选出所有正确项）

- A. 悬垂指针 / 悬垂引用
- B. 数据竞争
- C. 双重释放（double free）
- D. 整数溢出

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：借用检查器 + 所有权 + `Send`/`Sync` 分别封死这三类 UB：引用不能超出数据生命周期（A）、别名-可变分离保证无数据竞争（B）、移动语义 + 唯一所有者保证恰好释放一次（C）。D 有教学价值：整数溢出在 Rust 中**不是 UB**——debug 构建 panic、release 构建按定义良好的二进制补码环绕；它是"被定义的错误行为"，不属于"静态阻止的 UB"。

</details>

---

### 问题 12：🟢【判断】Rust 默认就是移动（move）语义，而 C++ 需要显式 `std::move`；移动后原变量在 Rust 中不可再使用，编译器强制执行这一点。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：`let s2 = s1;`（`s1: String`）在 Rust 中移动所有权，`s1` 随即失效，继续使用是编译错误。C++ 的 `std::move` 只是"允许移动"的转换，移动后源对象处于"有效但未指定"状态、仍可访问—— Rust 把 C++ 靠纪律维护的"moved-from 不可用"变成了编译期保证，消除了整类 use-after-move 缺陷。

</details>

---

### 问题 13：🟡【判断】Rust 的 `macro_rules!` 宏与 C 预处理器宏一样都是纯文本替换，因此二者的卫生性（hygiene）问题完全相同。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：C 预处理器在**文本**层面替换，发生在解析之前，因此有括号陷阱、多重求值、标识符意外捕获等经典问题；`macro_rules!` 在 **token/语法**层面工作，展开发生于解析之后，且默认**卫生**：宏内部引入的局部标识符不会与调用点同名标识符冲突。详见 [Preprocessor vs Macros](../06_macros_and_metaprogramming/05_c_preprocessor_vs_rust_macros.md) 的对比矩阵。

</details>
