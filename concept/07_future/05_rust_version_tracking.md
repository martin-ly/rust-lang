# Rust 形式模型演进跟踪（1.79–1.97+）

> **定位**: 本文件从**形式模型维度**跟踪 Rust 语言特性的演进，而非版本特性清单。仅收录对 Rust 的**所有权模型、类型系统、异步语义、Unsafe 边界**有结构性影响的特性。
> **原则**: 琐碎语法糖点到为止，聚焦"形式化语义发生了什么变化"。
> **更新频率**: 每 6 周对齐 stable release，每季度审计。
> **状态**: v1.4（2026-05-19 更新，对齐 Rust 1.95.0 stable + 1.96 beta 预览，权威来源对齐完成）
> **前置概念**: [Ownership](../01_foundation/01_ownership.md) · [Borrowing](../01_foundation/02_borrowing.md) · [Generics](../02_intermediate/02_generics.md) · [Async](../03_advanced/02_async.md) · [Unsafe](../03_advanced/03_unsafe.md)
> **后置概念**: [Formal Methods](./02_formal_methods.md) · [Evolution](./03_evolution.md)

---

> **Bloom 层级**: 分析 → 应用
>
## 〇、形式模型演进认知入口

```mermaid
mindmap
  root((Rust 形式模型演进<br/>1.79 → 1.97+))
    所有权与别名模型
      raw_op[&raw 操作符 1.82<br/>消除中间引用 UB]
      if_let_guards[if-let guards 1.95<br/>模式匹配条件细化]
      let_chains[let chains 1.88<br/>逻辑合取与模式绑定]
      get_disjoint[get_disjoint_mut 1.85<br/>编译期证明索引不重叠]
    类型系统扩展
      precise_capturing[use&lt;..&gt; precise capturing 1.82<br/>存在类型区域参数显化]
      trait_upcasting[Trait object upcasting 1.86<br/>子类型传递性闭合]
      infer_const[_ 推断 const generics 1.89<br/>HM 推断向常量扩展]
      assoc_bounds[Bounds on assoc types 1.79<br/>类型类约束组合传播]
    异步与效果系统
      async_closures[Async closures 1.85<br/>高阶函数异步扩展]
      rpit_capture[RPIT lifetime capture 2024Ed<br/>隐式→显式契约]
      gen_blocks[gen blocks 1.95 nightly<br/>同步协程语法糖]
    Unsafe 边界精细化
      unsafe_extern[unsafe extern + safe 1.82<br/>FFI 权限粒度细化]
      naked[naked functions 1.88<br/>形式化保证显式逃逸口]
      unsafe_op[unsafe_op_in_unsafe_fn 2024Ed<br/>调用者与实现者权限分离]
      as_ref_unchecked[as_ref_unchecked 1.95<br/>指针到引用零成本转换]
    编译期计算能力
      inline_const[inline const blocks 1.79<br/>表达式级编译期计算]
      const_asm[const in asm 1.82/1.87<br/>汇编与 Rust 控制流交互]
      cold_path[cold_path hint 1.95<br/>性能语义显式表达]
```

> **认知功能**: 此 mindmap 将 1.79–1.97+ 演进按**五维形式模型**结构化展开，叶节点标注版本号，支持读者按领域快速定位关注点并判断稳定状态。
>
> **使用建议**: 作为目录式入口按需展开；内存安全研究者优先关注"所有权与别名模型"，类型系统研究者优先关注"类型系统扩展"。
>
> **关键洞察**: `&raw`、`use<..>`、`unsafe_op_in_unsafe_fn` 分别代表别名模型、存在类型、安全契约三个核心方向的契约化演进。 [来源: 💡 原创分析]

> **认知路径**: 本 mindmap 将 1.79–1.97+ 的演进按**五维形式模型**组织。读者可按自身关注领域选择入口：内存安全研究者从"所有权与别名模型"进入，类型系统研究者从"类型系统扩展"进入，系统编程工程师从"Unsafe 边界精细化"进入。每个叶节点的后缀标注版本号，便于快速定位稳定状态。

---

## 一、演进总览：五个形式模型维度

```mermaid
graph TD
    F0[Rust 形式模型演进 1.79→1.95+] --> F1[所有权与别名模型]
    F0 --> F2[类型系统扩展]
    F0 --> F3[异步与效果系统]
    F0 --> F4[Unsafe 边界精细化]
    F0 --> F5[编译期计算能力]

    F1 --> F1a[&raw 操作符 1.82]
    F1 --> F1b[if-let guards 1.95]
    F1 --> F1c[let chains 1.88]
    F1 --> F1d[extract_if / get_disjoint_mut 1.85+]

    F2 --> F2a[use<..> precise capturing 1.82]
    F2 --> F2b[Trait object upcasting 1.86]
    F2 --> F2c[_ 推断 const generics 1.89]
    F2 --> F2d[关联类型约束传播 1.79]

    F3 --> F3a[async closures 1.85]
    F3 --> F3b[RPIT lifetime capture 2024 Edition]
    F3 --> F3c[gen blocks 1.95 nightly]

    F4 --> F4a[unsafe extern + safe 1.82]
    F4 --> F4b[naked functions 1.88]
    F4 --> F4c[unsafe_op_in_unsafe_fn 2024 Edition]
    F4 --> F4d[as_ref_unchecked 1.95]

    F5 --> F5a[inline const blocks 1.79]
    F5 --> F5b[const in asm 1.82/1.87]
    F5 --> F5c[cold_path hint 1.95]
```

> **认知功能**: 此 graph 将五维演进转化为**层级树状结构**，清晰展示特性归属与维度边界，建立"特性→维度→版本"的三级索引。
>
> **使用建议**: 对照后续各维度详细章节使用，快速定位特定版本的形式模型变更归属。
>
> **关键洞察**: "编译期计算能力"正在渗透其他维度（如 `const` in asm 影响 Unsafe 边界），预示 Rust 形式模型向统一化演进。 [来源: 💡 原创分析]

---

## 二、维度一：所有权与别名模型

### 2.1 `&raw const` / `&raw mut`（1.82 stable，RFC 2582）

**语法**: `&raw const expr` / `&raw mut expr` → `*const T` / `*mut T`

**形式化意义**: 消除了获取原始指针时的**中间引用创建**。在 `&expr as *const _` 中，若 `expr` 是未对齐的（如 `#[repr(packed)]` struct 字段），中间引用本身就是 UB。`&raw` 操作符直接创建原始指针，不经过引用类型，使别名模型的操作语义更精确。

**形式模型变化**:

- **前**: `&expr as *const _` = 创建 `&T` → 强制转换 `*const T`（中间态存在引用）
- **后**: `&raw const expr` = 直接创建 `*const T`（无中间态）
- **对应形式化**: Tree Borrows / Stacked Borrows 的别名规则中，`&raw` 不触发 borrow 检查器的引用创建事件

> **[来源: Rust Reference]** `&raw` operators avoid creating an intermediate reference.
> **[来源: RFC 2582]** 原始指针获取的语义澄清。

---

### 2.2 `if let` guards in match arms（1.95 stable）

**语法**: `pattern if let Some(x) = expr => { ... }`

**形式化意义**: 模式匹配的 **Guards 扩展**，允许在 match arm 内部进行进一步的模式细化。关键限制：guard **不算入**穷尽性检查，因为编译器无法证明 guard 条件覆盖所有值。

**形式模型变化**:

- 模式匹配的代数语义从"单一模式 → 分支"扩展为"模式 ∧ 条件 → 分支"
- 穷尽性检查（Exhaustiveness Checking）的判定算法需显式排除 guard arm
- 与 `let chains`（1.88）形成对偶：`let chains` 用于 `if` 条件的逻辑合取，`if let` guards 用于 match arm 的条件细化

> **[来源: Rust 1.95 Release Notes]** `if let` guards stabilize the ability to refine match arms with nested pattern bindings.

---

### 2.3 `let chains`（1.88 stable in 2024 Edition，RFC 2497）

**语法**: `if let Some(x) = foo && let Some(y) = bar && x > y { ... }`

**形式化意义**: 控制流中的**逻辑合取与模式绑定的统一**。将布尔表达式和模式匹配从语法层面融合，减少了嵌套层级。

**形式模型变化**:

- 条件表达式的语义从 "Expr ∧ Expr" 扩展为 "Expr ∧ LetBinding ∧ Expr"
- 绑定变量的作用域在逻辑合取的右侧延伸（类似 `&&` 的短路语义）
- 对形式化而言，这是 **Hindley-Milner 类型推断 + 模式匹配约束** 的组合扩展

> **[来源: Rust 1.88 Release Notes]** `let_chains` allows `&&`-chaining `let` statements inside `if` and `while`.

---

### 2.4 集合 API 的借用模型创新（1.85–1.95）

| API | 版本 | 形式化意义 |
|:---|:---|:---|
| `extract_if` / `pop_if` | 1.85+ | 在借用检查器约束下实现**条件性元素移除**，是 `drain_filter` 的稳定替代 |
| `get_disjoint_mut` | 1.85+ | 编译期证明多个索引不重叠，从而允许**同时获取多个可变引用**——所有权模型在集合操作中的新表达模式 |
| `Vec::push_mut` / `insert_mut` | 1.95 | **可变插入**：直接在容器内部构造元素，避免中间值的所有权转移 |

**形式化洞察**: `get_disjoint_mut` 是 Rust 借用检查器在**运行时数据结构**上的形式化证明能力的体现。编译器无法证明任意索引不重叠，但 API 设计通过运行时检查 + `unsafe` 内部实现，向外暴露安全的 `&mut` 引用。这是 **"形式化边界内推"** 的典型案例。

> **[来源: Rust Standard Library Docs]** `get_disjoint_mut` returns mutable references to multiple elements, checked at runtime for overlap.

---

## 三、维度二：类型系统扩展

### 3.1 `+ use<'lt>` precise capturing（1.82 stable，RFC 3617）

**语法**: `fn f() -> impl Trait + use<'a>`

**形式化意义**: **存在类型的区域参数显化**。`impl Trait`（RPIT）返回类型在 2024 Edition 之前隐式捕获所有输入生命周期，导致 API 契约不稳定。`use<..>` 语法允许显式声明捕获哪些生命周期，使存在类型的语义从"隐式闭包"变为"显式签名"。

**形式模型变化**:

- **前**: `impl Trait` 的捕获规则 = 隐式闭包（实现细节泄漏到公共接口）
- **后**: `impl Trait + use<'a>` = 显式捕获（接口契约精确化）
- **2024 Edition  Breaking Change**: RPIT 默认捕获行为变更，`cargo fix --edition` 自动迁移
- **对应形式化**: 向 System Fω 的**显式区域量化**（`∀<'a>` / `∃<'a>`）靠拢

> **[来源: RFC 3617]** Explicit lifetime capture in `impl Trait`.
> **[来源: Rust 2024 Edition Guide]** RPIT lifetime capture rules changed.

---

### 3.2 Trait object upcasting（1.86 stable）

**语法**: `dyn SubTrait` → `dyn SuperTrait`（隐式强制转换）

**形式化意义**: **子类型关系的传递性闭合**。此前 Trait object 的 upcasting 需要显式转换或中间 trait，现在编译器自动处理 vtable 的布局转换。

**形式模型变化**:

- 子类型关系（`<:`）在存在类型（`dyn Trait`）上的传递性得以体现
- vtable 布局从"单 trait"扩展为"trait + supertrait"的链式结构
- 对形式化验证工具（Kani/Verus）而言，vtable 的数学模型需更新以支持 upcasting

> **[来源: Rust 1.86 Release Notes]** Trait object upcasting allows implicit coercion from `dyn SubTrait` to `dyn SuperTrait`.

---

### 3.3 `_` 推断 const generics 参数（1.89 stable）

**语法**: `let x: Foo<_> = ...`（`_` 可由编译器推断为 const 参数）

**形式化意义**: **HM 类型推断向常量级别的扩展**。此前 const generics 参数必须显式提供，`_` 的加入使常量参数与类型参数在推断能力上趋于一致。

**形式模型变化**:

- HM 推断的约束求解从"类型变量"扩展到"常量变量"
- 常量参数的表达力提升，但推断的可判定性边界需重新评估

> **[来源: Rust 1.89 Release Notes]** `_` can infer const generic arguments.

---

### 3.4 Bounds on associated types in bounds（1.79 stable）

**语法**: `trait CopyIterator: Iterator<Item: Copy> {}`

**形式化意义**: **类型类（Type Class）约束的组合传播**。此前关联类型的约束需在 `where` 子句中单独声明，现在可直接在 trait bound 内嵌套。

**形式化洞察**: 这是 Haskell 类型类约束传播机制在 Rust 中的逐步对齐，减少了 boilerplate，但增加了约束求解的复杂度。

> **[来源: Rust 1.79 Release Notes]** Bounds on associated types in bounds.

---

## 四、维度三：异步与效果系统

### 4.1 Async closures（1.85 stable，RFC 3668）

**语法**: `async |x| { x.await }`

**形式化意义**: **高阶函数的异步扩展**。`AsyncFn` / `AsyncFnMut` / `AsyncFnOnce` trait 家族补齐了异步编程的类型系统拼图，使异步闭包可以作为 trait bound 使用。

**形式模型变化**:

- 闭包的类型系统从 `Fn(A) -> B` 扩展为 `AsyncFn(A) -> impl Future<Output = B>`
- `AsyncFn` 的 `call` 方法返回 `impl Future`，该 Future 可能借用闭包捕获的状态 → 调用后、Future 完成前，闭包不可再次调用
- **效果系统原型**: `AsyncFn` 可视为 Rust 向**显式效果追踪**迈出的第一步——函数签名中隐式携带了"异步效果"

**与同步闭包的对比**:

| 维度 | 同步 `Fn` | 异步 `AsyncFn` |
|:---|:---|:---|
| 调用语法 | `f(args)` | `f(args).await` |
| 返回类型 | `R` | `impl Future<Output = R>` |
| 捕获模式 | `&self` / `&mut self` / `self` | 同左，但返回 Future |
| 可重入性 | 调用后立即可再次调用 | Future 完成前不可重入 |

> **[来源: RFC 3668]** Async closures trait family.
> **[来源: Rust 1.85 Release Notes]** Async closures stabilized.

---

### 4.2 Rust 2024 Edition：RPIT lifetime capture 默认行为变更

**形式化意义**: 2024 Edition 的最核心 breaking change。`impl Trait` 返回类型现在**默认捕获所有输入生命周期**，此前不捕获。

**形式模型变化**:

- 存在类型的捕获规则从"最小捕获"变为"最大捕获"
- API 契约的稳定性提升（生命周期不会意外泄漏），但现有代码可能编译失败
- `cargo fix --edition` 自动添加 `+ use<'lt>` 以恢复旧行为
- **形式化洞察**: 这是 Rust 类型系统从"隐式推断"向"显式契约"演进的重要一步

> **[来源: Rust 2024 Edition Guide]** RPIT capture rules in 2024 Edition.

---

### 4.3 `gen` blocks（1.95 nightly，tracking）

**语法**: `gen move { yield expr; }` → `impl Iterator<Item = T>`

**形式化意义**: **同步协程（Coroutine）的语法糖**。`gen` block 在编译期被降阶为状态机（类似 `async` block 降阶为 `Future`），`yield` 暂停执行并产生值。

**形式模型变化**:

- 迭代器的实现方式从"手动状态机"扩展为"协程语法"
- 与 `async` 形成对偶：`async` = 协作式多任务（Future 状态机），`gen` = 协作式生成（Iterator 状态机）
- **注意**: `gen` block 是同步的，不能 `.await`。异步生成器（`Stream`）仍在 RFC 讨论中

> **[来源: rust-lang/rust #117078]** Gen blocks tracking issue.

---

## 五、维度四：Unsafe 边界精细化

### 5.1 `unsafe extern` blocks + `safe` 关键字（1.82 stable，RFC 3484）

**语法**:

```rust,ignore
unsafe extern "C" {
    safe fn printf(fmt: *const c_char, ...);  // 标记为 safe 的 FFI 函数
    fn malloc(size: usize) -> *mut c_void;    // 默认 unsafe
}
```

**形式化意义**: **FFI 边界的权限粒度细化**。此前 `extern` block 内的所有函数都是 unsafe 的，现在可以显式标记某些 FFI 函数为 `safe`（即调用者不需要 `unsafe {}` 块）。

**形式模型变化**:

- unsafe 契约的粒度从"块级"细化到"函数声明级"
- 这是 Rust 形式化中"安全边界内推"的继续：更多代码被纳入编译器的自动证明范围

> **[来源: RFC 3484]** `unsafe extern` blocks and `safe` keyword.

---

### 5.2 `naked_functions`（1.88 stable）

**语法**: `#[naked] fn f() { asm!(...); }`

**形式化意义**: **形式化保证的显式逃逸口**。naked 函数没有编译器生成的前导/后导代码，程序员完全控制汇编输出。这是 Rust 安全保证的明确边界——编译器在此**放弃所有自动证明**，程序员手动承担全部责任。

**形式模型变化**:

- 编译器的证明范围在 naked 函数处**显式截断**
- 与 `unsafe` 的关系：`#[naked]` 是更强烈的"无保证"标记，连栈帧管理都不由编译器负责

> **[来源: Rust 1.88 Release Notes]** Naked functions allow writing functions with no compiler-generated prologue/epilogue.

---

### 5.3 `unsafe_op_in_unsafe_fn`（2024 Edition 默认行为）

**形式化意义**: **调用者权限与实现者权限的分离**。在 2021 Edition 及之前，`unsafe fn` 的函数体隐式是 unsafe 的。2024 Edition 要求 `unsafe fn` 体内的 unsafe 操作仍需显式包裹在 `unsafe {}` 块中。

**形式模型变化**:

- `unsafe fn`: 标记"调用此函数需要 unsafe 权限"（约束**调用者**）
- `unsafe {}`: 标记"此块内的操作需要 unsafe 权限"（约束**实现者**）
- 权限分离使代码审查更清晰：每一行 unsafe 操作都可见
- 对应形式化：这是**安全契约的模块化**——契约声明与契约实现分离

> **[来源: Rust 2024 Edition Guide]** `unsafe_op_in_unsafe_fn` clarifies the separation between caller and implementer unsafe obligations.

---

### 5.4 `as_ref_unchecked` / `as_mut_unchecked`（1.95 stable）

**语法**: `ptr.as_ref_unchecked()` → `&T`

**形式化意义**: **指针到引用的零成本转换**，但放弃所有运行时检查。这是 unsafe 边界内"类型恢复"操作的标准化。

**形式模型变化**:

- 原始指针（`*const T`）到引用（`&T`）的转换，此前需 `unsafe { &*ptr }`，现在有更清晰的 API
- 对应形式化：内存模型中的"有效性（validity）"假设——调用者必须保证指针满足引用的所有不变量（对齐、非空、生命周期合法）

> **[来源: Rust 1.95 Release Notes]** Pointer `as_ref_unchecked` / `as_mut_unchecked` stabilized.

---

## 六、维度五：编译期计算能力

### 6.1 Inline const blocks（1.79 stable）

**语法**: `[u8; const { 4 + 4 }]` / `let x = const { std::mem::size_of::<u64>() };`

**形式化意义**: **常量求值与类型系统的交互扩展**。`const {}` 块可在任意表达式/类型位置插入编译期计算。

**形式模型变化**:

- 编译期计算（Const Eval）从"函数定义级"（`const fn`）扩展到"表达式级"
- 常量求值的能力边界直接影响类型系统的表达能力

---

### 6.2 Const in inline assembly（1.82/1.87 stable）

- 1.82: `const` immediates in inline assembly
- 1.87: jumps to Rust code from inline assembly

**形式化意义**: 内联汇编从"纯底层逃逸口"扩展为"与 Rust 控制流交互的构造"。跳转回 Rust 代码的能力使汇编片段可以参与 Rust 的类型安全控制流。

---

### 6.3 `core::hint::cold_path`（1.95 stable）

**语法**: `core::hint::cold_path()`

**形式化意义**: **性能语义的可表达性扩展**。向编译器传达路径冷热信息，帮助优化代码布局。虽然不改变语义，但扩展了程序员对编译器优化的**显式控制能力**。

> **[来源: Rust 1.95 Release Notes]** `cold_path` hint stabilized.

---

## 七、版本对比矩阵（形式模型视角）

| 形式模型维度 | 1.79 | 1.82 | 1.85 | 1.88 | 1.95 | 前沿（nightly）|
|:---|:---|:---|:---|:---|:---|:---|
| **所有权/别名** | `bounds on assoc types` | `&raw`, `unsafe extern`, `use<..>` | `extract_if`, `AsyncFn` | `let chains`, `naked` | `if let guards`, `as_ref_unchecked` | Tree Borrows 演进 |
| **类型系统** | inline const blocks | precise capturing | async closures, 2024 Ed | `_` infer const generics | mutable insert APIs | Effects 系统讨论 |
| **异步语义** | — | — | async closures 稳定 | let chains | — | async gen（RFC）|
| **Unsafe 边界** | — | `unsafe extern` + `safe` | 2024 Ed RPIT capture | naked functions | `unsafe_op` 默认 | Safety Tags RFC |
| **编译期计算** | inline const | const in asm | — | — | `cold_path` | `build-std` 进展 |

---

## 七、版本演进时间线

```mermaid
timeline
    title Rust 形式模型演进时间线 (1.79 – 1.97+)

    2024 Q2<br/>1.79 stable : inline const blocks : bounds on assoc types

    2024 Q3<br/>1.82 stable : &raw operators : unsafe extern + safe : use&lt;..&gt; precise capturing

    2024 Q4<br/>1.85 stable : extract_if / get_disjoint_mut : AsyncFn trait 家族 : async closures : 2024 Edition

    2025 Q1<br/>1.88 stable : let chains : naked functions : _ infer const generics

    2025 Q2<br/>1.95 stable : if-let guards : as_ref_unchecked : cold_path hint
    2025 Q2<br/>1.95 nightly : gen blocks

    2025 Q3<br/>1.96 beta : assert_matches! : core::range : NonZero iter : cargo config include

    2026+<br/>1.97+ nightly : Tree Borrows 演进 : Effects 系统讨论 : Safety Tags RFC : async gen / Stream
```

> **认知功能**: 此 timeline 将版本矩阵的**空间对比**转化为**时间演进**，揭示三个节奏：
>
> 1. **稳定节奏**：每 6 周一个 stable release，小步快跑
> 2. **Edition 节奏**：2024 Edition 是形式模型契约化的里程碑（RPIT capture、unsafe_op、let chains 三箭齐发）
> 3. **前沿节奏**：nightly 实验（gen blocks、Effects、Safety Tags）到 stable 通常需要 1–3 年
>
> 时间轴上的密度分布提示：2024 Q3–Q4 和 2025 Q1–Q2 是形式模型变更最密集的两个窗口，对应 Rust 2024 Edition 的发布周期。

---

## 八、形式化洞察：三个趋势

### 趋势 1：从隐式推断到显式契约
>
> `use<..>` precise capturing、2024 Edition RPIT 捕获规则、`unsafe_op_in_unsafe_fn` 都指向同一方向：Rust 类型系统从"编译器自动推断"向"程序员显式声明契约"演进。这使得形式化验证更容易（契约即规约），但增加了学习曲线。

### 趋势 2：效果系统（Effect System）的原型化
>
> `AsyncFn` trait 家族、`gen` blocks、`const {}` blocks 都在向**显式效果追踪**靠拢。虽然 Rust 尚未引入正式的 `effect` 关键字，但类型系统已经在通过 trait 和 edition 机制实现效果的分层。

### 趋势 3：Unsafe 边界的模块化与内推
>
> `unsafe extern` + `safe`、`unsafe_op_in_unsafe_fn`、`as_ref_unchecked` 表明 Unsafe 边界正在从"粗粒度块"向"细粒度函数/操作"演进。形式化验证工具（Kani/Verus）将因此获得更精确的验证目标。

---

## 九、待跟踪前沿（nightly / RFC 阶段）

| 特性 | 状态 | 形式化意义 |
|:---|:---|:---|
| **Tree Borrows 2025** | PLDI 2025 Distinguished Paper | 别名模型的工业级替代方案，Miri 默认启用 |
| **Safety Tags** | 2026 RFC 提交中 | unsafe 契约的机器可读格式，AI 生成代码的边界标注 |
| **Effects 系统** | 讨论中 | 显式追踪 IO、异步、异常等副作用的类型系统扩展 |
| **Never type (`!`)** | 部分稳定 | 底类型（Bottom type）的完整化，影响控制流类型论 |
| **async gen / Stream** | RFC 讨论中 | 异步协程的标准化，与 `gen` blocks 形成完整对偶 |
| **Specialization** | 部分实现 | 重叠 impl 的特化版本，需要类型论上的一致性保证 |
| **`build-std` 稳定化** | 推进中 | 标准库编译的标准化，影响 no_std 和嵌入式形式化 |

### 9.1 Rust 1.96 特性待跟踪表

> **[来源: Rust beta 1.96.0 2026-05-18; releases.rs; Cargo Book nightly; RFC tracking issues]** Rust 1.96.0 预计 2026-05-28 进入 stable，目前处于 beta 阶段。

| 特性 | 当前状态 | 影响维度 | 概念文件 | 优先级 | 1.96 预期 |
|:---|:---|:---|:---|:---:|:---|
| `return_type_notation` (RTN) | unstable | D2 类型 | `02_intermediate/01_traits.md` | 中 | 继续演进 |
| `associated_type_defaults` | unstable | D2 类型 | `02_intermediate/01_traits.md` | 中 | 继续演进 |
| `generic_const_exprs` | unstable | D1 计算 / D2 类型 | `02_intermediate/02_generics.md` | 中 | 继续演进 |
| `unsafe_fields` | experimental | D7 安全边界 | `03_advanced/03_unsafe.md` | **高** | 早期实验 |
| `new_range_syntax` (`..<`) | unstable | D1 计算 | `01_foundation/04_type_system.md` | 低 | 继续演进 |
| `effects` (keyword generics) | experimental | D3 控制流 / D7 安全 | `07_future/04_effects_system.md` | **高** | 长期演进 |
| `const_trait_impl` (`~const`) | unstable | D1 计算 | `01_foundation/01_ownership.md` | **高** | 继续演进 |
| `gen_blocks` | unstable | D3 控制流 | `03_advanced/02_async.md` | **高** | 继续演进 |
| `next_solver` | nightly，目标 2026 稳定 | D2 类型 / D5 编译期 | `02_intermediate/01_traits.md` §12 · `crates/c04_generic/next_solver_preview.rs` | **高** | 目标稳定 |
| `adt_const_params` | unstable | D2 类型 / D1 计算 | `02_intermediate/02_generics.md` | **高** | 目标稳定 |
| `min_generic_const_args` | unstable | D2 类型 / D1 计算 | `02_intermediate/02_generics.md` | **高** | 目标稳定 |
| `public_private_deps` | unstable · RFC 3516 · Help Wanted | D6 生态 | `concept/06_ecosystem/10_public_private_deps.md` | 中 | 目标稳定 |
| `cargo_script` | unstable · RFC 3502+3503 已批准 · nightly 已实现 | D6 生态 | `concept/06_ecosystem/09_cargo_script.md` | 中 | 目标稳定 |

> **1.96 Beta 已知变更**: Cargo 引入垃圾回收机制自动清理旧文件；`-Zscript` frontmatter 语法更新；`-Zwarnings` 新增 `build.warnings` 配置字段；`unstable-editions` 错误提示改进。

### 9.2 Rust 1.96 Beta 稳定化 API 详情

> **[来源: Rust 1.96.0 beta release notes 2026-05-18; doc.rust-lang.org/beta/releases.html]**

**标准库稳定化**:

| API | 类型 | 形式化意义 |
|:---|:---|:---|
| `<[T]>::element_offset` | 方法 | 计算元素在切片中的字节偏移，支持指针算术安全抽象 |
| `LazyCell::get_mut` | 方法 | 无初始化开销的可变访问，单线程懒加载缓存的可变性 |
| `LazyCell::force_mut` | 方法 | 强制初始化并返回可变引用，支持延迟初始化后的就地修改 |
| `LazyLock::get_mut` | 方法 | 多线程安全懒加载的可变访问（需 `&mut self`） |
| `LazyLock::force_mut` | 方法 | 多线程安全懒加载的强制初始化可变访问 |
| `std::iter::Peekable::next_if_map` | 方法 | 条件 peek + 映射组合，迭代器控制流的函数式抽象 |
| `std::iter::Peekable::next_if_map_mut` | 方法 | 上述方法的可变版本 |
| `impl TryFrom<char> for usize` | Trait impl | Unicode 标量值到机器字长的安全转换 |
| `f32/f64::consts::EULER_GAMMA` | 常量 | 欧拉-马歇罗尼常数，数学常数的编译期可用性 |
| `f32/f64::consts::GOLDEN_RATIO` | 常量 | 黄金比例常数 |
| `f32/f64::mul_add` (const) | const fn | 融合乘加运算的常量上下文可用，数值计算编译期优化 |
| x86 `avx512fp16` intrinsics | unsafe fn | AVX512 FP16 向量指令，AI/ML 推理的底层性能 |
| AArch64 NEON fp16 intrinsics | unsafe fn | ARM 半精度浮点向量指令，移动端 AI 加速 |

**Cargo 稳定化**:

| 特性 | 意义 |
|:---|:---|
| `config include` | 顶级配置支持加载额外配置文件，大型工作空间的配置模块化 |
| `pubtime` registry 字段 | 记录 crate 版本发布时间，支持基于时间的依赖解析策略 |
| TOML v1.1 解析 | Cargo.toml 和配置支持 TOML v1.1，但发布清单保持向后兼容 |
| `CARGO_BIN_EXE_<crate>` runtime | 运行时可用环境变量，支持测试中的二进制路径发现 |

**编译器/平台**:

- LLVM 20 升级
- `annotate-snippets` 替代 rustc 错误输出引擎
- 新增 Tier 3 目标: `riscv64im-unknown-none-elf`

**已覆盖的 stable 特性（1.95 及之前）**: `inline_const` · `async_fn_in_trait` · `impl_trait_in_assoc_type` · `let_chains` · `type_alias_impl_trait` · `async_closure` · `precise_capturing` · `trait_upcasting`

---

## 十、1.97 Nightly 前瞻跟踪

> **[来源: releases.rs 2026-05-18; rust-lang/rust GitHub]**

**预计稳定日期**: 2026-07-09 (约 52 天后)

**正在进行稳定化评审的 PR**:

| 特性 | PR | 状态 | 形式化意义 |
|:---|:---|:---|:---|
| `int_format_into` | #152902 | 94 天 · 需 FCP | 整数格式化写入预分配缓冲区，避免临时字符串分配，嵌入式/高性能场景关键优化 |
| `-Zinstrument-mcount` | #152544 | 102 天 · 等待作者 | LLVM 函数入口/出口计数插桩，性能分析基础设施 |
| `refcell_try_map` | #152122 | 102 天 · 等待作者 · 需 FCP | `RefCell::try_map` 允许在 borrow 期间进行条件性映射，函数式状态管理的安全抽象 |
| `proc_macro_value` | #152092 | 104 天 · 等待评审 · 需 FCP | 过程宏中获取字面量值的稳定 API，编译期元编程能力扩展 |
| `VecDeque::retain_back` (from `truncate_front`) | #151973 | 118 天 | 双端队列的后端保留/截断操作，与 `retain` 对称的 API 补全 |

**已在本 workspace 验证的 nightly 特性**:

- `gen_blocks` + `yield_expr`: c04_generic、c08_algorithms 已投入教学使用
- `never_type`: c02_type_system 深度专题
- `negative_impls` / `auto_traits`: c02_type_system、c04_generic 形式化演示
- `adt_const_params` / `min_generic_const_args`: c04_generic 扩展预览

**Miri 验证状态**: 12 个 crate 2,212+ 测试通过（Tree Borrows），详见 `reports/MIRI_VALIDATION_2026_05_18_COMPREHENSIVE.md`

---

## 十二、Rust 1.96.0 Beta 跟踪（2026-05-28 预计稳定）

> **[来源: GitHub rust-lang/rust #156512]** · **[来源: releases.rs]** · **[来源: Inside Rust Blog 2026-05-18]** ✅

**已确定稳定的新特性**:

| 特性 | 类别 | 项目覆盖 | 状态 |
|:---|:---|:---|:---:|
| `assert_matches!` / `debug_assert_matches!` | 标准库宏 | `docs/02_reference/quick_reference/assert_matches_guide.md` | ✅ 已创建 |
| `core::range` 补齐 (`Range`/`RangeFrom`/`RangeToInclusive` + 迭代器) | 标准库 API | `crates/c02_type_system/src/rust_196_features.rs` | ✅ 已更新 |
| `NonZero` 整数范围迭代 | 标准库 API | `crates/c02_type_system/src/rust_196_features.rs` | ✅ 已更新 |
| `impl From<bool> for {f32, f64}` | 标准库 trait | `crates/c02_type_system/src/rust_196_features.rs` | ✅ 已覆盖 |
| `unused_features` lint (warn-by-default) | 编译器 lint | `docs/06_toolchain/` | 🟡 待补充 |
| Cargo `frame-pointers` profile 选项 | 工具链 | `docs/06_toolchain/` | 🟡 待补充 |

**Project Goals 月度更新（2026-05-18）**:

- **流程变更**: Project Goals 从半年制改为年度制（2026 Goals）
- **cargo-script**: Cargo FCP 已结束，blocker 为 edition policy
- **BorrowSanitizer**: Shadow Stack 策略，RFC 起草中，RustConf 2026 演讲已入选
- **Const Generics**: `min_adt_const_params` 接近 RFC 最终规格
- **Rust for Linux**: 2026 RfL Roadmap 取代原目标
- **C++/Rust Interop**: Overloading 实验 PR 完成两轮 review

---

## 十一、长期演进跟踪表（P2 优先级）

| 特性 | 当前状态 | 预计稳定 | 项目覆盖 | 跟踪文件 |
|:---|:---:|:---:|:---:|:---|
| **Open Enums** | nightly 实验 | 2027+ | 🔴 缺失 | 待创建 `concept/07_future/open_enums_preview.md` |
| **BorrowSanitizer** | 原型阶段 | 2027+ | 🔴 缺失 | 待创建 `docs/05_guides/borrowsanitizer_preview.md` |
| **MC/DC Coverage** | rustc 跟踪中 (rust#124656) | 2026–2027 | 🔴 缺失 | `docs/04_research/safety_critical_alignment_2026.md` §5 |
| **cargo-semver-checks** | 社区工具，计划合并 cargo | 2026–2027 | 🔴 缺失 | 待加入工具链跟踪 |
| **Cargo plumbing commands** | 原型 | 2027+ | 🔴 缺失 | 待加入工具链跟踪 |
| **Safety Tags** | 设计讨论 | 2027+ | 🟡 跟踪 | `docs/05_guides/SAFETY_TAGS_GUIDE.md` |
| **derive(CoercePointee)** | RFC 前设计 | 2027+ | 🟡 跟踪 | `crates/c04_generic/src/derive_coerce_pointee_tracking.rs` |
| **并行前端编译** | nightly 可用 | 2026–2027 | 🟡 跟踪 | `docs/06_toolchain/parallel_frontend.md` |

---

## 十一、变更日志

| 版本 | 日期 | 变更 |
|:---|:---|:---|
| v1.0 | 2026-05-13 | 初始创建，对齐 Rust 1.95.0 stable，覆盖 1.79–1.95+ 五个形式模型维度 |
| v1.1 | 2026-05-18 | 补充 Next Solver 至 1.96 跟踪表；补充 `adt_const_params`/`min_generic_const_args`/`public_private_deps`/`cargo_script` 跟踪项 |
| v1.2 | 2026-05-18 | 网络对齐更新：1.96 beta 状态（2026-05-28 预计稳定）、cargo-script RFC 3502+3503 已批准、public/private deps RFC 3516 Help Wanted 状态、hickory CVE-2026-42254 记录 |
| v1.3 | 2026-05-18 | Miri 全 workspace 验证：12 个 crate 2,212+ 测试通过，修复 2 处真实 UB（c04_generic 未对齐读取、c07_process 未初始化内存）、1 处 gen block 逻辑错误（c08_algorithms）
| v1.4 | 2026-05-19 | 权威来源对齐冲刺完成：全项目 ~2,300+ Markdown 文件完成权威来源标注，concept/knowledge/docs/crates 100% 覆盖

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.4
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新: 2026-05-21
**状态**: ✅ 权威来源对齐完成 (Batch 8)
