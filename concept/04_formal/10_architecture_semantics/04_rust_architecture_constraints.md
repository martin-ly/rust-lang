> **内容分级**: [专家级]
>
> **代码状态**: ✅ 含可编译示例与编译错误反例

# Rust 架构语义约束（Rust Architecture Semantics Constraints）

> **EN**: Rust Architecture Semantics Constraints
> **Summary**: How Rust's module system, crate boundaries, visibility rules, ABI, and workspace mechanism constrain and shape software architecture semantics.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 系统分析 Rust 的模块系统、crate 边界、可见性规则、ABI 与 workspace 机制如何**约束**软件架构的语义——哪些架构不变量可以被编译器强制执行，哪些仍需工程自律。
> **前置概念**: [Module System](../../02_intermediate/05_modules_and_visibility/01_module_system.md) · [ABI](../05_rustc_internals/05_application_binary_interface.md) · [Software Architecture Formalization](01_software_architecture_formalization.md) · [Async/Await](../../03_advanced/01_async/01_async.md)
> **后置概念**: [Architecture Pattern Semantics](02_architecture_pattern_semantics.md) · [Architecture Refinement](03_architecture_refinement.md) · [Cargo Workspaces](../../06_ecosystem/01_cargo/14_cargo_workspaces.md)

---

> **来源**: [Rust Reference — Items and Visibility](https://doc.rust-lang.org/reference/visibility-and-privacy.html) ·
> [Rust Reference — Orphan Rules](https://doc.rust-lang.org/reference/items/traits.html#orphan-rules) ·
> [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) ·
> [Cargo Book — Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) ·
> [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

> **权威来源 / Provenance**: 本节 Rust 架构约束分析主要基于 Rust Reference（Items and Visibility、Orphan Rules）、Rust API Guidelines 与 Cargo Book；软件架构理论基础参考 Shaw & Garlan (1996)、Garlan & Shaw (1993)、Medvidovic & Taylor (2000)、Wermelinger (1994)、ISO/IEC/IEEE 42010:2022 与 ACME/Wright/Rapide 等经典 ADL 工作。
>
> - **Shaw & Garlan (1996)** — *Software Architecture: Perspectives on an Emerging Discipline*. Prentice Hall. [PDF](https://www.cs.cmu.edu/~search/articles/books/SA.book.pdf)
> - **Garlan & Shaw (1993)** — *An Introduction to Software Architecture*. [https://doi.org/10.1142/9789812813032_0001](https://doi.org/10.1142/9789812813032_0001)
> - **Medvidovic & Taylor (2000)** — *A Classification and Comparison Framework for Software Architecture Description Languages*. [https://doi.org/10.1109/32.825767](https://doi.org/10.1109/32.825767)
> - **Wermelinger (1994)** — *Formal Specification of Software Architecture*. [https://doi.org/10.1016/0167-6423(94)00022-5](https://doi.org/10.1016/0167-6423(94)00022-5)
> - **ISO/IEC/IEEE 42010:2022** — *Software and Systems Engineering — Architecture Description*. ISO, 2022. [https://www.iso.org/standard/74296.html](https://www.iso.org/standard/74296.html)
> - **Garlan, Monroe & Wile (1997)** — *ACME: An Architecture Description Interchange Language*. In *Proceedings of CASCON'97*, 169–183.
> - **Allen (1997)** — *A Formal Approach to Software Architecture*. Ph.D. thesis, Carnegie Mellon University. (Wright ADL based on CSP.)
> - **Luckham et al. (1995)** — *Specification and Analysis of System Architecture Using Rapide*. IEEE Transactions on Software Engineering, 21(4), 336–355. [https://doi.org/10.1109/32.385970](https://doi.org/10.1109/32.385970)
> - **Rust Reference — Items and Visibility** — [https://doc.rust-lang.org/reference/visibility-and-privacy.html](https://doc.rust-lang.org/reference/visibility-and-privacy.html)
> - **Rust Reference — Orphan Rules** — [https://doc.rust-lang.org/reference/items/traits.html#orphan-rules](https://doc.rust-lang.org/reference/items/traits.html#orphan-rules)
> - **RustBelt: Securing the Foundations of the Rust Programming Language** (Jung et al., POPL 2018) — [https://plv.mpi-sws.org/rustbelt/popl18/](https://plv.mpi-sws.org/rustbelt/popl18/)
> - **Rust RFC 1105 — API Evolution** — [https://rust-lang.github.io/rfcs/1105-api-evolution.html](https://rust-lang.github.io/rfcs/1105-api-evolution.html)
> - **cargo-semver-checks** — [https://crates.io/crates/cargo-semver-checks](https://crates.io/crates/cargo-semver-checks)
> - **Rust Reference — External Blocks** — [https://doc.rust-lang.org/reference/items/external-blocks.html](https://doc.rust-lang.org/reference/items/external-blocks.html)

## 📑 目录

- [Rust 架构语义约束（Rust Architecture Semantics Constraints）](#rust-架构语义约束rust-architecture-semantics-constraints)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 模块系统作为封装与可见性机制](#11-模块系统作为封装与可见性机制)
    - [1.2 Crate 边界：编译、隐私与语义版本](#12-crate-边界编译隐私与语义版本)
    - [1.3 Workspace：产品线与架构耦合](#13-workspace产品线与架构耦合)
    - [1.4 ABI 与跨边界契约](#14-abi-与跨边界契约)
    - [1.5 类型系统对架构不变量的强制执行](#15-类型系统对架构不变量的强制执行)
  - [二、架构不变量 → Rust 机制映射表](#二架构不变量--rust-机制映射表)
  - [三、Rust 示例](#三rust-示例)
    - [3.1 分层架构的可见性实现](#31-分层架构的可见性实现)
    - [3.2 六边形架构的端口-适配器实现](#32-六边形架构的端口-适配器实现)
  - [四、反例与边界](#四反例与边界)
    - [4.1 反例：`pub` 但内部类型泄漏](#41-反例pub-但内部类型泄漏)
    - [4.2 反例：crate 边界未阻止语义版本破坏](#42-反例crate-边界未阻止语义版本破坏)
    - [4.3 边界：孤儿规则限制跨 crate 的 trait 实现](#43-边界孤儿规则限制跨-crate-的-trait-实现)
    - [4.4 反例：冲突的 trait 实现触发 `E0119`](#44-反例冲突的-trait-实现触发-e0119)
  - [五、相关概念](#五相关概念)
  - [六、嵌入式测验（Embedded Quiz）](#六嵌入式测验embedded-quiz)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)
  - [权威来源索引](#权威来源索引)

---

## 一、核心概念

### 1.1 模块系统作为封装与可见性机制

Rust 的模块系统不是文件系统，而是**独立的命名空间与可见性层级**。关键可见性修饰符：

```text
可见性谱系:
  pub              : 完全公开
  pub(crate)       : 当前 crate 内可见
  pub(super)       : 父模块可见
  pub(in path)     : 指定路径内可见
  （默认）         : 当前模块及其子模块可见
```

这意味着**依赖方向可以被编译器强制**：若 `presentation` 模块只通过 `pub(in crate::application)` 暴露接口，则 `presentation` 无法被 `infrastructure` 直接引用，从而支撑分层架构。

### 1.2 Crate 边界：编译、隐私与语义版本

Crate 是 Rust 的三重边界：

1. **编译边界**：每个 crate 单独编译成 rlib/dylib，生成稳定中间产物；
2. **隐私边界**：`pub(crate)` 不会跨 crate 泄露；
3. **语义版本边界**：crate 作为发布单元，其 public API 变更受 semver 约束。

形式化上，crate 边界把系统划分为若干**信息隐藏单元**，与 Parnas 的模块化原则一致。

### 1.3 Workspace：产品线与架构耦合

Cargo workspace 允许一组 crate 共享 `Cargo.lock` 和 target 目录，但**不共享 privacy 边界**。*workspace 是构建产物组织，不是运行时架构单元*。滥用 workspace 共享内部类型会导致隐式跨 crate 耦合。

### 1.4 ABI 与跨边界契约

`extern "C"` 与 `#[repr(C)]` 定义了 Rust 与其他语言/运行时交互的**二进制契约**。ABI 是架构语义的物理承载：结构体布局、调用约定、符号可见性都必须显式约定，否则跨边界行为未定义。

### 1.5 类型系统对架构不变量的强制执行

- **Orphan rules**：限制 trait 实现的定义位置，防止多个 crate 为同一类型实现同一 trait，保证全局一致性；
- **Coherence**：确保任意类型+trait 组合最多一个 impl，使架构中的抽象替换是确定性的；
- **`Send`/`Sync`**：把并发安全从文档约定提升为类型检查。

---

## 二、架构不变量 → Rust 机制映射表

| 架构不变量 | Rust 机制 | 强制程度 |
|---|---|---|
| 分层依赖方向 | `pub(in path)` / module visibility | 编译期 |
| 接口与实现分离 | trait / impl | 编译期 |
| 信息隐藏 | `pub` 层级、crate 边界 | 编译期 |
| 跨语言边界契约 | `extern "C"`、`#[repr(C)]` | 链接期/运行时 |
| 全局一致性 | orphan rules、coherence | 编译期 |
| 并发安全边界 | `Send`/`Sync` | 编译期 |
| 版本兼容 | semver + cargo-semver-checks | 工程/工具 |

---

## 三、Rust 示例

### 3.1 分层架构的可见性实现

```rust
// crate::layered 内部：presentation 只能依赖 application
mod application {
    pub(in crate::layered) fn use_case() {}
}

mod infrastructure {
    // 无法访问 presentation，因为 presentation 未对其公开
}

mod presentation {
    use crate::layered::application::use_case;
    pub fn handle() { use_case(); }
}
```

### 3.2 六边形架构的端口-适配器实现

```rust
// domain 定义端口（trait），不依赖外部 crate
trait UserRepository {
    fn find(&self, id: u64) -> Option<String>;
}

// infrastructure 提供适配器
struct SqlUserRepository;
impl UserRepository for SqlUserRepository {
    fn find(&self, id: u64) -> Option<String> { Some(format!("user-{id}")) }
}

// application 只依赖 domain 端口
fn greet_user(repo: &dyn UserRepository, id: u64) -> String {
    match repo.find(id) {
        Some(name) => format!("Hello, {name}"),
        None => "Unknown".into(),
    }
}
```

---

## 四、反例与边界

### 4.1 反例：`pub` 类型泄漏私有字段类型

公开结构体的字段若使用 crate 外部无法命名的私有类型，编译器会拒绝这种“private-in-public”泄漏：

```rust,compile_fail
mod secret {
    struct InternalToken; // 仅模块内可见，完全私有
}

// ❌ 公开类型泄漏了私有字段类型
pub struct TokenIssuer {
    pub token: secret::InternalToken, //~ ERROR struct `InternalToken` is private
}

fn main() {}
```

> 架构含义：crate 的公开 API 是其架构契约。任何 `pub` 结构体的字段类型都必须是外部可调用的，否则下游组件无法命名或构造该契约，导致信息隐藏边界被意外破坏。
>
> 说明：若内部类型使用 `pub(crate)`，现代 Rust 会触发 `private_interfaces` lint（默认 warn）；本例使用完全私有类型以在 `compile_fail` 中直接得到硬错误。

### 4.2 反例：crate 边界未阻止语义版本破坏

公开函数签名变更（如参数类型改变）即使 crate 边界完整，也会破坏下游编译。Rust 编译器强制 API 兼容，但不强制**语义版本**；需配合 `cargo-semver-checks`。

### 4.3 边界：孤儿规则限制跨 crate 的 trait 实现

[Rust Reference — Orphan Rules](https://doc.rust-lang.org/reference/items/traits.html#orphan-rules) 规定：不能为在当前 crate 外部定义的类型实现外部 trait，否则多个 crate 可能为同一类型+trait 组合提供相互冲突的实现，破坏全局一致性。

```rust,compile_fail
// 错误：不能为外部类型实现外部 trait（违反 orphan rules）
impl std::fmt::Display for std::vec::Vec<u8> {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { Ok(()) }
}

fn main() {}
```

> 架构含义：orphan rules 把 trait 实现的定义位置约束为“本地类型或本地 trait 至少占一个”，从而保证跨 crate 组合时任意抽象替换都是确定性的。

### 4.4 反例：冲突的 trait 实现触发 `E0119`

`coherence` 规则保证任意类型+trait 组合最多只有一个 `impl`。以下代码同时声明 blanket impl 与专门化 impl，导致冲突：

```rust,compile_fail
trait Drawable {}

// 为所有类型提供 blanket 实现
impl<T> Drawable for T {}

// ❌ 冲突：u32 已被上面的 blanket impl 覆盖
impl Drawable for u32 {} //~ ERROR E0119: conflicting implementations of trait `Drawable` for type `u32`

fn main() {}
```

> 架构含义：coherence 是架构组合的全局一致性保证。多个 crate 或模块若能为同一类型实现同一 trait，替换抽象实现时将产生不确定性，破坏架构的可推断性与可替换性。

---

## 五、相关概念

- [Module System](../../02_intermediate/05_modules_and_visibility/01_module_system.md)
- [ABI](../05_rustc_internals/05_application_binary_interface.md)
- [Software Architecture Formalization](01_software_architecture_formalization.md)
- [Architecture Pattern Semantics](02_architecture_pattern_semantics.md)
- [Cargo Workspaces](../../06_ecosystem/01_cargo/14_cargo_workspaces.md)

---

## 六、嵌入式测验（Embedded Quiz）

1. **`pub(in crate::app)` 与 `pub(crate)` 的区别是什么？**（理解层）
2. **为什么 workspace 成员之间不共享 privacy 边界？**（分析层）
3. **Orphan rules 对架构可组合性有什么影响？**（分析层）
4. **`extern "C"` 在架构语义中承担什么角色？**（应用层）
5. **Rust 的模块系统能否完全替代架构审查？**（评价层）

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((Rust 架构语义约束))
    模块系统
      pub
      pub(crate)
      pub(in path)
    Crate 边界
      编译边界
      隐私边界
      语义版本边界
    Workspace
      共享依赖
      不共享隐私
    ABI
      extern C
      repr C
    类型系统
      Orphan Rules
      Coherence
      Send/Sync
```

---

## 权威来源索引

- [Rust Reference — Items and Visibility](https://doc.rust-lang.org/reference/visibility-and-privacy.html)
- [Rust Reference — Orphan Rules](https://doc.rust-lang.org/reference/items/traits.html#orphan-rules)
- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
- [Cargo Book — Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)
- [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
- **Shaw & Garlan (1996)** — *Software Architecture: Perspectives on an Emerging Discipline*. [PDF](https://www.cs.cmu.edu/~search/articles/books/SA.book.pdf)
- **Garlan & Shaw (1993)** — *An Introduction to Software Architecture*. [https://doi.org/10.1142/9789812813032_0001](https://doi.org/10.1142/9789812813032_0001)
- **Medvidovic & Taylor (2000)** — *A Classification and Comparison Framework for Software Architecture Description Languages*. [https://doi.org/10.1109/32.825767](https://doi.org/10.1109/32.825767)
- **Wermelinger (1994)** — *Formal Specification of Software Architecture*. [https://doi.org/10.1016/0167-6423(94)00022-5](https://doi.org/10.1016/0167-6423(94)00022-5)
- **ISO/IEC/IEEE 42010:2022** — *Software and Systems Engineering — Architecture Description*. [https://www.iso.org/standard/74296.html](https://www.iso.org/standard/74296.html)
- **Garlan, Monroe & Wile (1997)** — *ACME: An Architecture Description Interchange Language*. In *Proceedings of CASCON'97*, 169–183.
- **Allen (1997)** — *A Formal Approach to Software Architecture*. Ph.D. thesis, Carnegie Mellon University. (Wright ADL based on CSP.)
- **Luckham et al. (1995)** — *Specification and Analysis of System Architecture Using Rapide*. IEEE Transactions on Software Engineering, 21(4), 336–355. [https://doi.org/10.1109/32.385970](https://doi.org/10.1109/32.385970)
- **RustBelt: Securing the Foundations of the Rust Programming Language** (Jung et al., POPL 2018) — [https://plv.mpi-sws.org/rustbelt/popl18/](https://plv.mpi-sws.org/rustbelt/popl18/)
- **Rust RFC 1105 — API Evolution** — [https://rust-lang.github.io/rfcs/1105-api-evolution.html](https://rust-lang.github.io/rfcs/1105-api-evolution.html)
- **cargo-semver-checks** — [https://crates.io/crates/cargo-semver-checks](https://crates.io/crates/cargo-semver-checks)
- **Rust Reference — External Blocks** — [https://doc.rust-lang.org/reference/items/external-blocks.html](https://doc.rust-lang.org/reference/items/external-blocks.html)
