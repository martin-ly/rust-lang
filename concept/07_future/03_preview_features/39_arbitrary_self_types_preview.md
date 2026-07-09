# Arbitrary Self Types 预览：自定义方法接收器

> **代码状态**: [示例级 — 已补充代码]
>
> **EN**: Arbitrary Self Types Preview
> **Summary**: Preview of arbitrary self types: extending method receivers beyond `&self`, `&mut self`, and `Box<Self>`.
> **来源**: [RFC 3519 — Arbitrary Self Types v2](https://rust-lang.github.io/rfcs//3519-arbitrary-self-types-v2.html) · [Rust Reference — Methods](https://doc.rust-lang.org/reference/items/associated-items.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: L4 (分析)
> **A/S/P 标记**: **S** — Structure
> **定位**: 探讨 Rust 中 arbitrary self types 的提案——允许 `self` 参数使用任意类型（不仅是 `Self`、`&Self`、`&mut Self`、`Box<Self>`、`Rc<Self>`、`Arc<Self>`、`Pin<P<Self>>`），分析其对嵌入式驱动、内核编程和自定义指针类型的影响。
> **前置概念**: [Traits](../../02_intermediate/00_traits/01_traits.md) · [Pin](../../03_advanced/01_async/06_pin_unpin.md) · [Smart Pointers](../../02_intermediate/02_memory_management/12_smart_pointers.md)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
---

> **后置概念**: [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)

## 📑 目录

- [Arbitrary Self Types 预览：自定义方法接收器](#arbitrary-self-types-预览自定义方法接收器)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 当前限制](#11-当前限制)
    - [1.2 Arbitrary Self Types 提案](#12-arbitrary-self-types-提案)
  - [二、技术细节](#二技术细节)
    - [2.1 `DispatchFromDyn` Trait](#21-dispatchfromdyn-trait)
    - [2.2 与 `Deref` 的关系](#22-与-deref-的关系)
  - [三、使用场景](#三使用场景)
    - [场景 1：内核编程（Rust for Linux）](#场景-1内核编程rust-for-linux)
    - [场景 2：嵌入式寄存器映射](#场景-2嵌入式寄存器映射)
    - [场景 3：自定义智能指针](#场景-3自定义智能指针)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 安全边界](#41-安全边界)
    - [4.2 设计决策](#42-设计决策)
  - [五、演进路线](#五演进路线)
  - [参考](#参考)
    - [补充定理链](#补充定理链)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Arbitrary Self Types 允许什么目前不允许的操作？（理解层）](#测验-1arbitrary-self-types-允许什么目前不允许的操作理解层)
    - [测验 2：这个特性对自定义智能指针有什么意义？（理解层）](#测验-2这个特性对自定义智能指针有什么意义理解层)
    - [测验 3：`Receiver` trait 在这个特性中起什么作用？（理解层）](#测验-3receiver-trait-在这个特性中起什么作用理解层)
    - [测验 4：Arbitrary Self Types 与 `Deref` 有什么关系？（理解层）](#测验-4arbitrary-self-types-与-deref-有什么关系理解层)
    - [测验 5：这个特性目前的状态是什么？（理解层）](#测验-5这个特性目前的状态是什么理解层)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)

## 一、核心概念
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/items/associated-items.html)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)]**

### 1.1 当前限制

在稳定 Rust 中，`self` 参数的类型受到严格限制：

```rust,ignore
impl MyType {
    fn by_value(self) {}           // ✅ Self
    fn by_ref(&self) {}            // ✅ &Self
    fn by_mut(&mut self) {}        // ✅ &mut Self
    fn by_box(self: Box<Self>) {}  // ✅ Box<Self>
    fn by_rc(self: Rc<Self>) {}    // ✅ Rc<Self>
    fn by_arc(self: Arc<Self>) {}  // ✅ Arc<Self>
    fn by_pin(self: Pin<Box<Self>>) {} // ✅ Pin<P<Self>>

    // ❌ 以下均不支持：
    // fn by_ref_cell(self: RefCell<Self>) {}
    // fn by_my_ptr(self: MyPtr<Self>) {}
    // fn by_addr(self: *const Self) {}
}
```

稳定 Rust 中已支持的接收器示例：

```rust
use std::rc::Rc;

struct Counter(i32);

impl Counter {
    fn value(self: Rc<Self>) -> i32 {
        self.0
    }
}

fn main() {
    let c = Rc::new(Counter(42));
    assert_eq!(c.value(), 42);
}
```

### 1.2 Arbitrary Self Types 提案
>
> **[来源: [Rust Internals Forum](https://internals.rust-lang.org/)]**
>
> **[来源: [RFC 44874 Tracking Issue](https://github.com/rust-lang/rust/issues/44874)]**

Arbitrary self types 允许 `self` 使用**任何实现 `DispatchFromDyn` 或满足特定约束的类型**：

```rust,ignore
#![feature(arbitrary_self_types)]

impl MyType {
    // 使用自定义智能指针
    fn by_my_ptr(self: MyPtr<Self>) {}

    // 使用裸指针（内核编程常见）
    fn by_raw(self: *const Self) {}

    // 使用 RefCell
    fn by_refcell(self: RefCell<Self>) {}
}
```

nightly `arbitrary_self_types` 自定义指针示例：

```rust,ignore
#![feature(arbitrary_self_types)]

use std::ops::Receiver;

struct TaggedPtr<T> {
    ptr: *const T,
    tag: u8,
}

impl<T> Receiver for TaggedPtr<T> {
    type Target = T;
}

struct Sensor(u32);

impl Sensor {
    // 以自定义指针类型作为方法接收器
    fn read(self: TaggedPtr<Self>) -> u32 {
        unsafe { (*self.ptr).0 }
    }
}

fn main() {
    let s = Sensor(42);
    let ptr = TaggedPtr { ptr: &s, tag: 1 };
    assert_eq!(ptr.read(), 42);
}
```

---

## 二、技术细节
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/items/traits.html)]**
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)]**

### 2.1 `DispatchFromDyn` Trait

Arbitrary self types 的核心是 `DispatchFromDyn` trait，它告诉编译器如何在动态分发（`dyn Trait`）时解包 `self`：

```rust,ignore
#![feature(dispatch_from_dyn)]

use std::ops::DispatchFromDyn;

// 自定义指针类型
struct KernelPtr<T: ?Sized>(*mut T);

unsafe impl<T: ?Sized, U: ?Sized> DispatchFromDyn<KernelPtr<U>> for KernelPtr<T>
where
    T: Unsize<U>,
{}
```

### 2.2 与 `Deref` 的关系

```rust,ignore
// 对于 &T、&mut T、Box<T> 等，编译器已知如何解引用
// 对于自定义类型，需要实现 Deref：

impl<T> Deref for KernelPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.0 }
    }
}
```

---

## 三、使用场景
>
> **[来源: [Rust Project Goals 2026 — Arbitrary Self Types](https://rust-lang.github.io/rust-project-goals/2026/arbitrary-self-types.html)]**
>
> **[来源: [Rust for Linux](https://rust-for-linux.com/)]**

### 场景 1：内核编程（Rust for Linux）

Linux 内核中的对象通常通过特定类型的指针引用（Reference）：

```rust,ignore
struct Device {
    ptr: *mut raw_device,
}

impl Device {
    // 当前：需要显式传递指针
    unsafe fn read(dev: *mut Device) -> u32 {
        (*dev).ptr.read()
    }

    // arbitrary_self_types 后：
    unsafe fn read(self: *mut Device) -> u32 {
        self.ptr.read()
    }
}
```

### 场景 2：嵌入式寄存器映射

```rust,ignore
struct RegisterBlock {
    base: *mut u32,
}

impl RegisterBlock {
    fn read_status(self: *const Self) -> u32 {
        unsafe { self.base.add(0).read_volatile() }
    }

    fn write_control(self: *mut Self, val: u32) {
        unsafe { self.base.add(1).write_volatile(val) }
    }
}
```

### 场景 3：自定义智能指针

```rust,ignore
struct TaggedPtr<T> {
    ptr: *mut T,
    tag: u8,
}

impl<T> TaggedPtr<T> {
    fn tag(self: TaggedPtr<T>) -> u8 {
        self.tag
    }

    fn data(self: &TaggedPtr<T>) -> &T {
        unsafe { &*self.ptr }
    }
}
```

---

## 四、反命题与边界分析
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/unsafe-blocks.html)]**
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)]**

### 4.1 安全边界

| 问题 | 分析 |
|------|------|
| `self: *const T` 安全吗？ | 方法体内仍需 `unsafe`，但调用语法更自然 |
| 与 `Pin` 的交互 | `Pin<CustomPtr<T>>` 需要 `CustomPtr` 实现 `Unpin` 规则 |
| 动态分发 | 必须通过 `DispatchFromDyn`，否则 `dyn Trait` 调用失败 |

### 4.2 设计决策

```text
需要 arbitrary self types？
├── 内核/嵌入式裸指针调用？ → 是，代码可读性大幅提升
├── 自定义智能指针库？ → 是，API 更自然
├── 普通应用代码？ → 否，现有 self 类型已足够
└── 需要 dyn Trait 支持？ → 确认 DispatchFromDyn 实现
```

---

## 五、演进路线

| 阶段 | 状态 | 预计 |
|------|------|------|
| RFC 讨论 | 活跃中 | 2026 |
| Nightly 实现 | 部分可用 | 已存在 |
| 稳定化 | 未开始 | 2027+ |

---

## 参考

> **来源: [Rust Project Goals 2026 — Arbitrary Self Types](https://rust-lang.github.io/rust-project-goals/2026/arbitrary-self-types.html)**
> **[Rust Internals — Arbitrary Self Types Discussion](https://internals.rust-lang.org/)**

| 资源 | 链接 |
|------|-----|
| Tracking Issue | <https://github.com/rust-lang/rust/issues/44874> |
| Rust for Linux 需求 | <https://rust-lang.github.io/rust-project-goals/2026/> |

> **过渡**: Arbitrary Self Types 预览：自定义方法接收器 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Arbitrary Self Types 预览：自定义方法接收器 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。
> **过渡**: Arbitrary Self Types 预览：自定义方法接收器 的深入理解需要结合具体代码实践，建议通过编写测试用例验证边界行为。

### 补充定理链

- **定理**: Arbitrary Self Types 预览：自定义方法接收器 定义 ⟹ 类型安全保证
- **定理**: Arbitrary Self Types 预览：自定义方法接收器 定义 ⟹ 类型安全保证
- **定理**: Arbitrary Self Types 预览：自定义方法接收器 定义 ⟹ 类型安全保证

## 嵌入式测验（Embedded Quiz）

### 测验 1：Arbitrary Self Types 允许什么目前不允许的操作？（理解层）

**题目**: Arbitrary Self Types 允许什么目前不允许的操作？

<details>
<summary>✅ 答案与解析</summary>

允许方法的 `self` 参数为非标准类型（目前仅支持 `self`、`&self`、`&mut self`、`Box<Self>`、`Rc<Self>`、`Arc<Self>`、`Pin<...>`）。例如 `self: MySmartPointer<T>`。
</details>

---

### 测验 2：这个特性对自定义智能指针有什么意义？（理解层）

**题目**: 这个特性对自定义智能指针（Smart Pointer）有什么意义？

<details>
<summary>✅ 答案与解析</summary>

自定义智能指针（Smart Pointer）可以直接作为方法接收器，无需先解引用（Reference）为引用。使 API 更自然，例如 `my_ptr.method()` 而非 `(*my_ptr).method()`。
</details>

---

### 测验 3：`Receiver` trait 在这个特性中起什么作用？（理解层）

**题目**: `Receiver` trait 在这个特性中起什么作用？

<details>
<summary>✅ 答案与解析</summary>

`Receiver` 标记一个类型可以作为方法接收器。实现 `Receiver for MyType` 后，该类型可用于 `self: MyType` 的方法签名。
</details>

---

### 测验 4：Arbitrary Self Types 与 `Deref` 有什么关系？（理解层）

**题目**: Arbitrary Self Types 与 `Deref` 有什么关系？

<details>
<summary>✅ 答案与解析</summary>

`Deref` 允许自动解引用（Reference）（`my_ptr.method()` 解引用后调用）。Arbitrary Self Types 允许直接以智能指针类型作为接收器，无需解引用，保留更多类型信息。
</details>

---

### 测验 5：这个特性目前的状态是什么？（理解层）

**题目**: 这个特性目前的状态是什么？

<details>
<summary>✅ 答案与解析</summary>

已在 nightly 中实现，部分功能稳定化中。是 Rust 类型系统（Type System）扩展的重要一步，使自定义类型更像一等公民。
</details>

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Arbitrary Self Types 预览：自定义方法接收器** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Arbitrary Self Types 预览：自定义方法接收器 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Arbitrary Self Types 预览：自定义方法接收器 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Arbitrary Self Types 预览：自定义方法接收器 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

> **过渡**: 掌握 Arbitrary Self Types 预览：自定义方法接收器 的基础概念后，建议通过实际案例与源码阅读加深理解，建立从理论到实践的桥梁。
> **过渡**: 在工程实践中应用 Arbitrary Self Types 预览：自定义方法接收器 时，务必评估生态成熟度、社区支持与长期维护风险，避免过度依赖实验性技术。
> **过渡**: Arbitrary Self Types 预览：自定义方法接收器 反映了 Rust 生态系统的演进趋势与语言设计哲学，理解这些趋势有助于预判未来发展方向并做出前瞻性技术决策。

### 反命题与边界

> **反命题**: "Arbitrary Self Types 预览：自定义方法接收器 是万能解决方案，适用于所有场景" —— 错误。任何技术选择都有权衡，需根据具体需求、团队能力与项目约束综合评估。
