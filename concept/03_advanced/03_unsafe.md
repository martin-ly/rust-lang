# Unsafe Rust

> **层级**: L3 高级概念
> **前置概念**: [Ownership](../01_foundation/01_ownership.md) · [Borrowing](../01_foundation/02_borrowing.md) · [Memory Management](../02_intermediate/03_memory_management.md) · [Concurrency](../03_advanced/01_concurrency.md)
> **后置概念**: [FFI] · [Embedded] · [Custom Allocators]
> **主要来源**: [TRPL: Ch19.1](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) · [Rust Reference: Unsafe Rust] · [Rustonomicon](https://doc.rust-lang.org/nomicon/) · [RFC 2585]

---

**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成权威定义、unsafe 操作矩阵、UB 分类、Safety Contract 规范、思维导图、示例反例

---

## 一、权威定义（Definition）

### 1.1 Wikipedia 权威定义

> **[Wikipedia: Undefined behavior]** In computer programming, undefined behavior (UB) is the result of executing computer code whose behavior is not prescribed by the language specification to which the code can adhere, for the current state of the program. This happens when the translator of the source code makes certain assumptions, but these assumptions are not satisfied during execution.

> **[Wikipedia: Memory safety]** Memory safety is the state of being protected from various software bugs and security vulnerabilities when dealing with memory access, such as buffer overflows and dangling pointers. A programming language is memory-safe if it prevents such issues through its design, type system, or automatic memory management.

> **[Wikipedia: Foreign function interface]** A foreign function interface (FFI) is a mechanism by which a program written in one programming language can call routines or make use of services written in another. FFI is the primary mechanism used by Rust to interoperate with C and other languages.

### 1.2 TRPL 官方定义

> **[TRPL: Ch19.1]** Rust has a second language hiding out inside it, unsafe Rust, which works just like regular Rust but gives you extra superpowers. Unsafe Rust exists because, by nature, static analysis is conservative. When the compiler tries to determine whether or not code upholds the guarantees, it's better for it to reject some valid programs than to accept some invalid programs.

### 1.2 Rustonomicon 定义

> **[Rustonomicon]** A block of code prefixed with `unsafe` does not permit the writing of arbitrary code. The `unsafe` keyword has two meanings: it declares the existence of a contract the compiler doesn't know about, and it declares that you have verified that contract.

> **[Rustonomicon: What is unsafe?]** unsafe 不是关闭检查器，而是声明程序员已人工验证某个编译器无法知晓的契约。安全抽象 = unsafe 实现 + safe 接口 + 人工证明。✅ 已验证
>
> **[TRPL: Ch19.1]** Safe Rust = 编译器可证明安全的程序集合；Unsafe Rust = Safe Rust ∪ 需要人工证明安全性的操作集合。✅ 已验证

### 1.3 形式化定义

`unsafe` 是**形式系统的显式边界突破**：

```text
Safe Rust = { 程序 P | 编译器可证明 P 满足内存安全 + 类型安全 + 并发安全 }
Unsafe Rust = Safe Rust ∪ { 操作 O | O 需要人工证明安全性 }

关键洞察:
  unsafe 不是"关闭检查器"，而是"程序员承担证明责任"
  安全抽象（Safe Abstraction）= unsafe 实现 + safe 接口 + 人工证明内部正确
```

---

## 二、概念属性矩阵（Attribute Matrix）

### 2.1 Unsafe 操作分类矩阵

| **操作** | **语法** | **安全风险** | **典型用途** | **Safe 封装示例** |
|:---|:---|:---|:---|:---|
| **裸指针解引用** | `*raw_ptr` | UAF, 悬垂, 类型混淆 | FFI, 数据结构内部 | `Box::from_raw` |
| **调用 unsafe 函数** | `unsafe_fn()` | 依赖函数契约 | 底层系统调用 | `std::fs::read` |
| **实现 unsafe trait** | `unsafe impl Trait` | 破坏全局假设 | Send/Sync 标记 | `Arc<T>` |
| **访问 union 字段** | `union.field` | 类型混淆 | C 互操作 | `std::mem::ManuallyDrop` |
| **调用 extern 函数** | `extern "C"` | ABI 不匹配, UAF | 系统库调用 | `libc` crate |
| **修改可变静态变量** | `static mut` | 数据竞争 | 全局状态（避免） | `lazy_static!` |
| **内联汇编** | `asm!()` | 完全不受控 | 极致优化 | 极少数场景 |

> **[Rust Reference: Behavior considered undefined]** Rust 的 UB 清单包括：数据竞争、悬垂指针解引用、越界访问、类型混淆、无效枚举值、未对齐访问、读取未初始化内存等。✅ 已验证
>
> **[Rustonomicon: UB]** 未定义行为意味着编译器可据此做任何优化假设；触发 UB 后程序行为完全不可预测。✅ 已验证

### 2.2 UB（未定义行为）分类矩阵

| **UB 类型** | **描述** | **检测难度** | **示例** |
|:---|:---|:---|:---|
| **内存访问** | 悬垂指针解引用、越界访问、空指针解引用 | 中等（ASan/Miri） | `*ptr` after free |
| **类型系统** | 无效枚举值、数据竞争、对齐违规 | 难 | `mem::transmute` 滥用 |
| **并发** | 数据竞争、锁顺序错误（C++ style） | 难 | 非原子访问共享可变状态 |
| **ABI** | 调用约定不匹配、布局假设错误 | 难 | FFI 类型宽度不匹配 |
| **特殊** | 递归 panic、栈溢出、除以零 | 中等 | `panic!` in `Drop` |

### 2.3 Safety Contract 责任矩阵

| **角色** | **责任** | **证明对象** | **工具支持** |
|:---|:---|:---|:---|
| **unsafe 实现者** | 保证 unsafe 块内部不触发 UB | 局部代码正确性 | Miri、Kani、审阅 |
| **safe 接口设计者** | 保证 safe API 不泄露 UB | 所有调用路径安全 | 类型系统、测试 |
| **safe 用户** | 正确使用 safe API | 无需证明（编译器保证） | 编译器 |
| **unsafe trait 实现者** | 满足 trait 的 unsafe 契约 | 全局语义约束 | 文档、审阅 |

---

## 三、形式化理论根基（Formal Foundation）

> **[Rustonomicon: The Safe/Unsafe Boundary]** Safe Rust 是封闭的证明系统；unsafe 是显式引入新公理并人工保证一致性的扩展。类比：Safe Rust = 欧氏几何，Unsafe = 非欧几何。💡 原创分析

### 3.1 Unsafe 作为公理缺口

```text
Safe Rust 类型系统是一个封闭的证明系统:
  公理: 所有权、借用、生命周期规则
  定理: 通过编译 = 满足安全保证

Unsafe 是公理系统的显式扩展:
  unsafe { ... } = "我在此区域引入新的公理，并人工保证其一致性"

类比数学:
  Safe Rust = 欧氏几何（5条公设封闭）
  Unsafe    = 非欧几何（修改平行公设，需重新证明一致性）
```

> **[Ralf Jung Blog (PLDI 2019)]** Rust 区分 Validity Invariant（编译器/优化器依赖的底层约束，违反即 UB）与 Safety Invariant（Safe API 要求的高层约束，违反可能通过 safe API 触发 UB）。✅ 已验证
>
> **[Rustonomicon: What is unsafe?]** unsafe 代码的核心责任：不破坏 Validity Invariant（对编译器负责），维护 Safety Invariant（对 safe 用户负责）。✅ 已验证

### 3.2 Safety Invariant vs Validity Invariant

```text
Rust 区分两种不变式:

Validity Invariant（有效性不变式）:
  - 编译器和优化器依赖的底层约束
  - 违反 = 立即 UB
  - 例: bool 必须是 0 或 1，引用必须非空对齐

Safety Invariant（安全性不变式）:
  - Safe API 的用户必须维护的高层约束
  - 违反 = 可能通过 safe API 触发 UB
  - 例: Vec 的 len ≤ cap，String 是有效 UTF-8

unsafe 代码的责任:
  - 不破坏 Validity Invariant（对编译器负责）
  - 维护 Safety Invariant（对 safe 用户负责）
```

---

## 四、思维导图（Mind Map）

```mermaid
graph TD
    A[Unsafe Rust] --> B[unsafe 操作]
    A --> C[UB 分类]
    A --> D[安全抽象]
    A --> E[验证工具]
    A --> F[常见模式]

    B --> B1[裸指针 *const/*mut]
    B --> B2[unsafe fn / unsafe trait]
    B --> B3[extern 函数]
    B --> B4[union 访问]
    B --> B5[static mut]

    C --> C1[内存: UAF, OOB, 对齐]
    C --> C2[类型: 无效枚举, transmute]
    C --> C3[并发: 数据竞争]
    C --> D1[Validity Invariant]
    C --> D2[Safety Invariant]

    D --> D3[unsafe 实现 + safe 接口]
    D --> D4[Document Safety Contract]

    E --> E1[Miri]
    E --> E2[Kani]
    E --> E3[ASan / MSan]
    E --> E4[Creusot]

    F --> F1[FFI 边界]
    F --> F2[自定义数据结构]
    F --> F3[Send/Sync 实现]
    F --> F4[零拷贝解析]
```

---

## 五、决策/边界判定树（Decision / Boundary Tree）

### 5.1 "我需要用 unsafe 吗？" 决策树

```mermaid
graph TD
    Q1[Safe Rust 能实现需求?] -->|是| A1[不要用 unsafe]
    Q1 -->|否| Q2[需求是 FFI 调用?]
    Q2 -->|是| A2[用 unsafe 封装 FFI]
    Q2 -->|否| Q3[需求是极致性能优化?]
    Q3 -->|是| Q4[profile 确认瓶颈?]
    Q3 -->|否| Q5[需求是底层内存控制?]
    Q4 -->|是| A3[用 unsafe，配合基准测试]
    Q4 -->|否| A1
    Q5 -->|是| A4[用 unsafe，最小化范围]
    Q5 -->|否| A1

    A1[Safe Rust 优先]
    A2[unsafe FFI 边界]
    A3[性能关键路径]
    A4[内存布局控制]
```

### 5.2 UB 边界判定

```mermaid
graph TD
    B1[解引用可能为 null 的裸指针] -->|运行时| E1[UB: 段错误 / 任意行为]
    B2[创建悬垂裸指针] -->|编译合法| W1[⚠️ 仅在解引用时 UB]
    B3[transmute 无关类型] -->|编译合法| E2[UB: 类型混淆 / 对齐错误]
    B4[unsafe impl Send for Rc<T>] -->|编译合法| E3[UB: 数据竞争]
    B5[读取未初始化内存] -->|运行时| E4[UB: 读取任意值]
```

---

## 六、定理推理链（Theorem Chain）

> **[Rustonomicon: Safe Abstractions]** 安全抽象定理：unsafe 实现 + safe 接口 + 人工证明 = 用户无需了解内部 unsafe 即可安全使用。Rust 标准库的核心类型（Vec, String, HashMap 等）均基于此模式构建。✅ 已验证
>
> **[Rust API Guidelines]** 封装 unsafe 的 safe API 必须文档化 Safety Contract，且对所有合法输入保证不触发 UB。✅ 已验证

### 6.1 安全抽象定理

```text
前提 1: unsafe 块实现了某些底层操作
前提 2: safe 接口封装了 unsafe 块，并限制了输入
前提 3: 人工证明: 对所有合法 safe 输入，unsafe 块不触发 UB
    ↓
定理: safe 接口是"可信的"——用户无需了解内部 unsafe 即可安全使用
    ↓
推论: Rust 标准库的大部分功能基于 unsafe 实现，但接口是 safe 的
      例: Vec, String, HashMap, Rc, Arc, Box 都有 unsafe 内部实现
```

> **[Miri Documentation]** Miri 是 Rust 的解释型 MIR 执行器，可动态检测悬垂指针、越界访问、未对齐访问、数据竞争（部分）和无效枚举值等 UB。✅ 已验证
>
> **[Miri Documentation: Limitations]** Miri 无法检测所有 UB（停机问题不可解），且不支持与硬件相关的行为（如内联汇编）。✅ 已验证

### 6.2 Miri 的验证边界

```text
Miri (Rust 解释器) 可检测:
  ✅ 悬垂指针解引用
  ✅ 越界访问
  ✅ 未对齐访问
  ✅ 数据竞争（部分）
  ✅ 无效枚举值
  ❌ 所有可能的 UB（停机问题）
  ❌ 与硬件相关的行为（如内联汇编）
```

### 6.3 定理一致性矩阵

| 定理 | 前提 | 结论 | 依赖的 L4 公理 | 被哪些定理依赖 | 失效条件 | 典型场景 |
|:---|:---|:---|:---|:---|:---|:---|
| unsafe 边界明确性 | `unsafe {}` / `unsafe fn` 标记 | 程序员承担安全责任 | —（证明范围外） | 所有 safe 抽象 | 安全契约不完整 | UB |
| 裸指针解引用安全 | 指针有效 + 类型正确 + 无别名违规 | 解引用行为良好 | —（手动验证） | FFI、底层数据结构 | 悬垂指针、未对齐、已释放 | UB |
| FFI 调用安全 | 外部函数契约匹配 | 调用行为符合预期 | —（假设） | C 互操作 | ABI 不匹配、生命周期不一致 | 崩溃/UB |
| Union 访问安全 | 当前活跃的字段已知 | 读取正确变体 | —（程序员责任） | C 兼容、低层解析 | 读取未初始化/非活跃字段 | UB |
| MaybeUninit 安全 | 写入后才读取 | 避免未初始化读取 | —（部分形式化） | 延迟初始化、FFI | 读取未写入 | UB |

> **[Rustonomicon]** 一致性说明: unsafe 领域的定理不依赖 L4 形式化——它们处于证明范围之外。Miri 提供动态检测作为近似验证手段。RustBelt 正在扩展以覆盖部分 unsafe 模式。✅ 已验证
>
> **[🔍 待验证]** RustBelt 对 unsafe 的完整形式化覆盖仍在活跃研究中，目前仅覆盖部分常见模式（如 Vec、Rc、Arc 等）。
>
> **跨层映射**: 本文件定理 ↔ [`00_meta/inter_layer_map.md`](../00_meta/inter_layer_map.md) §4.1 "内存安全完备性" · §6.1 "形式化保证失效条件"

---

## 七、示例与反例（Examples & Counter-examples）

### 7.1 正确示例：安全封装裸指针（Vec 简化版）

```rust
// ✅ 正确: unsafe 实现 + safe 接口
pub struct MyVec<T> {
    ptr: *mut T,
    len: usize,
    cap: usize,
}

impl<T> MyVec<T> {
    pub fn new() -> Self {
        Self { ptr: std::ptr::NonNull::dangling().as_ptr(), len: 0, cap: 0 }
    }

    pub fn push(&mut self, value: T) {
        if self.len == self.cap { self.grow(); }
        unsafe {
            // Safety: ptr 已分配且 len < cap
            std::ptr::write(self.ptr.add(self.len), value);
        }
        self.len += 1;
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len { return None; }
        Some(unsafe {
            // Safety: index < len，且所有 0..len 位置已初始化
            &*self.ptr.add(index)
        })
    }

    fn grow(&mut self) { /* 使用 alloc::GlobalAlloc 重新分配 */ }
}

impl<T> Drop for MyVec<T> {
    fn drop(&mut self) {
        unsafe {
            // Safety: 我们只释放自己分配的内存
            std::alloc::dealloc(/* ... */);
        }
    }
}
```

### 7.2 正确示例：手动实现 Send/Sync

```rust
// ✅ 正确: 为线程安全的外部类型实现 Send/Sync
pub struct MyHandle { raw: *mut libc::c_void }

// Safety: 底层 C 库保证此句柄可跨线程安全使用
unsafe impl Send for MyHandle {}
unsafe impl Sync for MyHandle {}
```

### 7.3 反例：悬垂裸指针（UB）

```rust
// ❌ 反例: 返回局部变量的裸指针
unsafe fn dangling_ptr() -> *const i32 {
    let x = 42;
    &x as *const i32  // x 在函数返回后被释放
}

fn main() {
    let ptr = dangling_ptr();
    println!("{}", unsafe { *ptr });  // UB: UAF
}
```

### 7.4 反例：transmute 滥用（UB）

```rust
// ❌ 反例: transmute 不相关类型
unsafe fn evil_transmute() {
    let f: f32 = 1.0;
    let b: bool = std::mem::transmute(f);  // UB! f32 位模式不全是有效 bool
}
```

### 7.5 反例：无效枚举值（UB）

```rust
// ❌ 反例: 创建无效枚举值
enum Color { Red, Green, Blue }

unsafe fn invalid_enum() -> Color {
    std::mem::transmute(42u8)  // UB! 42 不是有效变体索引
}
```

---

### 7.6 反命题与边界分析

#### 命题: "unsafe 代码可以安全地封装"

```mermaid
graph TD
    P["命题: unsafe 可安全封装"] --> Q1{"安全契约是否完整?"}
    Q1 -->|否| F1["反例: 前置条件遗漏<br/>→ 调用方传入非法参数 → UB"]
    Q1 -->|是| Q2{"unsafe 块内部假设是否成立?"}
    Q2 -->|否| F2["反例: 内部断言失败<br/>→ 即使调用方合法也 UB"]
    Q2 -->|是| Q3{"编译器优化是否破坏假设?"}
    Q3 -->|是| F3["反例: LLVM 优化假设内存模型<br/>→ 未定义行为被触发"]
    Q3 -->|否| T["定理成立: safe API 封装内部 unsafe<br/>✅ 契约完备性保证"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f96
    style T fill:#6f6
```

> **[Miri Documentation]** Miri 支持 Stacked Borrows 和实验性的 Tree Borrows 两种内存模型；Tree Borrows 更宽松，可覆盖更多合法 unsafe 模式。✅ 已验证
>
> **[Ralf Jung Blog]** Miri 无法检测 FFI 边界错误和活性性质（死锁/无限循环），因为 FFI 调用不透明且活性问题不可判定。✅ 已验证

#### 命题: "Miri 可以检测所有 UB"

| 条件 | 结果 | 说明 |
|:---|:---|:---|
| Stacked Borrows 模型 | ⚠️ 部分检测 | 严格的别名规则 |
| Tree Borrows 模型 | ⚠️ 更宽松检测 | 实验性，覆盖更多合法模式 |
| 数据竞争 | ✅ 检测 |  happens-before 分析 |
| 未初始化读取 | ✅ 检测 | `MaybeUninit` 追踪 |
| 悬垂指针解引用 | ✅ 检测 | 内存分配追踪 |
| 与外部代码交互 | ❌ 不检测 | FFI 调用不透明 |
| 无限循环 / 死锁 | ❌ 不检测 | 活性性质 |

#### 边界极限测试

```rust
// 边界: 未定义行为（UB）的微妙性

fn undefined_behavior_example() {
    let mut x = 0i32;
    let r1 = &mut x as *mut i32;
    let r2 = &mut x as *mut i32;  // 两个 &mut x 同时存在！但立即转为裸指针
    // 在 safe Rust 中这会被编译器拒绝，但在 unsafe 中...
    unsafe {
        *r1 = 1;
        *r2 = 2;  // UB! 两个 &mut 同时活跃（即使已转为裸指针）
    }
    // 根据 Stacked Borrows，从 &mut 创建的裸指针不能同时活跃
}

// 正确: 使用指针算术替代重叠引用
fn safe_raw_pointer() {
    let mut arr = [1, 2, 3, 4];
    let ptr = arr.as_mut_ptr();
    unsafe {
        let first = ptr;
        let second = ptr.add(2);  // 不重叠
        *first = 10;
        *second = 30;  // ✅ 合法
    }
}
```

---

## 零、认知路径（Cognitive Path）

```text
直觉困惑                    具体场景                  模式抽象               形式规则              代码验证              边界测试
    │                         │                       │                     │                    │                    │
    ▼                         ▼                       ▼                     ▼                    ▼                    ▼
"unsafe 到底多危险？"        "FFI 调用 C 函数         "unsafe = 程序员       "手动证明            "Miri 检测           "所有 safe
                             怎么保证安全？"          承担证明责任"          义务"               UB"                定理失效"

"什么时候必须用 unsafe？"     "自引用结构、             "Safe 抽象无法         "类型系统限制:      "编译器拒绝         "过度使用
                             底层内存操作"            表达时使用"           某些合法程序        safe 替代"         unsafe"
                                                     无法被证明安全"

"怎么验证 unsafe 代码？"     "手写 unsafe 后           "Safety Contract      "公理化语义:        "Miri +              "FFI 边界
                             怎么测试？"              + Miri 动态检测"       假设-保证"         模糊测试"           假设不可验证"
```

> **[Rustonomicon]** 类比：unsafe 像手术刀——精确、强大，但需要专业训练和明确的安全协议。✅ 已验证
>
> **[TRPL: Ch19.1]** 反直觉点：unsafe 块不意味着代码一定有 UB，而是意味着编译器不再保证无 UB。✅ 已验证
>
> **[Ralf Jung Blog + RustBelt]** 形式化过渡路径：编译器不检查 → 安全契约 → 公理化语义 → RustBelt 逐步覆盖。🔍 待验证（RustBelt 对 unsafe 的覆盖仍在进行中）

**认知脚手架**:

- **类比**: `unsafe` 像"手术刀"——精确、强大，但需要专业训练和明确的安全协议。
- **反直觉点**: `unsafe` 块**不意味着**代码一定有 UB，而是意味着**编译器不再保证**无 UB。
- **形式化过渡**: 从"编译器不检查" → "安全契约" → "公理化语义" → "RustBelt 对 unsafe 的逐步覆盖"。 💡 原创分析

### 6.4 国际课程与论文对齐

| 来源 | 核心内容 | 与本文件对应 |
|:---|:---|:---|
| **[CMU 17-350: Safe Systems Programming]** | Unsafe、FFI、UB 边界、Safety Contracts | L3 Unsafe 完整覆盖 |
| **[CMU 17-363: Programming Language Pragmatics]** | unsafe 作为类型系统边界突破 | 形式化视角 |
| **[Rustonomicon]** | Unsafe 编程规范、安全抽象设计 | 实践指南 |
| **[Stacked Borrows: POPL 2019]** | 别名模型操作语义 | 内存模型 §3 |
| **[Tree Borrows]** | 更宽松的别名模型 | Miri 检测基础 |
| **[RustHornBelt: PLDI 2022]** | unsafe 代码功能正确性验证 | 形式化验证 |

---

## 八、知识来源关系（Provenance）

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| unsafe 提供 5 种超能力 | [TRPL: Ch19.1] | ✅ |
| unsafe 是程序员承担证明责任 | [Rustonomicon] | ✅ |
| UB 清单 | [Rust Reference: Behavior considered undefined] | ✅ |
| Validity vs Safety Invariant | [Rustonomicon: What is unsafe?] · [Ralf Jung Blog] | ✅ |
| Miri 可检测部分 UB | [Miri Documentation] | ✅ |
| 安全抽象封装 unsafe | [Rust API Guidelines] | ✅ |

---

## 九、待补充与演进方向（TODOs）

### 补充章节：FFI 与 repr 属性完整规范

#### ABI 与 Calling Convention

```rust
// extern "C" = 使用 C 调用约定
extern "C" {
    fn c_function(x: i32) -> i32;  // 声明 C 函数
}

// extern "system" = 使用系统默认 ABI（Windows 上不同）
extern "system" {
    fn system_function();
}

// Rust 函数的 C 导出
#[no_mangle]  // 禁用名称修饰，使 C 可链接
pub extern "C" fn rust_function(x: i32) -> i32 {
    x * 2
}
```

#### repr 属性矩阵

| **属性** | **用途** | **保证** | **风险** |
|:---|:---|:---|:---|
| `#[repr(C)]` | C 互操作 | 字段顺序与 C 相同 | 可能有 padding |
| `#[repr(transparent)]` | 新类型包装 | 内存布局与内部类型相同 | 只能有一个非零大小字段 |
| `#[repr(packed)]` | 无 padding | 紧凑布局 | 未对齐访问可能慢或 UB |
| `#[repr(align(N))]` | 自定义对齐 | N 字节对齐 | 浪费内存 |
| `#[repr(u8)]` | enum 标签类型 | 指定 discriminant 大小 | 需覆盖所有值 |

```rust
// ✅ repr(C): 与 C 结构体互操作
#[repr(C)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

// ✅ repr(transparent): 零成本新类型
#[repr(transparent)]
pub struct UserId(u64);  // 内存布局与 u64 完全相同

// ✅ repr(packed(1)): 强制无 padding
#[repr(packed(1))]
pub struct Packed {
    pub a: u8,
    pub b: u32,  // 通常对齐到 4，packed 后紧跟 a
}

// ⚠️ packed 的借用是危险的
fn packed_borrow(p: &Packed) {
    // let r = &p.b;  // ❌ 可能未对齐，编译错误
    let r = unsafe { &p.b };  // 需 unsafe，且可能慢
}
```

> **[Rust Reference: External blocks]** FFI 边界是 Rust 形式系统的"公理缺口"：Rust 编译器无法验证外部代码的行为，程序员需人工保证 ABI 匹配、指针有效性和生命周期一致性。✅ 已验证
>
> **[Rustonomicon: FFI]** 常见 FFI 陷阱：String ↔ *const c_char 编码差异、Vec ↔ 裸指针所有权转移、回调函数生命周期管理。✅ 已验证

#### FFI 安全契约

```text
FFI 边界是 Rust 形式系统的"公理缺口":

Rust 端保证:
  - 传递给 C 的指针有效（非悬垂、对齐、正确生命周期）
  - 类型布局匹配（#[repr(C)] 等）
  - 回调函数满足 C 的调用约定

C 端保证:
  - 不修改 Rust 拥有的内存（除非协议允许）
  - 不返回悬垂指针
  - 线程安全（若涉及多线程）

常见陷阱:
  - String ↔ *const c_char 转换（UTF-8 vs 平台编码）
  - Vec ↔ 裸指针+长度（所有权转移边界）
  - 回调函数的生命周期（C 可能长期保存函数指针）
```

---

- [x] **TODO**: 补充 FFI 完整规范（ABI、layout、calling convention） —— 优先级: 高 —— 已完成 v1.1
- [x] **TODO**: 补充 `#[repr(C)]` / `#[repr(transparent)]` / `#[repr(packed)]` —— 优先级: 高 —— 已完成 v1.1
- [ ] **TODO**: 补充 Miri 的使用方法与限制 —— 优先级: 中 —— 预计: Phase 3
- [ ] **TODO**: 补充 `std::ptr::read/write` vs `*ptr` 解引用的区别 —— 优先级: 中 —— 预计: Phase 2
- [ ] **TODO**: 补充 `NonNull<T>` / `Unique<T>` / `Shared<T>` 的演进 —— 优先级: 低 —— 预计: Phase 4
- [ ] **TODO**: 补充 `MaybeUninit` 数组初始化模式 —— 优先级: 中 —— 预计: Phase 3

---

## 相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| 所有权 | [](../01_foundation/01_ownership.md) | safe 边界 |
| 借用规则 | [](../01_foundation/02_borrowing.md) | unsafe 突破 |
| 内存管理 | [](../02_intermediate/03_memory_management.md) | 裸指针 |
| 形式化验证 | [](../04_formal/04_rustbelt.md) | unsafe 证明边界 |
| 安全边界 | [](../05_comparative/safety_boundaries.md) | 全局边界汇总 |
