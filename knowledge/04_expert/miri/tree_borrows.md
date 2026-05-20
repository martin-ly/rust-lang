# Miri Tree Borrows 深度解析

> **Bloom 层级**: 理解

> **📌 简介**: Tree Borrows 是 Rust 的下一代内存模型，由 Villani 等人在 PLDI 2025 以 Distinguished Paper 发表。它用**树形权限模型**替代了 Stacked Borrows 的线性栈模型，将 Miri 的误报率降低了 54%，同时保持对真实未定义行为（UB）的检测能力。
>
> **⏱️ 预计学习时间**: 60-90 分钟
> **📚 难度级别**: ⭐⭐⭐⭐⭐ 专家级
> **权威来源**: "Tree Borrows" - Villani et al., PLDI 2025 Distinguished Paper

---

## 🎯 学习目标
>
> **[来源: Rust Official Docs]**

完成本章后，你将能够：

- [x] 理解 Tree Borrows 与 Stacked Borrows 在**形式化模型**上的根本差异
- [x] 掌握四种权限状态（Reserved、Active、Frozen、Disabled）的语义与转换规则
- [x] 解释 Tree Borrows 为什么能减少 54% 的 Miri 误报，同时不遗漏真实 UB
- [x] 在 CI/CD 中集成 Miri Tree Borrows 检查
- [x] 分析和修复 Miri Tree Borrows 检测到的内存问题

---

## 📋 先决条件
>
> **[来源: Rust Official Docs]**

1. **Unsafe Rust** — 原始指针、别名规则、`unsafe` 块（`03_advanced/unsafe/unsafe_rust.md`）
2. **借用与引用** — `&mut T` 的独占性、`&T` 的共享性（`01_fundamentals/borrowing.md`）
3. **Miri 基础** — Miri 作为解释器的使用（`03_advanced/unsafe/unsafe_rust.md` 模块 7）

---

## 🧠 核心概念
>
> **[来源: Rust Official Docs]**

### 模块 1: 概念定义
>
> **[来源: Rust Official Docs]**

#### 1.1 直观定义
>
> **[来源: Rust Official Docs]**

**Tree Borrows (TB)** 是 Rust 的实验性内存模型，用于精确判断 `unsafe` 代码中的引用使用是否构成**未定义行为（Undefined Behavior, UB）**。它是 Miri 解释器的默认内存模型（自 Rust 1.70+），替代了早期的 **Stacked Borrows (SB)**。

TB 的核心洞察：引用的权限关系不是**线性的栈**，而是**树形的层次结构**。当一个引用被重新借用（reborrow）时，新引用与旧引用之间形成父子关系，而非 SB 中的"压栈/弹栈"关系。

> 💡 关键直觉：Stacked Borrows 问"谁在栈顶？"，Tree Borrows 问"谁在谁的子树中？"

#### 1.2 操作定义

**Stacked Borrows 的线性模型**：

```rust
fn sb_example(x: &mut i32) -> i32 {
    let y = &mut *x;  // SB: 将 &mut *x 压入栈顶，&mut x 被"覆盖"
    *y = 1;
    *x  // SB: 试图使用被覆盖的 &mut x → UB！
}
```

SB 将引用视为**栈帧**：新引用压栈，使用时必须位于栈顶。上述代码中，`y` 压栈后 `x` 不在栈顶，因此 `*x` 是 UB。

**Tree Borrows 的树形模型**：

```rust
fn tb_example(x: &mut i32) -> i32 {
    let y = &mut *x;  // TB: y 是 x 的子节点，形成树
    *y = 1;           // y 使用其权限
    *x                // TB: x 作为父节点，仍保留权限 → 合法！
}
```

TB 将引用视为**树节点**：`y` 是 `x` 的子节点。`y` 的使用不剥夺 `x` 的权限，只要 `y` 的权限与 `x` 兼容。

#### 1.3 形式化直觉

> ⚠️ **标注**: 本节与 PLDI 2025 Distinguished Paper "Tree Borrows" 的核心定义对齐。

**权限状态机**：

Tree Borrows 为每个内存位置的每个引用分配一个**权限状态**：

```
Reserved ──read──► Active ──write──► Active
    │                │                │
    │                │ read           │ read/write
    │                ▼                ▼
    │             Frozen ─────────► Frozen
    │                │                │
    │                │ write          │ incompatible access
    │                ▼                ▼
    │             Disabled          Disabled
    │                ▲                ▲
    └────────────────┘                │
         incompatible access          │
                                      │
                                      │
    Disabled: 权限被撤销，任何使用都是 UB
```

**四种权限状态**：

| 状态 | 读 | 写 | 子节点权限 | 说明 |
|------|-----|-----|-----------|------|
| **Reserved** | ✅ | ⚠️（首次写转为 Active） | 可变/共享 | 新创建的引用，尚未使用 |
| **Active** | ✅ | ✅ | 可变/共享 | 可读写的活跃引用 |
| **Frozen** | ✅ | ❌ | 仅共享 | 不可变引用或可变引用的只读阶段 |
| **Disabled** | ❌ | ❌ | 无 | 权限被撤销，使用即 UB |

**关键创新——Reserved 状态**：

SB 中，`&mut *x` 立即获得完整权限，导致父引用 `x` 被冻结或禁用。TB 引入 **Reserved** 状态：新引用创建时处于 Reserved，首次写操作时才转为 Active。在 Reserved 阶段，父引用仍可自由使用。

```rust
fn reserved_demo(x: &mut i32) {
    let y = &mut *x;  // y: Reserved, x: Active
    println!("{}", *x);  // ✅ x 仍可读
    *y = 42;              // y: Reserved → Active
    // 现在 y 是 Active，x 的子节点权限被限制
}
```

---

### 模块 2: 属性清单

| 属性名 | 类型 | 值域/取值 | 说明 | 反例边界 |
|--------|------|-----------|------|----------|
| **树形结构** | 固有属性 | 有根树 | 每个分配对象有一棵权限树 | 原始指针不参与树结构 |
| **Reserved 延迟激活** | 固有属性 | 写时激活 | 新引用首次写才转为 Active | 仅适用于可变引用 |
| **父节点保留** | 关系属性 | 子 Reserved 时 | 父节点在子 Reserved 期间保持 Active | 子 Active 后父受限 |
| **误报降低** | 关系属性 | 54% | 相比 SB，TB 减少 54% 的误报 | 仍可能有过度保守 |
| **Frozen 传播** | 关系属性 | 向下 | 父节点 Frozen 时，所有子节点必须 Frozen | 通过 &mut 写 Frozen 分支是 UB |
| **Disabled 不可逆** | 固有属性 | true | 一旦 Disabled，永久失去权限 | 即使子节点 drop 也不恢复 |

#### 关键推论

1. **推论 1（Reserved 解决 54% 误报）**: SB 的主要误报来源是"新引用创建立即禁用父引用"。TB 的 Reserved 状态允许父引用在新引用首次写之前继续使用，这正是 reborrow 后常见模式。
2. **推论 2（树的局部性）**: TB 的权限检查是**局部的**。如果引用 `a` 的子树中发生冲突，只需检查 `a` 的子树，不影响 `a` 的兄弟子树。这比 SB 的全局栈操作更精确。
3. **推论 3（与 LLVM 的兼容性）**: TB 的设计目标之一是**不引入新的优化障碍**。Frozen 状态对应 LLVM 的 `noalias` + `readonly`，Active 对应 `noalias` + `readnone`/`readwrite`。

---

### 模块 3: 概念依赖图

```mermaid
graph TD
    A[Ownership] --> B[Borrowing]
    B --> C[Reborrow]
    C --> D[Stacked Borrows]
    D --> E[Linear Stack Model]
    E --> F[54% False Positives]
    C --> G[Tree Borrows]
    G --> H[Tree Model]
    H --> I[Reserved State]
    H --> J[Parent Retention]
    G --> K[Four States]
    K --> L[Reserved / Active / Frozen / Disabled]
    G --> M[Miri Integration]
    M --> N[UB Detection]
    N --> O[CI/CD Validation]

    style G fill:#f9f,stroke:#333,stroke-width:2px
    style H fill:#bbf,stroke:#333,stroke-width:2px
    style I fill:#bfb,stroke:#333,stroke-width:2px
```

#### 承上（前置知识回溯）

| 前置概念 | 所在文档 | 本章中使用的具体点 |
|----------|----------|-------------------|
| **借用与 reborrow** | `01_fundamentals/borrowing.md` | `&mut *x` 是 reborrow，TB 的核心场景 |
| **Unsafe Rust** | `03_advanced/unsafe/unsafe_rust.md` | 原始指针的别名规则在 TB 下的判断 |
| **Miri** | `03_advanced/unsafe/unsafe_rust.md` | TB 是 Miri 的默认内存模型 |

#### 启下（后续延伸预告）

| 后续概念 | 所在文档 | 掌握本章后方可理解 |
|----------|----------|-------------------|
| **Unsafe Audit** | `04_expert/unsafe_audit.md` | 在审计流程中集成 Miri + TB |
| **Safety Critical** | `04_expert/safety_critical/04_axiomatic_reasoning/FORMAL_VERIFICATION_PRACTICAL_GUIDE.md` | 高完整性系统的内存模型验证与 Miri 集成 |
| **Formal Verification** | `04_expert/safety_critical/04_axiomatic_reasoning/RUST_AXIOMATIC_REASONING_TREES.md` | 公理化推理树与内存安全证明 |
| **编译器优化** | `04_expert/compiler_internals.md` | TB 权限如何映射到 LLVM `noalias` |

---

### 模块 4: 机制解释

#### 4.1 类型系统视角

**TB 与借用检查器的关系**：

TB **不替代** Rust 的编译期借用检查器。它是对借用检查的**运行时补充**，用于验证 `unsafe` 代码中绕过编译器检查的操作是否安全。

```rust
fn safe_code(x: &mut i32) {
    let y = &mut *x;
    // println!("{}", *x);  // ❌ 编译错误！借用检查器阻止
    *y = 1;
}

fn unsafe_code(x: *mut i32) {
    unsafe {
        let y = &mut *x;  // 编译器允许（unsafe）
        *y = 1;
        *x = 2;  // 编译器允许（unsafe），但 TB/Miri 检查此处是否 UB
    }
}
```

#### 4.2 内存模型视角

**树的构建过程**：

```rust
fn tree_construction() {
    let mut data = 0;
    let x = &mut data;      // 根节点: x (Active)
    {
        let y = &mut *x;    // 子节点: y (Reserved)
        // 树结构:
        // data (allocation)
        // └── x (Active)
        //     └── y (Reserved)

        *x = 1;             // ✅ x 仍 Active，y 是 Reserved

        *y = 2;             // y: Reserved → Active
        // 现在 y 是 Active，x 的子树权限受限

        let z = &*y;        // 子节点: z (Frozen)
        // data
        // └── x (Active, but subtree restricted)
        //     └── y (Active)
        //         └── z (Frozen)
    } // y, z drop，x 恢复完整权限
}
```

**Frozen 的传递性**：

当 `&T`（共享引用）被创建时，对应的树节点变为 Frozen。Frozen 状态**向下传递**：所有子节点也必须变为 Frozen。如果通过子节点尝试写入，TB 判定为 UB。

```rust
fn frozen_propagation(x: &mut i32) {
    let y = &*x;        // y: Frozen (共享引用)
    let z = &*y;        // z: Frozen
    // z 是 y 的子节点，y 是 x 的子节点
    // 整个分支都是 Frozen

    // unsafe { *x = 1; }  // ❌ TB: x 的子树有 Frozen 节点，写是 UB！
}
```

#### 4.3 运行时视角

**Miri 中的 TB 实现**：

Miri 为每个内存分配维护一棵权限树：

```text
Miri 执行时:
┌─────────────────────────────────────────┐
│ 每个分配对象 (Allocation)               │
│  ├── 权限树 (Permission Tree)           │
│  │    ├── 节点: 引用指针值              │
│  │    ├── 状态: Reserved/Active/        │
│  │    │         Frozen/Disabled        │
│  │    └── 子节点列表                    │
│  │                                       │
│  └── 内存内容                            │
│                                          │
│ 每次内存访问时:                           │
│ 1. 找到对应的树节点                      │
│ 2. 检查节点状态是否允许该操作            │
│ 3. 若不允许 → 报告 UB                   │
│ 4. 更新相关节点状态（如 Reserved→Active）│
└─────────────────────────────────────────┘
```

---

### 模块 5: 正例集

#### 5.1 Minimal（最小正例）

TB 允许的代码（SB 误报）：

```rust
// 这段代码在 SB 下是误报 UB，在 TB 下合法
fn reborrow_then_parent(x: &mut i32) -> i32 {
    let y = &mut *x;  // TB: y 是 Reserved，x 仍 Active
    *y = 1;
    *x                // TB: ✅ 合法；SB: ❌ 误报 UB
}

fn main() {
    let mut val = 0;
    println!("{}", reborrow_then_parent(&mut val));
}
```

#### 5.2 Realistic（真实场景）

递归数据结构中的内部可变性：

```rust
struct Node {
    value: i32,
    next: Option<Box<Node>>,
}

impl Node {
    // TB 允许这种递归遍历模式
    fn sum(&mut self) -> i32 {
        let child_sum = self.next.as_mut().map_or(0, |n| n.sum());
        self.value + child_sum
        // SB 可能在递归返回时误报，因为子节点的 &mut 与父节点冲突
    }
}
```

#### 5.3 Production-grade（生产级）

使用 Miri + TB 进行 CI 验证：

```yaml
# .github/workflows/miri.yml
name: Miri Tree Borrows Check

on: [push, pull_request]

jobs:
  miri:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Install Miri
        run: |
          rustup component add miri
          cargo miri setup
      - name: Run tests with Tree Borrows
        run: |
          MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test
      - name: Run examples with Tree Borrows
        run: |
          MIRIFLAGS="-Zmiri-tree-borrows" cargo miri run --example unsafe_demo
```

---

### 模块 6: 反例集

#### 反例 1: 通过 &mut 写 Frozen 分支

**错误代码**:

```rust
fn bad_write_through_frozen(x: &mut i32) {
    let y = &*x;        // y: Frozen
    let z = &*y;        // z: Frozen

    unsafe {
        *x = 42;        // ❌ TB: x 的子树包含 Frozen 节点，写是 UB！
    }
}
```

**Miri 错误**:

```text
error: Undefined Behavior: attempting to write through a pointer with Frozen permission
  |
  |         *x = 42;
  |         ^^^^^^^
```

**根因推导**: `y = &*x` 创建了共享引用，使 `x` 的子树进入 Frozen 状态。Frozen 分支禁止任何写入。这是**真实的 UB**，编译器可能基于"无别名写入"假设进行优化。

**修复方案**:

```rust
fn good_write(x: &mut i32) {
    *x = 42;  // ✅ 直接写，无需创建共享引用
}
```

**抽象原则**: **"Frozen 即只读承诺"**：一旦 `&T` 被创建，对应的内存区域在引用存活期间不可变。通过 `unsafe` 绕过此限制是 UB。

---

#### 反例 2: 悬垂引用的使用

**错误代码**:

```rust
fn bad_dangling() -> i32 {
    let ptr: *mut i32;
    {
        let x = 42;
        ptr = &mut x;
    }
    unsafe { *ptr }  // ❌ TB: ptr 指向的分配已释放，权限树已销毁
}
```

**Miri 错误**:

```text
error: Undefined Behavior: dereferencing pointer to deallocated memory
```

**根因推导**: `x` 在作用域结束时被 drop，对应的内存分配被释放。`ptr` 成为悬垂指针，解引用是 UB。

**修复方案**:

```rust
fn good_value() -> i32 {
    let x = 42;
    x  // 返回值，而非引用
}
```

---

#### 反例 3: 双重释放（Double Free）

**错误代码**:

```rust
fn bad_double_free() {
    let ptr = Box::into_raw(Box::new(42));
    unsafe {
        drop(Box::from_raw(ptr));  // 第一次释放
        drop(Box::from_raw(ptr));  // ❌ TB: 重复释放同一分配
    }
}
```

**Miri 错误**:

```text
error: Undefined Behavior: double-free of heap allocation
```

**根因推导**: `Box::from_raw(ptr)` 重建了 `Box`，第一次 `drop` 释放了内存。第二次 `drop` 时，该分配已不存在，构成双重释放。

**修复方案**:

```rust
fn good_drop() {
    let ptr = Box::into_raw(Box::new(42));
    unsafe {
        drop(Box::from_raw(ptr));
    }
    // ptr 不再有效，不可再次使用
}
```

---

## 🗺️ 模块 7: 思维表征套件

### 表征 A: Stacked Borrows vs Tree Borrows 对比图

```text
场景: fn example(x: &mut i32) { let y = &mut *x; *y = 1; *x }

Stacked Borrows (线性栈模型):
─────────────────────────────────
步骤 1: x = &mut data
    栈: [x (Active)]

步骤 2: y = &mut *x
    栈: [x (Active), y (Active)]
        ↑ SB 不允许两个 Active &mut 共存！
        或: [x (Disabled), y (Active)]

步骤 3: *y = 1
    栈: [x (Disabled), y (Active)]

步骤 4: *x
    栈: [x (Disabled), y (Active)]
        ↑ x 是 Disabled！❌ UB

─────────────────────────────────
结果: SB 报告 UB（误报）

Tree Borrows (树形模型):
─────────────────────────────────
步骤 1: x = &mut data
    树: data
        └── x (Active)

步骤 2: y = &mut *x
    树: data
        └── x (Active)
            └── y (Reserved)  ← 关键差异！y 是 Reserved 而非 Active

步骤 3: *y = 1
    树: data
        └── x (Active)
            └── y (Reserved → Active)

步骤 4: *x
    树: data
        └── x (Active)
            └── y (Active)
        ↑ x 作为父节点，仍保留读权限！✅ 合法

─────────────────────────────────
结果: TB 允许此代码
```

### 表征 B: 权限状态转换图

```text
                    ┌─────────────────────────────────────┐
                    │  新引用创建                           │
                    │  &mut T → Reserved                   │
                    │  &T     → Frozen                     │
                    └──────────────┬──────────────────────┘
                                   │
                                   ▼
                    ┌─────────────────────────────────────┐
                    │  Reserved                             │
                    │  • 可读（父节点仍 Active）             │
                    │  • 首次写 → Active                   │
                    │  • 父创建 &T → Frozen                │
                    └──────────────┬──────────────────────┘
                                   │
              ┌────────────────────┼────────────────────┐
              │ 首次写             │ 父被共享            │
              ▼                    ▼                    │
    ┌──────────────────┐  ┌──────────────────┐        │
    │ Active            │  │ Frozen            │        │
    │ • 可读可写        │  │ • 只读            │        │
    │ • 可创建子节点    │  │ • 不可写          │        │
    │                   │  │ • 子节点必须 Frozen│       │
    └───────┬───────────┘  └───────┬───────────┘        │
            │                      │                    │
            │ 子节点 Active        │ 尝试写             │
            │ 父变为受限           ▼                    │
            │              ┌──────────────────┐        │
            │              │ Disabled         │◄───────┘
            │              │ • 任何访问 = UB  │        │
            │              │ • 不可逆         │◄───────┘
            │              └──────────────────┘        │
            │                      ▲                   │
            └──────────────────────┘                   │
              不兼容访问（如通过 &mut 写 Frozen 分支）   │
```

### 表征 C: SB 误报 vs TB 合法代码矩阵

| 代码模式 | Stacked Borrows | Tree Borrows | 说明 |
|----------|----------------|--------------|------|
| `let y = &mut *x; *y; *x` | ❌ 误报 UB | ✅ 合法 | Reserved 允许父节点继续使用 |
| `let y = &*x; *x = 1` | ❌ UB（正确） | ❌ UB（正确） | 共享引用后不可写 |
| 递归 `&mut self` 调用 | ❌ 常误报 | ✅ 合法 | 递归遍历是安全模式 |
| `addr_of_mut!` 后通过 &mut 写 | ❌ 常误报 | ✅ 合法 | addr_of_mut 不创建 Active 引用 |
| 通过 `*mut T` 写 `&T` 存活区域 | ❌ UB（正确） | ❌ UB（正确） | 真实别名违规 |
| `Vec::swap` 内部实现 | ❌ 误报 | ✅ 合法 | 标准库模式 |

---

## 📚 模块 8: 国际化对齐

### 8.1 官方来源

| 来源 | 类型 | 对应章节/条目 | 本文档对应点 |
|------|------|---------------|--------------|
| [Miri 文档](https://github.com/rust-lang/miri) | 官方工具 | Tree Borrows 选项 | 模块 4.3 |
| [Rust Reference - Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | 官方参考 | UB 定义 | 模块 6 |
| [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | 官方参考 | 内存模型讨论 | 模块 1.3 |

### 8.2 学术来源

| 论文/来源 | 会议/机构 | 核心论证 | 本文档对应点 |
|-----------|-----------|----------|--------------|
| **"Tree Borrows"** | PLDI 2025 Distinguished Paper | 树形权限模型的形式化定义、与 Stacked Borrows 的对比评估、54% 误报降低的实证分析 | 全书 |
| **"Stacked Borrows"** | POPL 2019 (Jung et al.) | Rust 第一个形式化内存模型，线性栈结构 | 模块 1.3 |
| **"RustBelt"** | POPL 2018 | 用 Iris 分离逻辑证明 Rust 类型系统，为内存模型提供理论基础 | 模块 1.3 |

### 8.3 社区权威

| 作者 | 文章/演讲 | 核心观点 | 本文档对应点 |
|------|-----------|----------|--------------|
| **Ralf Jung** | [Tree Borrows 介绍](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html) | Tree Borrows 的设计动机与核心机制 | 模块 1 |
| **Miri 团队** | [Miri Changelog](https://github.com/rust-lang/miri/blob/master/CHANGELOG.md) | Tree Borrows 成为默认模型的演进过程 | 模块 4.3 |
| **Villani et al.** | PLDI 2025 演讲 | 论文作者对 Tree Borrows 的直观解释 | 模块 1.3 |

### 8.4 跨语言对比

| 维度 | Rust (Tree Borrows) | C/C++ | LLVM `noalias` | Java/JVM |
|------|---------------------|-------|----------------|----------|
| **别名分析精度** | 高（树形权限） | 低（程序员负责） | 中（基于 `noalias`） | 低（GC 掩盖） |
| **UB 检测工具** | Miri + TB | Valgrind/ASan/UBSan | 无专用工具 | 无 |
| **误报率** | 低（比 SB 降 54%） | N/A | N/A | N/A |
| **编译期保证** | ✅（safe Rust） | ❌ | ⚠️（仅优化提示） | ✅（类型安全） |
| **形式化验证** | RustBelt + TB | 无 | 无 | 无 |

> **关键差异**: Rust 是唯一在语言层面提供**形式化内存模型** + **自动 UB 检测工具**（Miri）的系统语言。C/C++ 依赖外部工具（Valgrind/ASan），但无法检测所有 UB 类型。TB 的 54% 误报降低使其比 SB 更实用，推动了 Miri 在生产代码中的采用。

---

## ⚖️ 模块 9: 设计权衡分析

### 9.1 为什么 Tree Borrows 替代了 Stacked Borrows？

核心驱动力是**误报率**：SB 的线性栈模型对常见的 reborrow 模式过于严格，导致 54% 的 Miri 报告是误报。这使得开发者倾向于忽略 Miri 警告，降低了工具的实用性。

TB 通过树形模型解决了这个问题：

1. **Reserved 状态**：允许父引用在子引用创建后继续使用，直到子引用首次写入。
2. **树的局部性**：冲突检查限定在子树范围内，不影响兄弟引用。
3. **更自然的语义**：与程序员的直觉（"reborrow 是子引用，不应立即禁用父引用"）一致。

### 9.2 该设计的成本

**实现复杂度**：TB 的树结构比 SB 的栈更复杂，Miri 的执行速度略有下降。

**仍有误报**：虽然降低了 54%，但 TB 仍有过度保守的情况。某些合法的 `unsafe` 模式（如复杂的指针运算）仍可能被误判。

**尚未稳定**：TB 仍是实验性内存模型，尚未写入 Rust 语言规范。未来可能进一步调整。

### 9.3 什么场景下 TB 是次优的？

1. **不运行 Miri 时**：TB 是 Miri 的内存模型，对不运行 Miri 的代码无直接影响。
2. **极端性能优化代码**：某些高性能 `unsafe` 代码可能依赖 TB 不允许的别名模式，需要 `-Zmiri-disable-validation` 跳过检查。
3. **与 C 代码混用时**：C 代码不遵守 Rust 的别名规则，TB 对 FFI 边界的检查有限。

---

## 📝 模块 10: 自我检测与练习

### 概念性问题

1. **Tree Borrows 的 Reserved 状态与 Stacked Borrows 的对应处理有何本质差异？** 为什么 Reserved 能解决 54% 的误报？

2. **在 TB 中，父引用在子引用变为 Active 后是否完全失去权限？** 如果子引用被 drop 呢？

3. **TB 的 Frozen 状态与 Rust 编译期的 `&T` 不可变性有何关系？** 为什么通过 `unsafe` 写 Frozen 区域是 UB，即使在编译期允许？

### 代码修复题

**题 1**: 以下代码在 Miri + TB 下会报告 UB。请解释原因并修复：

```rust
fn process(data: &mut [i32]) {
    let ptr = data.as_mut_ptr();
    for i in 0..data.len() {
        unsafe {
            *ptr.add(i) += 1;
        }
    }
}
```

<details>
<summary>参考答案</summary>

**分析**: 此代码在 TB 下通常**不会**报告 UB，因为 `as_mut_ptr()` 创建的原始指针与 `data` 的借用是兼容的（`addr_of_mut!` 语义）。但如果 Miri 的精确检查认为 `ptr` 的使用与 `data` 的活跃借用冲突，可能需要显式分离。

**更安全的写法**:

```rust
fn process(data: &mut [i32]) {
    for item in data.iter_mut() {
        *item += 1;
    }
}
```

> 此例实际上展示了 TB 相比 SB 的优势：SB 可能对 `as_mut_ptr()` 后的指针算术误报，而 TB 更精确地处理这种情况。

</details>

**题 2**: 分析以下代码在 TB 下的行为：

```rust
fn mixed_refs(x: &mut i32) {
    let y = &*x;        // 共享引用
    println!("{}", y);

    let z = &mut *x;    // 新的可变引用
    *z = 42;
}
```

<details>
<summary>参考答案</summary>

**分析**:

1. `y = &*x`：`y` 是 Frozen，`x` 的子树变为 Frozen
2. `println!("{}", y)`：合法，Frozen 允许读
3. `z = &mut *x`：尝试创建可变引用，但 `x` 的子树是 Frozen

**结果**: 第 3 行在**safe Rust**中会编译失败（借用检查器阻止）。如果通过 `unsafe` 实现类似逻辑，TB 会判定为 UB，因为 Frozen 分支不可写。

此例展示了 TB 与编译期借用检查的一致性。

</details>

### 开放设计题

**题 3**: 你正在维护一个使用大量 `unsafe` 的 crate（如自定义集合库）。你面临选择：

1. 在 CI 中运行 Miri + Stacked Borrows（保守，可能有很多误报）
2. 在 CI 中运行 Miri + Tree Borrows（较新，误报少）
3. 不运行 Miri，依赖人工代码审查
4. 使用 `cargo-fuzz` + `address-sanitizer` 替代

请从以下维度分析 trade-off：

- 检测覆盖率（能发现多少类 bug？）
- 开发者体验（误报率、运行时间）
- CI 成本（执行时间、基础设施）
- 长期维护（工具稳定性、社区支持）

> 💡 提示：参考模块 7 的对比矩阵和模块 9 的成本分析。

---

## 📖 延伸阅读

- [Tree Borrows PLDI 2025 Paper](https://pldi25.sigplan.org/) — 原始论文
- [Ralf Jung 的博客](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html) — Tree Borrows 介绍
- [Miri 文档](https://github.com/rust-lang/miri) — Miri 使用指南
- [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) — Rust UB 边界讨论

---

> 🎉 **恭喜你！** 你已经掌握了 Tree Borrows 的核心机制。理解树形权限模型、Reserved 状态的设计意图，以及 TB 与 SB 的根本差异，是深入 Rust 内存模型和 `unsafe` 代码验证的关键。
>
> **下一步建议**: 在你的项目中启用 `MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test`，观察 TB 与 SB 的差异，并修复任何检测到的真实 UB。

---

**文档版本**: 2.0
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-09
> **权威来源**: [Tree Borrows Paper (Villani et al., PLDI 2025)](https://pldi25.sigplan.org/), [Miri Tree Borrows](https://github.com/rust-lang/miri), [Rust Reference — Aliasing Rules](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 PLDI 2025 Distinguished Paper 来源标注、Miri 实现引用、Rust Reference 别名规则来源 [来源: Authority Source Sprint Batch 8]

**状态**: ✅ 权威来源对齐完成 (Batch 8)
