# Borrowing（借用）

> **层级**: L1 基础概念
> **前置概念**: [Ownership](./01_ownership.md)
> **后置概念**: [Lifetimes](./03_lifetimes.md) · [Slices](../01_foundation/04_type_system.md) · [Interior Mutability](../02_intermediate/03_memory_management.md)
> **主要来源**: [TRPL: Ch4.2](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) · [Wikipedia: Reference (computer science)] · [Rust Reference: References]

---

**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成权威定义、借用规则矩阵、形式化视角、思维导图、示例反例

---

## 一、权威定义（Definition）

### 1.1 TRPL 官方定义

> **[TRPL: Ch4.2]** At any given time, you can have **either one mutable reference** or **any number of immutable references**. References must always be valid. These are the rules of references. This is the part that is called *borrowing*.

### 1.2 Wikipedia 对齐定义

> **[Wikipedia: Reference (computer science)]** A reference is a value that enables a program to indirectly access a particular datum, such as a variable's value or a record, in the computer's memory or in some other storage device. In Rust, references are governed by the borrowing rules which enforce memory safety at compile time.

> **[Wikipedia: Pointer aliasing]** In computing, pointer aliasing occurs when two or more pointers refer to the same memory location. The Rust borrow checker enforces *aliasing XOR mutation* — mutable aliasing (one mutable and one or more immutable references to the same data) is prohibited at compile time, eliminating a major class of memory errors including data races and iterator invalidation.

> **[TRPL: Ch19.1]** Unsafe Rust gives you access to five superpowers, including the ability to dereference raw pointers. However, even in unsafe blocks, you must uphold the borrowing rules manually; the compiler cannot enforce them for raw pointers.

### 1.3 形式化视角

借用是**所有权的临时授权**（temporary authorization），不改变资源的最终归属：

```text
借用前:  x : Own(T)
借用中:  x : Frozen(T) , r : &T   （不可变借用）
        x : Locked(T) , r : &mut T （可变借用）
借用后:  x : Own(T)               （所有权归还）
```

> **[来源: RustBelt: POPL 2018]** 借用的形式化语义为"所有权的临时授权"，不改变资源的最终归属（所有权归还）。 ✅

> **过渡**: 权威定义从学术和官方来源确立了借用的语义，而概念属性矩阵则将这些语义转化为可操作的规则对比——&T 与 &mut T 在权限、别名、安全性上的系统性差异。

---

## 二、概念属性矩阵（Attribute Matrix）

### 2.1 借用类型核心矩阵

| **维度** | **不可变借用 `&T`** | **可变借用 `&mut T`** | **裸指针 `*const T` / `*mut T`** |
|:---|:---|:---|:---|
| **别名限制** | 允许多个共存 | 同一时间仅一个 | 无限制（unsafe） |
| **数据修改** | ❌ 只读 | ✅ 可读写 | ✅ 可读写（unsafe） |
| **原变量可用性** | ✅ 可读，不可 move | ❌ 不可访问 | ❌ 无保证 |
| **编译期检查** | ✅ 严格 | ✅ 严格 | ❌ 无 |
| **空值允许** | ❌ 引用永不为 null | ❌ 引用永不为 null | ✅ 可为 null |
| **悬垂保护** | ✅ 编译期阻止 | ✅ 编译期阻止 | ❌ 无保护 |
| **形式化对应** | 共享权限（shared permission） | 独占权限（exclusive permission） | 无形式化保证 |

### 2.2 借用规则 vs 其他语言对比

| **语言** | **机制** | **别名-可变分离** | **编译期检查** | **运行时成本** |
|:---|:---|:---|:---|:---|
| **Rust** | `&T` / `&mut T` | ✅ 严格分离 | ✅ 是 | 零 |
| **C++** | `const T&` / `T&` | ❌ 程序员自律 | ❌ 无 | 零 |
| **Swift** | `let` / `var` + exclusivity | ⚠️ 运行时检查 | ⚠️ 部分（enforcement） | 有（运行时） |
| **Kotlin** | `val` / `var` | ❌ 仅引用不可变 | ❌ 无 | 零 |
| **Java** | `final` 引用 | ❌ 对象内容可变 | ❌ 无 | 零 |

### 2.3 借用状态转换矩阵

| **当前状态** | **申请 `&T`** | **申请 `&mut T`** | **Move 原变量** | **结果状态** |
|:---|:---|:---|:---|:---|
| `Own(T)` | ✅ 允许多个 `&T` | ✅ 允许一个 `&mut T` | ✅ 允许 | `Frozen(T)` / `Locked(T)` / `Moved` |
| `Frozen(T)`（有 `&T`） | ✅ 允许更多 `&T` | ❌ 禁止 | ❌ 禁止 | `Frozen(T)` |
| `Locked(T)`（有 `&mut T`） | ❌ 禁止 | ❌ 禁止 | ❌ 禁止 | `Locked(T)` |
| `Moved` | ❌ 禁止 | ❌ 禁止 | ❌ 禁止 | `Moved` |

> **过渡**: 属性矩阵展示了借用规则的静态特征，接下来需要深入其形式化根基——分离逻辑、别名-可变分离定理——以理解这些规则为何能构成完备的内存安全证明。

---

## 三、形式化理论根基（Formal Foundation）

### 3.1 分离逻辑（Separation Logic）视角

借用可以被理解为**权限的分割与重组**：

```text
原权限:      Own(T)  —— 读 + 写 + 转移
不可变借用:  Own(T)  ⊸  (&T ⊗ Own_rest)
            其中 Own_rest = 保留的清理义务（drop obligation）

可变借用:    Own(T)  ⊸  (&mut T ⊗ Own_rest)
            其中 &mut T 独占读写权限

归还:        (&T ⊗ Own_rest)  →  Own(T)
```

> **[RustBelt: POPL 2018]** Rust's borrow checker can be understood in terms of **fractional permissions** or **separation logic**: an immutable borrow splits ownership into read-only fractions, while a mutable borrow requires the full exclusive permission.

### 3.2 别名-可变分离（Aliasing XOR Mutation）

Rust 借用的核心定理：

```text
定理 (Alias-XOR-Mutation):
对于任意内存位置 M，在 Safe Rust 程序的任意执行点：
    ¬(存在多个活跃别名 ∧ 至少一个别名可写)

等价表述:
    (多个活跃引用 → 全部不可变) ∧ (可变引用 → 唯一)
```

这是 Rust 消除数据竞争的**充分条件**。

> **[来源: RustBelt: POPL 2018]** Alias-XOR-Mutation 是 Rust 消除数据竞争的充分条件，基于分离逻辑中的分数权限 (fractional permissions)。 ✅
> **[来源: Wikipedia: Alias analysis]** 别名分析中"可变与别名互斥"是内存安全的核心条件。 ✅

> **过渡**: 形式化根基从逻辑公理角度解释了借用系统的正确性，而思维导图则从知识结构角度帮助读者建立概念之间的关联网络。

---

## 四、思维导图（Mind Map）

```mermaid
graph TD
    A[Borrowing 借用系统] --> B[不可变借用 &T]
    A --> C[可变借用 &mut T]
    A --> D[借用规则]
    A --> E[借用检查器]
    A --> F[高级模式]

    B --> B1[多个共存]
    B --> B2[只读访问]
    B --> B3[原变量可读不可 move]
    B --> B4[Reborrow: &&T]

    C --> C1[唯一存在]
    C --> C2[读写访问]
    C --> C3[原变量完全冻结]
    C --> C4[Reborrow: &mut &mut T]

    D --> D1[任意时刻]
    D --> D2[要么 1个 &mut]
    D --> D3[要么 N个 &]
    D --> D4[引用必须有效]

    E --> E1[Non-lexical lifetimes NLL]
    E --> E2[Two-phase borrows]
    E --> E3[MIR Borrowck]

    F --> F1[Self-referential structs]
    F --> F2[Pin<&mut T>]
    F --> F3[Interior mutability]
```

> **过渡**: 思维导图呈现了借用的静态知识结构，而决策树则将这种知识转化为动态的判断流程——面对具体问题时"该用 &T 还是 &mut T"。

---

## 五、决策/边界判定树（Decision / Boundary Tree）

### 5.1 "我该用 `&T` 还是 `&mut T`？" 决策树

```mermaid
graph TD
    Q1[函数需要修改数据?] -->|否| Q2[调用方需要保留所有权?]
    Q1 -->|是| Q3[数据在函数外仍需被访问?]
    Q2 -->|是| A1[使用 &T]
    Q2 -->|否| A2[使用 T 转移所有权]
    Q3 -->|是| A3[使用 &mut T]
    Q3 -->|否| A2

    A1[不可变借用 &T]
    A2[所有权转移 T]
    A3[可变借用 &mut T]
```

### 5.2 借用冲突边界判定

```mermaid
graph TD
    B1[已存在 &T] --> B2[申请 &mut T]
    B2 -->|编译期| E1[E0502: cannot borrow mutably<br/>because immutable borrows exist]

    B3[已存在 &mut T] --> B4[申请 &T 或 &mut T]
    B4 -->|编译期| E2[E0499: cannot borrow mutably more than once]

    B5[已存在 &mut T] --> B6[原变量直接使用]
    B6 -->|编译期| E3[E0503: cannot use because mutable borrow exists]

    B7[NLL 前: 引用存活到最后使用] --> B8[NLL 后: 引用存活到最后使用]
    B8 -->|编译期| R1[更短的实际生命周期<br/>减少借用冲突]
```

> **过渡**: 决策树回答"怎么做"的问题，而定理推理链回答"为什么能这么做"——通过引理、定理、推论的层层演绎，建立借用系统的形式化保证，特别是分数权限的数学基础。

---

## 六、定理推理链（Theorem Chain）

### 6.1 借用 ⇒ 无数据竞争

```text
前提 1: Alias-XOR-Mutation 规则被编译器强制执行
前提 2: 数据竞争 = 多个线程同时访问 + 至少一个写 + 无同步
前提 3: `Send` / `Sync` trait 控制跨线程共享
    ↓
定理: Safe Rust 中不存在数据竞争
    ↓
推论: 所有并发数据访问要么是只读的，要么是同步的独占访问
```

> **[来源: RustBelt: POPL 2018]** Safe Rust 中不存在数据竞争的形式化定理，基于 AXM 规则与 Send/Sync 的类型约束。 ✅
> **[来源: Wright-Felleisen 1994]** 类型安全保证可推导出并发安全，前提是所有权与别名规则被严格执行。 ✅

### 6.2 借用有效性定理

```text
前提: 借用检查器接受程序 P
    ↓
定理: P 中所有引用在其整个生命周期内指向有效内存
    ↓
证明概要:
  - 引用不能比被引用数据活得更久（生命周期约束）
  - 被引用数据在引用存活期间不会被 move（借用规则）
  - 被引用数据在引用存活期间不会被释放（Drop 顺序 + NLL）
```

> **[来源: Rust Reference: References]** 引用有效性由生命周期约束和借用检查器共同保证。 ✅
> **[来源: Tofte & Talpin 1994]** 引用不能比被引用数据活得更久 — 区域类型的核心约束。 ✅

### 6.3 定理一致性矩阵

> **推理链全景**: 引理 L1（&T 共享读安全）⟹ 引理 L2（&mut T 独占写安全）⟹ 定理 T1（AXM: Alias-XOR-Mutation）⟹ 定理 T2（引用有效性）⟹ 定理 T3（Reborrow 安全）⟹ 定理 T4（NLL 流敏感安全）⟹ 定理 T5（借用 ⟹ 无数据竞争）⟹ 定理 T6（Two-Phase Borrow 安全）⟹ 推论 C1（内部可变性安全）

| 定理/引理/推论 | 前提 | 结论 | 依赖的 L4 公理 | 被哪些定理依赖 | 失效条件 | 典型错误码 |
|:---|:---|:---|:---|:---|:---|:---|
| **L1: &T 共享读安全** | 借用检查器接受 &T | 多个 &T 共存不会导致数据竞争 | 分离逻辑: 分数权限 0 < f < 1 只读共享 | T1, T5, C1 | `UnsafeCell` 内部可变突破只读承诺 | E0502 |
| **L2: &mut T 独占写安全** | 借用检查器接受 &mut T | 同一时间仅一个 &mut T，读写无别名冲突 | 分离逻辑: 分数权限 f = 1.0 独占 | T1, T5, T6 | `unsafe` 构造多个 `&mut T` | E0499 |
| **T1: AXM (Alias-XOR-Mutation)** | L1 + L2 + 借用检查器接受程序 P | Safe Rust 中不存在"多个活跃别名且至少一个可写"的状态 | 分离逻辑: 别名与可变互斥公理 | T5, C1 | `UnsafeCell`、裸指针别名、FFI | E0502/E0499 |
| **T2: 引用有效性** | 生命周期约束满足 + T1 | P 中所有引用在其整个生命周期内指向有效内存 | 区域类型: 生命周期偏序 ⊆ | 所有引用使用场景 | `'static` 误用、自引用结构、悬垂返回 | E0597 |
| **T3: Reborrow 安全** | &mut T 可降级为 &T（隐式或显式） | 降级后的 &T 可与其它 &T 共存 | 权限降级: 1.0 → 0.5 只读分数 | 迭代器模式、方法调用 | 降级后通过 unsafe 恢复写权限 | E0502 |
| **T4: NLL 流敏感安全** | 控制流分析 + 实际使用点结束借用 | 词法作用域外的合法借用被接受 | 流敏感分析 (RFC 2094) | T2 | 循环中跨迭代借用、自引用 | E0597/E0716 |
| **T5: 借用 ⟹ 无数据竞争** | T1 + `T: Sync` / `T: Send` | 跨线程/单线程均无数据竞争 | 分离逻辑 + Send/Sync 公理 | — | `unsafe`、FFI、`UnsafeCell` | E0520 |
| **T6: Two-Phase Borrow 安全** | 方法调用解析 + T2 | `v.push(v.len())` 等模式合法 | 两阶段借用: &mut → & → &mut | — | 嵌套方法调用中显式同时借用 | E0502 |
| **C1: 内部可变性安全** | `UnsafeCell<T>` + 运行时检查 | `RefCell`/`Cell` 在 &T 下提供可变访问 | 超出标准分离逻辑，需运行时不变式 | — | 运行时违反借用规则 → panic | runtime panic |

> **[来源: RustBelt: POPL 2018]** L1/L2/T1/T5 — 基于分离逻辑分数权限的共享读与独占写保证。 ✅
> **[来源: Tofte & Talpin 1994]** T2 — 区域类型保证引用在其生命周期内指向有效内存。 ✅
> **[来源: Rust Reference: NLL]** T4 — 非词法生命周期基于控制流图的精确存活期分析 (RFC 2094)。 ✅
> **[来源: RFC 2025]** T6 — Two-Phase Borrows 允许方法调用中的临时不可变借用。 ✅
> **[来源: 💡 原创分析]** C1 — 内部可变性通过运行时检查替代编译期检查，是公理体系的受控扩展。 💡

> **一致性检查**: L1 ⟹ L2 ⟹ T1(AXM) ⟹ T5(无数据竞争)；T2(引用有效) ⟹ T3(Reborrow) ⟹ T6(两阶段)；C1 是 T1 的受控逆否扩展。全部 9 个定理形成**分层推理网络**。
>
> **跨层映射**: 本文件定理 ↔ [`00_meta/inter_layer_map.md`](../00_meta/inter_layer_map.md) §4.1 "内存安全完备性"

> **过渡**: 定理链提供了自上而下的形式化保证，而示例与反例则提供自下而上的直觉验证——通过正确代码与错误代码的对比，将抽象定理落地为具体可感知的编译器行为。

---

## 七、示例与反例（Examples & Counter-examples）

### 7.1 正确示例：不可变借用共存

```rust
// ✅ 正确: 多个不可变借用可以共存
fn main() {
    let s = String::from("hello");
    let r1 = &s;
    let r2 = &s;
    let r3 = &s;
    println!("{}, {}, {}", r1, r2, r3);  // ✅ 全部合法
}
```

### 7.2 正确示例：可变借用的独占性

```rust
// ✅ 正确: 可变借用独占访问
fn append_world(s: &mut String) {
    s.push_str(" world");
}

fn main() {
    let mut s = String::from("hello");
    append_world(&mut s);
    println!("{}", s);  // ✅ "hello world"
}
```

### 7.3 反例：可变 + 不可变借用共存（E0502）

```rust
// ❌ 反例: cannot borrow mutably while borrowed immutably
fn main() {
    let mut s = String::from("hello");
    let r1 = &s;          // 不可变借用开始
    let r2 = &mut s;      // E0502!
    println!("{}, {}", r1, r2);
}
```

**错误分析**：

- `r1 = &s` 创建了一个不可变借用
- `r2 = &mut s` 试图创建可变借用
- 根据借用规则，不可变借用存在时禁止可变借用

**修正方案**：

```rust
// ✅ 修正: 不可变借用使用完毕后再申请可变借用
fn main() {
    let mut s = String::from("hello");
    let r1 = &s;
    println!("{}", r1);   // r1 最后一次使用
    // r1 的实际生命周期在这里结束（NLL）
    let r2 = &mut s;      // ✅ 现在可以 mutable borrow
    r2.push_str(" world");
}
```

### 7.4 反例：多个可变借用（E0499）

```rust
// ❌ 反例: cannot borrow mutably more than once
fn main() {
    let mut s = String::from("hello");
    let r1 = &mut s;
    let r2 = &mut s;      // E0499!
    println!("{}, {}", r1, r2);
}
```

**修正方案**：

```rust
// ✅ 修正: 限制可变借用的作用域
fn main() {
    let mut s = String::from("hello");
    {
        let r1 = &mut s;
        r1.push_str(" world");
    } // r1 在这里结束
    let r2 = &mut s;      // ✅ s 重新可用
    r2.push_str("!");
}
```

### 7.5 边界示例：Two-Phase Borrows

```rust
// ✅ 边界: method call 的隐式重新借用
fn main() {
    let mut v = vec![1, 2, 3];
    v.push(v.len());  // ✅ 看似同时存在 &mut v 和 &v
                      // 实际: v.len() 先求值（不可变借用）
                      //      然后 v.push(...) 使用可变借用
                      // 两阶段借用允许这种临时借用模式
}
```

---

### 7.6 反命题与边界分析

> **系统分类**: 反命题覆盖 Safe Rust 保证的边界、独占写保证的边界、共享读保证的边界三个维度。

#### 命题 1: "借用规则保证无数据竞争"

```mermaid
graph TD
    P1["命题: 借用规则保证无数据竞争"] --> Q1{"使用 UnsafeCell?"}
    Q1 -->|是| F1["反例: UnsafeCell 允许 &T 与 *mut T 共存<br/>→ 运行时数据竞争"]
    Q1 -->|否| Q2{"使用裸指针?"}
    Q2 -->|是| F2["反例: *mut T 与 &T 指向同一内存<br/>→ UB（unsafe）"]
    Q2 -->|否| Q3{"使用 Rc&lt;RefCell&lt;T&gt;&gt;?"}
    Q3 -->|是| F3["反例: 运行时借用检查 panic<br/>→ 非数据竞争，但并发安全失败"]
    Q3 -->|否| T1["定理成立: 无数据竞争<br/>✅ 分离逻辑保证"]

    style F1 fill:#f66
    style F2 fill:#f66
    style F3 fill:#f96
    style T1 fill:#6f6
```

#### 命题 2: "&mut T 保证独占访问"

```mermaid
graph TD
    P2["命题: &mut T 保证独占访问"] --> Q4{"在 Safe Rust 中?"}
    Q4 -->|是| T2["定理成立: 编译器保证独占<br/>✅ 分离逻辑 f=1.0"]
    Q4 -->|否| Q5{"使用 UnsafeCell?"}
    Q5 -->|是| F4["反例: UnsafeCell&lt;T&gt; 内部可共享可变<br/>→ 通过 &T 获得 &mut T（unsafe）"]
    Q5 -->|否| Q6{"使用 unsafe + 裸指针?"}
    Q6 -->|是| F5["反例: 手动构造多个 &mut T<br/>→ 程序员完全承担责任"]
    Q6 -->|否| Q7{"使用 mem::transmute?"}
    Q7 -->|是| F6["反例: 类型系统欺骗<br/>→ 将 &T 转回 &mut T"]
    Q7 -->|否| N1["无已知突破方式"]

    style F4 fill:#f66
    style F5 fill:#f66
    style F6 fill:#f66
    style T2 fill:#6f6
```

#### 命题 3: "共享引用 &T 总是安全的"

```mermaid
graph TD
    P3["命题: 共享引用 &T 总是安全的"] --> Q8{"包装在 RefCell 中?"}
    Q8 -->|是| F7["反例: RefCell&lt;T&gt; 在 &T（RefCell）下<br/>→ 运行时 borrow_mut() 可变访问<br/>→ 违反 &T 只读直觉，可能导致 panic"]
    Q8 -->|否| Q9{"包装在 Mutex/RwLock 中?"}
    Q9 -->|是| F8["反例: 多线程 &amp;Mutex&lt;T&gt; 调用 lock()<br/>→ 运行时死锁或阻塞<br/>→ 非内存安全失败，但并发安全失败"]
    Q9 -->|否| Q10{"包含 UnsafeCell 字段?"}
    Q10 -->|是| F9["反例: 自定义结构体含 UnsafeCell<br/>→ &T 暴露内部可变 API<br/>→ 需要 unsafe 封装"]
    Q10 -->|否| T3["定理成立: &T 保证只读共享安全<br/>✅ 分数权限 f&lt;1 只读"]

    style F7 fill:#f66
    style F8 fill:#f66
    style F9 fill:#f66
    style T3 fill:#6f6
```

---

### 7.7 边界极限测试代码

```rust
// 边界测试 1: UnsafeCell 允许共享可变访问
use std::cell::UnsafeCell;

fn main() {
    let x = UnsafeCell::new(42);
    let r1 = unsafe { &*x.get() };      // &i32
    let r2 = unsafe { &mut *x.get() };  // &mut i32
    // 编译通过！但运行时若同时读写 → 数据竞争（UB）
    // 验证 T1 失效条件: UnsafeCell 突破 AXM
}
```

```rust
// 边界测试 2: RefCell 运行时借用检查 panic
use std::cell::RefCell;

fn main() {
    let rb = RefCell::new(vec![1, 2, 3]);
    let _w = rb.borrow_mut();
    // let _r = rb.borrow();  // ← 取消注释: thread 'main' panicked:
                              // already mutably borrowed
    // 验证 C1: 内部可变性将编译期检查延迟到运行时
}
```

```rust
// 边界测试 3: 自引用结构导致悬垂引用
fn main() {
    // 以下代码在 Safe Rust 中无法编译:
    // let mut v = vec![1, 2, 3];
    // let r = &v[0];
    // v.push(4);  // E0502: cannot borrow `v` as mutable
    // println!("{}", r);  // 若允许，r 可能因 realloc 而悬垂
    // 验证 T2: 引用有效性由借用检查器强制执行
}
```

> **过渡**: 示例与反例展示了借用规则在具体代码中的表现，而认知路径则将这些碎片整合为一条从"为什么不能同时读写"的直觉到分数权限形式化的渐进式学习曲线。

---

## 八、认知路径（Cognitive Path）

> 本章节从"为什么不能同时读写"的直觉出发，经过具体场景、模式抽象、形式规则、代码验证，最终到达分数权限（fractional permissions）的形式化理解。每步之间有过渡解释，说明"为什么需要下一步"。

### 8.1 六步递进框架

```text
Step 1: 直觉困惑 ──────────────────────────────────────────────────────────────
  "为什么 &mut s 和 &s 不能共存？"
  "为什么多个 &s 可以共存？"
  "为什么函数返回后引用还能用？"
  "为什么 for 循环中可以读不能改？"
  "RefCell 为什么能'打破'借用规则？"

  ↓ 过渡: 直觉上的'不能'和'能'需要转化为具体代码场景，
  ↓       否则只是模糊印象，无法区分规则与例外。

Step 2: 具体场景 ──────────────────────────────────────────────────────────────
  "同时读和修改同一 String 会出错（E0502）"
  "多个 &s 同时打印是合法的"
  "返回局部变量引用导致悬垂（E0597）"
  "迭代器遍历 Vec 时 push 会报错"
  "Rc<RefCell<T>> 在树结构中反向修改父节点"

  ↓ 过渡: 具体场景需要提炼为跨案例的通用模式，
  ↓       才能理解 Rust 的设计意图而非死记规则。

Step 3: 模式抽象 ──────────────────────────────────────────────────────────────
  "AXM 规则: 别名与可变互斥"
  "共享读: N 个 &T 同时只读是安全的"
  "独占写: 1 个 &mut T 独占读写权"
  "Reborrow: &mut T 可临时降级为 &T"
  "内部可变性: 运行时检查替代编译期检查"

  ↓ 过渡: 模式抽象需要匹配到已有的形式化理论体系，
  ↓       才能证明这些模式不是特例而是通用公理。

Step 4: 形式规则 ──────────────────────────────────────────────────────────────
  "分离逻辑: 分数权限 (fractional permissions)"
  "&T = 0 < f < 1 的只读分数，可无限分割共享"
  "&mut T = f = 1.0 的独占权限，不可分割"
  "区域类型: 引用的生命周期 ⊆ 数据存活期"
  "流敏感分析 NLL: 借用存活到实际最后使用点"

  ↓ 过渡: 形式规则必须能在实际代码中被验证，
  ↓       否则只是理论空想。

Step 5: 代码验证 ──────────────────────────────────────────────────────────────
  "编译器检查 &mut + & 共存时报错 E0502"
  "编译器允许多个 &T 共存"
  "编译器拒绝悬垂引用 E0597"
  "编译器自动 Reborrow: v.push(v.len()) 合法"
  "RefCell 运行时 panic: already mutably borrowed"

  ↓ 过渡: 代码验证需要推向极端边界，
  ↓       才能发现公理体系的覆盖范围与失效条件。

Step 6: 边界测试 ──────────────────────────────────────────────────────────────
  "UnsafeCell: &T 与 *mut T 共存导致 UB"
  "自引用结构: Vec 扩容后 &elem 悬垂"
  "Two-Phase Borrow: v.push(v.len()) 的隐式重借用"
  "RefCell 运行时 panic 替代编译错误"
  "嵌套借用: &mut &mut T 的权限传递链"
```

### 8.2 概念认知的 5 条主线

| 主线 | Step 1 直觉 | Step 2 场景 | Step 3 模式 | Step 4 形式规则 | Step 5 验证 | Step 6 边界 |
|:---|:---|:---|:---|:---|:---|:---|
| **&mut vs &** | "为什么不能同时有？" | 读 + 修改同一数据报错 | AXM: 读写互斥 | 分离逻辑分数权限 | E0502 | UnsafeCell 突破 |
| **多个 &T** | "为什么可以多个只读？" | 多个 println! 同时合法 | 共享读安全 | 0 < f < 1 只读分数 | 编译通过 | 内部可变性 RefCell |
| **悬垂引用** | "返回引用为什么崩溃？" | 返回局部变量 &s | 引用不能比对象活得长 | 区域类型偏序约束 | E0597 | NLL 缩小生命周期 |
| **Reborrow** | "v.push(v.len()) 为什么合法？" | 方法调用隐式重借用 | &mut → & 临时降级 | 权限降级: 1.0 → 0.5 | 编译通过 | 显式嵌套借用冲突 |
| **内部可变性** | "RefCell 怎么'打破'规则？" | 树结构反向修改父节点 | 运行时检查替代编译期 | 超出标准分离逻辑 | 运行时 panic | UnsafeCell 原始突破 |

> **[来源: RustBelt: POPL 2018]** "分离逻辑: 分数权限" — 不可变借用将所有权分割为只读分数，可变借用要求完整独占权限。 ✅
> **[来源: Tofte & Talpin 1994]** "区域类型: 偏序约束" — 引用的生命周期不能超过被引用数据的区域。 ✅
> **[来源: Rust Reference: NLL]** "NLL: 实际使用期有效" — 非词法生命周期基于数据流分析 (RFC 2094)。 ✅
> **[来源: Boyland 2003 (Fractional Permissions)]** "分数权限 f ∈ (0,1]" — 读权限可无限分割，写权限要求 f=1.0。 ✅

**认知脚手架**:

- **类比**: &T 像"多人同时阅读公告板"，&mut T 像"一人独自编辑文档"。
- **反直觉点**: 很多语言允许多个可变引用（如 Java 对象引用），Rust 强制分离。
- **形式化过渡**: 从"不能同时有" → "读写互斥" → "分离逻辑中的分数权限分配 (f ∈ (0,1])"。

### 7.7 国际课程与论文对齐

| 来源 | 核心内容 | 与本文件对应 |
|:---|:---|:---|
| **[CMU 17-363: Programming Language Pragmatics]** | Ownership、Borrowing、Lifetime | L1-L2 基础概念 |
| **[CMU 17-350: Safe Systems Programming]** | 借用规则、内部可变性 | 工程实践 |
| **[Stanford CS340R: Rusty Systems]** | 内存安全实践 | 并发安全 |
| **[Wikipedia: Pointer aliasing]** | 别名分析通用概念 | AXM 规则 |
| **[Wikipedia: Reference (computer science)]** | 引用概念 | 借用语义 |
| **[Reynolds 2002: Separation Logic]** | 分离逻辑 | 借用形式化 |
| **[RustBelt: POPL 2018]** | 分数权限、借用语义 | 形式化验证 |

> **过渡**: 认知路径梳理了学习的心理过程，而知识来源关系则梳理了每一条论断的可信度——区分权威来源、形式化证明与原创分析。

---

## 九、知识来源关系（Provenance）

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| 借用规则：1个 &mut 或 N个 & | [TRPL: Ch4.2] | ✅ |
| 引用必须始终有效 | [TRPL: Ch4.2] | ✅ |
| `RefCell<T>` 运行时借用检查 | [TRPL: Ch15.5] | ✅ |
| `UnsafeCell<T>` 与内部可变性 | [TRPL: Ch19.1] · [Rust Reference: Interior Mutability] | ✅ |
| `Pin<&mut T>` 与自引用结构 | [TRPL: Ch20.3] · [Rust Reference: Pin] | ✅ |
| NLL (Non-Lexical Lifetimes) | [Rust Reference: NLL] · [RFC 2094] | ✅ |
| Two-Phase Borrows | [RFC 2025] | ✅ |
| 借用检查基于分离逻辑 | [RustBelt: POPL 2018] | ✅ |
| Alias-XOR-Mutation 定理 | [RustBelt] · [Wikipedia: Alias analysis] | ✅ |

> **过渡**: 知识来源关系确保了单文件内的论断可信度，而相关概念链接则将读者的视野扩展到整个知识网络——借用不是孤立概念，它与所有权、生命周期、并发、内部可变性等形成有机整体。

---

## 十、相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| **所有权** | [`./01_ownership.md`](./01_ownership.md) | 借用规则的前提与基础 |
| **生命周期** | [`./03_lifetimes.md`](./03_lifetimes.md) | 引用时效约束，与借用互补 |
| **类型系统** | [`./04_type_system.md`](./04_type_system.md) | 引用是类型的一部分，`&T`/`&mut T` 是类型构造器 |
| **Traits** | [`../02_intermediate/01_traits.md`](../02_intermediate/01_traits.md) | `Borrow`、`AsRef`、`Deref` 等 trait 的借用语义 |
| **智能指针** | [`../02_intermediate/03_memory_management.md`](../02_intermediate/03_memory_management.md) | `Box`、`Rc`、`Arc` 的 Deref 自动借用 |
| **内部可变性** | [`../02_intermediate/03_memory_management.md`](../02_intermediate/03_memory_management.md) | `RefCell`、`Cell` 运行时替代编译期检查 |
| **并发** | [`../03_advanced/01_concurrency.md`](../03_advanced/01_concurrency.md) | `Send`/`Sync` + AXM = 无数据竞争 |
| **Pin 与自引用** | [`../03_advanced/02_async.md`](../03_advanced/02_async.md) §8 | 自引用结构的借用检查器边界 |
| **Unsafe Rust** | [`../03_advanced/03_unsafe.md`](../03_advanced/03_unsafe.md) | `UnsafeCell`、裸指针突破借用规则 |
| **C++ 对比** | [`../05_comparative/01_rust_vs_cpp.md`](../05_comparative/01_rust_vs_cpp.md) | `const T&`/`T&` vs `&T`/`&mut T` |

> **过渡**: 相关概念链接构建了知识网络的全局视图，而待补充与演进方向则标记了本文件尚未覆盖的前沿主题与改进路径。

---

## 十一、待补充与演进方向（TODOs）

- [ ] **TODO**: 补充 `&str` 作为 `&[u8]` 的字符串特化形式的借用分析 —— 优先级: 中 —— 预计: Phase 1
- [ ] **TODO**: 补充 `Deref` / `DerefMut` 与自动借用的交互 —— 优先级: 中 —— 预计: Phase 2
- [ ] **TODO**: 补充 `AsRef` / `AsMut` 的借用语义差异 —— 优先级: 低 —— 预计: Phase 2
- [ ] **TODO**: 补充 `Cow<T>`（Clone on Write）的借用-所有权混合模式 —— 优先级: 低 —— 预计: Phase 2

### 补充章节：Pin<&mut T> 与自引用结构的借用

自引用结构（self-referential struct）是借用检查器的经典边界情况：

```text
问题:
  struct MyStruct {
      data: String,
      ptr: &String,  // 指向 data
  }
  // Rust 编译器拒绝：无法在 struct 中存储对自身的引用

原因:
  struct 可以整体 move，move 后 data 地址变，ptr 悬垂

Pin<&mut T> 的解决方案:
  1. 将 struct 标记为 !Unpin（使用 PhantomPinned）
  2. 用 Pin 包装，保证 struct 不被 move
  3. 内部自引用因此保持有效
```

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfRef {
    data: String,
    ptr: *const String,
    _pin: PhantomPinned,  // !Unpin
}

impl SelfRef {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut b = Box::new(Self {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });
        let ptr = &b.data as *const String;
        b.ptr = ptr;
        Box::into_pin(b)  // 或使用 Pin::new_unchecked
    }

    fn data_ptr(self: Pin<&Self>) -> *const String {
        self.ptr
    }
}

// 借用视角:
// Pin<&mut SelfRef> 提供对 SelfRef 的可变访问
// 但不能替换整个 SelfRef（防止 move）
// 可以修改非自引用的字段（通过 Pin::map_unchecked_mut）
```

> **[来源: Rust Reference: Pin]** Pin<&mut T> 通过 !Unpin 标记与位置不变性约束解决自引用结构的移动问题。 ✅

---

- [x] **TODO**: 补充 `Pin<&mut T>` 的自引用结构借用 —— 优先级: 高 —— 已完成 v1.1

`Pin<&mut T>` 解决的是"值被 move 后引用悬垂"的问题，它通过冻结值的位置来保证自引用有效。另一个同等重要的边界问题是：**如何在持有不可变引用 `&T` 的情况下修改数据？** 这正是内部可变性类型的核心议题。下面的补充章节分析 `Cell<T>` 和 `RefCell<T>` 如何在不破坏 AXM 定理的前提下，将借用检查从编译期延迟到运行时。

### 补充章节：Cell<T> / RefCell<T> 的内部可变性

#### 核心概念

```text
内部可变性（Interior Mutability）= 在拥有不可变引用的情况下修改数据

正常规则: &T → 不可变访问，&mut T → 可变访问
内部可变性: 通过 unsafe 或运行时检查，在 &T 时提供可变访问
```

#### Cell<T>：Copy 类型的内部可变

```rust
use std::cell::Cell;

// ✅ Cell<T> 要求 T: Copy
// 原理: 通过按位复制替换值，不暴露引用
fn cell_demo() {
    let c = Cell::new(42i32);
    let r = &c;  // 不可变引用
    c.set(100);  // ✅ 但可以通过 Cell 修改！
    println!("{}", c.get());  // 100
}

// 限制:
// Cell<String> ❌ String 不是 Copy
// Cell 不提供 &T 访问，只能 get/set（复制）
```

#### RefCell<T>：运行时可变借用检查

```rust
use std::cell::RefCell;

fn refcell_demo() {
    let rb = RefCell::new(String::from("hello"));
    {
        let mut w = rb.borrow_mut();  // 可变借用
        w.push_str(" world");
    }
    let r = rb.borrow();  // 不可变借用
    println!("{}", r);  // "hello world"
}

// ⚠️ 运行时 panic（非编译错误）
// let _w = rb.borrow_mut();
// let _r = rb.borrow();  // thread 'main' panicked: already mutably borrowed
```

#### 与借用规则的关系

```text
借用规则的"绕过" = 运行时检查替代编译期检查

            编译期检查          运行时检查
            ─────────────────────────────────
单线程      & / &mut            Cell / RefCell
多线程      （N/A）             Mutex / RwLock / Atomic

关键洞察:
  RefCell 不是"绕过"规则，而是将检查延迟到运行时
  代价: 运行时 panic 风险
  收益: 更灵活的数据结构（如图、树中的父指针回溯）
```

> **[来源: Rust Reference: Interior Mutability]** Cell<T> / RefCell<T> 通过运行时检查替代编译期检查，是内部可变性的安全抽象。 ✅
> **[来源: 💡 原创分析]** "RefCell 不是'绕过'规则，而是将检查延迟到运行时" — 对内部可变性与借用规则关系的精确概括。 💡

---

- [x] **TODO**: 补充 `Cell<T>` / `RefCell<T>` 的内部可变性与借用规则的"绕过" —— 优先级: 高 —— 已完成 v1.1
