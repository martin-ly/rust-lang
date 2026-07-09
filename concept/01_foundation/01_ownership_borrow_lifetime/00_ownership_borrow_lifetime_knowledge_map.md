> **内容分级**: [综述级]
>
> **EN**: Ownership, Borrowing & Lifetimes Knowledge Map
> **Summary**: A panoramic knowledge map of the Rust ownership-borrowing-lifetime-scope cluster, showing concept dependencies, smart-pointer ecosystems, and learning paths. Authoritative explanations of each topic remain in the dedicated concept pages.
>
> **受众**: [初学者] → [进阶者] → [研究者]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Structure
> **前置概念**: [Ownership](./01_ownership.md) · [Borrowing](./02_borrowing.md) · [Lifetimes](./03_lifetimes.md)
> **后置概念**: [Smart Pointers](../../02_intermediate/02_memory_management/12_smart_pointers.md) · [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md)
> **权威来源**: 本页为 `Ownership-Borrowing-Lifetimes` 知识拓扑的权威概念页；crate 文档仅保留导航 stub。

# Rust 所有权-借用-生命周期知识图谱

本页从**结构（Structure）**视角梳理 Rust 所有权（Ownership）系统的概念层次、依赖关系与学习路径。
各主题的完整解释请参见下方【权威页面】链接。

> **L0 关联**: 本页属于 L1 基础概念层；全局知识拓扑参见 [Rust 知识体系全局思维导图](../../00_meta/00_framework/knowledge_mindmap.md)。

---

## 一、概念层次总览

```mermaid
graph TB
    subgraph 基础层["🔷 基础层 (Foundation Layer)"]
        A[内存管理]
        B[类型系统]
        C[编译器]
    end

    subgraph 核心层["🔶 核心层 (Core Layer)"]
        D[所有权 Ownership]
        E[借用 Borrowing]
        F[生命周期 Lifetime]
        G[作用域 Scope]
    end

    subgraph 应用层["🔸 应用层 (Application Layer)"]
        H[智能指针]
        I[并发安全]
        J[内存安全]
        K[零成本抽象]
    end

    subgraph 实践层["🔹 实践层 (Practice Layer)"]
        L[设计模式]
        M[最佳实践]
        N[性能优化]
        O[错误处理]
    end

    A --> D
    B --> D
    C --> D
    D --> E
    D --> F
    D --> G
    E --> H
    F --> H
    E --> I
    F --> I
    D --> J
    E --> J
    F --> J
    H --> L
    I --> L
    J --> K
    L --> M
    K --> N
    M --> O
```

---

## 二、核心层知识图谱

### 2.1 所有权系统

```mermaid
graph TB
    subgraph 所有权规则["所有权核心规则"]
        A[规则1: 每个值有唯一所有者]
        B[规则2: 同时只能有一个所有者]
        C[规则3: 所有者离开作用域时值被释放]
    end

    subgraph 所有权操作["所有权操作"]
        D[移动 Move]
        E[克隆 Clone]
        F[复制 Copy]
        G[借用 Borrow]
    end

    subgraph 所有权模式["所有权模式"]
        H[完全所有权]
        I[共享所有权]
        J[智能指针]
    end

    A --> D
    B --> D
    C --> D

    D --> H
    E --> I
    F --> H
    G --> I

    H --> K[Box<T>]
    I --> L[Rc<T>]
    I --> M[Arc<T>]
    J --> K
    J --> L
    J --> M
```

| 操作 | 语义 | 性能成本 | 适用场景 | 类型要求 |
| :--- | :--- | :--- | :--- | :--- |
| **Move** | 转移所有权（Ownership） | 零成本 | 默认行为 | 所有类型 |
| **Clone** | 深拷贝 | 高成本 | 需要独立副本 | 实现 `Clone` |
| **Copy** | 按位复制 | 零成本 | 简单类型 | 实现 `Copy` |
| **Borrow** | 临时访问 | 零成本 | 共享/修改 | 所有类型 |

权威页面：[Ownership](./01_ownership.md) · [Move Semantics](./23_move_semantics.md)

### 2.2 借用系统

```mermaid
graph TB
    subgraph 借用规则["借用核心规则"]
        A[规则1: 多个不可变借用]
        B[规则2: 一个可变借用]
        C[规则3: 不可变和可变借用互斥]
    end

    subgraph 借用类型["借用类型"]
        D[不可变借用 &T]
        E[可变借用 &mut T]
    end

    subgraph 借用检查["借用检查器"]
        F[编译时检查]
        G[生命周期分析]
        H[作用域分析]
    end

    subgraph 借用模式["借用模式"]
        I[共享借用]
        J[独占借用]
        K[内部可变性]
        L[分割借用]
    end

    A --> D
    B --> E
    C --> D
    C --> E

    D --> F
    E --> F
    F --> G
    F --> H

    D --> I
    E --> J
    I --> K
    J --> L

    K --> M[Cell<T>]
    K --> N[RefCell<T>]
    L --> O[结构体字段]
```

| 借用（Borrowing）模式 | 检查时机 | 运行时（Runtime）开销 | 灵活性 | 安全性 |
| :--- | :--- | :--- | :--- | :--- |
| 不可变借用（Immutable Borrow） | 编译时 | 零成本 | 高 | 完全安全 |
| 可变借用（Mutable Borrow） | 编译时 | 零成本 | 中 | 完全安全 |
| `Cell<T>` | 编译时 | 零成本 | 中 | 限制在 `Copy` 类型 |
| `RefCell<T>` | 运行时（Runtime） | 引用（Reference）计数 | 高 | 运行时 panic |
| `Mutex<T>` | 运行时 | 锁开销 | 高 | 线程安全 |
| `RwLock<T>` | 运行时 | 锁开销 | 最高 | 线程安全 |

权威页面：[Borrowing](./02_borrowing.md) · [Interior Mutability](../../02_intermediate/02_memory_management/08_interior_mutability.md)

### 2.3 生命周期系统

```mermaid
graph TB
    subgraph 生命周期概念["生命周期核心概念"]
        A[生命周期]
        B[生命周期参数]
        C[生命周期约束]
    end

    subgraph 生命周期规则["生命周期规则"]
        D[输入生命周期]
        E[输出生命周期]
        F[省略规则]
    end

    subgraph 生命周期应用["生命周期应用"]
        G[函数签名]
        H[结构体定义]
        I[trait 定义]
        J[实现块]
    end

    subgraph 特殊生命周期["特殊生命周期"]
        K['static]
        L['_]
        M[Higher-Rank Trait Bounds]
    end

    A --> B
    B --> C
    B --> D
    B --> E
    D --> F
    E --> F
    C --> G
    C --> H
    C --> I
    C --> J
    K --> N[全局静态]
    L --> O[匿名生命周期]
    M --> P[for<'a>]
```

| 规则 | 条件 | 推断结果 | 示例 |
| :--- | :--- | :--- | :--- |
| 规则1 | 每个引用（Reference）参数获得独立生命周期（Lifetimes） | `'a, 'b, 'c...` | `fn f(x: &i32, y: &i32)` |
| 规则2 | 只有一个输入生命周期（Lifetimes） | 输出继承该生命周期 | `fn f(x: &i32) -> &i32` |
| 规则3 | 方法的 `self` 引用 | 输出继承 `self` 生命周期 | `fn f(&self) -> &i32` |

权威页面：[Lifetimes](./03_lifetimes.md) · [Advanced Lifetimes](./30_lifetimes_advanced.md)

---

## 三、应用层：智能指针生态

```mermaid
graph TB
    subgraph 单线程智能指针["单线程智能指针"]
        A[Box<T>]
        B[Rc<T>]
        C[Cell<T>]
        D[RefCell<T>]
    end

    subgraph 多线程智能指针["多线程智能指针"]
        E[Arc<T>]
        F[Mutex<T>]
        G[RwLock<T>]
        H[Atomic*]
    end

    subgraph 特殊用途智能指针["特殊用途"]
        I[Cow<T>]
        J[Weak<T>]
        K[Pin<T>]
    end

    A --> L[堆分配]
    B --> M[引用计数]
    C --> N[内部可变性-Copy]
    D --> O[内部可变性-运行时]

    E --> P[线程安全引用计数]
    F --> Q[互斥锁]
    G --> R[读写锁]
    H --> S[原子操作]

    I --> T[写时复制]
    J --> U[弱引用]
    K --> V[固定内存]
```

| 智能指针（Smart Pointer） | 所有权 | 线程安全 | 运行时开销 | 使用场景 |
| :--- | :--- | :--- | :--- | :--- |
| `Box<T>` | 独占 | ❌ | 零成本 | 堆分配 |
| `Rc<T>` | 共享 | ❌ | 引用计数 | 单线程共享 |
| `Arc<T>` | 共享 | ✅ | 原子引用计数 | 多线程共享 |
| `Cell<T>` | 独占 | ❌ | 零成本 | `Copy` 类型内部可变 |
| `RefCell<T>` | 独占 | ❌ | 运行时检查 | 运行时借用（Borrowing） |
| `Mutex<T>` | 独占 | ✅ | 锁开销 | 线程间互斥 |
| `RwLock<T>` | 共享/独占 | ✅ | 锁开销 | 读多写少 |

权威页面：[Smart Pointers](../../02_intermediate/02_memory_management/12_smart_pointers.md)

---

## 四、概念关系矩阵

### 核心概念相互依赖

| | 所有权 | 借用 | 生命周期 | 作用域 | 类型系统（Type System） |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **所有权** | - | 必须 | 必须 | 必须 | 基础 |
| **借用** | 基于 | - | 必须 | 必须 | 相关 |
| **生命周期** | 基于 | 约束 | - | 密切 | 相关 |
| **作用域** | 决定 | 影响 | 影响 | - | 相关 |
| **类型系统（Type System）** | 支持 | 支持 | 支持 | 支持 | - |

### 特性影响矩阵

| | 内存安全（Memory Safety） | 并发安全（Concurrency Safety） | 性能 | 易用性 | 灵活性 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **所有权系统** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ |
| **借用检查** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ |
| **生命周期** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | ⭐⭐⭐ |
| **智能指针（Smart Pointer）** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **NLL** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ |

---

## 五、学习路径

### 初学者路径（0–3 个月）

所有权基础 → 移动语义 → 借用基础 → 不可变/可变借用 → 生命周期入门 → 作用域管理 → 简单智能指针 → 基础实践

### 进阶路径（3–12 个月）

高级所有权模式 → 复杂借用 → 生命周期省略（Lifetime Elision） → trait 对象生命周期 → 智能指针高级用法 → 内部可变性 → 并发模式 → 性能优化 → 设计模式

### 专家路径（1 年+）

类型理论 → 生命周期子类型 → HRTB → Unsafe 与 FFI → `Pin`/`Unpin` → async/await 深入 → 无锁并发 → 编译器内部 → 形式化验证

---

## 六、权威页面导航

| 主题 | 权威来源 |
| :--- | :--- |
| Ownership | [01_ownership.md](./01_ownership.md) |
| Borrowing | [02_borrowing.md](./02_borrowing.md) |
| Lifetimes | [03_lifetimes.md](./03_lifetimes.md) · [30_lifetimes_advanced.md](./30_lifetimes_advanced.md) |
| Move Semantics | [23_move_semantics.md](./23_move_semantics.md) |
| Smart Pointers | [12_smart_pointers.md](../../02_intermediate/02_memory_management/12_smart_pointers.md) |
| Interior Mutability | [08_interior_mutability.md](../../02_intermediate/02_memory_management/08_interior_mutability.md) |
| Concurrency | [01_concurrency.md](../../03_advanced/00_concurrency/01_concurrency.md) |

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust Standard Library](https://doc.rust-lang.org/std/)

---

## 七、认知路径与推理骨架

### 认知路径

1. **建立直觉**：从“堆内存需要被唯一拥有”出发，理解为什么 Rust 选择所有权模型。
2. **掌握规则**：学习移动、借用、生命周期的语法规则与编译器检查机制。
3. **扩展应用**：将所有权思维迁移到智能指针、并发安全（Concurrency Safety）、异步（Async） `Pin`/生命周期等高级场景。
4. **形式化理解**：在线性逻辑、区域类型和借用检查可判定性层面，建立对模型的深层信任。

### 定理链

- **T-OBL-1 所有权唯一性**：每个值在任一时刻有且仅有一个所有者 ⟹ 内存释放责任清晰。
- **T-OBL-2 借用不变性**：不可变借用（Immutable Borrow）可共享，可变借用唯一 ⟹ 数据竞争在编译期被排除。
- **T-OBL-3 生命周期子类型**：`'long: 'short` ⟹ 引用不会比其引用对象活得更长。

### 反向推理

- 要能安全地在多线程间共享数据 ⟸ 需要 `Sync`/`Send` 保证 ⟸ 其根基是所有权和生命周期规则。
- 要实现无垃圾回收的确定性内存管理 ⟸ 需要编译期可验证的所有权转移与析构调度。

### 反命题

- ❌ “生命周期标注越多越安全” → 生命周期标注只是显式约束；错误标注仍会导致编译失败或逻辑错误。
- ❌ “拥有 `Rc<RefCell<T>>` 就等同于 GC” → 循环引用仍会造成内存泄漏，需要 `Weak` 或显式解除。

> **过渡提示**：掌握上述结构后，可进入 [Ownership 权威页](./01_ownership.md) 开始逐项深入学习，或在 [Smart Pointers](../../02_intermediate/02_memory_management/12_smart_pointers.md) 中查看所有权系统的工程扩展。

## 过渡段

> **过渡**: 从所有权过渡到借用，可以理解 Rust 如何在保证内存安全（Memory Safety）的同时支持灵活的引用访问。
>
> **过渡**: 从借用过渡到生命周期，可以建立“引用有效范围由编译器静态验证”的核心直觉。
>
