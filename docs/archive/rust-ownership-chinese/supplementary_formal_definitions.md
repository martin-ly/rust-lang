# 补充形式化定义：内部可变性、Drop语义、Pin/Unpin

> 本文档补充主文档中缺失的高级形式化定义

## 📋 目录

- [补充形式化定义：内部可变性、Drop语义、Pin/Unpin](#补充形式化定义内部可变性drop语义pinunpin)
  - [📋 目录](#-目录)
  - [1. 内部可变性的形式语义](#1-内部可变性的形式语义)
    - [1.1 `UnsafeCell<T>` 核心定义](#11-unsafecellt-核心定义)
    - [1.2 `Cell<T>` 的公理系统](#12-cellt-的公理系统)
    - [1.3 `RefCell<T>` 的运行时借用检查](#13-refcellt-的运行时借用检查)
    - [1.4 内部可变性类型对比](#14-内部可变性类型对比)
  - [2. Drop Trait的形式语义](#2-drop-trait的形式语义)
    - [2.1 析构函数的形式定义](#21-析构函数的形式定义)
    - [2.2 Drop标志的形式语义](#22-drop标志的形式语义)
    - [2.3 析构顺序的形式化](#23-析构顺序的形式化)
    - [2.4 遗忘（Forget）与内存泄漏](#24-遗忘forget与内存泄漏)
  - [3. Copy Trait的形式语义](#3-copy-trait的形式语义)
    - [3.1 Copy的语义定义](#31-copy的语义定义)
    - [3.2 Copy的类型约束](#32-copy的类型约束)
  - [4. Pin/Unpin的形式语义](#4-pinunpin的形式语义)
    - [4.1 `Pin<P>` 核心定义](#41-pinp-核心定义)
    - [4.2 Unpin Trait 的形式语义](#42-unpin-trait-的形式语义)
    - [4.3 自引用结构的形式化](#43-自引用结构的形式化)
    - [4.4 Pin投影规则](#44-pin投影规则)
    - [4.5 Unpin的自动实现规则](#45-unpin的自动实现规则)
  - [5. 形式化定义索引](#5-形式化定义索引)

---

## 1. 内部可变性的形式语义

### 1.1 `UnsafeCell<T>` 核心定义

**直观定义**：`UnsafeCell<T>`是Rust内部可变性的基础原语，它关闭了编译器对`T`的别名优化假设，允许通过共享引用`&UnsafeCell<T>`进行内部修改。

**形式化定义**（基于RustBelt）：

设 $\mathcal{L}$ 为内存位置集合，$\mathcal{V}$ 为值集合：

$$\text{UnsafeCell}\langle T \rangle.\text{own}(\iota, v) \triangleq \exists \ell \in \mathcal{L}. \, \iota(\ell) = v \land \text{True}$$

其中关键区别：

- 普通类型 `T`: $\text{own}(\iota, v) \triangleq \ell \mapsto v$（排他性所有权）
- `UnsafeCell<T>`: $\text{own}(\iota, v) \triangleq \ell \mapsto v * \text{True}$（**无排他性保证**）

**分离逻辑解释**：

```text
[T].own(ℓ, v)          ≡ ℓ ↦ v                    (排他)
[UnsafeCell<T>].own(ℓ, v) ≡ ℓ ↦ v * True          (非排他)
```

`True` 断言表示"不拥有任何资源"，允许其他线程/引用同时"拥有"对该位置的访问权限。

---

### 1.2 `Cell<T>` 的公理系统

**直观定义**：`Cell<T>`提供单线程内部可变性，保证任何时刻只有一个执行上下文可以访问其内容。

**形式化公理**：

```text
┌─────────────────────────────────────────────────────────────────┐
│                    Cell<T> 公理系统                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Axiom C1 (值存储):                                             │
│  Cell<T>.own(ℓ, v) ≜ ℓ ↦ v * is_send(T)                        │
│  (Cell要求T: Send以保证线程安全)                                  │
│                                                                 │
│  Axiom C2 (获取操作语义):                                        │
│  {Cell<T>.own(ℓ, v)} get(&ℓ) {r. r = v ∧ Cell<T>.own(ℓ, v)}     │
│  (获取不改变状态)                                                │
│                                                                 │
│  Axiom C3 (设置操作语义):                                        │
│  {Cell<T>.own(ℓ, _)} set(&ℓ, v') {Cell<T>.own(ℓ, v')}           │
│  (设置更新值)                                                   │
│                                                                 │
│  Axiom C4 (替换操作语义):                                        │
│  {Cell<T>.own(ℓ, v)} replace(&ℓ, v') {r. r = v ∧ Cell<T>.own(ℓ, v')}│
│  (替换返回旧值)                                                 │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

**操作语义规则**：

$$
\frac{\Gamma \vdash e : \text{Cell}\langle T \rangle}{\Gamma \vdash e.\text{get}() : T} \quad \text{[CELL-GET]}
$$

$$
\frac{\Gamma \vdash e_1 : \text{Cell}\langle T \rangle \quad \Gamma \vdash e_2 : T}{\Gamma \vdash e_1.\text{set}(e_2) : ()} \quad \text{[CELL-SET]}
$$

---

### 1.3 `RefCell<T>` 的运行时借用检查

**直观定义**：`RefCell<T>`提供运行时借用检查，允许在单线程上下文中获取`&T`或`&mut T`，通过运行时计数器检查借用规则。

**形式化状态机**：

```text
RefCell<T> 状态:
  State ::= Unborrowed | Shared(n) | Exclusive

状态转换:
  Unborrowed --borrow()--> Shared(1)
  Shared(n) --borrow()--> Shared(n+1)
  Unborrowed --borrow_mut()--> Exclusive
  Shared(n) --drop()--> Shared(n-1)  (n>1)
  Shared(1) --drop()--> Unborrowed
  Exclusive --drop()--> Unborrowed
```

**形式化公理**（带运行时检查）：

$$
\text{RefCell}\langle T \rangle.\text{own}(\iota, (v, s)) \triangleq \ell \mapsto v * \text{borrow\_state}(\ell_s, s)
$$

其中 $s \in \{\text{Unborrowed}, \text{Shared}(n), \text{Exclusive}\}$

**借用检查谓词**：

$$
\text{can\_borrow}(s) \triangleq \exists n. s = \text{Shared}(n) \lor s = \text{Unborrowed}
$$

$$
\text{can\_borrow\_mut}(s) \triangleq s = \text{Unborrowed}
$$

**操作语义（带运行时检查）**：

$$
\frac{\Gamma \vdash e : \text{RefCell}\langle T \rangle \quad \text{can\_borrow}(s)}{\Gamma \vdash e.\text{borrow}() : \text{Ref}\langle T \rangle} \quad \text{[REFCELL-BORROW-OK]}
$$

$$
\frac{\Gamma \vdash e : \text{RefCell}\langle T \rangle \quad \neg\text{can\_borrow}(s)}{\Gamma \vdash e.\text{borrow}() : \text{panic}} \quad \text{[REFCELL-BORROW-PANIC]}
$$

---

### 1.4 内部可变性类型对比

| 类型 | 线程安全 | 运行时检查 | 形式化语义 | 适用场景 |
|------|----------|------------|------------|----------|
| `UnsafeCell<T>` | 否 | 无 | $\ell \mapsto v * \text{True}$ | 底层原语，Unsafe代码 |
| `Cell<T>` | 是(Send) | 无 | 单线程保证 | 简单值类型，Copy类型 |
| `RefCell<T>` | 否(!Sync) | 有 | 状态机 | 复杂借用模式 |
| `Mutex<T>` | 是 | 有(阻塞) | 分离逻辑 + 锁 | 多线程共享 |
| `RwLock<T>` | 是 | 有(阻塞) | 读/写锁分离 | 多读单写场景 |

---

## 2. Drop Trait的形式语义

### 2.1 析构函数的形式定义

**直观定义**：`Drop` trait定义了值生命周期结束时自动执行的清理代码。

**形式化定义**：

设 $T$ 是实现 `Drop` 的类型：

$$
\text{Drop}(T) \triangleq \exists f_{\text{drop}}. \, T \text{ implements } \text{Drop} \land f_{\text{drop}} : T \to ()
$$

**析构点判定**：

对于值 $x : T$ 其中 $\text{Drop}(T)$：

$$
\text{drop\_point}(x) \triangleq \min\{ t \mid t > \text{birth}(x) \land x \notin \text{live}(t) \}
$$

其中 $\text{live}(t)$ 是时刻 $t$ 的活跃变量集合。

---

### 2.2 Drop标志的形式语义

**标志定义**：

每个实现 `Drop` 的类型都有一个隐式的 **drop flag**（由编译器插入）：

$$
\text{drop\_flag}(x) \in \{0, 1\}
$$

**语义规则**：

1. **初始化**：$x$ 被创建时，$\text{drop\_flag}(x) = 1$
2. **移动后**：$x$ 被 move 后，$\text{drop\_flag}(x) = 0$
3. **析构时**：仅当 $\text{drop\_flag}(x) = 1$ 时调用 `drop(x)`

**形式化规则**：

$$
\frac{\text{drop\_flag}(x) = 1}{\text{at\_end\_of\_scope}(x) \Rightarrow \text{drop}(x)} \quad \text{[DROP-CALL]}
$$

$$
\frac{\text{move}(x, y)}{\text{drop\_flag}(x) := 0} \quad \text{[DROP-FLAG-CLEAR]}
$$

---

### 2.3 析构顺序的形式化

**变量析构顺序**（逆序）：

对于作用域内声明的变量序列 $x_1, x_2, \ldots, x_n$：

$$
\text{drop\_order} = x_n, x_{n-1}, \ldots, x_1
$$

**结构体字段析构顺序**（声明顺序）：

对于结构体 $S\{f_1: T_1, f_2: T_2, \ldots, f_n: T_n\}$：

$$
\text{field\_drop\_order} = f_1, f_2, \ldots, f_n
$$

**形式化定理（析构确定性）**：

$$
\forall x : T, \text{Drop}(T) \Rightarrow \exists! t. \text{drop}(x, t)
$$

（每个实现Drop的值有唯一的确定性析构时刻）

---

### 2.4 遗忘（Forget）与内存泄漏

**mem::forget 语义**：

```rust
pub fn forget<T>(t: T) { /* 不调用 drop */ }
```

**形式化效果**：

$$
\text{forget}(x) \Rightarrow \text{drop\_flag}(x) := 0 \land \text{no\_deallocation}
$$

**内存泄漏判定**：

程序 $P$ 存在内存泄漏，如果：

$$
\exists \ell \in \mathcal{L}, \exists t. \text{allocated}(\ell, t) \land \forall t' > t. \neg\text{deallocated}(\ell, t') \land \neg\text{reachable}(\ell, t')
$$

**定理（Safe Rust不保证无泄漏）**：

$$\text{Safe Rust} \not\Rightarrow \text{No Memory Leaks}$$

（Safe Rust代码可以通过`Rc`循环引用或`mem::forget`造成泄漏）

---

## 3. Copy Trait的形式语义

### 3.1 Copy的语义定义

**直观定义**：`Copy`标记表示类型的值在赋值时执行按位复制（隐式clone），而不是所有权转移。

**形式化定义**：

类型 $T$ 实现 `Copy` 当且仅当：

$$
\text{Copy}(T) \Leftrightarrow \forall v : T. \text{bitwise\_copy}(v) \text{ is valid} \land \text{no\_resources\_to\_drop}(v)
$$

**操作语义差异**：

对于 `Copy` 类型：

$$
\frac{\Gamma \vdash x : T \quad \text{Copy}(T)}{\Gamma \vdash \text{let } y = x; \Rightarrow \Gamma, x: T, y: T} \quad \text{[COPY-SEMANTICS]}
$$

对于非 `Copy` 类型：

$$
\frac{\Gamma \vdash x : T \quad \neg\text{Copy}(T)}{\Gamma \vdash \text{let } y = x; \Rightarrow \Gamma \setminus \{x\}, y: T} \quad \text{[MOVE-SEMANTICS]}
$$

---

### 3.2 Copy的类型约束

**Copy的自动推导条件**（结构体）：

结构体 $S\{f_1: T_1, \ldots, f_n: T_n\}$ 可自动实现 `Copy` 当且仅当：

$$
\forall i \in 1..n. \text{Copy}(T_i)
$$

**Copy的不可实现情况**：

- 包含 `Drop` 实现的类型
- 包含非 `Copy` 类型的结构体
- 包含资源（如堆分配）的类型

---

## 4. Pin/Unpin的形式语义

### 4.1 `Pin<P>` 核心定义

**直观定义**：`Pin<P>`是一个包装器，保证被包裹的指针指向的值在内存中不会移动（除非实现 `Unpin`）。

**形式化定义**：

设 $P$ 是指针类型（如 `Box<T>`, `&mut T`）：

$$
\text{Pin}\langle P \rangle.\text{own}(\iota, p) \triangleq P.\text{own}(\iota, p) * \text{pin\_constraint}(p)
$$

其中：

$$
\text{pin\_constraint}(p) \triangleq \square(\text{address}(p) \text{ is constant})
$$

$\square$ 表示"总是"（模态运算符）。

---

### 4.2 Unpin Trait 的形式语义

**直观定义**：`Unpin`是一个auto trait，标记类型**即使被Pin也不会改变语义**。大多数类型都实现`Unpin`。

**形式化定义**：

$$
\text{Unpin}(T) \Leftrightarrow \text{move\_safety}(T) = \text{unaffected\_by\_pin}
$$

**关键性质**：

```text
若 T: Unpin, 则 Pin<Box<T>> 和 Box<T> 语义等价
若 T: !Unpin, 则 Pin<Box<T>> 保证 T 的地址不变
```

**形式化规则**：

$$
\frac{\text{Unpin}(T)}{\text{Pin}\langle \&mut \, T \rangle \cong \&mut \, T} \quad \text{[UNPIN-EQUIVALENCE]}
$$

---

### 4.3 自引用结构的形式化

**自引用结构定义**：

结构体 $S$ 是**自引用**的，如果存在字段 $f_i, f_j$：

$$
\text{self\_referential}(S) \triangleq \exists f_i, f_j. \text{field}(f_i) \text{ points\_to } \text{field}(f_j)
$$

**Pin的必要性**：

```text
定理 (Pin对自引用的必要性):
对于自引用结构 S，如果不使用 Pin 固定，
则移动 S 会导致悬垂指针。

证明:
1. 设 S 包含字段 data: String 和 ptr: *const u8
2. ptr 指向 data 的内部缓冲区
3. 移动 S 到新位置，data 被移动
4. ptr 仍指向原位置 → 悬垂指针
5. Pin<S> 禁止移动，防止此问题 ∎
```

---

### 4.4 Pin投影规则

**Pin投影**：从 `Pin<Box<T>>` 安全获取 `Pin<&mut T.field>`。

**形式化条件**：

对于结构体 $S\{f_1: T_1, \ldots, f_n: T_n\}$，投影 $Pin<\&mut \, S> \to Pin<\&mut \, T_i>$ 是安全的当且仅当：

1. $T_i$ 是结构体（不是联合体）
2. 投影不改变内存布局

**投影公理**：

$$
\frac{\Gamma \vdash p : \text{Pin}\langle \&mut \, S \rangle \quad S\{f: T\} \text{ is struct}}{\Gamma \vdash \text{pin\_field\_projection}(p, f) : \text{Pin}\langle \&mut \, T \rangle} \quad \text{[PIN-PROJECTION]}
$$

---

### 4.5 Unpin的自动实现规则

**自动实现条件**：

类型 $T$ 自动实现 `Unpin` 当且仅当：

$$
\forall \text{field } f \text{ of } T. \text{Unpin}(\text{type}(f)) \land \neg\text{contains\_self\_reference}(T)
$$

**典型 !Unpin 类型**：

- `PhantomPinned`（显式标记）
- 包含自引用指针的结构体
- 某些异步生成器状态

---

## 5. 形式化定义索引

| 定义 | 符号 | 位置 |
|------|------|------|
| UnsafeCell所有权 | $\text{UnsafeCell}\langle T \rangle.\text{own}$ | 第1.1节 |
| Cell获取语义 | $\text{Cell::get}$ | 第1.2节 |
| RefCell状态机 | $\text{RefCell\_State}$ | 第1.3节 |
| Drop析构点 | $\text{drop\_point}(x)$ | 第2.1节 |
| Drop标志 | $\text{drop\_flag}(x)$ | 第2.2节 |
| Copy语义 | $\text{Copy}(T)$ | 第3节 |
| Pin约束 | $\text{pin\_constraint}(p)$ | 第4.1节 |
| Unpin等价 | $\text{Unpin}(T)$ | 第4.2节 |
| 自引用结构 | $\text{self\_referential}(S)$ | 第4.3节 |

---

*本文档为《Rust所有权与可判定性：全面形式语义分析与论证》的补充材料*:
