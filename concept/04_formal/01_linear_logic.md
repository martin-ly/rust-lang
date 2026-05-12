# Linear Logic & Affine Logic（线性逻辑与仿射逻辑）

> **层级**: L4 形式化理论
> **前置概念**: [Ownership](../01_foundation/01_ownership.md) · [Type System](../01_foundation/04_type_system.md)
> **后置概念**: [Ownership Formalization](./03_ownership_formal.md) · [RustBelt](./04_rustbelt.md)
> **主要来源**: [Wikipedia: Linear logic] · [Wikipedia: Affine logic] · [Girard 1987] · [RustBelt: POPL 2018] · [Utrecht: Ownership Types]

---

**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成 Girard 原始定义、结构规则矩阵、Rust 映射、命题-类型对应、思维导图、示例反例

---

## 一、权威定义（Definition）

### 1.1 Wikipedia 定义

> **[Wikipedia: Linear logic]** Linear logic is a substructural logic proposed by Jean-Yves Girard as a refinement of classical and intuitionistic logic, joining the dualities of the former with many of the constructive properties of the latter. The key operational intuition behind linear logic is that logical assumptions are consumed in proving a conclusion, rather than merely used as in classical logic.

> **[Wikipedia: Affine logic]** Affine logic is a substructural logic whose proof theory rejects the structural rule of contraction. It can also be characterized as linear logic with weakening. In affine logic, each hypothesis may be used at most once—unlike in linear logic, where each hypothesis must be used exactly once.

### 1.2 Girard 原始定义（1987）

> **Linear logic** introduces a new connective, the exponential `!A` ("of course A"), which allows a formula to be copied or discarded. Without `!`, every assumption must be used exactly once. This makes linear logic a **resource-sensitive logic**: propositions represent resources, and proofs represent resource-transforming processes.

### 1.3 与 Rust 的对应定义

> **[RustBelt: POPL 2018]** Rust's ownership system can be understood as an **affine type system** embedded in a larger language with managed copying (`Clone`) and shared borrowing (`&T`). The core insight is that ownership tracking enforces the resource discipline of affine logic at compile time.

---

## 二、概念属性矩阵（Attribute Matrix）

### 2.1 结构规则对比矩阵

| **结构规则** | **经典逻辑** | **直觉主义逻辑** | **线性逻辑** | **仿射逻辑** | **Rust** |
|:---|:---|:---|:---|:---|:---|
| **Weakening**（弱化/丢弃） | ✅ | ✅ | ❌ | ✅ | ✅ `let _ = x;` / drop |
| **Contraction**（收缩/复制） | ✅ | ✅ | ❌ | ❌ | ❌ `move` 语义 |
| **Exchange**（交换） | ✅ | ✅ | ✅ | ✅ | ✅ 变量声明顺序可交换 |
| **资源语义** | 真值永恒 | 构造性证明 | 资源必须消耗 | 资源最多使用一次 | 所有权转移 |

### 2.2 线性逻辑连接词矩阵

| **连接词** | **语法** | **资源语义** | **Rust 对应** | **对偶** |
|:---|:---|:---|:---|:---|
| **张量 (⊗)** | `A ⊗ B` | 同时拥有 A 和 B | `(T, U)` 元组 | ⅋ (Par) |
| **Par (⅋)** | `A ⅋ B` | A 和 B 的资源可交替使用 | `enum` 变体 | ⊗ |
| **线性蕴含 (⊸)** | `A ⊸ B` | 消耗 A 得到 B | `fn(T) -> U`（move） | ⊥ |
| **With (&)** | `A & B` | 选择拥有 A 或 B（外部选择） | `enum` / `match` | ⊕ |
| **Plus (⊕)** | `A ⊕ B` | 提供 A 或 B（内部选择） | `Result<T, E>` | & |
| **Of course (!)** | `!A` | 可复制/可丢弃的资源 | `Copy` trait | ? |
| **Why not (?)** | `?A` | 可忽略的消耗 | `Drop` + 允许不消费 | ! |
| **单位 1** | `1` | 空资源（恒等） | `()` 单元类型 | ⊥ |
| **单位 ⊥** | `⊥` | 不可达/矛盾 | `!` (never type) | 1 |

### 2.3 逻辑系统谱系矩阵

| **系统** | **weakening** | **contraction** | **exchange** | **编程语言对应** |
|:---|:---|:---|:---|:---|
| **经典逻辑** | ✅ | ✅ | ✅ | 无直接对应 |
| **直觉主义逻辑** | ✅ | ✅ | ✅ | Haskell（无所有权） |
| **仿射逻辑** | ✅ | ❌ | ✅ | **Rust（核心模型）** |
| **线性逻辑** | ❌ | ❌ | ✅ | 严格线性类型实验语言 |
| **有序逻辑** | ❌ | ❌ | ❌ | 栈操作语言 |

---

## 三、形式化理论根基（Formal Foundation）

### 3.1 线性逻辑的自然演绎

```text
张量引入 (⊗-intro):
  Γ ⊢ A    Δ ⊢ B
  ───────────────
  Γ, Δ ⊢ A ⊗ B

Rust 对应:
  let a = A::new();   // Γ ⊢ A
  let b = B::new();   // Δ ⊢ B
  let pair = (a, b);  // Γ, Δ ⊢ A ⊗ B

线性蕴含引入 (⊸-intro):
  Γ, A ⊢ B
  ──────────
  Γ ⊢ A ⊸ B

Rust 对应:
  fn consume(a: A) -> B { /* 使用 a 构造 B */ }
  // 前提: 拥有 A 可构造 B
  // 结论: 此函数是 A ⊸ B 的证明

弱化（Weakening）在仿射逻辑中允许:
  Γ ⊢ B
  ──────────  (Affine only)
  Γ, A ⊢ B

Rust 对应:
  fn ignore<T>(_x: T) {}  // 允许丢弃资源（weakening）
  // 但线性逻辑中此操作非法！
```

### 3.2 指数模态 (!A / ?A)

```text
!A 的规则:
  提升（Promotion）:  若 A 的证明不使用任何假设，则 !A 成立
  推导（Dereliction）: !A ⊢ A
  收缩（Contraction）: !A ⊢ !A ⊗ !A  （!A 可复制）
  弱化（Weakening）:   !A ⊢ 1         （!A 可丢弃）

Rust 对应:
  Copy trait = !T  （T 可被复制，不受线性约束）
  例: i32: Copy     →  !i32
  例: String: !Copy →  String 受线性约束
```

---

## 四、思维导图（Mind Map）

```mermaid
graph TD
    A[Linear / Affine Logic] --> B[结构规则]
    A --> C[连接词]
    A --> D[指数模态]
    A --> E[Rust 映射]

    B --> B1[Weakening: 丢弃]
    B --> B2[Contraction: 复制]
    B --> B3[Exchange: 交换]
    B --> B4[Affine = Linear + Weakening]

    C --> C1[⊗ 张量: (A, B)]
    C --> C2[⊸ 线性蕴含: fn(A)->B]
    C --> C3[& With: 外部选择]
    C --> C4[⊕ Plus: 内部选择]
    C --> C5[⅋ Par: 交替使用]

    D --> D1[!A Of course: Copy]
    D --> D2[?A Why not: Drop]

    E --> E1[Ownership = Affine Type]
    E --> E2[Move = Linear Consumption]
    E --> E3[Borrow = 临时授权]
    E --> E4[Copy = !A 指数模态]
```

---

## 五、决策/边界判定树（Decision / Boundary Tree）

### 5.1 "线性逻辑 vs 仿射逻辑？" 判定

```mermaid
graph TD
    Q1[资源允许被静默丢弃?] -->|是| A1[仿射逻辑 → Rust]
    Q1 -->|否| A2[严格线性逻辑]

    A1[Affine: 可用 0 次或 1 次<br/>Rust: 允许未使用变量]
    A2[Linear: 必须恰好使用 1 次<br/>实验语言: Linear Haskell]
```

---

## 六、定理推理链（Theorem Chain）

### 6.1 仿射类型 ⇒ 无 UAF/DF

```text
前提 1: 仿射规则: 每个资源最多使用一次（move 消耗资源）
前提 2: 资源在最后一次使用后自动释放（drop）
    ↓
定理: 资源不会被使用两次（无 double-free）
      资源不会在释放后被访问（无 use-after-free）
    ↓
边界: 需要配合生命周期系统防止悬垂引用
      需要 unsafe 突破时人工保证
```

---

## 七、示例与反例

### 7.1 Rust 中的线性/仿射对应

```rust
// ✅ 仿射逻辑: String 是线性资源（ Affine ）
fn affine_demo() {
    let s = String::from("hello");  // 获得资源
    let t = s;                       // s 被消耗（move），t 获得所有权
    // println!("{}", s);            // ❌ 编译错误: s 已被消耗
    println!("{}", t);              // ✅ t 使用资源
} // t 被 drop，资源释放

// ✅ 指数模态: i32 是 !T（Copy）
fn exponential_demo() {
    let n = 42i32;   // !i32: 可复制
    let a = n;       // n 被复制，n 仍然可用
    let b = n;       // n 再次复制
    println!("{} {} {}", n, a, b);  // ✅ 全部可用
}

// ✅ 弱化（Weakening）: 允许丢弃
fn weakening_demo() {
    let s = String::from("ignored");
    // s 未被使用，但允许（Affine 逻辑）
    // 严格线性逻辑中此操作非法
} // s 自动 drop
```

---

## 八、知识来源关系

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| 线性逻辑由 Girard 1987 提出 | [Wikipedia: Linear logic] | ✅ |
| 仿射逻辑 = 线性逻辑 + weakening | [Wikipedia: Affine logic] | ✅ |
| Rust 是仿射类型系统 | [RustBelt: POPL 2018] · [Utrecht] | ✅ |
| !A 对应 Copy trait | [RustBelt] · 原创分析 | 💡 |
| ⊗ 对应元组 | [Category Theory for Programmers] | 💡 |

---

## 九、待补充

- [ ] **TODO**: 补充线性逻辑的 sequent calculus 完整规则集
- [ ] **TODO**: 补充 Phase semantics 与 Rust 的直观联系
