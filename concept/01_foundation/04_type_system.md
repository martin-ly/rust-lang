# Type System Basics（类型系统基础）

> **层级**: L1 基础概念
> **前置概念**: [Ownership](./01_ownership.md)
> **后置概念**: [Traits](../02_intermediate/01_traits.md) · [Generics](../02_intermediate/02_generics.md) · [Algebraic Data Types](../02_intermediate/01_traits.md)
> **主要来源**: [TRPL: Ch3](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html) · [TRPL: Ch6](https://doc.rust-lang.org/book/ch06-00-enums.html) · [Wikipedia: Type system] · [Rust Reference: Types]

---

**变更日志**:

- v1.0 (2026-05-12): 初始版本，完成权威定义、类型分类矩阵、ADT 分析、形式化视角、思维导图、示例反例

---

## 一、权威定义（Definition）

### 1.1 Wikipedia 定义

> **[Wikipedia: Type system]** In computer programming, a type system is a logical system comprising a set of rules that assigns a property called a type to every term. A type system constrains the operations that can be performed on values of different types, preventing errors in programs.

> **[Wikipedia: Rust]** Rust has a strong, static type system with type inference. The type system supports algebraic data types, generics, and traits (type classes) but does not use garbage collection.

### 1.2 TRPL 官方定义

> **[TRPL: Ch3.2]** Rust is a statically typed language, which means that it must know the types of all variables at compile time. The compiler can usually infer what type we want to use based on the value and how we use it.

> **[TRPL: Ch6]** Rust's enums are most similar to algebraic data types in functional languages, such as Haskell, F#, OCaml, and others. They allow you to define a type by enumerating its possible variants.

### 1.3 形式化定义

Rust 的类型系统可以形式化为一个**带所有权约束的 Hindley-Milner 类型系统扩展**：

```text
类型推断规则（简化）:
─────────────────────────────────────────
  Γ ⊢ x : τ           （变量）
  Γ ⊢ c : τ           （常量）
  Γ, x:τ₁ ⊢ e : τ₂    （lambda 抽象）
  ─────────────────────
  Γ ⊢ λx.e : τ₁ → τ₂

Rust 扩展:
  Γ ⊢ e : τ₁    τ₁ implements Trait
  ──────────────────────────────────
  Γ ⊢ e : impl Trait

所有权约束:
  Γ; Σ ⊢ e : τ {Σ'}   （Σ = 堆状态，Σ' = 执行后的堆状态）
```

---

## 二、概念属性矩阵（Attribute Matrix）

### 2.1 类型分类矩阵

| **类别** | **子类别** | **Rust 类型** | **内存位置** | **Copy?** | **Size** |
|:---|:---|:---|:---|:---|:---|
| **标量** | 整数 | `i8`-`i128`, `u8`-`u128`, `isize`, `usize` | 栈 | ✅ | 固定 |
| | 浮点 | `f32`, `f64` | 栈 | ✅ | 固定 |
| | 布尔 | `bool` | 栈 | ✅ | 1 byte |
| | 字符 | `char` | 栈 | ✅ | 4 bytes |
| **复合** | 元组 | `(T, U, ...)` | 栈（若成员全栈） | 若成员全 Copy | 成员和 |
| | 数组 | `[T; N]` | 栈（通常） | 若 T: Copy | N × size(T) |
| | 结构体 | `struct` | 视成员而定 | 若成员全 Copy | 成员和 + padding |
| **引用** | 共享 | `&T` | 栈（指针大小） | ✅ | ptr 大小 |
| | 可变 | `&mut T` | 栈（指针大小） | ✅ | ptr 大小 |
| | 裸指针 | `*const T`, `*mut T` | 栈 | ✅ | ptr 大小 |
| **ADT** | 枚举 | `enum` | 标签 + 最大变体 | 若变体全 Copy | tag + max variant |
| | Option | `Option<T>` | 同 `enum` | 若 T: Copy | 优化: 零成本空值 |
| | Result | `Result<T, E>` | 同 `enum` | 若 T,E: Copy | tag + max(T, E) |
| **函数** | 函数指针 | `fn(T) -> U` | 栈 | ✅ | ptr 大小 |
| | 闭包 | `impl Fn/FnMut/FnOnce` | 视捕获而定 | 通常 ❌ | 捕获变量和 |
| **动态** | Trait Object | `dyn Trait` | 栈（胖指针） | ❌ | 2 × ptr |
| | Slice | `[T]` | 无法直接拥有 | N/A | 动态 |

### 2.2 Rust 类型系统特征矩阵

| **特征** | **Rust** | **Haskell** | **C++** | **Java** | **Go** |
|:---|:---|:---|:---|:---|:---|
| **类型检查时机** | 静态 + 编译期 | 静态 | 静态 | 静态 + 运行时擦除 | 静态 |
| **类型推断** | ✅ HM 扩展 | ✅ HM | ⚠️ `auto` | ❌（需显式） | ✅ 局部 |
| **代数数据类型** | ✅ `enum` | ✅ `data` | ⚠️ `variant` (C++17) | ❌ | ❌ |
| **空安全** | ✅ `Option<T>` | ✅ `Maybe` | ❌ `nullptr` | ⚠️ `Optional` | ❌ `nil` |
| **错误处理类型** | ✅ `Result<T,E>` | ✅ `Either` | ❌ 异常 | ⚠️ 异常/Optional | ⚠️ 多返回值 |
| **泛型** | ✅ 单态化 | ✅ | ✅ 模板 | ⚠️ 类型擦除 | ✅ 无约束 |
| **Trait/类型类** | ✅ | ✅ 类型类 | ⚠️ Concepts (C++20) | ✅ 接口 | ✅ 接口 |
| **线性/所有权类型** | ✅ | ⚠️ 线性类型扩展 | ❌ | ❌ | ❌ |

---

## 三、形式化理论根基（Formal Foundation）

### 3.1 代数数据类型（ADT）

Rust 的 `enum` 和 `struct` 对应范畴论中的**余积（Coproduct）**和**积（Product）**：

```text
积类型 (Product Type):
  struct Point { x: f64, y: f64 }  ≅  f64 × f64
  值: (3.0, 4.0)
  大小: size(f64) + size(f64) = 16 bytes

余积类型 (Sum Type / Coproduct):
  enum Shape { Circle(f64), Rectangle(f64, f64) }  ≅  f64 + (f64 × f64)
  值: Circle(5.0) 或 Rectangle(3.0, 4.0)
  大小: tag + max(size(Circle), size(Rectangle))

Option<T> ≅ 1 + T        （1 表示 None 单元类型）
Result<T, E> ≅ T + E
```

### 3.2 零成本空值优化（Null Pointer Optimization, NPO）

```text
对于 Option<&T> 和 Option<Box<T>>:
  通常: tag (1 byte) + padding + pointer (8 bytes) = 16 bytes
  NPO: 用指针的 0 值编码 None，tag 被消除
  结果: 只有 pointer (8 bytes)

形式化:
  Option<&T> ≅ &T ∪ {⊥}  其中 ⊥ 用 0x0 编码
  因为 &T 的有效值永不为 0（Rust 引用非空）
```

---

## 四、思维导图（Mind Map）

```mermaid
graph TD
    A[Type System 类型系统] --> B[标量类型]
    A --> C[复合类型]
    A --> D[代数数据类型 ADT]
    A --> E[引用类型]
    A --> F[特殊类型]

    B --> B1[整数: i8..i128, u8..u128, isize, usize]
    B --> B2[浮点: f32, f64]
    B --> B3[bool, char]

    C --> C1[元组: (T, U)]
    C --> C2[数组: [T; N]]
    C --> C3[结构体: struct]
    C --> C4[切片: [T]]

    D --> D1[枚举: enum = Sum Type]
    D --> D2[Option<T> = 1 + T]
    D --> D3[Result<T, E> = T + E]
    D --> D4[Never: ! = 空类型]

    E --> E1[&T: 共享引用]
    E --> E2[&mut T: 可变引用]
    E --> E3[*const/*mut T: 裸指针]

    F --> F1[impl Trait: 存在类型]
    F --> F2[dyn Trait: 动态分发]
    F --> F3[!: Never 类型]
    F --> F4[元类型: type/const 泛型]
```

---

## 五、决策/边界判定树（Decision / Boundary Tree）

### 5.1 "我该用哪种复合类型？" 决策树

```mermaid
graph TD
    Q1[需要命名字段?] -->|是| Q2[字段类型异构?]
    Q1 -->|否| Q3[元素数量编译期已知?]
    Q2 -->|是| A1[struct 命名字段]
    Q2 -->|否| A2[struct 元组结构体]
    Q3 -->|是| A3[数组 [T; N]]
    Q3 -->|否| Q4[需要动态大小?]
    Q4 -->|是| A4[切片 [T] / Vec<T>]
    Q4 -->|否| A5[元组 (T, U)]

    A1[struct S { a: T, b: U }]
    A2[struct S(T, U)]
    A3[[T; N]]
    A4[Vec<T> / [T]]
    A5[(T, U)]
```

### 5.2 "我该用 enum 还是 struct/trait？" 决策树

```mermaid
graph TD
    Q1[表示"可能是 A 或 B"?] -->|是| Q2[变体数量固定且较少?]
    Q1 -->|否| A1[struct / trait]
    Q2 -->|是| A2[enum: Shape { Circle, Rect }]
    Q2 -->|否| A3[trait object dyn Trait]

    A1[struct: 确定的数据组合<br/>trait: 共享行为接口]
    A2[enum: 编译期已知变体<br/>穷举匹配 match]
    A3[dyn Trait: 开放扩展<br/>运行时多态]
```

---

## 六、定理推理链（Theorem Chain）

### 6.1 ADT + Pattern Matching ⇒ 穷尽性检查

```text
前提 1: enum 定义了所有可能的变体（封闭集合）
前提 2: match 表达式要求覆盖所有变体（exhaustiveness check）
前提 3: 编译器验证 match 的每个分支类型正确
    ↓
定理: Safe Rust 中，对 enum 的 match 不会遗漏 case
    ↓
推论: 无需 default/else 分支即可保证穷尽性（若变体全覆盖）
    ↓
应用: Option<T> 强制处理 None 情况，消除空指针错误
```

### 6.2 类型推断完备性

```text
前提: Rust 类型推断基于 Hindley-Milner 算法的扩展
    ↓
定理: 对于无显式泛型约束的表达式，类型推断是完备的
    ↓
边界: 以下情况需要显式标注
  - 函数签名（公共 API 的文档需求）
  - 泛型约束（`T: Trait`）
  - 生命周期（`&'a T`）
  - 数值字面量后缀（`42i32` vs `42.0f64`）
  - `collect::<Vec<_>>()` 等需要目标类型的场景
```

---

## 七、示例与反例（Examples & Counter-examples）

### 7.1 正确示例：ADT + Pattern Matching

```rust
// ✅ 正确: enum 表示可能的状态，match 穷尽处理
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn process(msg: Message) {
    match msg {
        Message::Quit => println!("Quit"),
        Message::Move { x, y } => println!("Move to ({}, {})", x, y),
        Message::Write(text) => println!("Text: {}", text),
        Message::ChangeColor(r, g, b) => println!("RGB({}, {}, {})", r, g, b),
    } // ✅ 编译器验证：所有变体都被处理
}
```

### 7.2 正确示例：Option 消除空值

```rust
// ✅ 正确: Option 强制处理空值情况
fn divide(numerator: f64, denominator: f64) -> Option<f64> {
    if denominator == 0.0 {
        None
    } else {
        Some(numerator / denominator)
    }
}

fn main() {
    let result = divide(10.0, 2.0);
    match result {
        Some(x) => println!("Result: {}", x),
        None => println!("Cannot divide by zero"),
    }
    // 不能直接使用 result + 1（Option<f64> 不实现 Add）
    // 必须先 unwrap 或 match
}
```

### 7.3 反例：未覆盖的 match 分支

```rust
// ❌ 反例: non-exhaustive pattern
enum Color {
    Red,
    Green,
    Blue,
}

fn print_color(c: Color) {
    match c {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        // E0004: non-exhaustive patterns: `Blue` not covered
    }
}
```

**修正方案**：

```rust
// ✅ 修正: 覆盖所有变体或使用通配符
fn print_color(c: Color) {
    match c {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        Color::Blue => println!("Blue"),
    }
}

// 或
fn print_color(c: Color) {
    match c {
        Color::Red => println!("Red"),
        Color::Green => println!("Green"),
        _ => println!("Other"),  // ✅ 通配符覆盖剩余变体
    }
}
```

### 7.4 反例：递归类型需要间接层

```rust
// ❌ 反例: 递归类型直接自包含
enum List<T> {
    Cons(T, List<T>),  // E0072: recursive type has infinite size
    Nil,
}
```

**修正方案**：

```rust
// ✅ 修正: 使用 Box 提供间接层
enum List<T> {
    Cons(T, Box<List<T>>),  // Box 是指针，大小固定
    Nil,
}

// 或使用其他智能指针
enum List<T> {
    Cons(T, std::rc::Rc<List<T>>),  // 共享所有权
    Nil,
}
```

---

## 八、知识来源关系（Provenance）

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| Rust 是静态类型语言 | [TRPL: Ch3.2] | ✅ |
| 编译器通常可推断类型 | [TRPL: Ch3.2] | ✅ |
| enum 类似函数式语言的 ADT | [TRPL: Ch6] | ✅ |
| `Option<T>` 消除空指针 | [TRPL: Ch6.1] · [Wikipedia: Null pointer] | ✅ |
| `Result<T, E>` 强制错误处理 | [TRPL: Ch9] | ✅ |
| NPO 优化 Option<&T> | [Rust Reference: Enums] | ✅ |
| ADT 对应积与余积 | [Category Theory for Programmers] | 💡 |
| match 穷尽性检查 | [Rust Reference: Patterns] | ✅ |
| 递归类型需要间接层 | [TRPL: Ch15] | ✅ |

---

## 九、待补充与演进方向（TODOs）

- [ ] **TODO**: 补充 `!` (Never type) 的形式化分析 —— 优先级: 中 —— 预计: Phase 1

### 补充章节：`impl Trait` 与 `dyn Trait` 的类型论差异

#### 存在类型 vs 全称类型

```text
impl Trait 在返回位置 = 存在类型（Existential Type）:
  fn foo() -> impl Trait
  ≡  "存在某个具体类型 T 满足 Trait，且 T 由实现决定"
  类似: ∃T. T: Trait

impl Trait 在参数位置 = 全称类型（Universal Type）:
  fn foo(x: impl Trait)
  ≡  "对所有满足 Trait 的类型 T，接受 T"
  等价于: fn foo<T: Trait>(x: T)

dyn Trait = 动态分发类型（Dynamic Type）:
  Box<dyn Trait>
  ≡  运行时携带 vtable 的胖指针
  类型论: 存在类型 + 运行时擦除
```

#### 关键差异矩阵

| **维度** | **`impl Trait`** | **`dyn Trait`** |
|:---|:---|:---|
| **类型擦除** | 编译期（零成本） | 运行时（vtable 间接） |
| **大小已知** | ✅（单态化后） | ❌（胖指针） |
| **可存储异构集合** | ❌（同一函数只能返回一种类型） | ✅（`Vec<Box<dyn Trait>>`） |
| **递归类型** | ❌（不能直接自引用） | ✅（`Box<dyn Trait>` 可递归） |
| **生命周期标注** | 自动推断 | 显式 `'lifetime` |
| **用途** | 隐藏实现细节 | 运行时多态 |

#### 代码对比

```rust
// ✅ impl Trait: 静态分发，隐藏类型
trait Animal { fn speak(&self); }
struct Dog;
impl Animal for Dog { fn speak(&self) { println!("woof"); } }

fn get_animal() -> impl Animal { Dog }
// 调用方不知道返回的是 Dog，只知道是某种 Animal

// ✅ dyn Trait: 动态分发，运行时多态
fn make_speak(a: &dyn Animal) { a.speak(); }

fn main() {
    let dog = Dog;
    make_speak(&dog);  // ✅ 通过 vtable 调用
}
```

---

- [x] **TODO**: 补充 `impl Trait` 与 `dyn Trait` 的类型论差异 —— 优先级: 高 —— 已完成 v1.1
- [ ] **TODO**: 补充 Const Generics（常量泛型）的类型系统扩展 —— 优先级: 中 —— 预计: Phase 2
- [ ] **TODO**: 补充 Type Inference 的 HM 算法完整规则 —— 优先级: 低 —— 预计: Phase 3
- [ ] **TODO**: 补充 Zero-sized types (ZST) 和 PhantomData —— 优先级: 中 —— 预计: Phase 2
- [ ] **TODO**: 补充 Discriminant 和内存布局的底层分析 —— 优先级: 低 —— 预计: Phase 3
- [ ] **TODO**: 补充 `union` 的类型安全边界 —— 优先级: 低 —— 预计: Phase 3
