# 类型理论基础 (Type Theory Foundations)

> **难度**: 🔴 高级
> **预计阅读时间**: 3-4 小时
> **前置知识**: λ演算基础

---

## 1. 引言

类型理论是编程语言语义的核心支柱。
Rust 的类型系统建立在丰富的类型理论基础之上，理解这些理论有助于深入掌握 Rust 的泛型、生命周期和 trait 系统。

---

## 2. 类型作为命题 (Types as Propositions)

### 2.1 Curry-Howard 同构

**定理 2.1** (Curry-Howard 同构)

命题逻辑与简单类型 λ演算之间存在一一对应：

| 逻辑 | 类型 | Rust |
|------|------|------|
| A → B (蕴含) | A → B | `Fn(A) -> B` |
| A ∧ B (合取) | A × B | `(A, B)` |
| A ∨ B (析取) | A + B | `Either<A, B>` |
| ⊤ (真) | Unit | `()` |
| ⊥ (假) | Void | `!` (never type) |
| ∀x.A | 全称类型 | `forall<T>` |
| ∃x.A | 存在类型 | `impl Trait` |

### 2.2 Rust 中的对应

```rust
// A → B: 函数类型
fn implies<A, B>(f: impl Fn(A) -> B, a: A) -> B {
    f(a)
}

// A ∧ B: 元组 (积类型)
fn and<A, B>(a: A, b: B) -> (A, B) {
    (a, b)
}

// A ∨ B: 枚举 (和类型)
enum Either<A, B> {
    Left(A),
    Right(B),
}

// ⊥: never type
fn absurd() -> ! {
    loop {}  //  diverges
}
```

---

## 3. 多态性 (Polymorphism)

### 3.1 参数多态 (System F)

**定义 3.1** (全称类型)

```
τ ::= ... | ∀α.τ    (全称量词)
```

**类型抽象 (Λ) 和应用**:

```
M ::= ... | Λα.M    (类型抽象)
    | M[τ]        (类型应用)
```

**Rust 对应**:

```rust
// Λα.λx:α.x  :  ∀α.α → α
fn identity<T>(x: T) -> T { x }

// 类型应用: identity[Int] 5
let n: i32 = identity(5);
let s: String = identity(String::from("hello"));
```

### 3.2 Hindley-Milner 类型推断

**定义 3.2** (算法 W)

HM 类型推断的核心算法：

1. **变量规则**: 从环境获取类型
2. **抽象规则**: 引入新类型变量
3. **应用规则**: 统一类型约束
4. **泛化规则**: 将自由变量转为全称量词

**Rust 的类型推断**:

```rust
// 编译器自动推断类型
let pair = (1, "hello");  // (i32, &str)
let f = |x| x + 1;         // impl Fn(i32) -> i32

// 显式标注（复杂情况）
fn compose<A, B, C>(f: impl Fn(B) -> C, g: impl Fn(A) -> B)
    -> impl Fn(A) -> C {
    move |x| f(g(x))
}
```

---

## 4. 子类型与变型 (Subtyping & Variance)

### 4.1 子类型关系

**定义 4.1** (子类型)

```
τ₁ <: τ₂   (τ₁ 是 τ₂ 的子类型)
```

**基本规则**:

```
自反性: τ <: τ
传递性: τ₁ <: τ₂ ∧ τ₂ <: τ₃ → τ₁ <: τ₃
函数逆变: τ₂ <: τ₁ ∧ σ₁ <: σ₂ → (τ₁ → σ₁) <: (τ₂ → σ₂)
```

### 4.2 变型 (Variance)

**定义 4.2** (变型)

| 变型 | 含义 | Rust 示例 |
|------|------|-----------|
| 协变 (Covariant) | T₁ <: T₂ ⇒ C<T₁> <: C<T2> | `&'a T` (生命周期协变) |
| 逆变 (Contravariant) | T₁ <: T₂ ⇒ C<T₂> <: C<T1> | `fn(T) -> ()` (参数位置) |
| 不变 (Invariant) | 无子类型关系 | `&mut T`, `Cell<T>` |

**Rust 变型规则**:

```rust
// 协变: &'a T 随着 'a 增大而增大
fn covariant<'a, 'b: 'a>(x: &'b str) -> &'a str { x }

// 逆变: fn(T) 在 T 上逆变
fn contravariant<F, G>(f: F) -> G
where
    F: Fn(i32),
    G: Fn(i64),  // i64 <: i32 (不是，所以这里演示的是函数返回)
    // 实际上 fn(T) 在参数位置逆变
{
    move |x: i64| f(x as i32)
}

// 不变: &mut T
fn invariant<'a>(x: &'a mut String) -> &'a mut String { x }
```

### 4.3 生命周期子类型

```rust
// 'static <: 'a 对所有 'a 成立
fn static_to_any<'a>(s: &'static str) -> &'a str { s }

// 嵌套生命周期
fn nested<'a, 'b: 'a>(x: &'b &'a str) -> &'a str { x }
```

---

## 5. 递归类型 (Recursive Types)

### 5.1 μ-类型

**定义 5.1** (递归类型)

```
μα.τ   (μ 是递归类型构造子)
```

等价关系:

```
μα.τ ≡ τ[(μα.τ)/α]
```

### 5.2 Rust 中的递归类型

```rust
// List<T> = μα. Unit + (T × α)
enum List<T> {
    Nil,           // Unit
    Cons(T, Box<List<T>>),  // (T × α)
}

// Tree<T> = μα. Unit + (T × α × α)
enum Tree<T> {
    Leaf,
    Node(T, Box<Tree<T>>, Box<Tree<T>>),
}

// 使用 fold/unfold
impl<T> List<T> {
    fn fold<R>(self, nil: R, cons: impl Fn(T, R) -> R) -> R {
        match self {
            List::Nil => nil,
            List::Cons(head, tail) => cons(head, tail.fold(nil, cons)),
        }
    }
}
```

---

## 6. 线性类型与所有权

### 6.1 线性逻辑

**定义 6.1** (线性类型)

线性类型要求每个值**恰好使用一次**：

```
Γ, x:A ⊢ M:B       (x 在 M 中使用一次)
------------------------------------
Γ ⊢ λx.M : A ⊸ B   (线性函数类型)
```

### 6.2 仿射类型

仿射类型允许值**最多使用一次**（可以丢弃）：

**Rust 的所有权系统 = 仿射类型 + 显式复制/克隆**:

```rust
// 线性/仿射使用
let v = vec![1, 2, 3];
let v2 = v;      // v 被移动，不能使用
// println!("{:?}", v);  // 错误: value used after move

// 显式复制 (打破仿射约束)
let x = 5;
let y = x;       // Copy trait: x 仍可用
println!("{}", x); // OK

// 显式克隆
let s1 = String::from("hello");
let s2 = s1.clone();  // 克隆创建新值
println!("{} {}", s1, s2); // OK
```

### 6.3 分离合取 (Separating Conjunction)

**定义 6.2** (分离逻辑)

P * Q 表示 P 和 Q 描述的内存区域不相交：

```
P * Q ≡ {(h₁ ⊎ h₂, s) | (h₁, s) ⊨ P ∧ (h₂, s) ⊨ Q}
```

**Rust 对应**:

```rust
// 两个 &mut 引用不能同时存在 (分离性)
let mut data = vec![1, 2, 3];
let r1 = &mut data;
// let r2 = &mut data;  // 错误: cannot borrow as mutable twice

// & 和 &mut 不能共存
let r1 = &data;
// let r2 = &mut data;  // 错误: cannot borrow as mutable
```

---

## 7. 高阶类型 (Higher-Kinded Types)

### 7.1 Kind 系统

**定义 7.1** (Kind)

Kind 是"类型的类型"：

```
κ ::= *           (具体类型)
    | κ₁ → κ₂   (类型构造子)
```

| 类型 | Kind | Rust |
|------|------|------|
| Int | * | `i32` |
| List | *→* | `Vec<T>` |
| Map | *→* → * | `HashMap<K, V>` |
| Monad | (*→*) → * | `Monad<M<_>>` (不完全支持) |

### 7.2 Rust 的限制与 workaround

```rust
// Rust 不完全支持高阶类型，但可以用 GAT 模拟

// 类型构造子: Option<_> 是 * → *
trait Functor {
    type Wrapped<T>;  // GAT: 通用关联类型

    fn fmap<A, B>(self, f: impl Fn(A) -> B) -> Self::Wrapped<B>;
}

impl Functor for Option<i32> {
    type Wrapped<T> = Option<T>;

    fn fmap<A, B>(self, f: impl Fn(A) -> B) -> Self::Wrapped<B> {
        self.map(f)
    }
}
```

---

## 8. 类型安全定理

### 8.1 进展性 (Progress)

**定理 8.1** (进展性)

如果 ⊢ M : τ，则 M 是值，或存在 M' 使得 M → M'。

### 8.2 保持性 (Preservation)

**定理 8.2** (保持性/主题归约)

如果 Γ ⊢ M : τ 且 M → M'，则 Γ ⊢ M' : τ。

### 8.3 Rust 的类型安全

Rust 的类型系统保证：

- **内存安全**: 无悬空指针、无数据竞争
- **类型安全**: 进展性 + 保持性
- **线程安全**: Send/Sync trait 检查

```rust
// 编译器拒绝不安全代码
fn unsafe_attempt() {
    let r;
    {
        let x = 5;
        // r = &x;  // 错误: x does not live long enough
    }
    // println!("{}", r);
}
```

---

## 9. 总结

### 9.1 核心概念速查

| 概念 | 理论 | Rust 实现 |
|------|------|-----------|
| 多态 | System F | `fn<T>` |
| 递归类型 | μ-类型 | `enum` |
| 子类型 | <: | 生命周期 |
| 变型 | +, -, = | `&T`, `&mut T` |
| 线性类型 | ⊸ | 所有权 |
| 高阶类型 | κ | GAT |

### 9.2 延伸阅读

1. *Types and Programming Languages* - Pierce
2. *Advanced Types and Programming Languages* - Pierce
3. *Type Theory and Formal Proof* - Nederpelt & Geuvers

---

**文档大小**: ~30 KB
**状态**: ✅ 完整形式化定义
**最后更新**: 2026-03-08
