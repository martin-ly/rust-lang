# 概念映射：从 Rust 代码到形式化理论

> **本文档目标**：建立 Rust 源代码、直觉概念和形式化定义之间的映射，帮助读者在不同抽象层次间切换。

---

## 一、核心概念的三层映射

### 1.1 所有权（Ownership）

| Rust 代码 | 直觉概念 | 形式化定义 |
|-----------|---------|-----------|
| `let x = 5;` | x "拥有" 值 5 | `te_lookup Γ x = Some ti32` |
| `let y = x;` | 所有权移动到 y | `x` 从环境中移除 |
| `drop(x);` | 释放 x 拥有的内存 | 堆更新操作 |

**形式化解释**：

```coq
(* 所有权 = 在环境中有类型绑定 *)
Definition owns (Γ : type_env) (x : var) (τ : ty) : Prop :=
  te_lookup Γ x = Some τ.

(* 移动 = 从源环境移除，添加到目标环境 *)
Definition move_var (Γ : type_env) (x : var) : type_env :=
  te_remove Γ x.
```

### 1.2 借用（Borrowing）

| Rust 代码 | 直觉概念 | 形式化定义 |
|-----------|---------|-----------|
| `let y = &x;` | 借用 x 的引用 | `EBorrow RStatic Shrd (PVar x)` |
| `*y` | 解引用 | `EDeref (EVar y)` |
| `&mut x` | 可变借用 | `EBorrow RStatic Uniq (PVar x)` |

**形式化解释**：

```coq
(* 借用表达式 *)
Inductive expr :=
  | EBorrow : lifetime -> mutability -> place -> expr
  | EDeref : expr -> expr
  | ...

(* 可变性 *)
Inductive mutability :=
  | Shrd  (* 不可变借用：多个读者 *)
  | Uniq  (* 可变借用：单个写者 *)
```

### 1.3 生命周期（Lifetime）

| Rust 代码 | 直觉概念 | 形式化定义 |
|-----------|---------|-----------|
| `&'a i32` | 引用在 'a 期间有效 | `TRef (RVar "a") Shrd ti32` |
| `'a: 'b` | 'a 比 'b 长 | `LC_Outlives (RVar "a") (RVar "b")` |
| `'static` | 整个程序生命周期 | `RStatic` |

**形式化解释**：

```coq
(* 生命周期 *)
Inductive lifetime :=
  | RStatic                    (* 静态生命周期 *)
  | RVar : var -> lifetime     (* 命名生命周期 *)
  | RAnon : nat -> lifetime.   (* 匿名生命周期 *)

(* 引用类型包含生命周期 *)
Inductive ty :=
  | TRef : lifetime -> mutability -> ty -> ty
  | ...
```

---

## 二、类型系统的映射

### 2.1 基础类型

| Rust 类型 | 形式化类型 | 运行时值 |
|-----------|-----------|---------|
| `()` | `TBase TUnit` | `RVUnit` |
| `bool` | `TBase TBool` | `RVBool b` |
| `i32` | `TBase TI32` | `RVInt n` |
| `String` | `TBase TStr` | `RVString s` |

### 2.2 复合类型

| Rust 类型 | 形式化类型 | 构造方式 |
|-----------|-----------|---------|
| `(i32, bool)` | `TTuple [TI32; TBool]` | `ETuple [e1; e2]` |
| `Box<i32>` | `TBox TI32` | `EBox e` |
| `&i32` | `TRef ρ Shrd TI32` | `EBorrow ρ Shrd p` |
| `&mut i32` | `TRef ρ Uniq TI32` | `EBorrow ρ Uniq p` |

### 2.3 用户定义类型

| Rust 代码 | 形式化表示 |
|-----------|-----------|
| `struct Point { x: i32, y: i32 }` | `TStruct "Point" [TI32; TI32]` |
| `enum Option<T> { Some(T), None }` | `TEnum "Option" [T]` |

---

## 三、表达式映射

### 3.1 变量和值

| Rust 代码 | 形式化表达式 | 求值规则 |
|-----------|-------------|---------|
| `5` | `EValue (VInt 5)` | `E_Value` |
| `x` | `EVar x` | `E_Var`（查栈） |
| `true` | `EValue (VBool true)` | `E_Value` |

### 3.2 借用和解引用

| Rust 代码 | 形式化 | 语义 |
|-----------|--------|------|
| `&x` | `EBorrow RStatic Shrd (PVar x)` | 创建引用 |
| `&mut x` | `EBorrow RStatic Uniq (PVar x)` | 创建可变引用 |
| `*r` | `EDeref r` | 解引用 |
| `Box::new(v)` | `EBox (EValue v)` | 堆分配 |

### 3.3 控制流

| Rust 代码 | 形式化 | 语义 |
|-----------|--------|------|
| `e1; e2` | `ESeq e1 e2` | 顺序执行 |
| `let x = e1; e2` | `ELet Shrd x τ e1 e2` | 绑定 |
| `if b { e1 } else { e2 }` | `EIf b e1 e2` | 条件 |

---

## 四、判断的映射

### 4.1 类型判断

| 自然语言 | Rust 编译器 | 形式化 |
|---------|------------|--------|
| "e 有类型 τ" | 类型检查通过 | `has_type Δ Γ Θ e τ` |
| "变量 x 有类型 τ" | 环境查找成功 | `te_lookup Γ x = Some τ` |
| "p 有类型 τ" | 位置有效 | `place_has_type Δ Γ Θ p τ` |

**类型判断规则示例**：

```coq
(* Rust: let x: i32 = 5; *)
(* 形式化：T_Let *)
| T_Let : forall Δ Γ Θ ω x τ₁ e₁ e₂ τ₂,
    has_type Δ Γ Θ e₁ τ₁ ->
    has_type Δ (te_extend Γ x τ₁) Θ e₂ τ₂ ->
    has_type Δ Γ Θ (ELet ω x τ₁ e₁ e₂) τ₂
```

### 4.2 语义判断

| 自然语言 | 运行时行为 | 形式化 |
|---------|-----------|--------|
| "e 求值为 v" | 程序执行 | `eval s h e v h'` |
| "e 单步到 e'" | 一步执行 | `step s h e s' h' e'` |
| "e 多步到 e'" | 多步执行 | `star_step s h e h' e'` |

**语义规则示例**：

```coq
(* Rust: let x = 5; x *)
(* 求值：x 绑定到 5，然后返回 5 *)
| E_Let : forall s h ω x τ e₁ e₂ v₁ v₂ h' h'' ℓ,
    eval s h e₁ v₁ h' ->
    ℓ = fresh_loc h' ->
    eval (stack_extend s x (RVLoc ℓ))
         (heap_extend h' ℓ v₁) e₂ v₂ h'' ->
    eval s h (ELet ω x τ e₁ e₂) v₂ h''
```

### 4.3 安全性判断

| 自然语言 | 含义 | 形式化 |
|---------|------|--------|
| "e 是所有权安全的" | 没有所有权违规 | `ownership_safe_program Δ Γ Θ e` |
| "没有 use-after-free" | 不访问已释放内存 | `no_use_after_free h e` |
| "e 是内存安全的" | 没有内存错误 | `memory_safe e` |

---

## 五、从 Rust 程序到形式化证明

### 5.1 完整示例

**Rust 程序**：

```rust
fn main() {
    let x = 5;           // let x: i32 = 5;
    let y = &x;          // let y: &i32 = &x;
    println!("{}", *y);  // *y
}
```

**抽象语法**（去除语法糖）：

```
ELet Shrd "x" TI32
  (EValue (VInt 5))
  (ELet Shrd "y" (TRef RStatic Shrd TI32)
    (EBorrow RStatic Shrd (PVar "x"))
    (EDeref (EVar "y")))
```

**类型检查**（简化）：

```text
1. x: i32  （从 EValue 推断）
2. y: &i32 （从 EBorrow 推断）
3. *y: i32 （从 EDeref 推断）
```

**求值过程**：

```text
初始: ([], [], e)

步骤1: ELet x 5 ...
  栈: [("x", RVLoc 0)]
  堆: [(0, RVInt 5)]

步骤2: ELet y (&x) ...
  栈: [("y", RVLoc 0); ("x", RVLoc 0)]

步骤3: EDeref y
  查栈: y -> RVLoc 0
  查堆: 0 -> RVInt 5
  结果: RVInt 5
```

### 5.2 定理应用

**应用保持性定理**：

```text
前提：
- *y 有类型 i32
- *y 求值为 5

结论（保持性）：
- 5 有类型 i32 ✓
```

**应用进展定理**：

```text
前提：
- *y 有类型 i32

结论（进展）：
- *y 要么已经是值（不是）
- 要么可以求值（是！）
```

**应用类型安全**：

```text
前提：
- 程序通过类型检查

结论：
- 程序不会 use-after-free
- 程序不会 double-free
- 程序没有数据竞争
```

---

## 六、概念层次图

### 6.1 从具体到抽象

```text
Rust 源代码
    │
    │ 解析、去除语法糖
    ↓
抽象语法树（AST）
    │
    │ 类型检查
    ↓
类型化 AST
    │
    │ 语义解释
    ↓
操作语义（大步/小步）
    │
    │ 安全性分析
    ↓
安全性性质（内存安全）
    │
    │ 形式化证明
    ↓
定理（类型安全、终止性等）
```

### 6.2 形式化层次

```text
数学基础
    ├── 归纳类型（Inductive Types）
    ├── 良基关系（Well-Founded Relations）
    └── 逻辑（Logic）
         │
         ↓
元模型层
    ├── 语法（Syntax）
    │   ├── 表达式（Expressions）
    │   └── 类型（Types）
    ├── 语义域（Semantic Domains）
    │   ├── 栈（Stack）
    │   └── 堆（Heap）
    └── 判断（Judgments）
         │
         ↓
理论层
    ├── Linearizability
    ├── 类型秩（Type Rank）
    └── 语义（Semantics）
         │
         ↓
定理层
    ├── 终止性（Termination）
    ├── 保持性（Preservation）
    ├── 进展（Progress）
    ├── 类型安全（Type Safety）
    └── 可判定性（Decidability）
         │
         ↓
应用层
    ├── 内存安全保证
    ├── 编译器正确性
    └── 程序验证
```

---

## 七、常见模式和对应

### 7.1 所有权转移模式

| Rust 模式 | 形式化 | 含义 |
|----------|--------|------|
| `let y = x;` | `te_remove Γ x` | x 的所有权移动到 y |
| `let y = x.clone();` | `Γ` 不变 | 复制值，不转移所有权 |
| `drop(x);` | `heap_remove h ℓ` | 释放内存 |

### 7.2 借用模式

| Rust 模式 | 形式化 | 约束 |
|----------|--------|------|
| `&x` | `EBorrow RStatic Shrd (PVar x)` | x 不能被修改 |
| `&mut x` | `EBorrow RStatic Uniq (PVar x)` | x 不能被读取或再次借用 |
| `&*r` | `EBorrow ρ ω (PDeref p)` | reborrow，解引用后借用 |

### 7.3 生命周期模式

| Rust 模式 | 形式化 | 约束 |
|----------|--------|------|
| `&'a T` | `TRef (RVar "a") Shrd T` | 引用在 'a 期间有效 |
| `&'static T` | `TRef RStatic Shrd T` | 引用永久有效 |
| `fn foo<'a>(x: &'a T) -> &'a T` | 函数类型包含生命周期参数 | 输入输出生命周期关联 |

---

## 八、从形式化回到 Rust

### 8.1 形式化结果的解释

**定理：类型安全**

```text
形式化：
  has_type e τ -> eval e v -> has_type v τ

解释：
  "如果 Rust 程序通过编译，那么运行时不会出现类型错误"
```

**定理：内存安全**

```text
形式化：
  has_type e τ -> memory_safe e

解释：
  "如果 Rust 程序通过编译，那么运行时不会出现：
   - use-after-free
   - double-free
   - 数据竞争"
```

**定理：终止性**

```text
形式化：
  Linearizable Γ -> exists Γ', borrow_check_iter Γ = Some Γ'

解释：
  "Rust 编译器一定会在有限时间内完成借用检查"
```

### 8.2 形式化对 Rust 编程的指导

**理解编译器错误**：

```rust
let mut x = 5;
let y = &x;      // 不可变借用
let z = &mut x;  // 错误！不能同时拥有不可变和可变借用
```

**形式化解释**：

```text
y: &i32          -- Shrd 借用
z: &mut i32      -- Uniq 借用

借用规则：
  ~(exists p, is_mutable_ref r1 /\ is_shared_ref r2 /\ both_point_to r1 r2 p)

结论：编译器正确地拒绝了不安全的程序
```

**理解生命周期**：

```rust
fn foo(x: &i32) -> &i32 { x }  // 省略生命周期

fn foo<'a>(x: &'a i32) -> &'a i32 { x }  // 显式生命周期
```

**形式化解释**：

```text
输入：TRef (RVar "a") Shrd TI32
输出：TRef (RVar "a") Shrd TI32

生命周期省略规则：
  如果只有一个输入生命周期，输出使用该生命周期

形式化：
  fn_type = TFn [("x", TRef (RVar "a") Shrd TI32)]
                (TRef (RVar "a") Shrd TI32)
```

---

## 九、总结

这份概念映射文档建立了三个层次之间的联系：

1. **Rust 源代码**：开发者编写的程序
2. **直觉概念**：所有权、借用、生命周期
3. **形式化定义**：数学精确定义

通过这种映射，我们可以：

- 理解为什么 Rust 编译器拒绝某些程序
- 信任 Rust 的内存安全保证
- 在形式化和实现之间切换视角

**关键洞察**：
> Rust 的内存安全不是魔法，而是严格的数学规则的产物。形式化揭示了这些规则的本质。
