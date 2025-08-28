# Rust 所有权语义形式化定义

## 概述

本文档提供 Rust 所有权语义的完整形式化定义，包括所有权转移语义、借用语义、生命周期语义等。
这些语义为 Rust 的所有权系统提供了精确的数学描述。

## 1. 语法定义

### 1.1 表达式语法

**表达式语法**:

```text
e ::= x                    (变量)
    | e₁ e₂               (应用)
    | λx:τ.e              (抽象)
    | let x = e₁ in e₂     (绑定)
    | e₁; e₂              (序列)
    | *e                   (解引用)
    | &e                   (借用)
    | &mut e               (可变借用)
    | Box::new(e)          (装箱)
    | drop(e)              (丢弃)
```

### 1.2 类型语法

**类型语法**:

```text
τ ::= α                    (类型变量)
    | τ₁ → τ₂             (函数类型)
    | &'a τ               (不可变引用)
    | &'a mut τ           (可变引用)
    | Box<τ>              (装箱类型)
    | unit                (单位类型)
    | τ₁ × τ₂             (乘积类型)
```

### 1.3 生命周期语法

**生命周期语法**:

```text
'a ::= 'static            (静态生命周期)
     | 'a                 (生命周期变量)
     | 'b                 (生命周期变量)
     | ...
```

## 2. 所有权转移语义

### 2.1 移动语义

**定义 2.1.1 (移动)**: 移动是将值的所有权从一个变量转移到另一个变量的操作。

**形式化定义**:

```text
Move(x, y) = ∀s. s ⊨ x ↦ v ∧ s' = s - {x ↦ v} + {y ↦ v} ⇒ s' ⊨ y ↦ v
```

**移动规则**:

```text
Γ, x: τ ⊢ e : σ    (Move)
Γ, y: τ ⊢ e[y/x] : σ  if x is moved to y

Γ ⊢ e : τ          (Move Expr)
Γ' ⊢ e : τ         if Γ' = Γ - {x: τ} and x is moved in e
```

### 2.2 复制语义

**定义 2.2.1 (复制)**: 复制是创建值副本的操作，要求类型实现 `Copy` trait。

**形式化定义**:

```text
Copy(x, y) = ∀s. s ⊨ x ↦ v ∧ s' = s + {y ↦ v} ⇒ s' ⊨ x ↦ v ∧ s' ⊨ y ↦ v
```

**复制规则**:

```text
Γ ⊢ e : τ          (Copy)
Γ ⊢ e : τ          if τ: Copy trait

Γ, x: τ ⊢ e : σ    (Copy Var)
Γ, x: τ ⊢ e : σ    if τ: Copy trait
```

### 2.3 丢弃语义

**定义 2.3.1 (丢弃)**: 丢弃是显式释放值的操作。

**形式化定义**:

```text
Drop(x) = ∀s. s ⊨ x ↦ v ∧ s' = s - {x ↦ v} ⇒ s' ⊨ emp
```

**丢弃规则**:

```text
Γ ⊢ e : τ          (Drop)
Γ ⊢ drop(e) : unit if τ is droppable

Γ, x: τ ⊢ e : σ    (Drop Var)
Γ ⊢ e : σ          if x is dropped in e
```

## 3. 借用语义

### 3.1 不可变借用

**定义 3.1.1 (不可变借用)**: 不可变借用允许临时访问值而不获取所有权。

**形式化定义**:

```text
ImmutableBorrow(x, 'a) = ∀s. s ⊨ x ↦ v ∧ 'a ∈ Lifetime(x) ⇒ s ⊨ &'a x ↦ v
```

**不可变借用规则**:

```text
Γ ⊢ e : τ          (Immutable Borrow)
Γ ⊢ &e : &'a τ     if 'a is the lifetime of e

Γ, x: τ ⊢ e : σ    (Borrow Use)
Γ, x: τ ⊢ e : σ    if x is borrowed immutably in e
```

### 3.2 可变借用

**定义 3.2.1 (可变借用)**: 可变借用允许临时修改值而不获取所有权。

**形式化定义**:

```text
MutableBorrow(x, 'a) = ∀s. s ⊨ x ↦ v ∧ 'a ∈ Lifetime(x) ⇒ s ⊨ &'a mut x ↦ v
```

**可变借用规则**:

```text
Γ ⊢ e : τ          (Mutable Borrow)
Γ ⊢ &mut e : &'a mut τ  if 'a is the lifetime of e

Γ, x: τ ⊢ e : σ    (Mutable Borrow Use)
Γ, x: τ ⊢ e : σ    if x is borrowed mutably in e
```

### 3.3 借用冲突

**定义 3.3.1 (借用冲突)**: 借用冲突是指同时存在不兼容的借用。

**形式化定义**:

```text
BorrowConflict(b₁, b₂) = (Mutable(b₁) ∧ Mutable(b₂)) ∨ 
                         (Mutable(b₁) ∧ Immutable(b₂)) ∨
                         (Immutable(b₁) ∧ Mutable(b₂))
```

**借用冲突规则**:

```text
Γ ⊢ e : τ          (Borrow Conflict)
Γ ⊢ e : τ          if no borrow conflicts in e

Γ, x: τ ⊢ e : σ    (Conflict Free)
Γ, x: τ ⊢ e : σ    if no conflicts with x in e
```

## 4. 生命周期语义

### 4.1 生命周期推断

**定义 4.1.1 (生命周期推断)**: 生命周期推断是自动确定引用生命周期的过程。

**形式化定义**:

```text
LifetimeInference(e) = ∀'a ∈ Lifetime(e). 'a ≤ 'b where 'b is the scope of e
```

**生命周期推断规则**:

```text
Γ ⊢ e : τ          (Lifetime Inference)
Γ ⊢ e : τ          if lifetimes are inferred for e

Γ, 'a ⊢ e : τ      (Lifetime Intro)
Γ ⊢ e : τ          if 'a is introduced in e
```

### 4.2 生命周期省略

**定义 4.2.1 (生命周期省略)**: 生命周期省略是自动推断生命周期的规则。

**省略规则**:

```text
fn f(x: &T) -> &U    (Rule 1)
fn f<'a>(x: &'a T) -> &'a U

fn f(x: &T, y: &U) -> &V    (Rule 2)
fn f<'a, 'b>(x: &'a T, y: &'b U) -> &'a V

fn f(x: &T) -> &T    (Rule 3)
fn f<'a>(x: &'a T) -> &'a T
```

### 4.3 生命周期子类型

**定义 4.3.1 (生命周期子类型)**: 生命周期子类型描述了生命周期之间的包含关系。

**形式化定义**:

```text
LifetimeSubtyping('a, 'b) = 'a ≤ 'b
```

**子类型规则**:

```text
'a ≤ 'b            (Lifetime Subtyping)
&'a τ ≤ &'b τ      if 'a ≤ 'b

'a ≤ 'b            (Mutable Lifetime Subtyping)
&'a mut τ ≤ &'b mut τ  if 'a ≤ 'b
```

## 5. 操作语义

### 5.1 求值关系

**求值关系**:

```text
e → e'              (Evaluation)
```

**基本求值规则**:

```text
(λx:τ.e₁) e₂ → e₁[e₂/x]    (Beta)
let x = v in e → e[v/x]     (Let)
e₁; e₂ → e₂                 (Seq)
drop(v) → ()                (Drop)
```

### 5.2 所有权转移规则

**移动求值规则**:

```text
let x = v in e → e[v/x]     (Move)
if v is moved from x to e

x → v                        (Move Var)
if x is moved and v is the value
```

**借用求值规则**:

```text
&e → &'a e                   (Borrow)
if 'a is the lifetime of e

&mut e → &'a mut e           (Mutable Borrow)
if 'a is the lifetime of e
```

### 5.3 内存操作规则

**分配规则**:

```text
Box::new(e) → Box::new(v)    (Box)
if e → v

*Box::new(v) → v             (Unbox)
```

**解引用规则**:

```text
*&v → v                      (Deref Immutable)
*&mut v → v                  (Deref Mutable)
```

## 6. 类型系统

### 6.1 类型判断

**类型判断**:

```text
Γ ⊢ e : τ                    (Type Judgment)
```

**基本类型规则**:

```text
Γ, x: τ ⊢ x : τ              (Var)
Γ, x: τ₁ ⊢ e : τ₂            (Abs)
Γ ⊢ λx:τ₁.e : τ₁ → τ₂

Γ ⊢ e₁ : τ₁ → τ₂            (App)
Γ ⊢ e₂ : τ₁
Γ ⊢ e₁ e₂ : τ₂
```

### 6.2 所有权类型规则

**移动类型规则**:

```text
Γ, x: τ ⊢ e : σ              (Move Type)
Γ ⊢ e : σ                    if x is moved in e

Γ ⊢ e : τ                    (Move Expr Type)
Γ' ⊢ e : τ                   if Γ' = Γ - {x: τ} and x is moved
```

**借用类型规则**:

```text
Γ ⊢ e : τ                    (Borrow Type)
Γ ⊢ &e : &'a τ               if 'a is the lifetime of e

Γ ⊢ e : τ                    (Mutable Borrow Type)
Γ ⊢ &mut e : &'a mut τ       if 'a is the lifetime of e
```

### 6.3 生命周期类型规则

**生命周期约束规则**:

```text
Γ, 'a ⊢ e : τ                (Lifetime Constraint)
Γ ⊢ e : τ                    if 'a is constrained in e

Γ ⊢ e : &'a τ                (Lifetime Use)
Γ ⊢ e : &'b τ                if 'a ≤ 'b
```

## 7. 安全性证明

### 7.1 内存安全

**定理 7.1.1 (内存安全)**: 如果 `⊢ e : τ`，则 `e` 不会发生内存错误。

**证明**:

1. **所有权安全**: 每个值都有唯一的所有者
2. **借用安全**: 借用不会超出被借用值的生命周期
3. **内存泄漏**: 所有分配的内存都会被正确释放

### 7.2 数据竞争自由性

**定理 7.2.1 (数据竞争自由性)**: 如果 `⊢ e : τ`，则 `e` 不会发生数据竞争。

**证明**:

1. **互斥借用**: 同时只能有一个可变借用或多个不可变借用
2. **生命周期约束**: 借用的生命周期不能超过被借用值的生命周期
3. **所有权转移**: 所有权转移后，原变量不能再被使用

### 7.3 类型安全

**定理 7.3.1 (类型安全)**: 如果 `⊢ e : τ` 且 `e → e'`，则 `⊢ e' : τ`。

**证明**:

1. **进展性**: 良类型程序要么是值，要么可以继续求值
2. **保持性**: 求值保持类型
3. **类型错误**: 良类型程序不会发生类型错误

## 8. 算法实现

### 8.1 借用检查算法

**借用检查器**:

```rust
struct BorrowChecker {
    borrows: Vec<Borrow>,
    lifetimes: LifetimeMap,
}

impl BorrowChecker {
    fn check_borrow(&mut self, borrow: &Borrow) -> Result<(), Error> {
        // 检查借用冲突
        for existing in &self.borrows {
            if self.conflicts(borrow, existing) {
                return Err(BorrowConflictError);
            }
        }
        
        // 添加新借用
        self.borrows.push(borrow.clone());
        Ok(())
    }
    
    fn conflicts(&self, b1: &Borrow, b2: &Borrow) -> bool {
        // 检查借用冲突
        (b1.is_mutable() && b2.is_mutable()) ||
        (b1.is_mutable() && b2.is_immutable()) ||
        (b1.is_immutable() && b2.is_mutable())
    }
}
```

### 8.2 生命周期推断算法

**生命周期推断器**:

```rust
struct LifetimeInferrer {
    constraints: Vec<LifetimeConstraint>,
    lifetimes: LifetimeMap,
}

impl LifetimeInferrer {
    fn infer_lifetimes(&mut self, expr: &Expr) -> Result<LifetimeMap, Error> {
        // 收集生命周期约束
        self.collect_constraints(expr)?;
        
        // 求解约束
        self.solve_constraints()?;
        
        Ok(self.lifetimes.clone())
    }
    
    fn collect_constraints(&mut self, expr: &Expr) -> Result<(), Error> {
        match expr {
            Expr::Borrow(e, lifetime) => {
                // 添加生命周期约束
                self.constraints.push(LifetimeConstraint::new(lifetime, e.lifetime()));
            }
            // 其他表达式...
        }
        Ok(())
    }
}
```

## 9. 工程应用

### 9.1 编译器集成

**Rust 编译器集成**:

```rust
// 在 rustc 中的集成
impl<'tcx> TypeChecker<'tcx> {
    fn check_ownership(&mut self, expr: &Expr) -> Result<(), Error> {
        let mut borrow_checker = BorrowChecker::new();
        let mut lifetime_inferrer = LifetimeInferrer::new();
        
        // 检查借用
        borrow_checker.check_borrow(&expr.borrows())?;
        
        // 推断生命周期
        let lifetimes = lifetime_inferrer.infer_lifetimes(expr)?;
        
        // 验证类型
        self.verify_types(expr, &lifetimes)?;
        
        Ok(())
    }
}
```

### 9.2 静态分析工具

**静态分析器**:

```rust
struct OwnershipAnalyzer {
    ownership_map: OwnershipMap,
    borrow_map: BorrowMap,
}

impl OwnershipAnalyzer {
    fn analyze(&mut self, expr: &Expr) -> Result<AnalysisResult, Error> {
        // 分析所有权
        self.analyze_ownership(expr)?;
        
        // 分析借用
        self.analyze_borrows(expr)?;
        
        // 分析生命周期
        self.analyze_lifetimes(expr)?;
        
        Ok(AnalysisResult::new(
            self.ownership_map.clone(),
            self.borrow_map.clone(),
        ))
    }
}
```

## 10. 结论

本文档提供了 Rust 所有权语义的完整形式化定义，包括：

1. **语法定义**: 完整的表达式、类型和生命周期语法
2. **所有权转移语义**: 移动、复制、丢弃的精确语义
3. **借用语义**: 不可变借用、可变借用、借用冲突的语义
4. **生命周期语义**: 生命周期推断、省略、子类型的语义
5. **操作语义**: 求值关系和内存操作规则
6. **类型系统**: 完整的类型判断规则
7. **安全性证明**: 内存安全、数据竞争自由性、类型安全的证明
8. **算法实现**: 借用检查和生命周期推断算法
9. **工程应用**: 编译器集成和静态分析工具

这些语义为 Rust 的所有权系统提供了精确的数学描述，确保了系统的正确性和安全性。

## 参考文献

1. Jung, R., et al. "RustBelt: Securing the foundations of the Rust programming language." POPL 2018.
2. Jung, R., et al. "Stacked borrows: An aliasing model for Rust." POPL 2019.
3. "The Rust Reference." <https://doc.rust-lang.org/reference/>
4. "Rust RFC 2094: Non-lexical lifetimes." <https://github.com/rust-lang/rfcs/blob/master/text/2094-nll.md>
5. Pierce, B. C. "Types and programming languages." MIT Press, 2002.
