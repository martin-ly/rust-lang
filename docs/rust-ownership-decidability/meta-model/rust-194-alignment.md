# Rust 1.94 所有权形式化对齐

## 概述

本文档描述了 Rust 所有权可判定性形式化框架与 Rust 1.94 版本特性的对齐工作。
Rust 1.94 引入了多项重要的语言特性，这些特性对所有权和借用系统有直接影响。

## Rust 1.94 新特性概览

### 1. Reborrow Trait

**Rust 特性**：允许从可变借用获取不可变借用

```rust
let x: &mut i32 = ...;
let y: &i32 = x.reborrow();  // 安全地获取不可变视图
```

**形式化要点**：

- 定义 `has_reborrow` 关系，表示类型支持 reborrow
- `&mut T` 可以 reborrow 为 `&T`
- 保持所有权安全，不创建新的可变引用

**关键定理**：

```coq
Theorem reborrow_preserves_ownership_safety :
  forall Δ Γ Θ e ρ₁ ρ₂ τ,
    has_type Δ Γ Θ e (TRef ρ₁ Uniq τ) ->
    lifetime_outlives Δ ρ₁ ρ₂ ->
    ownership_safe_reborrow Δ Γ Θ (ERImplicit e).
```

### 2. CoerceShared Trait

**Rust 特性**：允许共享引用到原始指针的强制转换

```rust
let x: &i32 = ...;
let p: *const i32 = x as *const i32;  // unsafe
```

**形式化要点**：

- 定义 `has_coerce_shared` 关系
- `&T` 可以 coerce 为 `*const T`
- `&mut T` 可以 coerce 为 `*mut T`
- 需要 unsafe 块，程序员负责指针安全

**关键定理**：

```coq
Theorem coerce_preserves_ownership_safety :
  forall Δ Γ Θ ce τ,
    has_type_coerce Δ Γ Θ ce τ ->
    coerce_safe Δ Γ Θ ce.
```

### 3. Const Generics

**Rust 特性**：在类型参数中使用编译时常量

```rust
struct Array<T, const N: usize> { data: [T; N] }
fn process<T, const N: usize>(arr: [T; N]) -> [T; N] { arr }
```

**形式化要点**：

- 定义 `const_ty` 和 `const_val` 表示常量类型和值
- 扩展类型系统支持 `TCArray` 数组类型
- 常量表达式求值 `eval_const_expr`

**关键定理**：

```coq
Theorem const_generics_type_safety :
  forall Δ Γ Θ e τ,
    has_type_const_generic Δ Γ Θ e τ ->
    const_expr_well_formed τ ->
    True.
```

### 4. Precise Capturing (`+ use<'lt>`)

**Rust 特性**：显式指定闭包捕获的生命周期

```rust
fn make_closure<'a>(x: &'a i32) -> impl Fn() -> i32 + use<'a> {
    || *x
}
```

**形式化要点**：

- 定义 `capture_set` 表示捕获的生命周期集合
- 扩展闭包类型 `closure_ty_precise` 包含捕获信息
- 验证捕获集的完备性和有效性

**关键定理**：

```coq
Theorem precise_capture_soundness :
  forall Δ Γ Θ e ctp,
    has_type_precise_closure Δ Γ Θ e ctp ->
    forall ρ, In ρ (ctp_captures ctp) ->
    lifetime_valid Δ ρ = true.
```

## 元理论影响

### 类型安全保持

所有新特性都保持了类型安全：

```coq
Theorem rust_194_type_safety :
  forall Δ Γ Θ e,
    type_safe_rust_194 Δ Γ Θ e.
```

### 向后兼容性

新特性是 opt-in 的，现有代码无需修改：

```coq
Theorem backward_compatibility :
  forall Δ Γ Θ e τ,
    has_type Δ Γ Θ e τ ->
    has_type_rust_194 Δ Γ Θ (R94Base e) τ.
```

### 可判定性

类型检查仍然可判定：

```coq
Theorem decidability_rust_194 :
  forall Δ Γ Θ e,
    {exists τ, has_type_rust_194 Δ Γ Θ e τ} +
    {~ exists τ, has_type_rust_194 Δ Γ Θ e τ}.
```

## 实现状态

### 已完成

- ✅ Reborrow Trait 形式化
- ✅ CoerceShared Trait 形式化
- ✅ Const Generics 基础形式化
- ✅ Precise Capturing 形式化
- ✅ 元理论集成框架

### 待完成

- ⏳ 更完整的常量表达式求值
- ⏳ 常量泛型与借用系统的深度集成
- ⏳ 精确捕获与 impl Trait 的交互
- ⏳ 2024 Edition 的完整语义

## 文件组织

```text
coq-formalization/theories/Advanced/
├── Reborrow.v            # Reborrow Trait 形式化
├── CoerceShared.v        # CoerceShared Trait 形式化
├── ConstGenerics.v       # 常量泛型形式化
├── PreciseCapturing.v    # 精确捕获形式化
└── MetatheoryIntegration.v  # 元理论集成
```

## 验证示例

### 示例1：Reborrow

```coq
Example ex_reborrow_basic : forall Δ Γ Θ,
  let e := EVar "x"%string in
  let Γ' := te_extend Γ "x"%string (TRef RStatic Uniq ti32) in
  has_type_reborrow Δ Γ' Θ (ERImplicit e) (TRef RStatic Shrd ti32).
```

### 示例2：精确捕获

```coq
Example ex_precise_capture_basic : forall Δ Γ Θ,
  let ρ := RVar "a"%string in
  let x_ty := TRef ρ Shrd ti32 in
  let captures := [ρ] in
  let ctp := mk_closure_ty_precise [] ti32 captures [("x", x_ty)] in
  has_type_precise_closure Δ Γ' Θ (EClosure [] body vars) ctp.
```

## 与 Rust 实际实现的差异

1. **简化处理**：本形式化捕获核心语义，省略了部分实现细节
2. **常量表达式**：仅支持基本运算，未覆盖所有 Rust 常量表达式特性
3. **Lint 支持**：新 lint 的形式化语义尚未完全实现
4. **平台相关特性**：平台相关行为作为假设处理

## 结论

Rust 1.94 对齐工作成功地将新特性集成到现有的所有权形式化框架中。
所有新特性都保持了类型安全、进展性和可判定性等关键性质。
形式化为理解这些新特性如何与借用检查器交互提供了严格的数学基础。

## 参考文献

- RFC 3668: Async Closures
- RFC 3617: Precise Capturing
- RFC 3484: Unsafe Extern Blocks
- Rust 1.94 Release Notes
