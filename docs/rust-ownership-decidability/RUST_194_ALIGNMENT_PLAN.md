# Rust 1.94 特性对齐计划

> **本文档**：规划如何将形式化工作与 Rust 1.94 版本的语言特性对齐。

**日期**: 2026-03-05
**目标版本**: Rust 1.94 (预计 2026年)
**状态**: 阶段1已完成，阶段2进行中

---

## 一、Rust 1.94 特性分析

### 1.1 已稳定的特性（基于发展趋势）

根据 Rust 2025-2026 的发展路线，Rust 1.94 可能包含以下稳定特性：

#### A. 异步特性

- **Async Closures** - 已在 1.85 中稳定
- **Async Fn in Traits** - 已在近期版本中稳定
- **Future 协作** - 持续改进

#### B. 类型系统特性

- **Generic Const Expressions (GCE)** - 逐步稳定中
- **Type Alias Impl Trait (TAIT)** - 逐步稳定中
- **Precise Capturing (`+ use<>`)** - 已在 1.82 中稳定

#### C. 所有权和借用改进

- **Reborrow Trait** - 正在实现中
- **CoerceShared Trait** - 正在实现中
- **Deref/Receiver 改进** - 开发中

#### D. 2024 Edition 相关

- **2024 Edition** - 已在 1.85 中稳定
- **Edition 迁移工具** - 持续改进

### 1.2 与形式化相关的特性

**高优先级**（直接影响所有权系统形式化）：

1. Reborrow Trait - 影响借用规则
2. CoerceShared Trait - 影响共享借用
3. Generic Const Expressions - 影响类型系统

**中优先级**（间接相关）：
4. Async Closures - 影响控制流
5. Precise Capturing - 影响生命周期

**低优先级**（语法糖或库特性）：
6. 新的标准库 API
7. 编译器优化

---

## 二、当前形式化的覆盖分析

### 2.1 已覆盖的 Rust 子集

✅ **已完整覆盖**：

- 基础所有权和借用
- 不可变引用 (`&T`)
- 可变引用 (`&mut T`)
- Box 类型
- 基础生命周期
- 函数调用
- 结构体和枚举

✅ **部分覆盖**：

- 泛型（基础）
- Trait（基础）
- 生命周期参数

❌ **未覆盖**：

- 异步/并发
- 常量泛型
- 复杂的泛型约束
- Unsafe 代码
- 宏系统

### 2.2 与 Rust 1.94 的差距

| 特性 | Rust 1.94 | 当前形式化 | 差距 |
|------|-----------|-----------|------|
| 所有权系统 | 完整 | 基础覆盖 | 需要扩展 reborrow |
| 借用检查 | 完整 | 基础 | 需要 CoerceShared |
| 泛型 | GCE | 基础参数 | 需要常量泛型 |
| 异步 | async/await | 无 | 需要添加 |
| 生命周期 | 精确捕获 | 基础 | 需要扩展 |

---

## 三、对齐策略

### 3.1 策略原则

**原则1：核心优先**

```
优先扩展：
1. 所有权系统（Reborrow, CoerceShared）
2. 类型系统（常量泛型）
3. 生命周期（精确捕获）

延后：
- 异步（太复杂）
- Unsafe（超出范围）
```

**原则2：分层实现**

```
第1层：语法扩展（添加新构造）
第2层：类型系统扩展（添加新规则）
第3层：语义扩展（添加新语义）
第4层：元理论扩展（新定理证明）
```

**原则3：保持可理解性**

```
- 每个新特性都有自然语言解释
- 保持形式化的教学价值
- 不过度复杂化
```

### 3.2 实现路线图

#### 阶段1：基础扩展（4-6周）

**任务1.1：扩展借用系统**

```
目标：支持 Reborrow 和 CoerceShared

具体工作：
1. 添加 Reborrow trait 到类型系统
2. 添加 CoerceShared trait
3. 更新借用检查规则
4. 添加转换规则

文件修改：
- Syntax/Types.v - 添加新类型构造
- Typing/TypeSystem.v - 添加新类型规则
- Metatheory/BorrowChecking.v - 新证明
```

**任务1.2：扩展泛型系统**

```
目标：支持基础常量泛型

具体工作：
1. 添加常量参数到类型参数
2. 添加常量表达式类型
3. 更新泛型实例化规则

文件修改：
- Syntax/Types.v - 常量参数
- Syntax/Expressions.v - 常量表达式
- Typing/TypeSystem.v - 泛型规则
```

#### 阶段2：生命周期扩展（3-4周）

**任务2.1：精确捕获**

```
目标：支持 `+ use<>` 语法

具体工作：
1. 添加 use 子句到类型
2. 更新生命周期推断
3. 添加捕获检查

文件修改：
- Syntax/Types.v - use 子句
- Typing/LifetimeInference.v - 新文件
```

**任务2.2：生命周期复杂性**

```
目标：支持更复杂的生命周期模式

具体工作：
1. 添加 higher-ranked 生命周期
2. 添加 lifetime bounds
3. 更新子类型关系

文件修改：
- Syntax/Types.v - 扩展生命周期
- Typing/Subtyping.v - 新文件
```

#### 阶段3：异步基础（4-6周，可选）

**任务3.1：异步基础**

```
目标：基础 async/await 支持

具体工作：
1. 添加 async 函数类型
2. 添加 await 表达式
3. 添加 Future trait 基础

文件修改：
- Syntax/Types.v - async 类型
- Syntax/Expressions.v - await
- Semantics/AsyncSemantics.v - 新文件
```

#### 阶段4：元理论和文档（3-4周）

**任务4.1：更新元理论**

```
目标：为新特性提供理论保证

具体工作：
1. 扩展终止性证明
2. 更新保持性证明
3. 更新进展证明
```

**任务4.2：更新自然语言文档**

```
目标：记录新特性

具体工作：
1. 更新 OVERVIEW
2. 添加新定理解释
3. 添加新示例
```

---

## 四、技术实现细节

### 4.1 Reborrow Trait 形式化

**Rust 概念**：

```rust
// Reborrow 允许从 &mut T 获取 &T
trait Reborrow<'a, 'b: 'a> {
    fn reborrow(&'a mut self) -> &'b T;
}
```

**形式化添加**：

```coq
(* 添加 Reborrow trait *)
Inductive trait :=
  | Reborrow : lifetime -> lifetime -> trait
  | ...

(* 添加 reborrow 表达式 *)
Inductive expr :=
  | EReborrow : expr -> expr
  | ...

(* 类型规则 *)
| T_Reborrow : forall Δ Γ Θ e ρ₁ ρ₂ τ,
    has_type Δ Γ Θ e (TRef ρ₁ Uniq τ) ->
    ρ₂ ⊑ ρ₁ ->  (* ρ₂ 比 ρ₁ 短 *)
    has_type Δ Γ Θ (EReborrow e) (TRef ρ₂ Shrd τ)
```

### 4.2 CoerceShared Trait 形式化

**Rust 概念**：

```rust
// 允许 &mut T 转换为 &T
trait CoerceShared<T: Copy> {}
```

**形式化添加**：

```coq
(* 添加 CoerceShared trait *)
| CoerceShared : ty -> trait

(* 类型强制规则 *)
| TC_CoerceShared : forall ρ τ,
    is_copy τ ->  (* T 是 Copy *)
    coercion (TRef ρ Uniq τ) (TRef ρ Shrd τ)
```

### 4.3 常量泛型形式化

**Rust 概念**：

```rust
struct Array<T, const N: usize> {
    data: [T; N],
}
```

**形式化添加**：

```coq
(* 常量参数 *)
Inductive param :=
  | TypeParam : var -> param
  | ConstParam : var -> ty -> param

(* 依赖类型数组 *)
| TArray : ty -> const_expr -> ty

(* 常量表达式 *)
Inductive const_expr :=
  | CVar : var -> const_expr
  | CLit : value -> const_expr
  | CBinOp : binop -> const_expr -> const_expr -> const_expr
```

### 4.4 精确捕获形式化

**Rust 概念**：

```rust
fn foo<T>(x: &T) -> impl Sized + use<'_, T> {
    x
}
```

**形式化添加**：

```coq
(* use 子句 *)
Inductive use_clause :=
  | UseLifetimes : list lifetime -> use_clause
  | UseTypes : list ty -> use_clause

(* 扩展到 impl trait *)
| TImplTrait : trait -> use_clause -> ty

(* 捕获检查 *)
Definition captures (e : expr) : set var := ...

Definition check_use_clause (uc : use_clause) (e : expr) : bool :=
  (* 检查 use 子句包含所有捕获 *)
  subset (captures e) (vars_in_use_clause uc)
```

---

## 五、文件结构规划

### 5.1 新文件

```
coq-formalization/theories/
├── ...
├── Advanced/                    (* 新目录：高级特性 *)
│   ├── Reborrow.v              (* Reborrow trait *)
│   ├── CoerceShared.v          (* CoerceShared trait *)
│   ├── ConstGenerics.v         (* 常量泛型 *)
│   ├── PreciseCapturing.v      (* 精确捕获 *)
│   └── AsyncBasics.v           (* 异步基础 *)
├── Typing/
│   ├── ...
│   ├── LifetimeInference.v     (* 新文件：生命周期推断 *)
│   └── Subtyping.v             (* 新文件：子类型关系 *)
└── Examples/
    ├── ...
    ├── ReborrowExamples.v      (* 新文件：Reborrow 示例 *)
    └── ConstGenericExamples.v  (* 新文件：常量泛型示例 *)
```

### 5.2 修改的文件

```
Syntax/Types.v - 添加新类型构造
Syntax/Expressions.v - 添加新表达式
Typing/TypeSystem.v - 添加新类型规则
Semantics/OperationalSemantics.v - 添加新语义
```

---

## 六、验证和测试计划

### 6.1 单元测试

每个新特性都有：

- 类型检查测试
- 语义测试
- 反例测试（应该被拒绝的程序）

### 6.2 集成测试

- 组合多个新特性的测试
- 与现有特性的交互测试

### 6.3 定理验证

- 终止性仍然成立
- 保持性仍然成立
- 进展仍然成立
- 类型安全仍然成立

---

## 七、时间线

| 阶段 | 时间 | 主要任务 | 状态 |
|------|------|---------|------|
| 阶段1 | 4-6周 | Reborrow, CoerceShared, 常量泛型, Precise Capturing | ✅ 已完成 |
| 阶段2 | 3-4周 | 精确捕获完善, Associated Type Bounds, 2024 Edition | 🔄 进行中 |
| 阶段3 | 4-6周 | 异步基础（可选） | ⏳ 待开始 |
| 阶段4 | 3-4周 | 元理论完善, 文档更新 | ⏳ 待开始 |
| **总计** | **14-20周** | **完整对齐** | **~40% 完成** |

---

## 八、风险和缓解

### 8.1 风险识别

**风险1：复杂性爆炸**

```
风险：新特性使形式化过于复杂
缓解：分层实现，保持核心简洁
```

**风险2：证明困难**

```
风险：新特性的元理论证明困难
缓解：先建立框架，逐步填充 admit
```

**风险3：与现有代码冲突**

```
风险：新特性破坏现有证明
缓解：模块化设计，最小化修改
```

### 8.2 质量保证

- 每个新特性都有完整文档
- 每个新特性都有示例
- 定期回归测试

---

## 九、文档更新计划

### 9.1 更新现有文档

| 文档 | 更新内容 |
|------|---------|
| OVERVIEW | 添加新特性概览 |
| THEOREM_INTUITIONS | 添加新定理的解释 |
| CONCEPT_MAP | 更新概念映射 |
| PROOF_STRATEGIES | 添加新证明策略 |

### 9.2 新文档

| 文档 | 内容 |
|------|------|
| ADVANCED_FEATURES.md | 高级特性总览 |
| REBORROW_DEEP_DIVE.md | Reborrow 深入解释 |
| CONST_GENERICS_GUIDE.md | 常量泛型指南 |

---

## 十、结论

对齐 Rust 1.94 是一个重大但可行的任务。关键是：

1. **优先核心特性**：Reborrow, CoerceShared, 常量泛型
2. **分层实现**：语法 → 类型 → 语义 → 元理论
3. **保持质量**：每个特性都有文档和测试
4. **持续验证**：确保新特性不破坏现有理论

这将进一步提升形式化工作的完整性和实用性。

---

*计划创建时间: 2026-03-05*
*预计完成时间: 2026-07-15 (14-20周)*
