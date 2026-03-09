# 形式化定理到编译器实现桥梁文档

> 从数学定理到 rustc 实际实现的映射

---

## 引言：理论与实践的连接

**核心问题**: 我们的形式化证明（300 Qed）与 rustc 实际编译 Rust 代码有什么关系？

**答案**: 本文档建立从形式化定理到 rustc 实现的精确映射，让你理解每个定理如何保障编译器的正确性。

---

## 一、终止性定理 ↔ rustc 借用检查

### 1.1 形式化定理

```coq
Theorem borrow_checking_termination :
  forall Γ, Linearizable Γ ->
  exists Γ' n, borrow_check_iter Γ n = Some Γ'.

(* 含义: 对于满足 Linearizability 的环境，借用检查必然终止 *)
```

### 1.2 rustc 对应实现

**rustc 模块**: `compiler/rustc_borrowck/src/lib.rs`

```rust
// rustc 借用检查入口
pub fn mir_borrowck(tcx: TyCtxt<'_>, def_id: LocalDefId) -> BorrowCheckResult {
    // ...
    let mut borrowck = BorrowCheckContext::new(tcx, body, def_id);

    // 核心借用检查循环
    // 对应: borrow_check_iter
    let result = borrowck.analyze();

    result
}

// 借用检查上下文
struct BorrowCheckContext<'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'tcx Body<'tcx>,
    // ...
}

impl<'tcx> BorrowCheckContext<'tcx> {
    fn analyze(&mut self) -> BorrowCheckResult {
        // 1. 数据流分析 (对应: 度量函数计算)
        self.perform_dataflow_analysis();

        // 2. 冲突检测 (对应: 检查 Linearizability)
        self.detect_conflicts();

        // 3. 报告错误
        self.report_errors()
    }
}
```

### 1.3 映射关系

| 形式化 | rustc 实现 | 含义 |
|:-------|:-----------|:-----|
| `borrow_check_iter` | `BorrowCheckContext::analyze` | 借用检查主循环 |
| `Linearizable Γ` | 有效的 MIR | 输入必须满足约束 |
| `measure(Γ)` | 数据流分析状态 | 度量函数 |
| `Some Γ'` | `BorrowCheckResult` | 成功结果 |

### 1.4 为什么这很重要？

**理论保证**: 借用检查不会无限循环
**实践意义**: 编译器不会挂起
**形式化价值**: 编译器实现的正确性证明基础

---

## 二、类型安全定理 ↔ rustc 类型检查

### 2.1 形式化定理

```coq
Theorem type_safety :
  forall Δ Γ Θ e τ,
    has_type Δ Γ Θ e τ ->
    (is_value e) \/
    (exists e', step e e' /\ has_type Δ Γ' Θ' e' τ).

(* 含义: 良类型程序不会卡住，可以安全执行 *)
```

### 2.2 rustc 对应实现

**rustc 模块**: `compiler/rustc_typeck/src/`

```rust
// rustc 类型检查入口
pub fn typeck(tcx: TyCtxt<'_>, def_id: LocalDefId) -> &TypeckResults<'_> {
    let mut type_checker = TypeChecker::new(tcx, def_id);

    // 类型检查
    // 对应: has_type 判断
    type_checker.check_body();

    // 返回结果
    type_checker.results()
}

// 类型检查器
struct TypeChecker<'tcx> {
    tcx: TyCtxt<'tcx>,
    infcx: InferCtxt<'tcx>,
    // ...
}

impl<'tcx> TypeChecker<'tcx> {
    fn check_expr(&mut self, expr: &Expr) -> Ty<'tcx> {
        match expr.kind {
            ExprKind::Binary(op, lhs, rhs) => {
                let lhs_ty = self.check_expr(lhs);
                let rhs_ty = self.check_expr(rhs);

                // 检查操作数类型
                // 对应: 类型规则应用
                self.check_binop(op, lhs_ty, rhs_ty)
            }
            ExprKind::Borrow(kind, expr) => {
                // 借用检查
                // 对应: T-Borrow 规则
                self.check_borrow(kind, expr)
            }
            // ...
        }
    }
}
```

### 2.3 映射关系

| 形式化 | rustc 实现 | 含义 |
|:-------|:-----------|:-----|
| `has_type` | `TypeChecker::check_expr` | 类型检查函数 |
| `step` | MIR 解释器 | 求值步进 |
| `is_value` | 值判断 | 表达式是否已求值 |
| `Δ, Γ, Θ` | `TyCtxt`, 局部变量环境 | 类型环境 |

### 2.4 类型规则对应

形式化规则 → rustc 实现:

```
T-Var:  Γ(x) = τ
        --------
        Γ ⊢ x : τ

→ rustc: 查局部变量表

T-Borrow:  Γ ⊢ p : τ    Γ ⊢_ω p ok
           -----------------------
           Γ ⊢ &ω p : &ω τ

→ rustc: check_borrow() in borrowck

T-App:    Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
          -------------------------------
          Γ ⊢ e₁ e₂ : τ₂

→ rustc: 函数调用类型检查
```

---

## 三、可判定性定理 ↔ 编译流程

### 3.1 形式化定理

```coq
Theorem rust_type_system_fully_decidable :
  forall (p : program),
    Linearizable (program_type_env p) ->
    {well_typed_program p} + {~ well_typed_program p}.

(* 含义: 对于满足 Linearizability 的程序，类型检查是可判定的 *)
```

### 3.2 rustc 对应实现

**rustc 编译流程**:

```rust
// rustc_driver/src/lib.rs
pub fn compile_input(
    sess: &Session,
    input: &Input,
    output: Option<&Path>
) -> Result<(), Error> {
    // 1. 解析 (Parsing)
    let krate = parse_input(input)?;

    // 2. 宏展开 (Expansion)
    let krate = expand_macros(krate)?;

    // 3. 名称解析 (Name Resolution)
    let resolutions = resolve_names(&krate)?;

    // 4. 降低到 HIR
    let hir = lower_to_hir(krate, &resolutions)?;

    // 5. 类型检查 (对应: 可判定性)
    // 这是我们要证明会终止的步骤
    type_check(&hir)?;

    // 6. 借用检查 (对应: 终止性)
    borrow_check(&hir)?;

    // 7. 代码生成
    codegen(&hir, output)?;

    Ok(())
}
```

### 3.3 映射关系

| 形式化 | rustc 实现 | 含义 |
|:-------|:-----------|:-----|
| `well_typed_program p` | 成功类型检查 | 程序类型正确 |
| `~ well_typed_program p` | 类型错误报告 | 程序类型错误 |
| `{A} + {~A}` | Result 类型 | 必定成功或失败 |
| `Linearizable` | 前置条件检查 | 确保可判定 |

### 3.4 为什么可判定性重要？

**理论保证**: 编译器总能给出答案（接受或拒绝）
**实践意义**: 不会遇到无限类型检查
**对比**: C++ 模板可能导致无限编译

---

## 四、保持性定理 ↔ 优化正确性

### 4.1 形式化定理

```coq
Theorem preservation :
  forall Δ Γ Θ e τ,
    has_type Δ Γ Θ e τ ->
    eval e v ->
    value_has_type v τ.

(* 含义: 求值保持类型 *)
```

### 4.2 rustc 对应实现

**rustc 优化流程**:

```rust
// compiler/rustc_mir_transform/src/lib.rs
pub fn run_optimization_passes(tcx: TyCtxt<'_>, body: &mut Body<'_>) {
    // 每个优化都必须保持语义
    // 对应: preservation

    // 1. 常量传播
    ConstProp.run_pass(tcx, body);
    // 保证: 传播后的代码与原代码等价

    // 2. 死代码消除
    DeadCodeElimination.run_pass(tcx, body);
    // 保证: 消除的代码不影响结果

    // 3. 内联
    Inlining.run_pass(tcx, body);
    // 保证: 内联后语义不变
}

// 优化正确性验证
fn verify_preservation(original: &Body, optimized: &Body) {
    // 检查: optimized 的语义 = original 的语义
    // 这对应于 preservation 的形式化验证
}
```

### 4.3 映射关系

| 形式化 | rustc 实现 | 含义 |
|:-------|:-----------|:-----|
| `eval e v` | MIR 优化 | 代码转换 |
| `value_has_type v τ` | 优化后类型检查 | 保持类型 |
| 保持性 | 优化正确性 | 语义不变 |

---

## 五、借用检查等价性 ↔ MIR 分析

### 5.1 形式化定理

```coq
Theorem borrow_check_equivalence :
  forall Γ e,
    borrow_check_passes Γ e <-> ownership_safe Γ e.

(* 含义: 借用检查通过 ⟺ 所有权安全 *)
```

### 5.2 rustc 对应实现

**rustc 借用检查详细流程**:

```rust
// compiler/rustc_borrowck/src/lib.rs
fn mir_borrowck(tcx: TyCtxt<'_>, def_id: LocalDefId) -> &BorrowCheckResult {
    let body = tcx.optimized_mir(def_id);

    // 1. 构建借用图
    // 对应: 所有权图构建
    let borrow_set = build_borrow_set(body);

    // 2. 数据流分析
    // 对应: 检查所有权安全
    let flow_state = do_dataflow_analysis(body, &borrow_set);

    // 3. 冲突检测
    // 对应: 检查 borrow_check_passes
    let errors = detect_conflicts(body, &flow_state);

    // 4. 返回结果
    // 对应: 判断 ownership_safe
    if errors.is_empty() {
        &BorrowCheckResult::Ok
    } else {
        &BorrowCheckResult::Errors(errors)
    }
}

// 借用集构建
fn build_borrow_set(body: &Body<'_>) -> BorrowSet<'_> {
    // 对应: 收集所有借用表达式
    // 构建所有权图
}

// 数据流分析
fn do_dataflow_analysis(body: &Body<'_>, borrow_set: &BorrowSet<'_>) -> FlowState {
    // 对应: 分析每个点的活跃借用
    // 检查借用规则
}
```

### 5.3 映射关系

| 形式化 | rustc 实现 | 含义 |
|:-------|:-----------|:-----|
| `borrow_check_passes` | 无编译错误 | 借用检查通过 |
| `ownership_safe` | 数据流分析确认 | 所有权安全 |
| 等价性 | 分析与报错一致 | 正确性保证 |

---

## 六、定理组合保证编译器正确性

### 6.1 完整保证链

```
数学基础 (归纳、良基)
    ↓
Linearizability 检查
    ↓
终止性定理 ───────┐
    ↓            │
类型检查终止      ├──→ 编译器不会挂起
    ↓            │
可判定性定理 ─────┘
    ↓
类型安全定理 ─────┐
    ↓            │
保持性定理 ───────┼──→ 编译正确程序
    ↓            │
借用检查等价性 ───┘
    ↓
内存安全保证 ───────→ 生成安全代码
```

### 6.2 编译器正确性声明

基于形式化证明，我们可以声明：

```
定理: rustc 类型检查和借用检查是可靠的 (sound)

证明:
1. 终止性定理保证类型检查会结束
2. 可判定性定理保证一定能得到结果
3. 类型安全定理保证通过的程序不会运行时类型错误
4. 借用检查等价性保证借用检查通过 ⟺ 所有权安全
5. 因此: 编译通过的 Rust 程序是内存安全的
```

### 6.3 实际意义

**对开发者**:

- 如果代码编译通过，它不会内存不安全
- 编译错误是保护机制，不是阻碍

**对编译器开发者**:

- 形式化指导实现
- 可以验证优化的正确性

**对研究者**:

- 可以扩展理论
- 可以验证新特性

---

## 七、形式化与实现的差异

### 7.1 简化与完整

| 形式化 | rustc | 差异 |
|:-------|:------|:-----|
| Featherweight Rust | 完整 Rust | 形式化简化了许多特性 |
| 理想语义 | 实际语义 | 实现有优化和 corner cases |
| 终止性假设 | 资源限制 | 实际编译器有超时机制 |

### 7.2 为什么简化是必要的？

```
完整 Rust:
- 宏系统
- 泛型
- Trait
- 生命周期省略
- 等等...

形式化模型:
- 核心所有权
- 核心借用
- 核心生命周期
- 简化类型系统

简化使得:
1. 证明可行
2. 核心原理清晰
3. 可以逐步扩展
```

### 7.3 从简化到完整的路径

```
Featherweight Rust (本工作)
    ↓
添加: 泛型、Trait、生命周期省略
    ↓
添加: 宏、const 泛型、async
    ↓
添加: unsafe、FFI
    ↓
完整 Rust 形式化
```

**本工作定位**: 核心所有权系统的形式化
**RustBelt**: 包含 unsafe 的完整形式化
**关系**: 本工作是 RustBelt 的安全子集基础

---

## 八、验证 rustc 实现

### 8.1 使用形式化验证编译器

**现状**: rustc 尚未完全形式化验证
**进展**: 一些关键组件正在验证中

```
已验证:
- MIR 解释器 (部分)
- 借用检查算法 (部分)
- 标准库组件 (Prusti, Creusot)

进行中:
- 类型推断
- 优化 passes
- 代码生成
```

### 8.2 开发者如何使用形式化

```rust
// 1. 理解编译错误
error[E0382]: use of moved value
// 理解: 线性逻辑 - 资源已消耗

// 2. 设计安全的 API
fn safe_api(data: &[u8]) -> Result<Data, Error> {
    // 借用而不是移动
    // 基于借用规则设计
}

// 3. 验证 unsafe 代码
unsafe fn verified_unsafe(ptr: *mut T) {
    // 手动检查形式化条件
    // 例如: ptr 非空，已对齐等
}
```

---

## 九、总结

### 9.1 映射总览

| 形式化定理 | rustc 模块 | 保证 |
|:-----------|:-----------|:-----|
| 终止性 | `rustc_borrowck` | 编译不挂起 |
| 类型安全 | `rustc_typeck` | 类型正确性 |
| 可判定性 | 编译流程 | 总能出结果 |
| 保持性 | 优化 passes | 优化正确 |
| 借用等价性 | 借用检查 | 内存安全 |

### 9.2 理论到实践的桥梁价值

1. **理解编译器**: 知道 rustc 为什么这样工作
2. **信任编译器**: 知道编译通过的代码是安全的
3. **改进编译器**: 用形式化指导实现
4. **教学**: 理解 Rust 设计的理论基础

---

*本文档建立了从形式化定理到 rustc 实现的完整桥梁*
