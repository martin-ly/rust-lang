# 证明技术概念族谱

> **创建日期**: 2026-02-23
> **最后更新**: 2026-02-23
> **状态**: ✅ 新建 (Phase 1 Week 1)
> **任务ID**: P1-W6-T4

---

## 证明技术全景

```text
                        证明技术概念族
                               │
        ┌──────────────────────┼──────────────────────┐
        │                      │                      │
   【归纳法】              【构造法】              【反证法】
        │                      │                      │
    ├─结构归纳             ├─存在构造             ├─归谬法
    ├─数学归纳             ├─算法构造             ├─对角线法
    ├─良基归纳             ├─Witness构造          └─矛盾推导
    └─共归纳               └─类型构造
        │
   【分离逻辑】           【类型系统】           【模型论】
        │                      │                      │
    ├─资源代数             ├─进展性               ├─指称语义
    ├─模态断言             ├─保持性               ├─操作语义
    ├─框架规则             ├─强规范化             └─逻辑关系
    └─不变式               └─类型安全
```

---

## 一、归纳法家族

### 1.1 结构归纳法 (Structural Induction)

**适用场景**: 对归纳定义的数据类型（如表达式、类型）进行证明

```coq
(* 示例：表达式上的结构归纳 *)
Theorem expr_induction :
  forall (P : Expr -> Prop),
    P EUnit ->
    (forall b, P (EBool b)) ->
    (forall n, P (EInt n)) ->
    (forall x, P (EVar x)) ->
    (forall x e, P e -> P (EFn x e)) ->
    (forall e1 e2, P e1 -> P e2 -> P (EApp e1 e2)) ->
    forall e, P e.
```

**在Rust形式化中的应用**:
- T-OW2: 对State转移进行归纳
- T-TY1: 对表达式结构进行归纳
- T-BR1: 对借用生命周期进行归纳

### 1.2 数学归纳法 (Mathematical Induction)

**适用场景**: 自然数性质证明

```coq
(* 示例：自然数归纳 *)
Theorem nat_induction :
  forall (P : nat -> Prop),
    P 0 ->
    (forall n, P n -> P (S n)) ->
    forall n, P n.
```

**应用**:
- 证明归纳定义的语义等价
- 证明迭代次数相关的性质

### 1.3 良基归纳法 (Well-Founded Induction)

**适用场景**: 递归函数终止性证明

```
良基关系 R: A -> A -> Prop
- 无无限下降链
- 可用于证明递归终止
```

---

## 二、构造法家族

### 2.1 存在构造 (Existential Construction)

**适用场景**: 证明存在性命题

```coq
(* 示例：证明存在类型安全的表达式 *)
Lemma exists_well_typed_expr :
  exists e tau, has_type empty_ctx e tau.
Proof.
  exists EUnit, (TBase TUnit).
  apply T_Unit.
Qed.
```

### 2.2 Witness构造

**在分离逻辑中的应用**:

```coq
(* Iris: 存在资源构造 *)
Lemma alloc_spec :
  {{{ True }}}
    ref v
  {{{ l, RET l; l ↦ v }}}.
```

---

## 三、反证法家族

### 3.1 归谬法 (Proof by Contradiction)

**适用场景**: 否定性质证明

```coq
(* 示例：数据竞争自由 *)
Theorem no_data_race :
  ~ has_data_race valid_program.
Proof.
  unfold not. intros H.
  (* 假设有数据竞争，推出矛盾 *)
  destruct H as [i [j [a1 [a2 Hrace]]]].
  (* 借用检查规则保证这种访问不可能 *)
  contradiction.
Qed.
```

### 3.2 对角线法 (Diagonalization)

**适用场景**: 不可判定性证明

---

## 四、分离逻辑技术

### 4.1 资源代数

```
资源代数 (Resource Algebra):
- 载体集合 Carrier
- 组合操作 • : Carrier -> Carrier -> Carrier
- 单位元 ε
- 有效性谓词 Valid

在Rust中的应用:
- Points-to断言: l ↦ v
- 所有权资源: Own(x, v)
- 借用资源: Borrow(x, mut/immut)
```

### 4.2 模态断言

```
Persistence (□P): 持久资源，可被任意复制
Later (▷P): 下一步成立
Update (|={E}=> P): 资源更新
```

### 4.3 框架规则 (Frame Rule)

```
{P} C {Q}
-----------------
{P * R} C {Q * R}

（C不触及R中的资源）
```

---

## 五、类型系统证明技术

### 5.1 进展性 (Progress)

```coq
Theorem progress :
  forall e tau,
    has_type empty_ctx e tau ->
    Value e \/ exists e', step e e'.
```

**证明策略**:
1. 对类型推导进行归纳
2. 每种情况证明表达式是值或可约

### 5.2 保持性 (Preservation)

```coq
Theorem preservation :
  forall Gamma e e' tau,
    has_type Gamma e tau ->
    step e e' ->
    has_type Gamma e' tau.
```

**证明策略**:
1. 对类型推导进行归纳
2. 对求值关系进行案例分析
3. 使用替换引理

### 5.3 替换引理 (Substitution Lemma)

```coq
Lemma substitution :
  forall Gamma x e1 e2 tau1 tau2,
    has_type (extend_ctx Gamma x tau1) e2 tau2 ->
    has_type empty_ctx e1 tau1 ->
    has_type Gamma (subst x e1 e2) tau2.
```

**关键**: 替换保持类型

---

## 六、Rust特有证明技术

### 6.1 所有权唯一性证明

```
核心思想:
1. 定义所有权状态转移
2. 证明每种转移保持唯一性
3. 对可达状态归纳
```

### 6.2 借用检查正确性证明

```
核心思想:
1. 定义借用生命周期
2. 证明互斥性（&mut与任何其他借用互斥）
3. 证明共享性（&允许共享）
```

### 6.3 Send/Sync安全性证明

```
核心思想:
1. Send: 值可安全跨线程移动
2. Sync: 值可安全跨线程共享（通过引用）
3. 与借用检查器结合
```

---

## 七、证明技术选择决策树

```
要证明的性质类型?
├── 对所有...成立?
│   ├── 自然数 → 数学归纳
│   ├── 归纳数据类型 → 结构归纳
│   └── 可达状态 → 对可达性归纳
├── 存在...满足条件?
│   └── 构造法（给出具体witness）
├── 不可能发生?
│   └── 反证法
├── 程序行为?
│   ├── 终止性 → 良基归纳 + 度量函数
│   ├── 类型安全 → 进展 + 保持
│   └── 资源安全 → 分离逻辑
└── 并发性质?
    └── 分离逻辑 + 资源不变式
```

---

## 八、与核心定理的对应

| 定理 | 主要证明技术 | 辅助技术 |
| :--- | :--- | :--- |
| T-OW2 | 结构归纳 | 状态机、不变式 |
| T-BR1 | 反证法 | 分离逻辑资源互斥 |
| T-TY3 | 进展+保持 | 替换引理 |
| T-LF2 | 共归纳 | 最大不动点 |
| T-ASYNC | 共归纳 + 分离逻辑 | 状态机组合 |

---

## 九、学习路径

```
入门 (Week 1-4):
├── Software Foundations Vol 1
├── 基本归纳证明练习
└── 简单类型系统证明

进阶 (Week 5-12):
├── Software Foundations Vol 2 (PL)
├── 分离逻辑基础
└── RustBelt论文研读

高级 (Week 13-24):
├── Iris框架深入
├── 并发分离逻辑
└── 机器证明实践
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-23
**状态**: ✅ 已完成 - 证明技术概念族谱
