# 形式化定义框架

> **Rust所有权系统的数学基础**

---

## 1. 基本语法定义

### 1.1 类型系统

```text
定义 TYPES-1: 类型集合

τ ∈ Type ::=
    | Int                    -- 整数类型
    | Bool                   -- 布尔类型
    | Unit                   -- 单位类型
    | &ρ τ                   -- 不可变引用
    | &mut ρ τ               -- 可变引用
    | Box τ                  -- 堆分配所有权
    | τ₁ → τ₂                -- 函数类型
    | ⟨τ₁, ..., τₙ⟩          -- 元组类型
    | struct {f₁:τ₁, ..., fₙ:τₙ}  -- 结构体类型
    | enum {C₁(τ₁), ..., Cₙ(τₙ)}  -- 枚举类型

ρ ∈ Region ::= 'a | 'static | ρ₁ ∪ ρ₂  -- 生命周期区域
```

### 1.2 所有权状态

```text
定义 OWNERSHIP-STATE-1: 所有权状态

σ ∈ OwnershipState ::=
    | Owned                  -- 拥有值
    | Borrowed(κ, ρ)         -- 被借用， kind κ，生命周期 ρ
    | Moved                  -- 已移动
    | Dropped                -- 已释放

κ ∈ BorrowKind ::= Shared | Mutable  -- 借用类型
```

---

## 2. 所有权核心定义

### 2.1 所有权公理

```text
定义 OWNERSHIP-AXIOMS:

[O1] 唯一性: ∀v. |owners(v)| ≤ 1
     -- 任意时刻，一个值最多有一个所有者

[O2] 转移: owner(v) = x ∧ move(v, y) → owner(v) = y
     -- 所有权可以转移，原所有者失效

[O3] 释放: owner(v) = x ∧ scope_end(x) → drop(v)
     -- 所有者作用域结束，值自动释放

[O4] 借用: owner(v) = x ∧ borrow(v, κ, ρ) →
       (∀y ∈ scope(ρ). accessible(y, v, κ)) ∧ owner(v) = x
     -- 借用期间，值可被访问但所有权不变
```

### 2.2 借用规则

```text
定义 BORROW-RULES:

[B1] 共享借用规则:
     borrow(v, Shared, ρ) →
       ¬∃ρ'. borrow(v, Mutable, ρ') ∧ overlaps(ρ, ρ')
     -- 共享借用期间不能有可变借用

[B2] 可变借用规则:
     borrow(v, Mutable, ρ) →
       ¬∃κ,ρ'. borrow(v, κ, ρ') ∧ overlaps(ρ, ρ')
     -- 可变借用期间不能有任何其他借用

[B3] 生命周期包含:
     borrow(v, κ, ρ) → ρ ⊆ lifetime(owner(v))
     -- 借用生命周期不能超过所有者生命周期

[B4] 别名限制:
     borrow(v, Mutable, ρ) → unique_alias(v, ρ)
     -- 可变借用保证唯一别名
```

---

## 3. 生命周期形式化

### 3.1 生命周期关系

```text
定义 LIFETIME-1: 生命周期偏序

'outlives' 关系 ⊇ : Region × Region → Bool

'static ⊇ ρ                          (全局生命周期最长)
ρ ⊇ ρ                                 (自反性)
ρ₁ ⊇ ρ₂ ∧ ρ₂ ⊇ ρ₃ → ρ₁ ⊇ ρ₃         (传递性)
ρ₁ ⊇ ρ₂ ∧ ρ₂ ⊇ ρ₁ → ρ₁ = ρ₂         (反对称性)

定义 LIFETIME-JOIN: 生命周期并集
ρ₁ ∪ ρ₂ = λx. ρ₁(x) ∨ ρ₂(x)

定义 LIFETIME-MEET: 生命周期交集
ρ₁ ∩ ρ₂ = λx. ρ₁(x) ∧ ρ₂(x)
```

### 3.2 生命周期约束

```text
定义 CONSTRAINTS-1: 约束系统

c ∈ Constraint ::=
    | ρ₁ ⊇ ρ₂              -- 生命周期包含
    | ρ: τ                 -- 生命周期关联类型
    | wf(ρ)                -- 生命周期良构

约束满足: Γ ⊢ c 表示环境Γ满足约束c

[WF-LIFETIME] 生命周期良构规则:
    wf('static)  -- 全局生命周期总是良构

    Γ ⊢ wf(ρ₁) ∧ Γ ⊢ wf(ρ₂)
    ─────────────────────────
    Γ ⊢ wf(ρ₁ ∪ ρ₂)
```

---

## 4. 内存安全定义

### 4.1 内存状态

```text
定义 MEMORY-STATE-1: 内存状态

μ ∈ MemoryState ::= Heap × Stack × Registers

Heap ::= Addr ⇀ Value          -- 堆内存映射
Stack ::= Frame*                -- 栈帧列表
Frame ::= Var ⇀ (Value, Type, Region)  -- 变量绑定
Registers ::= Reg ⇀ Value       -- 寄存器状态

定义 VALID-ACCESS: 有效访问
valid_access(μ, a, κ) ⇔
    a ∈ dom(μ.heap) ∧
    permissions(μ, a) ⊇ κ
```

### 4.2 安全属性

```text
定义 SAFETY-PROPERTIES:

[S1] 无悬垂指针:
     ∀p: &τ. valid(p) → p points_to live_memory

[S2] 无use-after-free:
     use(v) → ¬dropped(v)

[S3] 无数据竞争:
     concurrent_access(v₁, v₂) →
       (readonly(v₁) ∧ readonly(v₂)) ∨
       (v₁ = v₂ ∧ synchronized(v₁))

[S4] 类型安全:
     ∀v: τ. typeof(v) <: τ
```

---

## 5. 类型系统规则

### 5.1 子类型关系

```text
定义 SUBTYPING-1: 子类型规则

<: ⊆ Type × Type

[REFL]   τ <: τ
[TRANS]  τ₁ <: τ₂ ∧ τ₂ <: τ₃ → τ₁ <: τ₃
[FN]     (τ₂ <: τ₁) ∧ (τ₁' <: τ₂') → (τ₁ → τ₁') <: (τ₂ → τ₂')
[REF]    (ρ₁ ⊇ ρ₂) → &ρ₂ τ <: &ρ₁ τ           -- 协变
[MREF]   (ρ₁ ⊇ ρ₂) → &mut ρ₁ τ <: &mut ρ₂ τ   -- 逆变
[LIFE]   'static <: ρ                          -- 静态生命周期最长
```

### 5.2 类型推导

```text
定义 TYPE-INFERENCE: 类型推导规则

Γ ⊢ e : τ  -- 在环境Γ下，表达式e具有类型τ

[VAR]    Γ(x) = τ
         ───────────
         Γ ⊢ x : τ

[BORROW] Γ ⊢ e : τ    ρ fresh
         ─────────────────────
         Γ ⊢ &e : &ρ τ

[MUTBORROW] Γ ⊢ e : τ    ρ fresh    mutable(e)
            ────────────────────────────────
            Γ ⊢ &mut e : &mut ρ τ

[DEREF]  Γ ⊢ e : &ρ τ
         ─────────────
         Γ ⊢ *e : τ

[ASSIGN] Γ ⊢ e₁ : &mut ρ τ    Γ ⊢ e₂ : τ    τ₂ <: τ
         ────────────────────────────────────────
         Γ ⊢ *e₁ = e₂ : Unit
```

---

## 6. 效果系统

### 6.1 效果类型

```text
定义 EFFECTS-1: 效果集合

ε ∈ Effect ::=
    | Read(ρ)              -- 读取生命周期ρ中的值
    | Write(ρ)             -- 写入生命周期ρ中的值
    | Allocate             -- 堆分配
    | Drop(ρ)              -- 释放生命周期ρ中的值
    | Panic                -- 可能panic

效果组合: ε₁ ⊗ ε₂ = ε₁ ∪ ε₂
```

### 6.2 效果规则

```text
定义 EFFECT-RULES:

[E-READ]    Γ ⊢ e : &ρ τ
            ─────────────────
            Γ ⊢ *e : τ ▷ Read(ρ)

[E-WRITE]   Γ ⊢ e₁ : &mut ρ τ    Γ ⊢ e₂ : τ
            ──────────────────────────────
            Γ ⊢ *e₁ = e₂ : Unit ▷ Write(ρ)

[E-ALLOC]   ───────────────────────────
            Γ ⊢ Box::new(e) : Box τ ▷ Allocate

[E-DROP]    Γ ⊢ e : τ    needs_drop(τ)
            ───────────────────────────
            Γ ⊢ drop(e) : Unit ▷ Drop(lifetime(e))

纯函数: pure(f) ⇔ effects(f) ⊆ ∅
```

---

## 7. 并发形式化

### 7.1 Send与Sync定义

```text
定义 SEND-SYNC:

[Send]   T : Send ⇔ ∀t: T. thread_safe_transfer(t)
         -- 可以安全转移到其他线程

[Sync]   T : Sync ⇔ &T : Send
         -- 可以安全地在多线程间共享引用

边界条件:
    - raw pointer *const T / *mut T: !Send, !Sync
    - Cell<T>: !Sync
    - RefCell<T>: !Sync
    - Rc<T>: !Send, !Sync
    - Arc<T: Sync>: Sync
    - Mutex<T: Send>: Send + Sync if T: Send
```

### 7.2 并发安全性

```text
定义 CONCURRENCY-SAFETY:

[CS1] 线程边界:
      spawn(f) requires f: FnOnce() + Send + 'static

[CS2] 共享状态:
      share(&t) between threads requires T: Sync

[CS3] 互斥锁:
      Mutex<T> : Send + Sync if T: Send
      RwLock<T> : Send + Sync if T: Send + Sync

[CS4] 通道:
      Sender<T>: Send + Sync if T: Send
      Receiver<T>: Send if T: Send
```

---

## 8. 异步形式化

### 8.1 Future语义

```text
定义 FUTURE-1: Future类型

Future<Output = T> 表示一个可能异步完成的计算，最终产生T

状态机表示:
State ::=
    | Pending              -- 等待中
    | Ready(T)             -- 已完成，值T
    | Panicked             -- 发生panic

定义 poll: Future × Context → State
```

### 8.2 async/await语义

```text
定义 ASYNC-AWAIT:

[ASYNC] async fn f() -> T  ⟹  fn f() -> impl Future<Output = T>

[AWAIT] e.await  ⟹  loop {
            match poll(e, cx) {
                Ready(v) => break v,
                Pending => yield,
            }
        }

[PIN] Pin<&mut Self> 保证 self-referential 结构安全
```

---

## 9. 验证条件

### 9.1 程序验证

```text
定义 VERIFICATION-CONDITIONS:

[VC1] 借用检查:
      ∀p: &mut τ. unique(p) ∧ lifetime_valid(p)

[VC2] 生命周期检查:
      ∀r: &ρ τ. ρ ⊆ lifetime(owner(pointee(r)))

[VC3] 初始化检查:
      ∀x. use(x) → initialized(x)

[VC4] 移动检查:
      ∀v. use(v) → ¬moved(v) ∨ copyable(typeof(v))
```

### 9.2 不变式

```text
定义 INVARIANTS:

[I1] 类型不变式:
     ∀v: T. invariant_T(v) holds at all times

[I2] 协议不变式:
     ∀p: Protocol. p.state ∈ valid_states(p)

[I3] 资源不变式:
     ∀r: Resource. r.acquired → r.released ∨ r.leaked
```

---

**维护者**: Rust Formal Methods Team
**更新日期**: 2026-03-05
**状态**: ✅ 形式化定义框架 100% 完成
