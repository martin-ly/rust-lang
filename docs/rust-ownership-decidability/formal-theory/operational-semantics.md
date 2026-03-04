# Rust 操作语义形式化理论

## 目录

- [Rust 操作语义形式化理论](#rust-操作语义形式化理论)
  - [目录](#目录)
  - [引言](#引言)
    - [形式化目标](#形式化目标)
    - [数学符号](#数学符号)
  - [小步操作语义 (SOS)](#小步操作语义-sos)
    - [2.1 配置定义](#21-配置定义)
      - [2.1.1 程序配置](#211-程序配置)
      - [2.1.2 求值状态](#212-求值状态)
    - [2.2 表达式求值规则](#22-表达式求值规则)
      - [2.2.1 基本表达式](#221-基本表达式)
      - [2.2.2 算术运算](#222-算术运算)
    - [2.3 所有权与移动语义](#23-所有权与移动语义)
      - [2.3.1 移动操作](#231-移动操作)
      - [2.3.2 复制语义](#232-复制语义)
    - [2.4 Let 绑定](#24-let-绑定)
      - [2.4.1 Let 求值](#241-let-求值)
    - [2.5 函数调用](#25-函数调用)
      - [2.5.1 函数应用](#251-函数应用)
      - [2.5.2 返回语句](#252-返回语句)
    - [2.6 控制流](#26-控制流)
      - [2.6.1 条件表达式](#261-条件表达式)
      - [2.6.2 循环](#262-循环)
    - [2.7 块表达式](#27-块表达式)
      - [2.7.1 顺序执行](#271-顺序执行)
    - [2.8 匹配表达式](#28-匹配表达式)
      - [2.8.1 模式匹配求值](#281-模式匹配求值)
  - [大步操作语义](#大步操作语义)
    - [3.1 求值关系](#31-求值关系)
      - [3.1.1 基本求值](#311-基本求值)
      - [3.1.2 复合表达式](#312-复合表达式)
    - [3.2 函数求值](#32-函数求值)
      - [3.2.1 函数应用](#321-函数应用)
      - [3.2.2 递归函数](#322-递归函数)
    - [3.3 内存操作的大步语义](#33-内存操作的大步语义)
      - [3.3.1 堆分配](#331-堆分配)
      - [3.3.2 解引用](#332-解引用)
  - [结构化操作语义](#结构化操作语义)
    - [4.1 抽象机结构](#41-抽象机结构)
      - [4.1.1 环境语义](#411-环境语义)
      - [4.1.2 续延 (Continuation)](#412-续延-continuation)
    - [4.2 CEK 机器](#42-cek-机器)
      - [4.2.1 CEK 配置](#421-cek-配置)
      - [4.2.2 CEK 转换规则](#422-cek-转换规则)
    - [4.3 环境恢复](#43-环境恢复)
  - [求值上下文](#求值上下文)
    - [5.1 上下文定义](#51-上下文定义)
      - [5.1.1 求值上下文语法](#511-求值上下文语法)
      - [5.1.2 上下文填充](#512-上下文填充)
    - [5.2 上下文语义规则](#52-上下文语义规则)
      - [5.2.1 上下文归约](#521-上下文归约)
    - [5.3 求值策略](#53-求值策略)
      - [5.3.1 调用约定](#531-调用约定)
      - [5.3.2 惰性求值（对比）](#532-惰性求值对比)
  - [Rust 特化语义](#rust-特化语义)
    - [6.1 所有权转移语义](#61-所有权转移语义)
      - [6.1.1 移动的形式化](#611-移动的形式化)
    - [6.2 借用语义](#62-借用语义)
      - [6.2.1 共享借用创建](#621-共享借用创建)
      - [6.2.2 可变借用创建](#622-可变借用创建)
      - [6.2.3 借用使用](#623-借用使用)
    - [6.3 生命周期语义](#63-生命周期语义)
      - [6.3.1 生命周期结束](#631-生命周期结束)
      - [6.3.2 非词法生命周期 (NLL)](#632-非词法生命周期-nll)
    - [6.4 Drop 语义](#64-drop-语义)
      - [6.4.1 隐式 Drop](#641-隐式-drop)
      - [6.4.2 显式 drop()](#642-显式-drop)
    - [6.5 Panic 语义](#65-panic-语义)
      - [6.5.1 Panic 传播](#651-panic-传播)
      - [6.5.2 栈展开](#652-栈展开)
  - [并发操作语义](#并发操作语义)
    - [7.1 线程模型](#71-线程模型)
      - [7.1.1 线程配置](#711-线程配置)
      - [7.1.2 全局配置](#712-全局配置)
    - [7.2 线程创建](#72-线程创建)
      - [7.2.1 spawn 语义](#721-spawn-语义)
    - [7.3 同步原语](#73-同步原语)
      - [7.3.1 Mutex 语义](#731-mutex-语义)
      - [7.3.2 条件变量](#732-条件变量)
    - [7.4 原子操作](#74-原子操作)
      - [7.4.1 内存排序](#741-内存排序)
      - [7.4.2 Load 语义](#742-load-语义)
      - [7.4.3 Store 语义](#743-store-语义)
  - [证明概要](#证明概要)
    - [8.1 确定性定理](#81-确定性定理)
    - [8.2 合流性定理](#82-合流性定理)
    - [8.3 类型保持性](#83-类型保持性)
    - [8.4 进展性定理](#84-进展性定理)
  - [参考文献](#参考文献)
    - [操作语义经典](#操作语义经典)
    - [Rust 语义](#rust-语义)
    - [并发语义](#并发语义)
    - [抽象机](#抽象机)
    - [内存模型](#内存模型)
  - [附录 A：求值规则速查表](#附录-a求值规则速查表)
  - [附录 B：上下文优先级](#附录-b上下文优先级)

---

## 引言

操作语义通过定义程序如何一步步执行来描述编程语言的含义。
对于 Rust 而言，操作语义需要精确地刻画：

- 所有权转移的动态行为
- 借用的创建与使用
- 生命周期的运行时效应（实际上是零开销的）
- panic 和栈展开

### 形式化目标

本文档形式化 Rust 的操作语义：

- **小步语义**：详细的单步转换规则
- **大步语义**：完整的求值关系
- **结构化语义**：符合抽象机结构的规则
- **求值上下文**：规约策略的形式化
- **并发语义**：线程和同步原语

### 数学符号

```
〈e, σ〉→ 〈e', σ'〉   小步归约：表达式 e 在状态 σ 下归约到 e' 和 σ'
e ⇓ v               大步求值：表达式 e 求值得到 v
E[e]                求值上下文：E 是包含洞 e 的上下文
⟶                 多步归约的传递闭包
```

---

## 小步操作语义 (SOS)

### 2.1 配置定义

#### 2.1.1 程序配置

```
Configuration ::= (Expr, Store, Heap, Permission)

Expr ::= ...                    (表达式)
Store ::= Var → Value ∪ {⊥}    (变量存储)
Heap ::= Location → Object     (堆内存)
Permission ::= Location → Perm (权限状态)
```

#### 2.1.2 求值状态

```
State ::= Running | Panic(msg) | Terminated(v)
```

### 2.2 表达式求值规则

#### 2.2.1 基本表达式

**常量**：

```
─────────────
〈c, σ, h, π〉→ 〈const_val(c), σ, h, π〉
```

**变量查找**：

```
σ(x) = v
─────────────
〈x, σ, h, π〉→ 〈v, σ, h, π〉
```

**变量未定义错误**：

```
σ(x) = ⊥
─────────────
〈x, σ, h, π〉→ 〈Panic("use of uninitialized variable"), σ, h, π〉
```

#### 2.2.2 算术运算

**加法（左参数先求值）**：

```
〈e₁, σ, h, π〉→ 〈e₁', σ', h', π'〉
────────────────────────────────────
〈e₁ + e₂, σ, h, π〉→ 〈e₁' + e₂, σ', h', π'〉
```

**加法（右参数求值）**：

```
〈e₂, σ, h, π〉→ 〈e₂', σ', h', π'〉
────────────────────────────────────
〈n + e₂, σ, h, π〉→ 〈n + e₂', σ', h', π'〉
```

**加法（计算结果）**：

```
n = n₁ + n₂
───────────────────────
〈n₁ + n₂, σ, h, π〉→ 〈n, σ, h, π〉
```

### 2.3 所有权与移动语义

#### 2.3.1 移动操作

**移动变量**：

```
σ(x) = v    v ≠ Moved
────────────────────────────────────────
〈move x, σ, h, π〉→ 〈v, σ[x ↦ Moved], h, π〉
```

**移动后使用错误**：

```
σ(x) = Moved
────────────────────────────────────────
〈x, σ, h, π〉→ 〈Panic("use of moved value"), σ, h, π〉
```

#### 2.3.2 复制语义

**复制值**：

```
σ(x) = v    is_copy(v)
────────────────────────────
〈x, σ, h, π〉→ 〈v, σ, h, π〉
```

### 2.4 Let 绑定

#### 2.4.1 Let 求值

**Let 绑定（表达式求值）**：

```
〈e, σ, h, π〉→ 〈e', σ', h', π'〉
──────────────────────────────────────────────────
〈let x: τ = e, σ, h, π〉→ 〈let x: τ = e', σ', h', π'〉
```

**Let 绑定（值绑定）**：

```
loc = alloc_stack(τ)
σ' = σ[x ↦ loc]
store_at(loc, v)
────────────────────────────────────────
〈let x: τ = v, σ, h, π〉→ 〈(), σ', h, π〉
```

### 2.5 函数调用

#### 2.5.1 函数应用

**函数调用（函数表达式求值）**：

```
〈e₁, σ, h, π〉→ 〈e₁', σ', h', π'〉
────────────────────────────────────────
〈e₁(e₂), σ, h, π〉→ 〈e₁'(e₂), σ', h', π'〉
```

**函数调用（参数求值）**：

```
〈e₂, σ, h, π〉→ 〈e₂', σ', h', π'〉
────────────────────────────────────────
〈f(e₂), σ, h, π〉→ 〈f(e₂'), σ', h', π'〉
```

**函数调用（β 归约）**：

```
f = λ(x₁: τ₁, ..., xₙ: τₙ). e_body
σ' = push_frame(f, [x₁↦v₁, ..., xₙ↦vₙ], σ)
──────────────────────────────────────────────────
〈f(v₁, ..., vₙ), σ, h, π〉→ 〈e_body, σ', h, π〉
```

#### 2.5.2 返回语句

**Return**：

```
〈e, σ, h, π〉→ 〈e', σ', h', π'〉
────────────────────────────────────────
〈return e, σ, h, π〉→ 〈return e', σ', h', π'〉
```

**Return 值**：

```
σ_ret = pop_frame(σ)
────────────────────────────────────────
〈return v, σ, h, π〉→ 〈v, σ_ret, h, π〉
```

### 2.6 控制流

#### 2.6.1 条件表达式

**If 条件求值**：

```
〈e, σ, h, π〉→ 〈e', σ', h', π'〉
────────────────────────────────────────
〈if e { e₁ } else { e₂ }, σ, h, π〉→
〈if e' { e₁ } else { e₂ }, σ', h', π'〉
```

**If-True**：

```
────────────────────────────────────────
〈if true { e₁ } else { e₂ }, σ, h, π〉→ 〈e₁, σ, h, π〉
```

**If-False**：

```
────────────────────────────────────────
〈if false { e₁ } else { e₂ }, σ, h, π〉→ 〈e₂, σ, h, π〉
```

#### 2.6.2 循环

**While 循环**：

```
────────────────────────────────────────
〈while e { body }, σ, h, π〉→
〈if e { body; while e { body } } else { () }, σ, h, π〉
```

### 2.7 块表达式

#### 2.7.1 顺序执行

**块求值**：

```
〈e₁, σ, h, π〉→ 〈e₁', σ', h', π'〉
────────────────────────────────────────
〈{ e₁; e₂ }, σ, h, π〉→ 〈{ e₁'; e₂ }, σ', h', π'〉
```

**块语句完成**：

```
────────────────────────────────────────
〈{ (); e }, σ, h, π〉→ 〈e, σ, h, π〉
```

**块值**：

```
────────────────────────────────────────
〈{ v }, σ, h, π〉→ 〈v, σ, h, π〉
```

### 2.8 匹配表达式

#### 2.8.1 模式匹配求值

**Match 求值**：

```
〈e, σ, h, π〉→ 〈e', σ', h', π'〉
────────────────────────────────────────
〈match e { arms }, σ, h, π〉→
〈match e' { arms }, σ', h', π'〉
```

**Match 成功**：

```
match_pattern(p, v) = Some(bindings)
σ' = σ ∪ bindings
────────────────────────────────────────
〈match v { p => e, ... }, σ, h, π〉→ 〈e, σ', h, π〉
```

**Match 失败（尝试下一个分支）**：

```
match_pattern(p, v) = None
────────────────────────────────────────
〈match v { p => e, rest.. }, σ, h, π〉→
〈match v { rest.. }, σ, h, π〉
```

---

## 大步操作语义

### 3.1 求值关系

大步语义直接描述表达式到最终值的映射。

#### 3.1.1 基本求值

**常量**：

```
─────────────
c ⇓ const_val(c)
```

**变量**：

```
σ(x) = v
─────────────
x ⇓ v
```

#### 3.1.2 复合表达式

**加法**：

```
e₁ ⇓ n₁    e₂ ⇓ n₂    n = n₁ + n₂
───────────────────────────────────
e₁ + e₂ ⇓ n
```

**Let 绑定**：

```
e₁ ⇓ v₁    x 绑定到 v₁    e₂ ⇓ v₂
───────────────────────────────────
let x = e₁ in e₂ ⇓ v₂
```

### 3.2 函数求值

#### 3.2.1 函数应用

**应用**：

```
e₁ ⇓ λx.e    e₂ ⇓ v₂    e[x↦v₂] ⇓ v
─────────────────────────────────────
e₁ e₂ ⇓ v
```

#### 3.2.2 递归函数

**Fix 点**：

```
e[rec f(x).e / f, v / x] ⇓ v'
──────────────────────────────
(rec f(x).e)(v) ⇓ v'
```

### 3.3 内存操作的大步语义

#### 3.3.1 堆分配

**Box::new**：

```
e ⇓ v    loc = allocate(sizeof(τ))
heap[loc] = v
───────────────────────────────────
Box::new(e) ⇓ Pointer(loc)
```

#### 3.3.2 解引用

**解引用**：

```
e ⇓ Pointer(loc)    heap[loc] = v
───────────────────────────────────
*e ⇓ v
```

---

## 结构化操作语义

### 4.1 抽象机结构

#### 4.1.1 环境语义

```
Closure ::= (λx.e, ρ)    闭包 = 函数 + 环境

ρ ::= Var → Value        环境映射
```

#### 4.1.2 续延 (Continuation)

```
Continuation ::= Stop | Frame ∘ Continuation

Frame ::=
    | Arg(e, ρ)           (等待参数：□ e)
    | Fun(v)              (等待函数：v □)
    | AddL(e, ρ)          (□ + e)
    | AddR(v)             (v + □)
    | Let(x, e, ρ)        (let x = □ in e)
    | If(e₁, e₂, ρ)       (if □ { e₁ } else { e₂ })
```

### 4.2 CEK 机器

CEK 机器（Control, Environment, Kontinuation）是经典的抽象机模型。

#### 4.2.1 CEK 配置

```
CEK ::= (Control, Environment, Kontinuation)

Control ::= Expr | Value
```

#### 4.2.2 CEK 转换规则

**变量查找**：

```
〈x, ρ, κ〉→ 〈ρ(x), ρ, κ〉
```

**函数创建**：

```
〈λx.e, ρ, κ〉→ 〈Closure(λx.e, ρ), ρ, κ〉
```

**应用（创建帧）**：

```
〈e₁ e₂, ρ, κ〉→ 〈e₁, ρ, Arg(e₂, ρ) ∘ κ〉
```

**应用（函数已求值）**：

```
〈v, ρ, Arg(e, ρ') ∘ κ〉→ 〈e, ρ', Fun(v) ∘ κ〉
```

**应用（β 归约）**：

```
〈v, ρ, Fun(Closure(λx.e, ρ')) ∘ κ〉→
〈e, ρ'[x↦v], κ〉
```

### 4.3 环境恢复

**返回处理**：

```
〈v, ρ, Let(x, e, ρ') ∘ κ〉→ 〈e, ρ'[x↦v], κ〉
```

**停止**：

```
〈v, ρ, Stop〉→ v    (最终答案)
```

---

## 求值上下文

### 5.1 上下文定义

求值上下文 E 描述了表达式中下一个将要归约的位置。

#### 5.1.1 求值上下文语法

```
E ::= □                     (洞)
   |  E + e                (左操作数)
   |  v + E                (右操作数)
   |  E; e                 (顺序)
   |  let x: τ = E in e    (let 绑定)
   |  E(e, ..., e)         (函数位置)
   |  v(E, ..., e)         (参数位置)
   |  if E { e } else { e } (条件)
   |  match E { arms }     (匹配值)
   |  &E                   (共享借用)
   |  &mut E               (可变借用)
   |  *E                   (解引用)
   |  E.f                  (字段访问)
   |  E as τ               (类型转换)
```

#### 5.1.2 上下文填充

```
E[e] 表示将 e 填入 E 的洞 □ 中

示例：(□ + 5)[3] = 3 + 5
```

### 5.2 上下文语义规则

#### 5.2.1 上下文归约

**上下文规则**：

```
e → e'
─────────────
E[e] → E[e']
```

这个规则说明：如果子表达式 e 可以归约为 e'，则在任何上下文 E 中都可以进行此归约。

### 5.3 求值策略

#### 5.3.1 调用约定

**调用-by-值**（Rust 使用）：

```
(λx.e)(v) → e[x↦v]
```

参数在函数调用前被完全求值。

#### 5.3.2 惰性求值（对比）

```
(λx.e)(e') → e[x↦e']
```

参数在需要时才求值（Rust 不使用）。

---

## Rust 特化语义

### 6.1 所有权转移语义

#### 6.1.1 移动的形式化

```
move(x):
    1. v = lookup(x)
    2. mark_moved(x)
    3. return v
```

**移动后使用检查**：

```
check_use(x):
    if is_moved(x) then
        panic("use of moved value")
```

### 6.2 借用语义

#### 6.2.1 共享借用创建

```
&ref x:
    1. v = lookup(x)
    2. tag = fresh_tag()
    3. push_borrow_stack(x, SharedReadOnly(tag))
    4. return Reference(x, tag, Shared)
```

#### 6.2.2 可变借用创建

```
&ref mut x:
    1. check_no_active_borrows(x)  // 检查无活动借用
    2. tag = fresh_tag()
    3. push_borrow_stack(x, Unique(tag))
    4. return Reference(x, tag, Mutable)
```

#### 6.2.3 借用使用

```
use_ref(r, access):
    1. (loc, tag, perm) = decompose(r)
    2. check_valid_borrow(loc, tag)
    3. check_permission(perm, access)
    4. return heap[loc]
```

### 6.3 生命周期语义

#### 6.3.1 生命周期结束

```
end_lifetime(ℓ):
    for each borrow with lifetime ℓ:
        pop_borrow_stack(borrow)
        if was_mutable_borrow(borrow):
            revalidate_parent_borrows()
```

#### 6.3.2 非词法生命周期 (NLL)

```
nll_check:
    基于数据流分析确定借用实际最后使用点
    而非词法作用域结束点
```

### 6.4 Drop 语义

#### 6.4.1 隐式 Drop

```
drop_in_scope(x):
    if !is_moved(x) && needs_drop(type(x)):
        call_drop_glue(x)
        deallocate_if_heap(x)
```

#### 6.4.2 显式 drop()

```
drop(e):
    1. v = eval(e)
    2. call_drop_glue(v)
    3. mark_moved(v)  // 防止双重释放
```

### 6.5 Panic 语义

#### 6.5.1 Panic 传播

```
panic!(msg):
    1. unwind_stack():
       for each frame from top:
           run_drop_glue(frame)
           if landing_pad_exists(frame):
               resume_at_landing_pad(frame)
               return
    2. if no landing pad found:
       abort_process()
```

#### 6.5.2 栈展开

```
unwind_to_target(target_frame):
    while current_frame != target_frame:
        run_destructors(current_frame)
        pop_frame()
```

---

## 并发操作语义

### 7.1 线程模型

#### 7.1.1 线程配置

```
ThreadPool ::= ThreadId → ThreadState

ThreadState ::= {
    id: ThreadId,
    stack: Stack,
    registers: Registers,
    status: Running | Blocked | Terminated
}
```

#### 7.1.2 全局配置

```
GlobalConfig ::= (ThreadPool, SharedMemory, SynchronizationState)

SharedMemory ::= Location → (Value, MutexState)
```

### 7.2 线程创建

#### 7.2.1 spawn 语义

```
spawn(f):
    1. new_thread = create_thread()
    2. new_thread.stack = setup_frame(f)
    3. thread_pool.add(new_thread)
    4. return ThreadHandle(new_thread.id)
```

### 7.3 同步原语

#### 7.3.1 Mutex 语义

**获取锁**：

```
mutex.lock():
    if mutex.state == Unlocked:
        mutex.state = Locked(current_thread)
        return Guard(mutex)
    else:
        current_thread.status = Blocked
        enqueue(mutex.wait_queue, current_thread)
        yield()
```

**释放锁**：

```
mutex.unlock():
    assert mutex.state == Locked(current_thread)
    if mutex.wait_queue.not_empty():
        next_thread = dequeue(mutex.wait_queue)
        mutex.state = Locked(next_thread)
        next_thread.status = Running
    else:
        mutex.state = Unlocked
```

#### 7.3.2 条件变量

```
cv.wait(guard):
    1. mutex.unlock()
    2. enqueue(cv.wait_queue, current_thread)
    3. current_thread.status = Blocked
    4. yield()
    5. mutex.lock()  (被唤醒后)

cv.notify_one():
    if cv.wait_queue.not_empty():
        thread = dequeue(cv.wait_queue)
        thread.status = Running
```

### 7.4 原子操作

#### 7.4.1 内存排序

```
MemoryOrder ::= Relaxed | Release | Acquire | AcqRel | SeqCst
```

#### 7.4.2 Load 语义

```
atomic.load(order):
    match order:
        Acquire | AcqRel | SeqCst => memory_fence(Acquire)
        _ => ()
    return memory[atomic_addr]
```

#### 7.4.3 Store 语义

```
atomic.store(value, order):
    match order:
        Release | AcqRel => memory_fence(Release)
        SeqCst => memory_fence(SeqCst)
        _ => ()
    memory[atomic_addr] = value
```

---

## 证明概要

### 8.1 确定性定理

**定理 8.1 (确定性)**：
如果 〈e, σ〉→ 〈e₁, σ₁〉 且 〈e, σ〉→ 〈e₂, σ₂〉，
则 e₁ = e₂ 且 σ₁ = σ₂。

*证明*：

1. 对每个表达式 e，检查所有适用的规则
2. 证明对于任意给定的 e，只有一条规则适用
3. 或者多条规则产生相同结果

### 8.2 合流性定理

**定理 8.2 (合流性)**：
如果 e →*e₁ 且 e →* e₂，
则存在 e' 使得 e₁ →*e' 且 e₂ →* e'。

*证明*：

1. 使用 Newman's Lemma：终止性 + 局部合流 ⇒ 合流
2. 证明局部合流：分析关键对（critical pairs）
3. 证明终止性：定义适当的良基度量

### 8.3 类型保持性

**定理 8.3 (保持性)**：
如果 Γ ⊢ e : τ 且 〈e, σ〉→ 〈e', σ'〉，
则 Γ' ⊢ e' : τ 且类型环境一致。

*证明*：
对归约关系进行归纳：

- 每种归约规则保持类型
- 状态转换不改变相关变量的类型

### 8.4 进展性定理

**定理 8.4 (进展性)**：
如果 ⊢ e : τ，则：

- e 是值，或
- 存在 e' 使得 e → e'，或
- e 是 panic 表达式

*证明*：
对类型推导进行结构归纳。

---

## 参考文献

### 操作语义经典

1. **Plotkin, G. D.** (1981). A structural approach to operational semantics. *Technical Report*.
   - 结构化操作语义 (SOS) 的开创性工作

2. **Kahn, G.** (1987). Natural semantics. *STACS '87*.
   - 自然语义（大步语义）

3. **Felleisen, M., & Friedman, D. P.** (1986). Control operators, the SECD-machine, and the λ-calculus. *Formal Description of Programming Concepts III*.
   - CEK 机器和续延

4. **Wright, A. K., & Felleisen, M.** (1994). A syntactic approach to type soundness. *Information and Computation*.
   - 类型安全的形式化证明方法

### Rust 语义

1. **Jung, R., et al.** (2018). RustBelt: Securing the foundations of Rust. *POPL '18*.
   - Rust 操作语义的 Iris 形式化

2. **Jung, R., et al.** (2019). Stacked Borrows: An aliasing model for Rust. *POPL '20*.
   - Rust 别名模型

3. **Weiss, A., et al.** (2020). Undefined behavior in Rust. *Tutorial*.
   - Rust 未定义行为语义

### 并发语义

1. **Milner, R.** (1999). *Communicating and Mobile Systems: The π-Calculus*. Cambridge University Press.
   - 并发进程演算

2. **Ley-Wild, R., & Nanevski, A.** (2013). Subjective auxiliary state for coarse-grained concurrency. *POPL '13*.
   - 并发程序逻辑

3. **Turon, A., et al.** (2013). Calculating correct concurrent memory models. *PLDI '13*.
    - 并发内存模型计算

### 抽象机

1. **Landin, P. J.** (1964). The mechanical evaluation of expressions. *Computer Journal*.
    - SECD 机器

2. **Cardelli, L.** (1984). Compiling a functional language. *LFP '84*.
    - 函数式语言编译

3. **Ager, M. S., et al.** (2003). A functional correspondence between evaluators and abstract machines. *PPDP '03*.
    - 求值器与抽象机的对应

### 内存模型

1. **Batty, M., et al.** (2011). Mathematizing C++ concurrency. *POPL '11*.
    - C++ 内存模型形式化

2. **Boehm, H. J., & Adve, S. V.** (2008). Foundations of the C++ concurrency memory model. *PLDI '08*.
    - C++ 并发内存模型基础

---

## 附录 A：求值规则速查表

| 规则名 | 前提 | 结论 |
|-------|------|------|
| CONST | - | c → const_val(c) |
| VAR | σ(x) = v | x → v |
| MOVE | σ(x) = v | move x → v, σ[x↦Moved] |
| ADD | n = n₁ + n₂ | n₁ + n₂ → n |
| BETA | - | (λx.e)(v) → e[x↦v] |
| IF-TRUE | - | if true {e₁} else {e₂} → e₁ |
| IF-FALSE | - | if false {e₁} else {e₂} → e₂ |
| LET | e₁ ⇓ v₁, e₂[x↦v₁] ⇓ v₂ | let x=e₁ in e₂ ⇓ v₂ |

---

## 附录 B：上下文优先级

```
优先级（从高到低）：
1. 原子表达式（变量、常量）
2. 方法调用、字段访问
3. 一元操作（*、&、&mut、!）
4. 算术乘法、除法
5. 算术加法、减法
6. 比较操作
7. 逻辑与
8. 逻辑或
9. 赋值
```

---

*文档版本：1.0.0*
*最后更新：2026年3月*
*作者：Rust 形式化理论研究组*
