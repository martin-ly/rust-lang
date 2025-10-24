# 异步编程形式语义 (Formal Semantics)

> **文档类型**: 🔬 数学模型 | 📐 形式化方法 | 🎓 理论基础  
> **目标**: 提供异步编程的精确数学语义和形式化规范  
> **方法**: 操作语义 + 指称语义 + 类型论 + 范畴论


## 📊 目录

- [📋 形式系统概览](#形式系统概览)
  - [语义层次](#语义层次)
- [🎯 第一部分: 抽象语法](#第一部分-抽象语法)
  - [1.1 核心语法](#11-核心语法)
    - [类型语法](#类型语法)
    - [表达式语法](#表达式语法)
    - [运行时语法](#运行时语法)
- [🎯 第二部分: 类型系统](#第二部分-类型系统)
  - [2.1 类型规则](#21-类型规则)
    - [Future类型](#future类型)
    - [Pin类型](#pin类型)
    - [Send/Sync规则](#sendsync规则)
  - [2.2 子类型关系](#22-子类型关系)
- [🎯 第三部分: 操作语义](#第三部分-操作语义)
  - [3.1 Small-Step语义](#31-small-step语义)
    - [基本规则](#基本规则)
    - [Future规约](#future规约)
    - [状态机转换](#状态机转换)
  - [3.2 并发语义](#32-并发语义)
    - [join语义](#join语义)
    - [select语义](#select语义)
- [🎯 第四部分: 指称语义](#第四部分-指称语义)
  - [4.1 语义域](#41-语义域)
    - [域定义](#域定义)
  - [4.2 语义函数](#42-语义函数)
    - [表达式语义](#表达式语义)
  - [4.3 组合性原理](#43-组合性原理)
- [🎯 第五部分: 代数语义](#第五部分-代数语义)
  - [5.1 Monad结构](#51-monad结构)
    - [Future Monad](#future-monad)
  - [5.2 Functor结构](#52-functor结构)
  - [5.3 Applicative结构](#53-applicative结构)
  - [5.4 等式推理](#54-等式推理)
    - [组合子等式](#组合子等式)
- [🎯 第六部分: 并发模型](#第六部分-并发模型)
  - [6.1 进程演算](#61-进程演算)
    - [CCS风格](#ccs风格)
  - [6.2 CSP模型](#62-csp模型)
  - [6.3 Actor模型](#63-actor模型)
- [🎯 第七部分: 正确性性质](#第七部分-正确性性质)
  - [7.1 类型安全](#71-类型安全)
  - [7.2 内存安全](#72-内存安全)
  - [7.3 数据竞争自由](#73-数据竞争自由)
  - [7.4 活性性质](#74-活性性质)
- [📝 总结](#总结)
  - [形式化框架](#形式化框架)


**最后更新**: 2025-10-19

---

## 📋 形式系统概览

### 语义层次

```text
形式语义体系
├── 语法 (Syntax)
│   ├── abstract syntax
│   ├── type grammar
│   └── well-formedness rules
│
├── 类型系统 (Type System)
│   ├── typing rules
│   ├── subtyping
│   └── type safety
│
├── 操作语义 (Operational Semantics)
│   ├── small-step semantics
│   ├── big-step semantics
│   └── reduction rules
│
├── 指称语义 (Denotational Semantics)
│   ├── domain theory
│   ├── mathematical mapping
│   └── compositional semantics
│
└── 代数语义 (Algebraic Semantics)
    ├── equational laws
    ├── category theory
    └── monad laws
```

---

## 🎯 第一部分: 抽象语法

### 1.1 核心语法

#### 类型语法

```text
τ ::= T                        // 基础类型
    | τ₁ → τ₂                  // 函数类型
    | Future<τ>                // Future类型
    | Pin<Ptr<τ>>              // Pin类型
    | (τ₁, τ₂, ..., τₙ)        // 元组类型
    | &'a τ                    // 引用类型
    | &'a mut τ                // 可变引用

Ptr ::= Box<τ>                 // 堆指针
      | &τ                     // 引用
      | &mut τ                 // 可变引用

约束 ::= T: Send               // Send约束
       | T: Sync               // Sync约束
       | T: Unpin              // Unpin约束
       | T: 'static            // 静态生命周期
```

#### 表达式语法

```text
e ::= x                        // 变量
    | v                        // 值
    | e₁ e₂                    // 函数应用
    | λx: τ. e                 // lambda抽象
    | async { e }              // 异步块
    | e.await                  // await表达式
    | poll(e, cx)              // poll操作
    | let x = e₁ in e₂         // let绑定
    | (e₁, e₂, ..., eₙ)        // 元组

v ::= ()                       // unit
    | n                        // 整数
    | Ready(v)                 // Ready值
    | Pending                  // Pending值
    | Future(S, k)             // Future值 (状态S, 延续k)
    | Pin(ptr)                 // Pin值
```

#### 运行时语法

```text
状态 S ::= S₀                  // 初始状态
         | S₁                  // 中间状态
         | ...
         | Sₙ                  // 最终状态

上下文 Γ ::= ∅                 // 空上下文
          | Γ, x: τ            // 变量绑定
          | Γ, 'a              // 生命周期参数

执行上下文 cx ::= Context {
    waker: Waker,
    local: TaskLocal,
    ...
}
```

---

## 🎯 第二部分: 类型系统

### 2.1 类型规则

#### Future类型

```text
Future类型规则:

              Γ ⊢ e: τ
    ───────────────────────────────
    Γ ⊢ async { e }: Future<τ>

              Γ ⊢ e: Future<τ>
    ───────────────────────────────
    Γ ⊢ e.await: τ

前提: Γ是async上下文
```

#### Pin类型

```text
Pin类型规则:

    τ: Unpin    Γ ⊢ ptr: Ptr<τ>
    ──────────────────────────────
    Γ ⊢ Pin::new(ptr): Pin<Ptr<τ>>

    Γ ⊢ ptr: Ptr<τ>
    ──────────────────────────────── (unsafe)
    Γ ⊢ Pin::new_unchecked(ptr): Pin<Ptr<τ>>

    Γ ⊢ p: Pin<Ptr<τ>>    τ: Unpin
    ──────────────────────────────────
    Γ ⊢ Pin::into_inner(p): Ptr<τ>
```

#### Send/Sync规则

```text
Send传递规则:

    Γ ⊢ τ₁: Send    Γ ⊢ τ₂: Send
    ──────────────────────────────
    Γ ⊢ (τ₁, τ₂): Send

    Γ ⊢ τ: Send
    ──────────────────────────────
    Γ ⊢ Vec<τ>: Send

    Γ ⊢ τ: Send + Sync
    ──────────────────────────────
    Γ ⊢ Arc<τ>: Send + Sync

Sync定义:

    Γ ⊢ &τ: Send
    ──────────────────────────────
    Γ ⊢ τ: Sync
```

### 2.2 子类型关系

```text
子类型规则:

    τ <: τ                     // 反射性

    τ₁ <: τ₂    τ₂ <: τ₃
    ────────────────────       // 传递性
    τ₁ <: τ₃

    τ₂ <: τ₁    τ₃ <: τ₄
    ──────────────────────     // 函数逆变/协变
    τ₁ → τ₃ <: τ₂ → τ₄

    τ <: τ'
    ──────────────────────     // Future协变
    Future<τ> <: Future<τ'>

    'a ⊆ 'b    τ <: τ'
    ──────────────────────     // 引用逆变/协变
    &'b τ <: &'a τ'
```

---

## 🎯 第三部分: 操作语义

### 3.1 Small-Step语义

#### 基本规则

```text
求值关系: ⟨e, σ⟩ → ⟨e', σ'⟩
(表达式e在状态σ下归约到e'和新状态σ')

变量查找:
    ⟨x, σ⟩ → ⟨v, σ⟩    where σ(x) = v

函数应用:
    ⟨(λx. e) v, σ⟩ → ⟨e[v/x], σ⟩

let绑定:
    ⟨let x = v in e, σ⟩ → ⟨e, σ[x ↦ v]⟩
```

#### Future规约

```text
async块创建:
    ⟨async { e }, σ⟩ → ⟨Future(S₀, e), σ⟩
    
    where S₀ = initial state
          e = continuation

await规约:
    ⟨Future(Ready(v)).await, σ⟩ → ⟨v, σ⟩

    ⟨Future(Pending).await, σ⟩ → ⟨Pending, σ⟩
    (暂停，返回给运行时)

poll调用:
    ⟨poll(Future(S, k), cx), σ⟩ → 
        ⟨match execute_state(S, k, cx) {
            Ready(v) => Ready(v),
            Pending => {
                register_waker(cx.waker);
                Pending
            }
        }, σ'⟩
```

#### 状态机转换

```text
状态转换规则:

初始状态:
    S₀ ─execute─> S₁    or    Ready(v)

中间状态:
    Sᵢ ─poll─> Sᵢ₊₁    or    Ready(v)    or    Pending

.await点:
    Sᵢ at await_point ─poll_inner─> 
        if inner.poll() == Ready(v):
            Sᵢ₊₁ with v
        else:
            Pending (save Sᵢ)

完成:
    Sₙ ─> Ready(final_value)
```

### 3.2 并发语义

#### join语义

```text
join规则:

    ⟨poll(f₁, cx)⟩ → Ready(v₁)
    ⟨poll(f₂, cx)⟩ → Ready(v₂)
    ────────────────────────────────
    ⟨join(f₁, f₂)⟩ → Ready((v₁, v₂))

    ⟨poll(f₁, cx)⟩ → Pending  ∨  ⟨poll(f₂, cx)⟩ → Pending
    ──────────────────────────────────────────────────────
    ⟨join(f₁, f₂)⟩ → Pending

并发性质:
    join(f₁, f₂) ≡ join(f₂, f₁)    // 交换律
    join(join(f₁, f₂), f₃) ≡ join(f₁, join(f₂, f₃))    // 结合律
```

#### select语义

```text
select规则:

    ⟨poll(f₁, cx)⟩ → Ready(v₁)
    ────────────────────────────────
    ⟨select(f₁, f₂)⟩ → Ready(v₁)
    (并取消f₂)

    ⟨poll(f₂, cx)⟩ → Ready(v₂)
    ────────────────────────────────
    ⟨select(f₁, f₂)⟩ → Ready(v₂)
    (并取消f₁)

    ⟨poll(f₁, cx)⟩ → Pending  ∧  ⟨poll(f₂, cx)⟩ → Pending
    ─────────────────────────────────────────────────────
    ⟨select(f₁, f₂)⟩ → Pending

非确定性:
    select(f₁, f₂) ≢ select(f₂, f₁)    // 可能不同
```

---

## 🎯 第四部分: 指称语义

### 4.1 语义域

#### 域定义

```text
值域 V = {(), n, Ready(V), Pending, ...}

Future域 F:
    F[τ] = (State × Context) → (Poll[τ] × State)

    where Poll[τ] = Ready(τ) | Pending

状态域 State:
    State = 局部变量 × 捕获变量 × 程序计数器

上下文域 Context:
    Context = Waker × TaskLocal
```

### 4.2 语义函数

#### 表达式语义

```text
语义函数 ⟦·⟧: Expr → Env → Value

⟦x⟧(ρ) = ρ(x)

⟦v⟧(ρ) = v

⟦λx. e⟧(ρ) = Closure(x, e, ρ)

⟦e₁ e₂⟧(ρ) = 
    let v₁ = ⟦e₁⟧(ρ)
    let v₂ = ⟦e₂⟧(ρ)
    apply(v₁, v₂)

⟦async { e }⟧(ρ) = 
    Future(λ(s, cx). 
        let v = ⟦e⟧(ρ ⊕ {state: s, context: cx})
        match v {
            Ready(v) => (Ready(v), s'),
            Pending => (Pending, s)
        }
    )

⟦e.await⟧(ρ) = 
    let Future(f) = ⟦e⟧(ρ)
    loop {
        match f(state, cx) {
            (Ready(v), s') => return v,
            (Pending, s') => {
                save_state(s');
                yield_to_runtime();
            }
        }
    }
```

### 4.3 组合性原理

```text
组合性 (Compositionality):
    ⟦e[e'/x]⟧ = ⟦e⟧[⟦e'⟧/x]

单调性 (Monotonicity):
    e ⊑ e' ⟹ ⟦e⟧ ⊑ ⟦e'⟧

连续性 (Continuity):
    ⟦⊔ᵢ eᵢ⟧ = ⊔ᵢ ⟦eᵢ⟧
```

---

## 🎯 第五部分: 代数语义

### 5.1 Monad结构

#### Future Monad

```text
Future作为Monad:

unit (return):
    return: τ → Future<τ>
    return(v) = ready(v)

bind (>>=):
    (>>=): Future<τ> → (τ → Future<υ>) → Future<υ>
    m >>= f = then(m, f)

Monad律:

1. 左单位律:
    return(v) >>= f  ≡  f(v)

2. 右单位律:
    m >>= return  ≡  m

3. 结合律:
    (m >>= f) >>= g  ≡  m >>= (λx. f(x) >>= g)

证明:
    使用指称语义展开验证每条定律
```

### 5.2 Functor结构

```text
Future作为Functor:

fmap (map):
    fmap: (τ → υ) → Future<τ> → Future<υ>
    fmap(f, m) = map(m, f)

Functor律:

1. 恒等律:
    fmap(id, m)  ≡  m

2. 组合律:
    fmap(g ∘ f, m)  ≡  fmap(g, fmap(f, m))

实现:
    fmap(f, Future(poll)) = Future(λcx. 
        match poll(cx) {
            Ready(v) => Ready(f(v)),
            Pending => Pending
        }
    )
```

### 5.3 Applicative结构

```text
Future作为Applicative:

pure:
    pure: τ → Future<τ>
    pure = return

ap (<*>):
    (<*>): Future<τ → υ> → Future<τ> → Future<υ>
    ff <*> fa = join(ff, fa).map(|(f, a)| f(a))

Applicative律:

1. 恒等律:
    pure(id) <*> v  ≡  v

2. 组合律:
    pure(∘) <*> u <*> v <*> w  ≡  u <*> (v <*> w)

3. 同态律:
    pure(f) <*> pure(x)  ≡  pure(f(x))

4. 交换律:
    u <*> pure(y)  ≡  pure(λf. f(y)) <*> u
```

### 5.4 等式推理

#### 组合子等式

```text
map等式:
    map(ready(v), f)  ≡  ready(f(v))
    map(pending, f)  ≡  pending
    map(map(m, f), g)  ≡  map(m, g ∘ f)

then等式:
    then(ready(v), f)  ≡  f(v)
    then(pending, f)  ≡  pending
    then(then(m, f), g)  ≡  then(m, λx. then(f(x), g))

join等式:
    join(ready(v₁), ready(v₂))  ≡  ready((v₁, v₂))
    join(m₁, m₂)  ≡  join(m₂, m₁)
    join(join(m₁, m₂), m₃)  ≡  join(m₁, join(m₂, m₃))

select等式:
    select(ready(v), m)  ≡  ready(v)
    select(m, ready(v))  ≡  ready(v)
    // 注: select不满足结合律和交换律 (非确定性)
```

---

## 🎯 第六部分: 并发模型

### 6.1 进程演算

#### CCS风格

```text
进程语法:
    P ::= 0                    // 空进程
        | a.P                  // 前缀
        | P | Q                // 并发
        | P + Q                // 选择
        | (νa)P                // 限制
        | !P                   // 复制

异步进程:
    async(e) | rest  ≈  spawn(e) ; rest
    await(f) | rest  ≈  f.poll() ; (if Ready(v) then rest[v] else suspend)

通信:
    send(ch, v) | recv(ch)  →  0 | ⟨v⟩
```

### 6.2 CSP模型

```text
CSP进程:
    P ::= SKIP                 // 成功终止
        | STOP                 // 死锁
        | a → P                // 前缀
        | P □ Q                // 外部选择
        | P ⊓ Q                // 内部选择
        | P ||| Q              // 交错
        | P || Q               // 并行

映射到异步:
    select(f₁, f₂)  ≈  (await f₁ → P) ⊓ (await f₂ → Q)
    join(f₁, f₂)  ≈  (await f₁ → P) ||| (await f₂ → Q)
```

### 6.3 Actor模型

```text
Actor = (State, Behavior, Mailbox)

异步Actor:
    actor A {
        state: S
        
        async fn handle(msg: M) -> Response {
            match msg {
                Msg1 => ...,
                Msg2 => ...,
            }
        }
    }

消息传递:
    A ! msg  ≈  channel.send(msg).await
    receive  ≈  channel.recv().await
```

---

## 🎯 第七部分: 正确性性质

### 7.1 类型安全

```text
类型安全定理 (Type Safety):

进展性 (Progress):
    ∀ e, τ. (∅ ⊢ e: τ) ⟹ (e = v ∨ ∃ e'. e → e')

保型性 (Preservation):
    ∀ e, e', τ. (∅ ⊢ e: τ ∧ e → e') ⟹ ∅ ⊢ e': τ

证明思路:
    对类型推导规则和归约规则进行结构归纳
```

### 7.2 内存安全

```text
Pin安全性:

定理: Pin保证内存位置不变
    ∀ p: Pin<&mut T>, t₁, t₂.
        addr(p@t₁) = addr(p@t₂)

证明:
    1. Pin构造受限 (new需T: Unpin或unsafe)
    2. Pin::into_inner需T: Unpin
    3. 不暴露&mut T (除非T: Unpin)
```

### 7.3 数据竞争自由

```text
Send/Sync保证:

定理: 无数据竞争
    ∀ T: Send, 线程T₁, T₂.
        T₁拥有x: T ∧ T₁ send x to T₂ ⟹ 
        ¬(T₁访问x ∧ T₂访问x 同时发生)

定理: 共享安全
    ∀ T: Sync, 线程T₁, T₂.
        T₁持有&x: &T ∧ T₂持有&y: &T ∧ x = y ⟹
        安全 (无数据竞争)
```

### 7.4 活性性质

```text
最终完成性 (Eventual Completion):

假设:
    1. 资源充足
    2. 所有waker会被调用
    3. 无死锁

定理:
    ∀ f: Future<T>. 
        will_complete(f) ⟺ 
        ∃ n. pollⁿ(f) = Ready(v)

注: 实际中可能因死锁、资源耗尽等无法保证
```

---

## 📝 总结

### 形式化框架

```text
三层语义:
    操作语义 - 如何执行
    指称语义 - 表示什么
    代数语义 - 如何组合

四大性质:
    类型安全 - 进展性+保型性
    内存安全 - Pin机制
    并发安全 - Send/Sync
    活性性质 - 最终完成

关键洞察:
    1. Future是Monad - 组合性
    2. Pin保证安全性 - 内存不变
    3. Send/Sync保证并发 - 无数据竞争
    4. 协作式调度 - 显式让出
```

---

**理论基础**: Type Theory + Category Theory + Process Calculus  
**形式化程度**: ⭐⭐⭐⭐⭐  
**版本**: v1.0

🔬 **严格的数学基础为异步编程提供坚实理论保障！**
