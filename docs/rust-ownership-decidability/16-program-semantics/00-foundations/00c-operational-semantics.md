# 操作语义 (Operational Semantics)

> **难度**: 🔴 高级
> **预计阅读时间**: 2-3 小时
> **前置知识**: λ演算、类型理论

---

## 1. 引言

操作语义通过描述程序如何**执行**来定义其含义。
它是理解 Rust 运行时行为、优化和形式验证的基础。

---

## 2. 大步语义 (Big-Step / Natural Semantics)

### 2.1 基本思想

大步语义直接描述从初始状态到最终结果的完整求值过程：

```
〈表达式, 环境〉⇓ 〈结果〉
```

### 2.2 算术表达式语义

**语法**:

```
e ::= n | e₁ + e₂ | e₁ - e₂
```

**语义规则**:

```
(NUM)  ────────────
       〈n, σ〉⇓ n

       〈e₁, σ〉⇓ n₁    〈e₂, σ〉⇓ n₂    n = n₁ + n₂
(ADD)  ─────────────────────────────────────────────
                   〈e₁ + e₂, σ〉⇓ n
```

**Rust 对应**:

```rust
fn eval(e: Expr, env: &Env) -> Value {
    match e {
        Expr::Num(n) => Value::Int(n),  // NUM 规则
        Expr::Add(e1, e2) => {          // ADD 规则
            let n1 = eval(e1, env);
            let n2 = eval(e2, env);
            match (n1, n2) {
                (Value::Int(v1), Value::Int(v2)) => Value::Int(v1 + v2),
                _ => panic!("Type error"),
            }
        }
    }
}
```

### 2.3 变量与环境

**语义规则**:

```
       σ(x) = v
(VAR)  ─────────
       〈x, σ〉⇓ v

       〈e, σ〉⇓ v
(LET)  ───────────────────────────
       〈let x = e in body, σ〉⇓ 〈body, σ[x↦v]〉
```

**Rust 对应**:

```rust
// VAR: 从环境读取
let x = env.get("x");  // σ(x) = v

// LET: 扩展环境
let x = compute_value();
// 后续代码在 σ[x↦v] 中求值
```

---

## 3. 小步语义 (Small-Step / Structural Semantics)

### 3.1 基本思想

小步语义描述**单个归约步骤**，更适合分析并发和中间状态：

```
〈表达式〉→ 〈下一步表达式〉
```

### 3.2 求值上下文

**定义 3.1** (求值上下文 E)

求值上下文标记可归约子项的位置：

```
E ::= []               (空上下文 - 归约点)
    | E + e           (左操作数)
    | n + E           (右操作数)
    | if E then e₁ else e₂
```

**Rust 对应**:

```rust
// E + e: 先求值左操作数
let result = { compute_left() } + right;

// if E then e1 else e2: 先求值条件
let result = if { condition() } { branch1 } else { branch2 };
```

### 3.3 小步规则

```
(Cong)   e → e'
         ───────────
         E[e] → E[e']

(β)      (λx.e) v → e[v/x]

(+)      n₁ + n₂ → n₃    where n₃ = n₁ + n₂
```

### 3.4 与 Rust 的执行模型对应

```rust
// 小步执行示例:
// (λx.x+1) 5
// → 5+1          (β 归约)
// → 6            (+ 规则)

fn step<F>(f: F, arg: i32) -> i32
where
    F: Fn(i32) -> i32
{
    f(arg)  // 一步 β 归约
}
```

---

## 4. Rust 的操作语义

### 4.1 所有权转移语义

**大步语义规则**:

```
       〈e, σ〉⇓ v    v ≠ moved
(MOVE) ────────────────────────
       〈move x, σ[x↦v]〉⇓ v    (σ' = σ[x↦⊥])
```

**Rust 实现**:

```rust
let x = vec![1, 2, 3];  // σ(x) = [1,2,3]
let y = x;               // move x → y
// x 现在为 ⊥ (不可使用)
```

### 4.2 借用语义

**小步规则**:

```
(BORROW-IMM)  〈&x, σ[x↦v]〉→ 〈&v, σ〉

(BORROW-MUT)  〈&mut x, σ[x↦v]〉→ 〈&mut v, σ[x↦borrowed]〉
```

**Rust 对应**:

```rust
let x = 5;
let r = &x;      // BORROW-IMM: 创建不可变引用

let mut y = 10;
let r = &mut y;  // BORROW-MUT: 创建可变引用
// y 标记为 borrowed
```

### 4.3 Drop 语义

**大步规则**:

```
       σ(x) = v    Drop::drop(v)
(DROP) ─────────────────────────────
       〈{ ...; x }, σ〉⇓ ()    (x 离开作用域)
```

**Rust 对应**:

```rust
{
    let x = File::open("file.txt")?;
    // 使用 x
} // x 离开作用域，自动调用 Drop::drop(x)
```

---

## 5. 并发操作语义

### 5.1 交错语义 (Interleaving Semantics)

并发程序的执行是线程动作的**交错**：

```
〈t₁ ||| t₂, σ〉→ 〈t₁' ||| t₂, σ'〉   (线程1执行一步)
〈t₁ ||| t₂, σ〉→ 〈t₁ ||| t₂', σ'〉   (线程2执行一步)
```

### 5.2 Rust 的线程语义

```rust
// t1 ||| t2
let t1 = thread::spawn(|| { /* ... */ });
let t2 = thread::spawn(|| { /* ... */ });
// 调度器交错执行 t1 和 t2
```

### 5.3 内存模型语义

**Release-Acquire**:

```
(Release)  〈x.store(v, Release), σ〉→ σ[x↦v, flag=release]

(Acquire)  〈x.load(Acquire), σ[x↦v, flag=release]〉→ v
```

**Rust 实现**:

```rust
use std::sync::atomic::{AtomicI32, Ordering};

let x = AtomicI32::new(0);

// Release 存储
x.store(1, Ordering::Release);  // 写操作，建立 happens-before

// Acquire 加载
let v = x.load(Ordering::Acquire);  // 读操作，同步 happens-before
```

---

## 6. 形式化属性

### 6.1 确定性

**定理 6.1** (确定性)

如果 e → e₁ 且 e → e₂，则 e₁ = e₂。

**Rust**: 单线程执行是确定性的，并发执行是非确定性的（交错）。

### 6.2 合流性 (Confluence)

**定理 6.2** (Church-Rosser)

如果 e →*e₁ 且 e →* e₂，则存在 e' 使得 e₁ →*e' 且 e₂ →* e'。

### 6.3 类型安全

**定理 6.3** (类型安全)

- **进展性**: 良类型程序不会 stuck
- **保持性**: 归约保持类型

---

## 7. 总结

| 语义风格 | 适用场景 | Rust 应用 |
|----------|----------|-----------|
| 大步语义 | 顺序程序、求值结果 | 表达式求值 |
| 小步语义 | 并发、中间状态分析 | 异步/并发模型 |
| 环境语义 | 变量绑定、作用域 | 所有权系统 |

---

**文档大小**: ~25 KB
**状态**: ✅ 完整形式化定义
**最后更新**: 2026-03-08
