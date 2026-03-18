# Iris 框架: 高阶并发分离逻辑

> **难度**: 🔴 专家级
> **预计阅读时间**: 4-5 小时
> **前置知识**: 分离逻辑、模态逻辑、类型理论
> **参考**: Iris Project (iris-project.org), POPL 2015-2023 论文

---

## 1. 引言

Iris 是一个用于验证并发高阶程序的框架，基于高阶分离逻辑。
它是 RustBelt 验证 Rust 代码的基础。

### 1.1 核心设计目标

| 特性 | 说明 | Rust 相关性 |
|------|------|-------------|
| **高阶性** | 支持高阶函数和抽象谓词 | trait、闭包 |
| **并发性** | 模块化验证共享状态并发 | Arc、Mutex、原子操作 |
| **原子性** | 验证原子操作的规约 | Atomic* 类型 |
| **模块化** | 资源推理的组合性 | 所有权系统 |

---

## 2. 基础: 分离逻辑回顾

### 2.1 分离合取 (*)

```
P * Q  ≡  P 和 Q 在不相交的堆上成立
```

**推理规则**:

```
P₁ * P₂ ⊢ Q₁ * Q₂    (如果 P₁ ⊢ Q₁ 且 P₂ ⊢ Q₂)
```

**Rust 对应**:

```rust
// {x ↦ v} * {y ↦ w} 表示 x 和 y 拥有不相交的资源
let x = Box::new(1);
let y = Box::new(2);  // x 和 y 的资源分离
```

### 2.2 分离蕴含 (*-)

```
P -* Q  ≡  如果添加满足 P 的资源，则得到 Q
```

---

## 3. Iris 核心概念

### 3.1 资源代数 (Resource Algebra)

**定义 3.1** (资源代数)

资源代数 (M, ⋅, ε) 是一个带有组合运算的幺半群：

```
a ⋅ b = c    (资源组合)
ε       (单位元)
```

**Rust 所有权作为资源代数**:

```
owned(T) : 独占所有权
shared(n, T) : n 个共享引用
```

### 3.2 命题与资源

Iris 命题包含：

| 命题 | 含义 | 符号 |
|------|------|------|
| `l ↦ v` | 位置 l 存储值 v | 点态断言 |
| `P * Q` | 分离合取 | * |
| `P -* Q` | 分离蕴含 | -* |
| `□ P` | 持续性 (persistently) | □ |
| `◇ P` | 可能性 (later modality) | ◇ |

### 3.3 持续性模态 (□)

**定义 3.2** (持续性)

□P 表示 P 是永远成立的资源，可以复制：

```
□P ⊢ P           (提取)
□P ⊢ □P * □P     (复制)
```

**Rust 对应**:

```rust
// 'static 生命周期是持续的
fn static_value() -> &'static str {
    "hello"  // □(str)
}

// Copy trait 允许复制
let x: i32 = 5;
let y = x;  // 可以使用 x 和 y (□P)
```

### 3.4 Later 模态 (◇)

**定义 3.3** (Later)

◇P 表示"在下一步递归中 P 成立"，用于处理递归定义：

```
◇P ⊢ P    (在不动点中)
```

---

## 4. Hoare 类型 (Hoare Type Theory)

### 4.1 计算类型

```
{e} : ST P A Q   ≡   在前提 P 下，e 产生类型 A 的值，并建立 Q
```

### 4.2 Rust 函数的 Iris 规约

```rust
// fn take<T>(x: Box<T>) -> T
// 规约: {x ↦ v} take(x) {ret. ret = v}

// fn clone<T: Clone>(x: &T) -> T
// 规约: {x ↦□ v} clone(x) {ret. ret = v * x ↦□ v}
```

---

## 5. 并发验证

### 5.1 线程局部资源

```
{P} fork {e} {Q}    ≡    创建新线程，拥有资源 Q
```

### 5.2 共享资源: 不变量

**定义 5.1** (不变量)

```
inv N P    ≡    命名空间 N 中的不变量 P
```

P 在任何时候都成立，但只能在原子操作时短暂"打开"。

**Rust 对应**:

```rust
// Mutex 保护的不变量
lazy_static! {
    static ref COUNTER: Mutex<i32> = Mutex::new(0);
}
// inv "counter" (∃n. COUNTER ↦ n)
```

### 5.3 原子操作规约

```
〈l ↦ v〉  load(l)  〈l ↦ v * ret = v〉

〈l ↦ _〉  store(v)  〈l ↦ v〉

〈l ↦ v〉  CAS(v, v')  〈l ↦ v' * ret = true〉
    ∨ 〈l ↦ v * ret = false〉 (如果 CAS 失败)
```

**Rust 实现**:

```rust
use std::sync::atomic::{AtomicI32, Ordering};

let x = AtomicI32::new(0);

// Load: 〈x ↦ 0〉
let v = x.load(Ordering::SeqCst);  // ret = 0
// 〈x ↦ 0 * ret = 0〉

// CAS: 尝试将 0 换成 1
let success = x.compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst);
// 成功: 〈x ↦ 1 * ret = Ok(0)〉
```

---

## 6. RustBelt 连接

### 6.1 类型作为 Iris 命题

RustBelt 将 Rust 类型映射到 Iris 谓词：

```
⟦Box<T>⟧ = ∃l. l ↦ ⟦T⟧

⟦&'a mut T⟧ = ∃l. &frac{l. ⟦T⟧}{⟦'a⟧}

⟦&'a T⟧ = ∃l. &frac{l. □⟦T⟧}{⟦'a⟧}
```

### 6.2 生命周期逻辑

生命周期建模为时间区间：

```
⟦'a⟧ = [t₁, t₂)    (时间区间)

&frac{P}{[t₁,t₂)}    (P 在区间内有效)
```

### 6.3 Send 和 Sync

```
Send T  ≡  T 可以跨线程传递 (资源可重组)
Sync T  ≡  &T 可以跨线程共享 (共享资源安全)
```

---

## 7. 验证示例: 无锁栈

### 7.1 代码

```rust
struct Node<T> {
    data: T,
    next: AtomicPtr<Node<T>>,
}

struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> LockFreeStack<T> {
    fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: AtomicPtr::new(ptr::null_mut()),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            unsafe { (*new_node).next.store(head, Ordering::Relaxed); }

            if self.head.compare_exchange(
                head, new_node,
                Ordering::Release, Ordering::Relaxed
            ).is_ok() {
                break;
            }
        }
    }
}
```

### 7.2 Iris 规约

```
{stack(s) * P(data)}
  s.push(data)
{stack(s) * ret = ()}

where stack(s) = ∃l, nodes. s.head ↦ l * list(l, nodes)
```

---

## 8. 工具链

| 工具 | 用途 | 状态 |
|------|------|------|
| Iris Coq 开发 | 交互式证明 | 稳定 |
| RustBelt | Rust 验证 | 研究原型 |
| Creusot | Rust 到 Why3 | 活跃开发 |
| Prusti | Viper 基础 | 活跃开发 |

---

## 9. 总结

Iris 提供了验证复杂 Rust 代码的数学基础：

1. **分离逻辑** 处理所有权
2. **高阶性** 处理 trait 和泛型
3. **并发原语** 处理线程安全
4. **生命周期逻辑** 处理借用检查

---

**文档大小**: ~25 KB
**状态**: ✅ 完整形式化
**最后更新**: 2026-03-08
