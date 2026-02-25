# Rust形式化概念百科

> **创建日期**: 2026-02-23
> **更新日期**: 2026-02-23
> **目标**: 全面汇总Rust形式化方法的核心概念定义
> **级别**: L1/L2 (给人看的形式化论证)

---

## 目录

- [Rust形式化概念百科](#rust形式化概念百科)
  - [目录](#目录)
  - [一、所有权与借用](#一所有权与借用)
    - [1.1 所有权 (Ownership)](#11-所有权-ownership)
      - [概念定义](#概念定义)
      - [所有权转移 (Move)](#所有权转移-move)
      - [复制 (Copy)](#复制-copy)
    - [1.2 借用 (Borrowing)](#12-借用-borrowing)
      - [不可变借用 (\&T)](#不可变借用-t)
      - [可变借用 (\&mut T)](#可变借用-mut-t)
      - [借用规则总结](#借用规则总结)
    - [1.3 生命周期 (Lifetime)](#13-生命周期-lifetime)
  - [二、类型系统](#二类型系统)
    - [2.1 类型安全](#21-类型安全)
    - [2.2 型变 (Variance)](#22-型变-variance)
    - [2.3 Trait系统](#23-trait系统)
  - [三、生命周期](#三生命周期)
    - [3.1 生命周期省略规则](#31-生命周期省略规则)
    - [3.2 生命周期边界](#32-生命周期边界)
  - [四、并发与异步](#四并发与异步)
    - [4.1 Send与Sync](#41-send与sync)
    - [4.2 异步与Future](#42-异步与future)
  - [五、分布式模式](#五分布式模式)
    - [5.1 Saga模式](#51-saga模式)
    - [5.2 CQRS模式](#52-cqrs模式)
    - [5.3 熔断器模式](#53-熔断器模式)
  - [六、工作流](#六工作流)
    - [6.1 状态机工作流](#61-状态机工作流)
    - [6.2 补偿事务](#62-补偿事务)
  - [附录：反例索引](#附录反例索引)
    - [A.1 所有权反例](#a1-所有权反例)
    - [A.2 借用反例](#a2-借用反例)
    - [A.3 Send/Sync反例](#a3-sendsync反例)

---

## 一、所有权与借用

### 1.1 所有权 (Ownership)

#### 概念定义

**定义 (所有权)**: 在Rust中，每个值在任意时刻有且只有一个**所有者**（变量）。当所有者离开作用域，值将被丢弃。

**形式化表示**:

```text
∀v: Value, ∃!x: Var, owns(x, v)
```

**理解要点**:

- **唯一性**: 一个值不能被多个变量同时拥有
- **排他性**: 所有者拥有对值的完全控制权
- **生命周期绑定**: 值的生命周期与所有者的作用域绑定

#### 所有权转移 (Move)

**定义 (Move)**: 将值的所有权从一个变量转移到另一个变量。转移后，原变量不再有效。

```rust
let x = String::from("hello");
let y = x;  // 所有权从x转移到y
// x 不再有效
```

**形式化规则**:

```text
Move(x, y, v):
  pre:  owns(x, v) ∧ valid(y)
  post: owns(y, v) ∧ ¬valid(x)
```

#### 复制 (Copy)

**定义 (Copy)**: 对于实现了`Copy` trait的类型，赋值操作会复制值而非转移所有权。

**Copy类型的条件**:

- 类型只包含标量值（整数、浮点、布尔、字符）
- 或者只包含其他Copy类型的元组/数组

```rust
let x = 5;
let y = x;  // 复制，x仍然有效
println!("{}", x);  // OK
```

---

### 1.2 借用 (Borrowing)

#### 不可变借用 (&T)

**定义 (不可变借用)**: 允许一个或多个引用读取数据，但不允许修改。

**形式化规则**:

```
&Borrow(x, r, v):
  pre:  owns(x, v)
  post: borrowed_imm(x, r, v) ∧ owns(x, v)
        ∧ ∀r': Ref, can_read(r', v) → r' = r ∨ r' is imm borrow of v
```

**约束**:

- 可以有多个不可变借用同时存在
- 不可变借用期间不能有可变借用
- 原所有者不能修改数据

#### 可变借用 (&mut T)

**定义 (可变借用)**: 允许一个引用读取和修改数据，具有排他性。

**形式化规则**:

```
&mut Borrow(x, r, v):
  pre:  owns(x, v) ∧ no_active_borrows(v)
  post: borrowed_mut(x, r, v) ∧ ¬owns(x, v) temporarily
        ∧ ∀r': Ref, ¬can_access(r', v) ∨ r' = r
```

**约束**:

- 同一时间只能有一个可变借用
- 可变借用期间不能有其他借用（可变或不可变）
- 原所有者暂时不能访问数据

#### 借用规则总结

**规则 1**: 任意时刻，要么有一个可变引用，要么有任意数量的不可变引用
**规则 2**: 引用必须始终有效（不能悬垂）

---

### 1.3 生命周期 (Lifetime)

**定义 (生命周期)**: 引用有效的程序区间。编译器通过生命周期确保引用不会比它指向的数据活得更长。

**形式化表示**:

```
'a: Lifetime  // 'a是一个生命周期参数
&'a T: 类型T的引用，生命周期为'a
```

**生命周期关系**:

```
'a: 'b  表示 'a 至少和 'b 一样长（'a包含'b）
```

**理解示例**:

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
// 返回的引用生命周期与x和y中较短的一致
```

---

## 二、类型系统

### 2.1 类型安全

**定义 (类型安全)**: 良类型的程序不会陷入未定义行为。具体表现为：

- **进展性 (Progress)**: 良类型的表达式要么是值，要么可以进一步求值
- **保持性 (Preservation)**: 求值保持类型

**形式化**:

```
Γ ⊢ e : τ  →  (value(e) ∨ ∃e', e → e')  [进展性]
Γ ⊢ e : τ ∧ e → e'  →  Γ ⊢ e' : τ  [保持性]
```

### 2.2 型变 (Variance)

**定义 (型变)**: 描述复合类型的子类型关系如何依赖于其组成部分的子类型关系。

| 型变类型 | 含义 | 示例 |
| :--- | :--- | :--- |
| **协变 (Covariant)** | T <: U ⇒ C<T> <: C<U> | `Box<T>`, `Vec<T>`, `Option<T>` |
| **逆变 (Contravariant)** | T <: U ⇒ C<U> <: C<T> | `fn(T) -> U` 对T |
| **不变 (Invariant)** | T = U ⇒ C<T> = C<U> | `&mut T`, `Cell<T>` |

**理解要点**:

- 协变：子类型关系保持方向
- 逆变：子类型关系反转
- 不变：必须完全相同

### 2.3 Trait系统

**定义 (Trait)**: 定义类型必须实现的方法集合，类似其他语言中的接口。

**形式化**:

```
trait Eq {
    fn eq(&self, other: &Self) -> bool;
}

impl Eq for MyType {
    fn eq(&self, other: &Self) -> bool { ... }
}
```

**Trait对象**:

```
dyn Trait: 动态分发，运行时确定具体类型
impl Trait: 静态分发，编译时确定
```

---

## 三、生命周期

### 3.1 生命周期省略规则

Rust编译器会自动推断生命周期，遵循以下规则：

**规则 1**: 每个引用参数都有自己的生命周期参数
**规则 2**: 如果只有一个输入生命周期，它会被赋给所有输出生命周期
**规则 3**: 如果有多个输入生命周期，但一个是`&self`或`&mut self`，则`self`的生命周期赋给所有输出

### 3.2 生命周期边界

**定义 (生命周期边界)**: `'static`表示整个程序运行期间都有效。

**理解**:

- 字符串字面量: `&'static str`
- 全局常量: 具有`'static`生命周期
- 拥有所有权的类型: 隐式`'static`

---

## 四、并发与异步

### 4.1 Send与Sync

**定义 (Send)**: 类型T可以安全地跨线程边界移动。

**条件**: 所有权可以转移给另一个线程。

**非Send示例**:

- `Rc<T>`: 引用计数不是线程安全的
- 裸指针

**定义 (Sync)**: 类型T可以安全地被多个线程共享（通过引用）。

**等价定义**: `T: Sync ⇔ &T: Send`

**非Sync示例**:

- `Cell<T>`: 内部可变性，非线程安全
- `RefCell<T>`: 运行时借用检查，非线程安全

**常用组合**:

| 类型 | Send | Sync | 说明 |
| :--- | :--- | :--- | :--- |
| `Arc<T>` | ✅ | ✅(若T:Sync) | 线程安全引用计数 |
| `Mutex<T>` | ✅ | ✅ | 互斥锁 |
| `RwLock<T>` | ✅ | ✅ | 读写锁 |
| `Rc<T>` | ❌ | ❌ | 非线程安全 |
| `Cell<T>` | ✅ | ❌ | 内部可变性 |
| `RefCell<T>` | ✅ | ❌ | 运行时借用 |

### 4.2 异步与Future

**定义 (Future)**: 表示异步计算的trait，可以被轮询以检查是否完成。

```rust
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

**状态机转换**:

```
Pending -> Ready(Output)  (完成)
  ↓
Wake -> poll() -> ...
```

**Pin与自引用**:

- `Pin<P>`: 保证指针指向的值不会被移动
- 用于自引用结构（异步状态机）

---

## 五、分布式模式

### 5.1 Saga模式

**定义 (Saga)**: 将长事务分解为一系列本地事务，每个本地事务有对应的补偿操作。

**两种实现**:

**编排式 (Orchestration)**: 集中协调器控制流程

```
Coordinator -> Service A -> Compensate A
           -> Service B -> Compensate B
           -> Service C -> Compensate C
```

**编制式 (Choreography)**: 事件驱动，各服务自主决策

```
Service A -(event)-> Service B -(event)-> Service C
```

**形式化**:

```
Saga = [LocalTx₁, LocalTx₂, ..., LocalTxₙ]
每个 LocalTxᵢ 有 Compensateᵢ
执行失败时：执行 Compensateᵢ₋₁, ..., Compensate₁
```

### 5.2 CQRS模式

**定义 (CQRS)**: 命令查询职责分离，读写使用不同的模型。

**形式化**:

```
Command → Write Model → Event Store
                         ↓
Query   ← Read Model ← Projector
```

**适用场景**:

- 读多写少
- 复杂查询
- 事件溯源

### 5.3 熔断器模式

**定义 (熔断器)**: 防止故障扩散，当错误率超过阈值时快速失败。

**状态机**:

```
Closed (正常) --失败率>阈值--> Open (熔断)
    ↑                              │
    └── 成功次数>阈值 ─── Half-Open <--
```

---

## 六、工作流

### 6.1 状态机工作流

**定义**: 工作流由状态和转移组成。

**形式化**:

```
Workflow = (S, s₀, T, F)
S: 状态集合
s₀: 初始状态
T: 转移函数 S × Event → S
F: 终结状态集合
```

### 6.2 补偿事务

**定义**: 在分布式系统中，通过执行补偿操作来撤销已完成的操作。

**向后补偿 (Backward Compensation)**:

```
T₁, T₂, T₃ 失败 → C₂, C₁
```

**向前补偿 (Forward Compensation)**:

```
执行补偿操作使系统达到一致状态（不撤销已完成操作）
```

---

## 附录：反例索引

### A.1 所有权反例

**反例 1: 使用已移动值**

```rust
let x = String::from("hello");
let y = x;
println!("{}", x);  // 错误: value borrowed here after move
```

**反例 2: 双重释放（C/C++问题，Rust防止）**

```rust
// Rust中不可能发生，因为所有权系统禁止
```

### A.2 借用反例

**反例 1: 可变借用与不可变借用冲突**

```rust
let mut x = 5;
let r1 = &x;
let r2 = &mut x;  // 错误: cannot borrow as mutable
println!("{}", r1);
```

**反例 2: 悬垂引用**

```rust
let r;
{
    let x = 5;
    r = &x;  // 错误: `x` does not live long enough
}
```

### A.3 Send/Sync反例

**反例: Rc跨线程**

```rust
use std::rc::Rc;
use std::thread;

let data = Rc::new(5);
thread::spawn(move || {
    println!("{}", data);  // 错误: `Rc<i32>` cannot be sent between threads
});
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-23
**用途**: 给人看的形式化概念定义
