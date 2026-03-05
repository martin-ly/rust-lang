# 分离逻辑：理论基础与Rust应用

> **权威来源**: Reynolds (2002), O'Hearn (2007), Iris Framework (Jung et al. 2018)
> **Rust应用**: RustBelt, Prusti, Verus

---

## 目录

- [分离逻辑：理论基础与Rust应用](#分离逻辑理论基础与rust应用)
  - [目录](#目录)
  - [1. 分离逻辑的诞生](#1-分离逻辑的诞生)
    - [1.1 问题背景：传统Hoare逻辑的局限](#11-问题背景传统hoare逻辑的局限)
    - [1.2 分离逻辑的解决方案](#12-分离逻辑的解决方案)
  - [2. 分离逻辑断言语言](#2-分离逻辑断言语言)
    - [2.1 基本断言](#21-基本断言)
    - [2.2 Points-To 断言详解](#22-points-to-断言详解)
    - [2.3 分离合取的性质](#23-分离合取的性质)
  - [3. Hoare三元组与推理规则](#3-hoare三元组与推理规则)
    - [3.1 基本命令的规范](#31-基本命令的规范)
    - [3.2 帧规则](#32-帧规则)
  - [4. 分离逻辑与Rust所有权](#4-分离逻辑与rust所有权)
    - [4.1 所有权作为分离逻辑](#41-所有权作为分离逻辑)
    - [4.2 借用与权限](#42-借用与权限)
  - [5. Iris：高阶并发分离逻辑](#5-iris高阶并发分离逻辑)
    - [5.1 Iris的核心创新](#51-iris的核心创新)
    - [5.2 资源代数详解](#52-资源代数详解)
    - [5.3 Iris中的所有权谓词](#53-iris中的所有权谓词)
  - [6. 验证工具中的分离逻辑](#6-验证工具中的分离逻辑)
    - [6.1 Prusti的Viper后端](#61-prusti的viper后端)
    - [6.2 Verus的资源代数](#62-verus的资源代数)
  - [7. 实例与验证案例](#7-实例与验证案例)
    - [7.1 链表验证](#71-链表验证)
    - [7.2 树结构验证](#72-树结构验证)
  - [8. 与其他理论的联系](#8-与其他理论的联系)
    - [8.1 与线性逻辑的关系](#81-与线性逻辑的关系)
    - [8.2 与Hoare逻辑的关系](#82-与hoare逻辑的关系)
  - [9. 高级主题](#9-高级主题)
    - [9.1 分数权限](#91-分数权限)
    - [9.2 幽灵状态](#92-幽灵状态)
  - [10. 参考文献](#10-参考文献)

---

## 1. 分离逻辑的诞生

### 1.1 问题背景：传统Hoare逻辑的局限

传统Hoare逻辑处理堆内存时面临**帧问题**（Frame Problem）：

**问题示例**:

```text
传统Hoare三元组:
{x = 5} x := x + 1 {x = 6}

但堆上的指针呢?
{*p = 5} *p := *p + 1 {*p = 6}

问题: 这个命令对其他内存位置有什么影响?
需要显式说明"所有其他位置不变" - 繁琐且易错
```

### 1.2 分离逻辑的解决方案

分离逻辑通过**分离合取**（Separating Conjunction）解决帧问题：

```text
关键创新: * (分离合取)

P * Q  表示: P和Q分别在不同的、不相交的内存区域成立

帧规则 (Frame Rule):
{P} C {Q}  ⊢  {P * R} C {Q * R}

条件: C不修改R中提到的任何内存

意义: 证明局部性质时，自动获得全局不变性
```

**对比示例**:

```text
传统Hoare逻辑:
{x ↦ 5 * y ↦ 10} x := 6 {x ↦ 6 * y ↦ 10}
需要显式保留 y ↦ 10

分离逻辑:
{x ↦ 5} x := 6 {x ↦ 6}
自动保持 y ↦ 10 (通过帧规则)
```

---

## 2. 分离逻辑断言语言

### 2.1 基本断言

| 断言 | 符号 | 含义 | Rust对应 | 示例 |
|------|------|------|---------|------|
| **空堆** | emp | 堆为空 | () | 无内存分配 |
| **指向** | ℓ ↦ v | 位置ℓ包含值v | Box::new(v) | 堆上值 |
| **分离合取** | P * Q | P和Q在不相交堆上 | (T, U) | 两个独立资源 |
| **分离蕴含** | P -* Q | 将P加到当前堆可得Q | 借用返回 | 资源转换 |
| **存在量词** | ∃x.P | 存在x使P成立 | 泛型 | 抽象位置 |
| **全称量词** | ∀x.P | 对所有x，P成立 | Trait约束 | 所有实现 |

### 2.2 Points-To 断言详解

```text
ℓ ↦ v 的精确语义:

- ℓ是内存位置（地址）
- v是存储在该位置的值
- 断言拥有对ℓ的独占访问权

在Rust中:
let b = Box::new(42);
// b 拥有堆位置，语义上对应 b ↦ 42
```

**示例 - Points-To 的演变**:

```rust
// 创建
let b = Box::new(42);
// 断言: b ↦ 42

// 读取
let x = *b;
// 断言: b ↦ 42 ∧ x = 42

// 写入
*b = 100;
// 断言: b ↦ 100

// 释放
drop(b);
// 断言: emp
```

### 2.3 分离合取的性质

```text
P * Q 的性质:

交换律:   P * Q ≡ Q * P
结合律:   (P * Q) * R ≡ P * (Q * R)
单位元:   P * emp ≡ P
分配律:   (P ∨ Q) * R ≡ (P * R) ∨ (Q * R)

注意: P * P ≢ P  （关键区别！）
      P * P 意味着两块不相交的内存都满足P

反例:
如果 x ↦ 5 * x ↦ 5 成立
那么 x 同时指向两个不同的值5 - 矛盾！
```

---

## 3. Hoare三元组与推理规则

### 3.1 基本命令的规范

```text
分配命令:
{emp} x := alloc() {x ↦ _}

释放命令:
{x ↦ _} free(x) {emp}

读取命令:
{x ↦ v} y := *x {x ↦ v ∧ y = v}

写入命令:
{x ↦ _} *x := v {x ↦ v}
```

**Rust对应**:

```rust
// 分配
let b = Box::new(42);
// {emp} b = Box::new(42) {b ↦ 42}

// 释放
drop(b);
// {b ↦ _} drop(b) {emp}
```

### 3.2 帧规则

```text
帧规则 (Frame Rule):

{P} C {Q}
─────────────────── (Frame)
{P * R} C {Q * R}

条件: Mod(C) ∩ Free(R) = ∅
      (C不修改R中提到的任何内存)

意义:
- 局部验证蕴含全局正确性
- 模块化推理
```

**示例 - 帧规则的应用**:

```rust
// 已知: {emp} let b = Box::new(5) {b ↦ 5}

// 应用帧规则，保持 y ↦ 10 不变
// {y ↦ 10} let b = Box::new(5) {b ↦ 5 * y ↦ 10}

fn frame_example() {
    let y = Box::new(10);
    let b = Box::new(5);  // b 的分配不影响 y
    // 两个 Box 独立存在
}
```

---

## 4. 分离逻辑与Rust所有权

### 4.1 所有权作为分离逻辑

```text
Rust所有权的分离逻辑解释:

所有权转移:
let y = x;  // x: Box<T>

分离逻辑推导:
{x ↦ v} let y = x {y ↦ v ∧ x = invalid}

借用:
let r = &x;

分离逻辑:
{x ↦ v} let r = &x {x ↦ v * r ↦ &x}
// 注意: x ↦ v 仍然存在，但被"冻结"
```

**完整示例 - 所有权链**:

```rust
// 分离逻辑推导链

fn ownership_chain() {
    // {emp}
    let b = Box::new(42);
    // {b ↦ 42}

    let c = b;
    // {c ↦ 42 * b = invalid}

    // 编译错误: 使用了已移动的值
    // println!("{}", b);

    println!("{}", c);
    // {c ↦ 42}

    drop(c);
    // {emp}
}
```

### 4.2 借用与权限

```text
共享借用 (&T):
&T 对应于只读权限

可表示为: readonly(ℓ, T)
性质: 可以复制，不转移所有权

分离逻辑表示:
&T ≡ ∃π. ℓ ↦^π T  其中 π < 1 (分数权限)

可变借用 (&mut T):
&mut T 对应于独占写权限

可表示为: &mut(ℓ, T)
性质: 不可复制，独占访问

分离逻辑表示:
&mut T ≡ ℓ ↦^1 T  (完整权限)
```

**示例 - 权限转换**:

```rust
fn permission_flow() {
    // 独占所有权
    let mut data = Box::new(5);
    // data ↦^1 5

    // 共享借用: 权限分割
    let r1 = &data;
    let r2 = &data;
    // data ↦^(1/2) 5 * r1 ↦ data * data ↦^(1/2) 5 * r2 ↦ data

    // 不能使用 data，因为权限被借用
    // *data = 10;  // 错误！

    // 可变借用: 需要完整权限
    let r_mut = &mut data;
    // data ↦^1 5 (临时转移给 r_mut)
    *r_mut = 10;

    // 借用结束，权限返回
    // data ↦^1 10
}
```

---

## 5. Iris：高阶并发分离逻辑

### 5.1 Iris的核心创新

Iris是RustBelt的基础逻辑框架：

```text
Iris的关键特性:

1. 高阶幽灵状态 (Higher-Order Ghost State)
   - 支持任意复杂的不变量
   - 用户可定义资源代数

2. 模态算子 (Modalities)
   ▷ P (Later): 下一步成立
   □ P (Persistence): 持久真
   ◇ P (Update): 原子更新

3. 不变量 (Invariants)
   P^N: 在命名空间N中的不变量
   可共享的资源断言

4. 资源代数 (Resource Algebras)
   定义资源的组合规则
```

### 5.2 资源代数详解

```text
资源代数 (Resource Algebra, RA):

结构: (M, ⋅, ε, ✓)

- M: 资源集合
- ⋅: 组合操作 (偏函数)
- ε: 单位元
- ✓: 有效性谓词

公理:
1. 结合性: (a ⋅ b) ⋅ c = a ⋅ (b ⋅ c)
2. 单位元: ε ⋅ a = a
3. 有效性: ✓(a ⋅ b) ⇒ ✓(a) ∧ ✓(b)

分数权限示例:
M = [0,1] (权限分数)
a ⋅ b = a + b  如果 a + b ≤ 1
ε = 0
✓(a) ⇔ a ≤ 1
```

**示例 - 资源代数的Rust实现**:

```rust
// Verus中的资源代数示例

// 定义一个简单的资源: 计数器
struct Counter {
    v: u64,
}

// 资源代数: 计数器可以"相加"
// counter1(v1) ⋅ counter2(v2) = counter(v1 + v2)

// 使用资源代数证明并发安全
proof fn increment(counter: &mut Counter)
    requires
        counter.v < 0xffff_ffff_ffff_ffff,
    ensures
        counter.v == old(counter).v + 1,
{
    counter.v = counter.v + 1;
}
```

### 5.3 Iris中的所有权谓词

```text
RustBelt在Iris中的类型解释:

[[own_n τ]].own(t, [ℓ]) ≡
  ∃v̄. ℓ ↦ v̄ * ▷[[τ]].own(t, v̄) * ▷Dealloc(ℓ, n, |τ|)

含义:
- ℓ ↦ v̄: 堆位置ℓ包含值v̄
- [[τ]].own(t, v̄): 递归解释内部类型
- Dealloc(ℓ, ...): 释放权限
- ▷ (Later): 递归的guard

[[&mut^α τ]].own(t, [ℓ]) ≡
  &^α(∃v̄. ℓ ↦ v̄ * ▷[[τ]].own(t, v̄))

含义:
- &^α: 生命周期α上的借用
- 在α期间，拥有对ℓ的独占访问
```

---

## 6. 验证工具中的分离逻辑

### 6.1 Prusti的Viper后端

```text
Viper (Verification Infrastructure for Permission-based Reasoning):

基于隐式动态帧 (Implicit Dynamic Frames, IDF):

断言示例:
acc(x.f)       // 拥有x.f的访问权
acc(x.f, 1/2)  // 拥有x.f的一半权限

x.f == 5       // x.f的值等于5

组合:
acc(x.f) * x.f == 5  // 拥有x.f且其值为5

与分离逻辑的关系:
acc(x.f) 对应于 x.f ↦ _
acc(x.f) * acc(y.f) 要求 x ≠ y
```

**Prusti示例**:

```rust
// Prusti 使用 Viper 后端
use prusti_contracts::*;

#[requires(acc(x))]
#[requires(x.f == 5)]
#[ensures(acc(x))]
#[ensures(x.f == 6)]
fn increment(x: &mut MyStruct) {
    x.f = x.f + 1;
}
```

### 6.2 Verus的资源代数

```rust
// Verus中的资源代数示例
use vstd::prelude::*;

// 定义并发安全的资源
verus! {
    struct Resource<T> {
        data: T,
    }

    impl<T> Resource<T> {
        // 获取独占访问
        fn acquire(&mut self) -> T
            requires
                old(self).data == self.data,
            ensures
                result == old(self).data,
        {
            // 实现
        }
    }
}
```

---

## 7. 实例与验证案例

### 7.1 链表验证

```rust
// 分离逻辑验证链表操作

struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
}

// 规范: 链表表示为分离合取的节点
// List(ℓ) ≡ ℓ = null * emp ∨ ℓ ↦ (v, next) * List(next)

impl<T> LinkedList<T> {
    // 前置: List(self.head)
    // 后置: result == len * List(self.head)
    fn len(&self) -> usize {
        let mut count = 0;
        let mut current = &self.head;

        while let Some(node) = current {
            count += 1;
            current = &node.next;
        }

        count
    }

    // 前置: List(self.head)
    // 后置: List(self.head) * result ↦ v
    fn push(&mut self, value: T) {
        let new_node = Box::new(Node {
            value,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }
}
```

### 7.2 树结构验证

```rust
// 二叉树的分离逻辑规范

struct TreeNode<T> {
    value: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

// 树谓词:
// Tree(ℓ) ≡ ℓ = null * emp
//         ∨ ℓ ↦ (v, left, right) * Tree(left) * Tree(right)

impl<T: Ord> TreeNode<T> {
    // BST插入
    // 前置: Tree(self)
    // 后置: Tree(self) * BST(self)
    fn insert(&mut self, value: T) {
        if value < self.value {
            if let Some(ref mut left) = self.left {
                left.insert(value);
            } else {
                self.left = Some(Box::new(TreeNode {
                    value,
                    left: None,
                    right: None,
                }));
            }
        } else {
            if let Some(ref mut right) = self.right {
                right.insert(value);
            } else {
                self.right = Some(Box::new(TreeNode {
                    value,
                    left: None,
                    right: None,
                }));
            }
        }
    }
}
```

---

## 8. 与其他理论的联系

### 8.1 与线性逻辑的关系

```text
分离逻辑 ←→ 线性逻辑

共同点:
- 都关注资源管理
- 都有"分离"的概念 (*)
- 都用于程序验证

区别:
- 线性逻辑: 证明论，关注证明结构
- 分离逻辑: 模型论，关注内存模型

联系:
分离逻辑的 * (separating conjunction) 直接来自线性逻辑的 ⊗
Iris 框架将两者结合用于 Rust 验证
```

**映射关系**:

| 线性逻辑 | 分离逻辑 | Rust概念 |
|---------|---------|---------|
| ⊗ | * (分离合取) | 所有权组合 |
| ⊸ | -* (magic wand) | 借用返回 |
| !A | 持久断言 | Copy类型 |

### 8.2 与Hoare逻辑的关系

```text
Hoare逻辑 ←→ 分离逻辑

Hoare三元组: {P} C {Q}

分离逻辑扩展:
- 添加了堆的显式推理
- 帧规则作为基本原则
- 局部推理蕴含全局正确性

关系:
分离逻辑 = Hoare逻辑 + 分离合取 + 堆断言
```

---

## 9. 高级主题

### 9.1 分数权限

```text
分数权限 (Fractional Permissions):

Boyland (2003) 提出:

权限分数: π ∈ (0,1]

ℓ ↦^π v: 拥有位置ℓ的π份额

性质:
- ℓ ↦^1 v: 独占所有权 (可读写)
- ℓ ↦^π v (π < 1): 共享读权限
- ℓ ↦^π₁ v * ℓ ↦^π₂ v ≡ ℓ ↦^(π₁+π₂) v (如果π₁+π₂ ≤ 1)

Rust应用:
&mut T 对应 ℓ ↦^1 v
&T 对应 ℓ ↦^π v (π < 1)
```

### 9.2 幽灵状态

```rust
// 幽灵状态在Rust验证中的应用

// 幽灵变量: 只在规范中存在，运行时无成本
#[verifier::spec]
fn ghost_example(x: u64) -> u64 {
    let ghost mut y: int = 0;  // 幽灵变量

    // 证明逻辑
    proof {
        y = y + 1;
        assert(y == 1);
    }

    x + 1
}
```

---

## 10. 参考文献

1. Reynolds, J.C. (2002). Separation Logic: A Logic for Shared Mutable Data Structures. *LICS*.
2. O'Hearn, P.W. (2007). Resources, Concurrency, and Local Reasoning. *Theoretical Computer Science*.
3. Jung, R., et al. (2018). Iris from the Ground Up: A Modular Foundation for Higher-Order Concurrent Separation Logic. *JFP*.
4. Boyland, J. (2003). Checking Interference with Fractional Permissions. *SAS*.
5. Smans, J., Jacobs, B., & Piessens, F. (2012). Implicit Dynamic Frames: Combining Dynamic Frames and Separation Logic. *ECOOP*.
