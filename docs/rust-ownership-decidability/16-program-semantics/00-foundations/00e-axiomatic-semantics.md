
### 6.4 链表反转示例

**程序**:

```rust
// 反转链表
fn reverse(head: *mut Node) -> *mut Node {
    let mut prev = std::ptr::null_mut();
    let mut curr = head;
    while !curr.is_null() {
        let next = (*curr).next;
        (*curr).next = prev;
        prev = curr;
        curr = next;
    }
    prev
}
```

**规约**:

$$
\{ls(x, \alpha)\}\ \text{reverse}(x)\ \{ls(\text{ret}, \text{rev}(\alpha))\}
$$

其中:

- $ls(p, \alpha)$: 指针 $p$ 指向表示序列 $\alpha$ 的链表
- $\text{rev}(\alpha)$: 序列 $\alpha$ 的反转

**循环不变量**:

$$
I = \exists \alpha_1, \alpha_2. ls(\text{curr}, \alpha_1) * ls(\text{prev}, \alpha_2) \land \alpha = \text{rev}(\alpha_2) \cdot \alpha_1
$$

---

## 7. 并发程序验证

### 7.1 Owicki-Gries 方法

**并行组合规则**:

$$
\frac{\{P_1\}\ c_1\ \{Q_1\} \quad \{P_2\}\ c_2\ \{Q_2\} \quad \text{不干涉}}{\{P_1 \land P_2\}\ c_1 \parallel c_2\ \{Q_1 \land Q_2\}}
$$

**不干涉**: 一个命令的执行不破坏另一个命令的前置/后置条件。

### 7.2 资源不变量

**思想**: 共享资源由不变量描述，临界区执行时暂时破坏，退出时恢复。

$$
\frac{\{P * R\}\ c\ \{Q * R\}}{\{P\}\ \text{with } R \text{ do } c\ \{Q\}}
$$

### 7.3 Rely-Guarantee 推理

**Rely 条件** $R$: 环境可能执行的状态转换。

**Guarantee 条件** $G$: 线程保证不违反的状态转换。

**并行规则**:

$$
\frac{R \cup G_2 \subseteq R_1 \quad R \cup G_1 \subseteq R_2}{...}
$$

---

## 8. 在 Rust 中的应用

### 8.1 Rust 的前置/后置条件

**类型作为轻量级规约**:

```rust
// { true }
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
// { ret >= 0 }

// { true }
fn divide(x: i32, y: i32) -> Option<i32> {
    if y == 0 { None } else { Some(x / y) }
}
// { y != 0 => ret == Some(x / y) }
```

### 8.2 所有权作为分离逻辑

**所有权 = 独占访问权限**:

$$
x : T \approx x \mapsto \_
$$

**借用 = 临时权限转移**:

$$
\&x : \&T \approx \text{read\_perm}(x)
$$

$$
\&mut x : \&mut T \approx x \mapsto \_
$$

### 8.3 Prusti 验证工具

**Prusti**: Rust 程序的形式验证器。

```rust
#[requires(x > 0)]
#[ensures(ret > 0)]
fn double(x: i32) -> i32 {
    x * 2
}
```

**规格语法**:

- `requires`: 前置条件
- `ensures`: 后置条件
- `pure`: 纯函数（无副作用）
- `forall`, `exists`: 量词

### 8.4 不安全代码契约

**不安全块的前置/后置**:

```rust
/// 前置条件: ptr 非空且已对齐
/// 后置条件: 返回 ptr 指向的值
unsafe fn read_ptr<T>(ptr: *const T) -> T {
    *ptr
}
```

---

## 9. 霍尔逻辑的扩展

### 9.1 完全正确性 (Total Correctness)

**需要终止性证明**。

**循环变体** (Loop Variant): 递减的良基度量。

$$
\frac{\{I \land b \land V = v\}\ c\ \{I \land V < v\} \quad V \geq 0}{[I]\ \text{while } b \text{ do } c\ [I \land \neg b\]}
$$

### 9.2 过程/函数

**过程规约**:

$$
\{P\}\ \text{call } f\ \{Q\}
$$

其中 $f$ 有规约 $\{P_f\}\ f\ \{Q_f\}$。

**递归过程**: 使用归纳法。

### 9.3 异常/错误

**三元组扩展**: $\{P\}\ c\ \{Q\}_E$

其中 $E$ 是异常处理器。

**Rust 对应**: `Result` 和 `Option` 类型。

```rust
// { true }
fn may_fail() -> Result<i32, Error> { ... }
// { ret.is_ok() => ... }
```

---

## 10. 工具与实践

### 10.1 验证工具链

| 工具 | 语言 | 特性 |
|------|------|------|
| **Dafny** | 专用 | 自动验证 |
| **Why3** | ML | 多后端证明 |
| **Viper** | 专用 | 分离逻辑 |
| **Prusti** | Rust | 所有权感知 |
| **Creusot** | Rust | 基于Why3 |

### 10.2 验证流程

```
1. 编写程序
   ↓
2. 编写规约 (requires/ensures)
   ↓
3. 工具生成验证条件 (VC)
   ↓
4. SMT 求解器或证明助手验证
   ↓
5. 通过/失败反馈
```

---

## 11. 总结

| 概念 | 含义 | Rust应用 |
|------|------|----------|
| **Hoare 三元组** | 程序规约 | 类型/文档 |
| **循环不变量** | 循环正确性 | 迭代器协议 |
| **WP/SP** | 自动推导 | 静态分析 |
| **分离逻辑** | 堆内存推理 | 所有权系统 |
| **并发验证** | 无数据竞争 | Send/Sync |

公理语义提供了程序正确性的数学基础，是形式验证的理论支柱。

---

## 参考文献

1. Hoare, C. A. R. (1969). "An Axiomatic Basis for Computer Programming".
2. Floyd, R. W. (1967). "Assigning Meanings to Programs".
3. Reynolds, J. C. (2002). "Separation Logic: A Logic for Shared Mutable Data Structures".
4. O'Hearn, P. W. (2019). "Separation Logic".
5. Nipkow, T., & Klein, G. (2014). *Concrete Semantics with Isabelle/HOL*.

---

**难度级别**: 🔴 高级 (理论基础)
**前置知识**: 一阶逻辑、操作语义
**后续学习**: 分离逻辑、程序验证
