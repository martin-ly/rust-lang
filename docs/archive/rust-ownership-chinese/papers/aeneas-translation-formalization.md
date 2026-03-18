# Aeneas：Rust到函数式翻译的完整形式化

> 本文档详细定义从Rust MIR到LLBC（Low-Level Borrow Calculus）的翻译函数
> 基于 Ho & Protzenko (2022) Aeneas: Rust Verification by Functional Translation

---

## 目录

- [Aeneas：Rust到函数式翻译的完整形式化](#aeneasrust到函数式翻译的完整形式化)
  - [目录](#目录)
  - [1. LLBC 完整语法定义](#1-llbc-完整语法定义)
    - [1.1 类型系统](#11-类型系统)
    - [1.2 表达式和语句](#12-表达式和语句)
    - [1.3 控制流图](#13-控制流图)
  - [2. 翻译函数 ⟦·⟧: Rust MIR → LLBC](#2-翻译函数--rust-mir--llbc)
    - [2.1 翻译签名](#21-翻译签名)
    - [2.2 类型翻译](#22-类型翻译)
    - [2.3 操作数翻译](#23-操作数翻译)
    - [2.4 路径（Place）翻译](#24-路径place翻译)
    - [2.5 Rvalue翻译](#25-rvalue翻译)
    - [2.6 语句翻译](#26-语句翻译)
  - [3. 控制流翻译](#3-控制流翻译)
    - [3.1 基本块翻译](#31-基本块翻译)
    - [3.2 终结符翻译](#32-终结符翻译)
    - [3.3 函数体翻译](#33-函数体翻译)
  - [4. 借用处理与状态单子](#4-借用处理与状态单子)
    - [4.1 状态单子类型](#41-状态单子类型)
    - [4.2 读写操作翻译](#42-读写操作翻译)
    - [4.3 借用翻译成高阶类型](#43-借用翻译成高阶类型)
  - [5. 循环翻译成递归](#5-循环翻译成递归)
    - [5.1 While循环翻译](#51-while循环翻译)
    - [5.2 翻译规则](#52-翻译规则)
  - [6. 类型保持定理](#6-类型保持定理)
    - [6.1 定理陈述](#61-定理陈述)
    - [6.2 证明概要](#62-证明概要)
  - [7. 完整翻译示例](#7-完整翻译示例)
    - [7.1 简单函数](#71-简单函数)
    - [7.2 带借用的函数](#72-带借用的函数)
  - [参考文献](#参考文献)

## 1. LLBC 完整语法定义

### 1.1 类型系统

```text
═══════════════════════════════════════════════════════════════════
                        LLBC 类型 (τ)
═══════════════════════════════════════════════════════════════════

τ ::=
  | Scalar(int_type)             (标量类型: i32, u64, bool, ...)
  | T                            (类型变量)
  | Box<τ>                       (堆分配)
  | &{mut} τ                     (借用)
  | Array<τ, n>                  (定长数组)
  | Tuple(τ₁, ..., τₙ)           (元组)
  | Adt(DefId, τ₁, ..., τₙ)      (代数数据类型: struct, enum)
  | Never                        (! 类型)
  | Region(ρ)                    (生命周期)

═══════════════════════════════════════════════════════════════════
                        LLBC 操作数 (op)
═══════════════════════════════════════════════════════════════════

op ::=
  | Const(v)                     (常量值)
  | Copy(p)                      (复制路径p的值)
  | Move(p)                      (移动路径p的值)

═══════════════════════════════════════════════════════════════════
                        LLBC 路径 (p)
═══════════════════════════════════════════════════════════════════

p ::=
  | Var(x)                       (变量)
  | Proj(p, Field(n))            (字段投影: p.n)
  | Proj(p, Deref)               (解引用: *p)
  | Proj(p, Index(i))            (索引: p[i])
```

### 1.2 表达式和语句

```text
═══════════════════════════════════════════════════════════════════
                        LLBC 右值 (rvalue)
═══════════════════════════════════════════════════════════════════

rvalue ::=
  | Use(op)                      (使用操作数)
  | Ref(BorrowKind, p)           (创建借用: &p 或 &mut p)
  | BinaryOp(BinOp, op₁, op₂)    (二元运算)
  | UnaryOp(UnOp, op)            (一元运算)
  | Aggregate(AggKind, op*)      (聚合构造: struct, enum, tuple, array)
  | Discriminant(p)              (获取enum判别式)
  | Len(p)                       (获取数组/切片长度)

BorrowKind ::= Shared | Mutable
AggKind ::= Tuple | Array | Struct(DefId) | Enum(DefId, Variant)

═══════════════════════════════════════════════════════════════════
                        LLBC 语句 (statement)
═══════════════════════════════════════════════════════════════════

stmt ::=
  | Assign(p, rvalue)            (赋值: p = rvalue)
  | FakeRead(p)                  (假读，用于NLL)
  | SetDiscriminant(p, variant)  (设置enum判别式)
  | StorageLive(local)           (标记存储存活)
  | StorageDead(local)           (标记存储死亡)
  | Deinit(p)                    (反初始化)
  | Nop                          (无操作)

═══════════════════════════════════════════════════════════════════
                        LLBC 终结符 (terminator)
═══════════════════════════════════════════════════════════════════

terminator ::=
  | Goto(target)                 (无条件跳转)
  | SwitchInt(op, targets)       (整数切换)
  | SwitchDiscriminant(p, targets) (判别式切换)
  | Call(func, args, destination, target) (函数调用)
  | Return                       (返回)
  | Unwind                       (展开/异常)
  | Abort                        (中止)
  | Drop(p, target)              (析构)
```

### 1.3 控制流图

```text
block ::= Block {
    statements: Vec<stmt>,
    terminator: terminator
}

body ::= Body {
    local_decls: Vec<LocalDecl>,
    basic_blocks: Vec<block>
}
```

---

## 2. 翻译函数 ⟦·⟧: Rust MIR → LLBC

### 2.1 翻译签名

$$
\llbracket \cdot \rrbracket : \text{MIR} \to \text{LLBC}
$$

翻译上下文：

- $\Sigma$：类型定义环境
- $\Gamma$：局部变量类型映射
- $B$：基本块映射

### 2.2 类型翻译

**基本类型**：

$$
\llbracket \text{i32} \rrbracket_{\text{type}} = \text{Scalar}(\text{Int}(\text{I32}))
$$

$$
\llbracket \text{bool} \rrbracket_{\text{type}} = \text{Scalar}(\text{Bool})
$$

**借用类型**：

$$
\llbracket \&'a \, T \rrbracket_{\text{type}} = \& \, \llbracket T \rrbracket_{\text{type}}
$$

$$
\llbracket \&'a \, \text{mut} \, T \rrbracket_{\text{type}} = \&\text{mut} \, \llbracket T \rrbracket_{\text{type}}
$$

**Box类型**：

$$
\llbracket \text{Box}\langle T \rangle \rrbracket_{\text{type}} = \text{Box}\langle \llbracket T \rrbracket_{\text{type}} \rangle
$$

### 2.3 操作数翻译

$$
\llbracket \text{Operand::Copy}(p) \rrbracket_{\text{op}} = \text{Copy}(\llbracket p \rrbracket_{\text{place}})
$$

$$
\llbracket \text{Operand::Move}(p) \rrbracket_{\text{op}} = \text{Move}(\llbracket p \rrbracket_{\text{place}})
$$

$$
\llbracket \text{Operand::Constant}(c) \rrbracket_{\text{op}} = \text{Const}(\llbracket c \rrbracket_{\text{const}})
$$

### 2.4 路径（Place）翻译

**变量**：

$$
\llbracket \text{Place::Local}(x) \rrbracket_{\text{place}} = \text{Var}(x)
$$

**投影**：

$$
\llbracket p.\text{field}(n) \rrbracket_{\text{place}} = \text{Proj}(\llbracket p \rrbracket_{\text{place}}, \text{Field}(n))
$$

$$
\llbracket *p \rrbracket_{\text{place}} = \text{Proj}(\llbracket p \rrbracket_{\text{place}}, \text{Deref})
$$

$$
\llbracket p[i] \rrbracket_{\text{place}} = \text{Proj}(\llbracket p \rrbracket_{\text{place}}, \text{Index}(\llbracket i \rrbracket_{\text{op}}))
$$

### 2.5 Rvalue翻译

**借用创建**：

$$
\llbracket \text{Rvalue::Ref}(\text{BorrowKind}, p) \rrbracket_{\text{rv}} = \text{Ref}(\llbracket \text{BorrowKind} \rrbracket_{\text{bk}}, \llbracket p \rrbracket_{\text{place}})
$$

其中：

- $\llbracket \text{BorrowKind::Shared} \rrbracket_{\text{bk}} = \text{Shared}$
- $\llbracket \text{BorrowKind::Mutable} \rrbracket_{\text{bk}} = \text{Mutable}$

**二元运算**：

$$
\llbracket \text{Rvalue::BinaryOp}(\text{op}, \text{op}_1, \text{op}_2) \rrbracket_{\text{rv}} = \text{BinaryOp}(\llbracket \text{op} \rrbracket_{\text{bin}},
\llbracket \text{op}_1 \rrbracket_{\text{op}}, \llbracket \text{op}_2 \rrbracket_{\text{op}})
$$

**函数调用**：

$$
\llbracket \text{Call}(f, \text{args}, p, \text{target}) \rrbracket_{\text{term}} = \text{Call}(\llbracket f \rrbracket_{\text{fn}}, \llbracket \text{args}
\rrbracket_{\text{args}}, \llbracket p \rrbracket_{\text{place}}, \llbracket \text{target} \rrbracket_{\text{bb}})
$$

### 2.6 语句翻译

**赋值**：

$$
\llbracket p = \text{rv} \rrbracket_{\text{stmt}} = \text{Assign}(\llbracket p \rrbracket_{\text{place}}, \llbracket \text{rv} \rrbracket_{\text{rv}})
$$

**存储管理**：

$$
\llbracket \text{StorageLive}(x) \rrbracket_{\text{stmt}} = \text{StorageLive}(x)
$$

$$
\llbracket \text{StorageDead}(x) \rrbracket_{\text{stmt}} = \text{StorageDead}(x)
$$

---

## 3. 控制流翻译

### 3.1 基本块翻译

$$
\llbracket \text{BasicBlock} \{ \text{stmts}, \text{term} \} \rrbracket_{\text{bb}} = \text{Block} \{ \llbracket \text{stmts} \rrbracket_{\text{stmts}},
\llbracket \text{term} \rrbracket_{\text{term}} \}
$$

### 3.2 终结符翻译

**无条件跳转**：

$$
\llbracket \text{Terminator::Goto}(\text{target}) \rrbracket_{\text{term}} = \text{Goto}(\llbracket \text{target} \rrbracket_{\text{bb}})
$$

**条件分支**：

$$
\llbracket \text{Terminator::SwitchInt} \{ \text{discr}, \text{targets} \} \rrbracket_{\text{term}} =
\text{SwitchInt}(\llbracket \text{discr} \rrbracket_{\text{op}}, \llbracket \text{targets} \rrbracket_{\text{targets}})
$$

**返回**：

$$
\llbracket \text{Terminator::Return} \rrbracket_{\text{term}} = \text{Return}
$$

### 3.3 函数体翻译

$$
\llbracket \text{Body} \{ \text{locals}, \text{basic\_blocks} \} \rrbracket_{\text{body}} =
\text{Body} \{ \llbracket \text{locals} \rrbracket_{\text{locals}}, \llbracket \text{basic\_blocks} \rrbracket_{\text{bbs}} \}
$$

---

## 4. 借用处理与状态单子

### 4.1 状态单子类型

Aeneas将LLBC进一步翻译为函数式语言的纯函数，使用状态单子：

$$
\text{StateM}\langle S, A \rangle \triangleq S \to (A \times S)
$$

其中：

- $S$：状态类型（内存映射）
- $A$：结果类型

### 4.2 读写操作翻译

**读操作**：

$$
\llbracket \text{read}(p) \rrbracket_{\text{monad}} = \lambda s. \text{let } v = \text{lookup}(s, p) \text{ in } (v, s)
$$

**写操作**：

$$
\llbracket \text{write}(p, v) \rrbracket_{\text{monad}} = \lambda s. ((), \text{update}(s, p, v))
$$

### 4.3 借用翻译成高阶类型

**共享借用**：

$$
\llbracket \&T \rrbracket_{\text{trans}} = \text{State} \to T \times \text{State}
$$

**可变借用**：

$$
\llbracket \&\text{mut} \, T \rrbracket_{\text{trans}} = T \to \text{State} \to () \times \text{State}
$$

**解释**：

- 共享借用：从状态读取值的函数
- 可变借用：接受新值并更新状态的函数

---

## 5. 循环翻译成递归

### 5.1 While循环翻译

**源（Rust MIR）**：

```rust
bb1:  // 循环头
  switchInt(cond) -> [0: bb3, otherwise: bb2]

bb2:  // 循环体
  // 循环体语句
  goto bb1

bb3:  // 循环后
  // 继续
```

**目标（LLBC/函数式）**：

```rust
// 翻译成递归函数
fn loop_body(s: State) -> ((), State) {
  if eval(cond, s) {
    let (_, s1) = exec_body(s);
    loop_body(s1)  // 递归调用
  } else {
    ((), s)
  }
}
```

### 5.2 翻译规则

$$
\llbracket \text{while } c \text{ do } b \rrbracket_{\text{loop}} = \mu f. \lambda s. \text{if } \llbracket c \rrbracket(s) \text{ then } f(\llbracket b \rrbracket(s)) \text{ else } s
$$

其中 $\mu$ 表示不动点（递归定义）。

---

## 6. 类型保持定理

### 6.1 定理陈述

**定理（Aeneas类型保持）**：

若 Rust MIR 程序 $P$ 在 Rust 类型系统中类型良好，则翻译后的 LLBC 程序 $\llbracket P \rrbracket$ 在 LLBC 类型系统中类型良好：

$$
\Gamma \vdash_{\text{Rust}} P : T \Rightarrow \llbracket \Gamma \rrbracket \vdash_{\text{LLBC}} \llbracket P \rrbracket : \llbracket T \rrbracket
$$

### 6.2 证明概要

**结构归纳**：

1. **基本情况**：变量、常量
   - Rust类型直接映射到LLBC类型

2. **归纳步骤**：
   - 复合表达式：假设子表达式保持类型，则整体保持
   - 控制流：每个分支类型一致
   - 函数调用：参数类型匹配

**关键引理**：

- 操作数翻译保持类型
- 路径翻译保持类型
- Rvalue翻译保持类型

---

## 7. 完整翻译示例

### 7.1 简单函数

**Rust代码**：

```rust
fn add(x: i32, y: i32) -> i32 {
    let z = x + y;
    z
}
```

**MIR表示**：

```
bb0:
    _0 = _1 + _2;  // 返回值 = x + y
    return;
```

**LLBC翻译**：

```rust
fn add(x: i32, y: i32) -> i32 {
    let z = x + y;
    z
}
```

**函数式翻译（Lean）**：

```lean
def add (x : i32) (y : i32) : i32 :=
  let z := x + y
  z
```

### 7.2 带借用的函数

**Rust代码**：

```rust
fn sum(vec: &Vec<i32>) -> i32 {
    vec.iter().sum()
}
```

**LLBC翻译**：

```rust
fn sum(vec: &Vec<i32>) -> State -> i32 × State {
    // 借用作为状态读取函数
    let v = read(vec);
    v.iter().sum()
}
```

---

## 参考文献

1. Ho, J., & Protzenko, J. (2022). Aeneas: Rust Verification by Functional Translation. ICFP.
2. Rust Compiler Team. (2024). Mid-level Intermediate Representation (MIR).
3. Leroy, X. (2009). Formal verification of a realistic compiler. CACM.

---

*本文档为《Rust所有权与可判定性》项目的Aeneas翻译形式化补充*
