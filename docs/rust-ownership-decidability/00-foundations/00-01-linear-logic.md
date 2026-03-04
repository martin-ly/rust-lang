# 线性逻辑基础

> **权威来源**: Jean-Yves Girard (1987). *Linear Logic*. Theoretical Computer Science 50:1-102
> **关联文献**: Girard, Lafont, Taylor (1989). *Proofs and Types*. Cambridge Tracts in Theoretical Computer Science

---

## 目录

- [线性逻辑基础](#线性逻辑基础)
  - [目录](#目录)
  - [1. 逻辑重心的范式转移](#1-逻辑重心的范式转移)
    - [1.1 从经典逻辑到线性逻辑](#11-从经典逻辑到线性逻辑)
    - [1.2 结构规则的拒绝](#12-结构规则的拒绝)
  - [2. 线性逻辑的连接词体系](#2-线性逻辑的连接词体系)
    - [2.1 乘法连接词 (Multiplicatives)](#21-乘法连接词-multiplicatives)
    - [2.2 加法连接词 (Additives)](#22-加法连接词-additives)
    - [2.3 指数连接词 (Exponentials)](#23-指数连接词-exponentials)
  - [3. Curry-Howard 对应与编程语言](#3-curry-howard-对应与编程语言)
    - [3.1 证明即程序](#31-证明即程序)
    - [3.2 与Rust类型的对应](#32-与rust类型的对应)
  - [4. 证明网](#4-证明网)
    - [4.1 证明网作为计算模型](#41-证明网作为计算模型)
    - [4.2 正确性标准](#42-正确性标准)
  - [5. 与Rust所有权的深层联系](#5-与rust所有权的深层联系)
    - [5.1 所有权即线性类型](#51-所有权即线性类型)
    - [5.2 仿射类型的引入](#52-仿射类型的引入)
  - [6. 形式化语义](#6-形式化语义)
    - [6.1 线性λ演算](#61-线性λ演算)
    - [6.2 操作语义](#62-操作语义)
  - [7. 实例与反例](#7-实例与反例)
    - [7.1 线性类型的正确用法](#71-线性类型的正确用法)
    - [7.2 反例：违反线性性](#72-反例违反线性性)
  - [8. 与其他理论的联系](#8-与其他理论的联系)
    - [8.1 与分离逻辑的关系](#81-与分离逻辑的关系)
    - [8.2 与范畴论的关系](#82-与范畴论的关系)
  - [9. 研究前沿与扩展](#9-研究前沿与扩展)
    - [9.1 微分线性逻辑](#91-微分线性逻辑)
    - [9.2 带递归的线性逻辑](#92-带递归的线性逻辑)
    - [9.3 模态线性逻辑](#93-模态线性逻辑)
  - [10. 参考文献](#10-参考文献)

---

## 1. 逻辑重心的范式转移

### 1.1 从经典逻辑到线性逻辑

经典逻辑（Classical Logic）和直觉主义逻辑（Intuitionistic Logic）基于**真理传递**（truth-transmission）范式：

**经典逻辑规则示例**:

```
经典逻辑: A → A 是永真式
问题: 这个推导忽略了资源的实际消耗

A ∧ A → A    (合取消除 - 可以忽略一个A)
A → A ∨ A    (析取引入 - 可以复制一个A)
```

**线性逻辑的核心洞见**：**证明即过程**（Proofs as Processes），资源是**有代价的**。

```
线性逻辑视角:
A ⊸ A        (线性蕴含 - 精确消耗一个A产生一个A)
A ⊗ A ⊸ A    (不可行 - 不能免费丢弃资源)
A ⊸ A ⊕ A    (不可行 - 不能免费复制资源)
```

### 1.2 结构规则的拒绝

| 规则 | 经典/直觉主义 | 线性逻辑 | 仿射逻辑 |
|------|--------------|----------|----------|
| **弱化 (Weakening)** | 允许 | ❌ 禁止 | ✅ 允许 |
| **收缩 (Contraction)** | 允许 | ❌ 禁止 | ❌ 禁止 |
| **交换 (Exchange)** | 允许 | ✅ 允许 | ✅ 允许 |

---

## 2. 线性逻辑的连接词体系

### 2.1 乘法连接词 (Multiplicatives)

| 连接词 | 符号 | 读法 | 规则 | 计算解释 | Rust对应 |
|--------|------|------|------|---------|---------|
| **tensor** | ⊗ | "tensor" | 同时持有两者 | 有序对 (A, B) | (A, B) |
| **par** | ⅋ | "par" | 资源选择 | 并行计算 | - |
| **linear implication** | ⊸ | "lollipop" | 消耗A产生B | 函数 A → B | 非Copy类型的转移 |
| **unit** | 1 | "one" | 空资源 | unit type | () |
| **bottom** | ⊥ | "bottom" | 空消耗 | never type | ! |

**Tensor (⊗) 引入与消除**:

```
Γ ⊢ A    Δ ⊢ B        Γ, A, B ⊢ C
─────────────── ⊗R    ─────────── ⊗L
 Γ, Δ ⊢ A ⊗ B         Γ, A ⊗ B ⊢ C
```

**示例 - Tensor 在Rust中的体现**:

```rust
// A ⊗ B 对应元组 (A, B)
// 同时持有一个String和一个Vec
let pair: (String, Vec<i32>) = (String::from("hello"), vec![1, 2, 3]);

// 解构时同时消费两者
let (s, v) = pair;
// pair 不再可用
```

**反例 - 错误的使用**:

```rust
// 尝试"免费"丢弃资源 - 在严格线性类型中不允许
fn drop_freely<T>(x: T) {
    // 在严格线性类型中，这是非法的
    // 必须显式消费或返回 x
}

// Rust是仿射的，所以这是允许的
// 但 Drop trait 确保资源被清理
```

### 2.2 加法连接词 (Additives)

| 连接词 | 符号 | 读法 | 规则 | 计算解释 | Rust对应 |
|--------|------|------|------|---------|---------|
| **with** | & | "with" | 外部选择 | 产品类型 | struct with多个字段 |
| **plus** | ⊕ | "plus" | 内部选择 | 和类型 | enum |
| **top** | ⊤ | "top" | 万能产品 | unit | () |
| **zero** | 0 | "zero" | 空和 | void | ! (never type) |

**示例 - Plus (⊕) 对应 Rust enum**:

```rust
// A ⊕ B 对应 enum Either<A, B>
enum Either<A, B> {
    Left(A),   // ⊕R1
    Right(B),  // ⊕R2
}

// 使用
let value: Either<i32, String> = Either::Left(42);
```

### 2.3 指数连接词 (Exponentials)

> 指数连接词允许受控的"经典"行为

| 连接词 | 符号 | 读法 | 含义 | Rust对应 |
|--------|------|------|------|---------|
| **of course** | !A | "bang" | 无限复制能力 | Copy trait |
| **why not** | ?A | "why not" | 无限消耗能力 | 借用 |

**示例 - !A 对应 Copy**:

```rust
// !i32 - 可以任意复制
let x: i32 = 5;
let y = x;  // 复制
let z = x;  // 再次复制 - 合法！

// 非 !T 的类型
let s = String::from("hello");
let t = s;  // 移动，不是复制
// let u = s;  // 错误！s 已被移动
```

**示例 - ?A 对应借用**:

```rust
// ?T - 可以临时访问而不消耗
let data = String::from("data");
let ref1 = &data;  // 借用
let ref2 = &data;  // 再次借用 - 合法！

// 原始值仍然有效
println!("{}", data);
```

---

## 3. Curry-Howard 对应与编程语言

### 3.1 证明即程序

```
线性逻辑的Curry-Howard对应:

证明                    程序
─────────────────────────────────────────────────────
Γ ⊢ A                   在上下文Γ下，项t具有类型A
线性蕴含 A ⊸ B          函数类型 A → B (消耗A)
张量积 A ⊗ B            对类型 (A, B) - 必须同时使用
加法积 A & B            产品类型 - 可选择使用
加法并 A ⊕ B            和类型 (Either A B)
指数 !A                 可复制类型 (Copy trait)
```

### 3.2 与Rust类型的对应

```rust
// Rust中的线性类型概念映射

// 线性函数: 消耗参数所有权
fn linear_consume(v: String) -> usize {
    v.len()  // v被移动，之后不可用
}

// !A 对应 Copy trait
let x: i32 = 5;
let y = x;  // 复制，x仍然可用 - !i32

// A ⊸ B 对应非Copy类型的转移
let s = String::from("hello");
let t = s;  // 移动，s不再可用 - String ⊸ String

// &A 对应 ?A 或借用
let r = &s;  // 借用，s仍保留所有权
```

**反例 - 违反线性性**:

```rust
// 严格线性类型会拒绝以下代码
fn bad_linear_usage() {
    let s = String::from("hello");
    let t = s;  // s 被移动
    // 在严格线性类型中，这是非法的：
    // drop(t);  // 必须显式处理 t
    // 不能忽略 t
}

// Rust是仿射的，所以允许忽略变量
// Drop trait 自动清理
```

---

## 4. 证明网

### 4.1 证明网作为计算模型

> 证明网消除了语法中的虚假差异，只保留本质结构

```
经典证明 vs 证明网:

传统证明树:                证明网:
    ⊗R                        ⊗
   /  \                      / \
  A    B        ====>      A   B
  │    │                   │   │
  └────┘                   └───┘
  A ⊗ B

优势:
1. 消除交换规则的排列等价问题
2. 直接表示计算过程
3. 切割消除对应归约
```

**示例 - 证明网与程序执行**:

```rust
// 证明网中的切割消除对应程序归约

// 原始程序 (带切割)
let pair = (String::from("a"), String::from("b"));
let (x, y) = pair;  // 解构

// 归约后 (消除切割)
let x = String::from("a");
let y = String::from("b");
```

### 4.2 正确性标准

```
Danos-Regnier 标准:

对于证明网中的每个节点，检查:
1. 每个公式作为前提/结论的次数正确
2. 无"悬挂"边
3. 切割消除过程终止

长旅行条件 (Long Trip Condition):
- 检查所有可能的"旅行"都返回起点
- 确保网络无"短路"
```

---

## 5. 与Rust所有权的深层联系

### 5.1 所有权即线性类型

```
Rust所有权系统 ←→ 线性/仿射类型系统

所有权规则                    类型理论解释
────────────────────────────────────────────────────────
每个值有且只有一个所有者       线性性: 变量必须恰好使用一次
所有权可转移                   线性函数: A ⊸ B
借用 (&T, &mut T)             线性逻辑中的模态/能力
生命周期                      区域的时序逻辑
Drop trait                    线性逻辑的duality
```

### 5.2 仿射类型的引入

Rust实际是**仿射类型系统**（Affine Type System）而非严格线性：

```
线性 vs 仿射:

线性: 变量必须恰好使用一次 (use exactly once)
仿射: 变量最多使用一次     (use at most once)

Rust允许:
let x = String::from("hello");
// x 可能不被使用 - 这是仿射的
// 但Drop trait确保资源最终释放
```

**Kopylov (2001) 的可判定性结果**:
> 完整的命题仿射逻辑（包含所有乘法、加法、指数和常量）是**可判定的**。这与线性逻辑的不可判定性形成鲜明对比。

---

## 6. 形式化语义

### 6.1 线性λ演算

```
语法:
t ::= x | λx.t | t t' | (t, t') | let (x,y) = t in t' | inli t | inr t

类型:
τ ::= τ ⊸ τ | τ ⊗ τ | τ & τ | τ ⊕ τ | !τ

类型规则:

x:τ ∈ Γ
──────────── (Var)
Γ ⊢ x : τ

Γ, x:τ₁ ⊢ t : τ₂
──────────────────── (⊸I)
Γ ⊢ λx.t : τ₁ ⊸ τ₂

Γ ⊢ t : τ₁ ⊸ τ₂    Δ ⊢ s : τ₁
────────────────────────────── (⊸E)
Γ, Δ ⊢ t s : τ₂
```

**示例 - 类型推导**:

```
推导 λx.x (恒等函数):

x:A ⊢ x:A          (Var)
──────────────────── (⊸I)
⊢ λx.x : A ⊸ A

对应 Rust:
fn id<T>(x: T) -> T { x }  // T ⊸ T
```

### 6.2 操作语义

```
值: v ::= λx.t | (v, v') | inl v | inr v | !v

归约规则:

(λx.t) v  ⟶  t[v/x]                         (β-归约)
let (x,y) = (v₁,v₂) in t  ⟶  t[v₁/x, v₂/y]   (张量消除)
```

---

## 7. 实例与反例

### 7.1 线性类型的正确用法

**示例 1: 文件句柄管理**:

```rust
// 严格线性类型风格的文件管理
struct FileHandle {
    fd: i32,
}

impl FileHandle {
    // 创建文件 - 获得所有权
    fn open(path: &str) -> FileHandle {
        FileHandle { fd: /* ... */ 0 }
    }

    // 读取 - 使用但不消耗
    fn read(&self) -> Vec<u8> {
        vec![]
    }

    // 关闭 - 消耗所有权
    fn close(self) {
        // self 被消耗，之后不可用
    }
}

fn good_usage() {
    let file = FileHandle::open("data.txt");
    let data = file.read();
    file.close();
    // file 不再可用，防止use-after-close
}
```

**示例 2: 资源转换链**:

```rust
// 线性资源转换
fn process_data(input: String) -> Vec<u8> {
    let bytes = input.into_bytes();  // String ⊸ Vec<u8>
    let processed = transform(bytes); // Vec<u8> ⊸ Vec<u8>
    processed
}

fn transform(data: Vec<u8>) -> Vec<u8> {
    data  // 简单返回，所有权传递
}
```

### 7.2 反例：违反线性性

**反例 1: 双重释放 (如果无Drop保护)**:

```rust
// 假设没有Drop trait的假想情况
fn double_free_risk() {
    let ptr = allocate_memory();
    free(ptr);
    free(ptr);  // 错误！双重释放
}

// Rust的线性/仿射系统防止这种情况
// 第一次 free 后，ptr 被移动/消耗
```

**反例 2: 使用已移动的值**:

```rust
fn use_after_move() {
    let s = String::from("hello");
    let t = s;  // s 被移动
    println!("{}", s);  // 编译错误！使用了已移动的值
}
```

**反例 3: 悬垂引用**:

```rust
fn dangling_reference() -> &String {  // 编译错误！
    let s = String::from("hello");
    &s  // s 在函数结束时被释放
}  // 返回的引用指向无效内存
```

---

## 8. 与其他理论的联系

### 8.1 与分离逻辑的关系

```
线性逻辑 ←→ 分离逻辑

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

### 8.2 与范畴论的关系

```
线性逻辑 ←→ 范畴论

*-自治范畴 (Symmetric Monoidal Closed Category):
- 对象: 类型
- 态射: 程序/证明
- ⊗: 张量积 (monoidal product)
- ⊸: 内部hom (线性函数)

Rust类型系统近似于:
- 仿射范畴 (Affine Category) - 允许弱化
- 带生命周期参数的范畴
- 有向图范畴 (用于借用)
```

---

## 9. 研究前沿与扩展

### 9.1 微分线性逻辑

> Ehrhard & Regnier (2003) - 引入微分算子到线性逻辑

### 9.2 带递归的线性逻辑

> 类型等式的可判定性成为关键问题

### 9.3 模态线性逻辑

```
线性时序逻辑 (LTL) 与生命周期的联系:

□A  (Globally)  ↔  'static 生命周期
◇A  (Eventually) ↔  可能悬垂的引用
○A  (Next)       ↔  下一执行点的有效性
```

---

## 10. 参考文献

1. Girard, J.-Y. (1987). Linear Logic. *Theoretical Computer Science*, 50:1-102.
2. Girard, J.-Y., Lafont, Y., & Taylor, P. (1989). *Proofs and Types*. Cambridge University Press.
3. Kopylov, A.P. (2001). Decidability of Linear Affine Logic. *Information and Computation*, 164(1):173-198.
4. Wadler, P. (1990). Linear Types can Change the World! In *Programming Concepts and Methods*.
5. Reynolds, J.C. (2002). Separation Logic: A Logic for Shared Mutable Data Structures. *LICS*.
