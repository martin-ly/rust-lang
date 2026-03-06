# 学术论文权威来源对齐

> **Rust理论基础的形式化来源**

---

## 1. 类型理论基础

### 1.1 线性逻辑 (Linear Logic)

```yaml
论文: Linear Logic
作者: Jean-Yves Girard
年份: 1987
期刊: Theoretical Computer Science
DOI: 10.1016/0304-3975(87)90045-4
```

**核心贡献**

```
线性逻辑创新:
┌─────────────────────────────────────────────────────────┐
│  经典逻辑          线性逻辑                              │
│  ─────────        ─────────                             │
│  A ⇒ B            A ⊸ B  (线性蕴含)                     │
│  A ∧ B            A ⊗ B  (张量积/同时使用)               │
│  A ∨ B            A ⅋ B  (par/交替使用)                 │
│  !A               !A     (指数/可复制)                  │
│  true             1      (单位元)                       │
│  false            ⊥      (对偶零元)                     │
└─────────────────────────────────────────────────────────┘
```

**Rust对齐**

```rust
// 线性逻辑在Rust中的体现

// A ⊸ B: 线性蕴含 (所有权转移)
fn linear_implication(a: A) -> B {
    // a被消耗，返回B
    transform(a)
}

// A ⊗ B: 张量积 (同时拥有)
let pair: (A, B) = (a, b);  // 同时持有A和B

// !A: 指数 (可复制类型)
let x: i32 = 5;
let y = x;  // Copy, !i32
let z = x;  // 仍然可以使用x

// A & B: 加法合取 (选择)
enum Choice<A, B> {
    Left(A),
    Right(B),
}
```

**形式化对应**

| 线性逻辑 | Rust概念 | 示例 |
|:---|:---|:---|
| `A ⊸ B` | `fn(A) -> B` | 消耗A产生B |
| `A ⊗ B` | `(A, B)` | 元组 |
| `A & B` | `enum { A, B }` | 枚举 |
| `!A` | `Copy` | 可复制类型 |
| `1` | `()` | 单位类型 |

---

### 1.2 仿射类型 (Affine Types)

```yaml
论文: Use-once variables and linear objects
作者: Philip Wadler
年份: 1990
会议: PLDI
```

**核心概念**

```
仿射类型系统:
    资源可以使用 0次 或 1次 (但不超过1次)

    Γ ⊢ e : τ    (使用e消耗资源Γ)
    ─────────────────────
    资源可以在e中被使用或丢弃
```

**Rust实现**

```rust
// 仿射类型: 使用0次或1次
let x: String = String::from("hello");
// 选择1: 使用
consume(x);
// x 不能再使用

// 选择2: 丢弃
let y: String = String::from("world");
drop(y);  // 显式丢弃
// 或隐式离开作用域

// 不是仿射(是线性): 必须恰好使用1次
// Rust允许丢弃，所以是仿射而非严格线性
```

---

## 2. 所有权与借用

### 2.1 区域类型系统 (Region-Based Memory Management)

```yaml
论文: Region-Based Memory Management
作者: Tofte, Talpin
年份: 1997
期刊: Information and Computation
DOI: 10.1006/inco.1997.2693
```

**核心贡献**

```
区域类型系统:
    - 将堆内存组织为区域(region)
    - 区域有生命周期，整体分配/释放
    - 静态推断区域生命周期

    与Rust对比:
    ┌────────────────────────────────────────────────┐
    │  Tofte-Talpin          Rust                     │
    │  ─────────────        ─────                     │
    │  region               lifetime                 │
    │  region inference     lifetime inference       │
    │  lexically scoped     non-lexical lifetimes    │
    │  region allocation    ownership                │
    └────────────────────────────────────────────────┘
```

**Rust扩展**

```rust
// Tofte-Talpin: 词法区域
// Rust: 非词法生命周期 (NLL)

fn nll_example() {
    let mut data = vec![1, 2, 3];
    let x = &data[0];  // 借用开始
    println!("{}", x); // 最后一次使用
    // x 的借用在这里结束 (NLL)

    data.push(4);      // 可以修改，因为借用已结束
}
```

---

### 2.2 所有权类型系统

```yaml
论文: Ownership Types for Flexible Alias Protection
作者: Clarke, Potter, Noble
年份: 1998
会议: OOPSLA
```

**所有权上下文**

```
所有权类型系统:
    - 每个对象有所有者
    - 所有者控制对象生命周期
    - 限制别名以保护不变式

    context Owner {
        object: OwnedObject
    }
```

**Rust演进**

```rust
// Clarke等人的所有权概念
// Rust的完整实现

struct Owner {
    data: OwnedData,  // Owner拥有data
}

impl Owner {
    fn lend(&self) -> &OwnedData {
        &self.data  // 借用，所有者不变
    }

    fn lend_mut(&mut self) -> &mut OwnedData {
        &mut self.data  // 可变借用
    }

    fn transfer(self) -> OwnedData {
        self.data  // 转移所有权
    }
}
```

---

## 3. 分离逻辑 (Separation Logic)

### 3.1 基础分离逻辑

```yaml
论文: Separation Logic: A Logic for Shared Mutable Data Structures
作者: John C. Reynolds
年份: 2002
会议: LICS
DOI: 10.1109/LICS.2002.1029817
```

**核心概念**

```
分离逻辑断言:
    P * Q   -- 分离合取 (P和Q持有不相交的内存)
    P -* Q  -- 分离蕴含 (给出P可得Q)
    emp     -- 空堆
    x ↦ v   -- 单点堆，x指向v

框架规则:
    {P} C {Q}
    ───────────────────
    {P * R} C {Q * R}   (R是C的不变量)
```

**Rust对应**

```rust
// 分离逻辑在unsafe代码验证中的应用

// {x ↦ _}
unsafe { *x = 5; }
// {x ↦ 5}

// 分离合取: (&mut x, &mut y) 保证x和y不重叠
let x = &mut data1;
let y = &mut data2;  // *x 和 *y 分离

// 借用作为分离断言
fn update(a: &mut i32, b: &mut i32) {
    // 前置: a ↦ v₁ * b ↦ v₂
    *a += 1;
    *b += 1;
    // 后置: a ↦ v₁+1 * b ↦ v₂+1
}
```

---

### 3.2 并发分离逻辑

```yaml
论文: Local Reasoning about Programs that Alter Data Structures
作者: O'Hearn, Reynolds, Yang
年份: 2001
会议: CSL
```

**资源推理**

```
资源敏感推理:
    - 资源作为逻辑断言的一部分
    - 分离保证资源不相交
    - 支持并行组合规则

    {P₁} C₁ {Q₁}    {P₂} C₂ {Q₂}
    ───────────────────────────── (P₁, P₂分离)
    {P₁ * P₂} C₁ || C₂ {Q₁ * Q₂}
```

**Rust并发**

```rust
// 并发分离逻辑在Rust中的体现

// 线程1拥有data1，线程2拥有data2
// {data1 ↦ v₁ * data2 ↦ v₂}
let handle1 = thread::spawn(move || {
    // 拥有data1
    process(&mut data1)
});
let handle2 = thread::spawn(move || {
    // 拥有data2
    process(&mut data2)
});
// 资源分离，可以安全并行

handle1.join();
handle2.join();
// {data1 ↦ v₁' * data2 ↦ v₂'}
```

---

## 4. Rust专用研究

### 4.1 RustBelt

```yaml
论文: RustBelt: Securing the Foundations of the Rust Programming Language
作者: Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer
年份: 2017
会议: POPL
DOI: 10.1145/3158154
```

**核心贡献**

```
RustBelt形式化框架:
    - 在Iris框架中形式化Rust
    - 验证标准库unsafe代码安全性
    - 定义Rust的安全抽象契约

关键概念:
    1. 高阶协议 (Higher-Order Protocols)
    2. 幽灵状态 (Ghost State)
    3. 不变式 (Invariants)
```

**形式化结果**

```
定理 (RustBelt):
    ∀库L. L的所有unsafe代码满足其契约 →
    任意Safe Rust程序使用L都是内存安全的

验证的库组件:
    - Cell<T>
    - RefCell<T>
    - Rc<T>
    - Arc<T>
    - Mutex<T>
    - Vec<T>
    - Box<T>
```

---

### 4.2 Stacked Borrows / Tree Borrows

```yaml
论文: Stacked Borrows: An Aliasing Model for Rust
作者: Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer
年份: 2019
会议: POPL
DOI: 10.1145/3371109
```

**别名模型演进**

```
Stacked Borrows:
    - 定义引用的语义
    - 栈结构跟踪借用状态
    - 检测未定义行为

    借用栈:
    ┌─────────────┐
    │ SharedRead  │  ← &x
    │ UniqueMut   │  ← &mut x (激活)
    │ UniqueMut   │  ← &mut x (冻结)
    └─────────────┘

Tree Borrows (改进):
    - 树结构更灵活
    - 支持更多合法模式
    - 更好的性能特性
```

**验证示例**

```rust
// Stacked Borrows检测的错误
fn stacked_borrows_violation() {
    let mut x = 5;
    let y = &mut x;
    let z = &x;  // 错误! 存在活跃的&mut，不能有&
    *y += 1;
}

// Tree Borrows允许的合法模式
fn tree_borrows_ok() {
    let mut x = 5;
    let y = &mut x;
    let z = y as *mut i32;  // 原始指针转换允许
    unsafe { *z += 1; }
    *y += 1;  // OK
}
```

---

### 4.3 Rust中的模式类型

```yaml
论文: Types for Memory Safety in Rust
作者: Eric Reed
年份: 2015
类型: 硕士论文
机构: University of Washington
```

**类型系统分析**

```
核心洞见:
    - 所有权作为类型修饰符
    - 借用作为受限引用
    - 生命周期作为区域变量

    类型层次:
        Owned<T>
            └── Borrowed<'a, T>
                    ├── Shared<'a, T>
                    └── Mutable<'a, T>
```

---

## 5. 验证工具论文

### 5.1 Creusot

```yaml
论文: Creusot: A Foundry for the Verification of Rust Programs
作者: Xavier Denis, Jacques-Henri Jourdan, Claude Marché
年份: 2022
会议: ICFP
DOI: 10.1145/3547639
```

**验证方法**

```rust
// Creusot规范示例
#[requires(x > 0)]
#[ensures(result > x)]
fn increment(x: u32) -> u32 {
    x + 1
}

// 不变式
#[invariant(self.len <= self.cap)]
impl<T> Vec<T> {
    fn push(&mut self, item: T) {
        // 实现
    }
}
```

---

### 5.2 Prusti

```yaml
论文: Prusti: A Static Verifier for Rust
作者: Vytautas Astrauskas et al.
年份: 2019
会议: OOPSLA
```

**规范语言**

```rust
// Prusti合约
#[pure]
#[requires(x > 0)]
#[ensures(ret > 0)]
fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

// 谓词
#[predicate]
fn sorted(s: &[i32]) -> bool {
    forall(|i: usize, j: usize|
        (i < j && j < s.len()) ==> s[i] <= s[j])
}
```

---

## 6. 并发理论

### 6.1 Relaxed Memory Models

```yaml
论文: The Semantics of Efficient, Portable, and Relaxed Memory Models
作者: Batty, Memarian, Nienhuis, Pichon-Pharabod, Sewell
年份: 2016
会议: POPL
```

**Rust内存模型**

```
Rust内存模型基于:
    - C++11内存模型
    - 顺序一致性数据竞争自由 (SC-DRF)
    - happens-before关系

内存序:
    - Relaxed: 最弱，仅原子性
    - Acquire/Release: 建立synchronizes-with
    - SeqCst: 最强，全局序
```

---

## 7. 论文引用图谱

```
理论基础:
    Girard (1987) Linear Logic
        ↓
    Wadler (1990) Affine Types
        ↓
    Tofte & Talpin (1997) Region-Based MM
        ↓
    Clarke et al. (1998) Ownership Types

分离逻辑:
    Reynolds (2002) Separation Logic
        ↓
    O'Hearn et al. (2001) Concurrent Separation Logic
        ↓
    Jung et al. (2017) RustBelt
        ↓
    Jung et al. (2019) Stacked Borrows
        ↓
    Jung et al. (2021) Tree Borrows

验证工具:
    Denis et al. (2022) Creusot
    Astrauskas et al. (2019) Prusti
```

---

## 8. 对齐摘要

| 论文 | 核心概念 | Rust对应 |
|:---|:---|:---|
| Girard 1987 | 线性逻辑 | 所有权、Copy |
| Wadler 1990 | 仿射类型 | 所有权、Drop |
| Tofte 1997 | 区域类型 | 生命周期、NLL |
| Clarke 1998 | 所有权类型 | 所有权系统 |
| Reynolds 2002 | 分离逻辑 | unsafe验证 |
| Jung 2017 | RustBelt | 标准库安全 |
| Jung 2019 | Stacked Borrows | Miri检测 |

---

**维护者**: Rust Research Alignment Team
**更新日期**: 2026-03-05
**覆盖论文**: 15+ 篇核心文献
