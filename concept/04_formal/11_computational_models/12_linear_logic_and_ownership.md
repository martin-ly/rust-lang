> **内容分级**: [专家级]

# 线性逻辑与所有权：作为计算模型的资源演算（Linear Logic and Ownership: Resource Calculus as a Computational Model）

> **EN**: Linear Logic and Ownership: Resource Calculus as a Computational Model
> **Summary**: Treats linear/affine logic as a computational model for Rust ownership, mapping Girard's linear connectives to Rust's move, borrow, Copy, Drop, and thread-shared resources, while distinguishing the structural proof theory from the engineering borrow checker.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从**计算模型**视角把线性/仿射逻辑当作 Rust 所有权的**资源演算**：不重复介绍 Girard 的 sequent calculus，而是说明 `⊗, ⊸, !, &` 等连接词如何精确对应 Rust 的值移动、函数调用、共享借用、引用计数等工程机制，并为 [范畴论与 Rust](10_category_theory_and_rust.md) 的「仿射范畴直觉」与 [RustBelt 所有权逻辑](16_rustbelt_ownership_logic.md) 提供证明论语义基础。
> **前置概念**:
> [Linear Logic](../01_ownership_logic/01_linear_logic.md) ·
> [Ownership Formalization](../01_ownership_logic/02_ownership_formal.md) ·
> [Category Theory and Rust](10_category_theory_and_rust.md) ·
> [Separation Logic for Rust](08_separation_logic_for_rust.md)
> **后置概念**:
> [Session Types and Rust Channels](13_session_types_and_rust_channels.md) ·
> [RustBelt Ownership Logic](16_rustbelt_ownership_logic.md) ·
> [Effect Handlers and Rust Limited Effects](14_effect_handlers_and_rust_limited_effects.md) ·
> [Unsafe Contracts Formal](../01_ownership_logic/07_unsafe_contracts_formal.md) ·
> [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md)

---

## 📑 目录

- [线性逻辑与所有权：作为计算模型的资源演算（Linear Logic and Ownership: Resource Calculus as a Computational Model）](#线性逻辑与所有权作为计算模型的资源演算linear-logic-and-ownership-resource-calculus-as-a-computational-model)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 线性逻辑作为计算模型](#11-线性逻辑作为计算模型)
    - [1.2 子结构规则与 Rust 的结构规则](#12-子结构规则与-rust-的结构规则)
    - [1.3 乘法合取 ⊗：结构体与资源组合](#13-乘法合取-结构体与资源组合)
    - [1.4 线性蕴含 ⊸：move 函数与消费](#14-线性蕴含-move-函数与消费)
    - [1.5 指数 !：Copy 与共享借用](#15-指数-copy-与共享借用)
    - [1.6 加法合取 \& 与选择 ⊕：trait 对象与枚举](#16-加法合取--与选择-trait-对象与枚举)
    - [1.7 仿射 vs 线性：Drop 与 weakening](#17-仿射-vs-线性drop-与-weakening)
    - [1.8 从单线程到并发：线性资源的线程迁移](#18-从单线程到并发线性资源的线程迁移)
  - [二、形式化属性矩阵](#二形式化属性矩阵)
  - [三、正向示例](#三正向示例)
    - [示例 1：⊗ 作为 struct 字段组合](#示例-1-作为-struct-字段组合)
    - [示例 2：⊸ 作为消费型函数](#示例-2-作为消费型函数)
    - [示例 3：! 作为 Copy 类型](#示例-3-作为-copy-类型)
    - [示例 4：\& 与 ⊕ 作为选择器](#示例-4-与--作为选择器)
  - [四、反例与边界测试](#四反例与边界测试)
    - [反例 1：违反 contraction 导致二次释放](#反例-1违反-contraction-导致二次释放)
    - [反例 2：把非 Copy 值当作 !A 使用](#反例-2把非-copy-值当作-a-使用)
    - [反例 3：线性通道被丢弃导致协议死锁](#反例-3线性通道被丢弃导致协议死锁)
  - [五、反命题决策树](#五反命题决策树)
    - [命题：「Rust 就是线性类型系统」](#命题rust-就是线性类型系统)
    - [命题：「Copy 类型打破了线性逻辑」](#命题copy-类型打破了线性逻辑)
  - [六、嵌入式测验（Embedded Quiz）](#六嵌入式测验embedded-quiz)
    - [测验 1：Rust 所有权对应哪一种子结构逻辑？](#测验-1rust-所有权对应哪一种子结构逻辑)
    - [测验 2：`fn(T) -> U` 中 T 被 move，最接近哪个线性连接词？](#测验-2fnt---u-中-t-被-move最接近哪个线性连接词)
    - [测验 3：共享引用 `&T` 对应线性逻辑的哪个概念？](#测验-3共享引用-t-对应线性逻辑的哪个概念)
  - [七、权威来源 / International Authority References](#七权威来源--international-authority-references)
  - [八、🧭 思维导图（Mindmap）](#八-思维导图mindmap)

---

## 一、核心概念

### 1.1 线性逻辑作为计算模型

线性逻辑（Girard 1987）通常被介绍为「资源敏感的逻辑」。从**计算模型**视角看，它提供了一套**资源演算**：命题是资源，证明是资源变换过程，结构规则（weakening / contraction / exchange）控制资源能否被丢弃、复制或重排。

```text
线性逻辑作为计算模型
├── 命题 A: 类型为 A 的资源
├── 证明 Γ ⊢ A: 把上下文 Γ 中的资源变换成 A
├── ⊗ (tensor): 同时拥有两种资源
├── ⊸ (lollipop): 消费一种资源以产出另一种
├── ! (of course): 可任意复制/丢弃的资源模态
├── & (with): 外部选择 / 同时提供两种能力
├── ⊕ (plus): 内部选择 / 两种资源之一
└── 结构规则: weakening(丢弃) / contraction(复制) / exchange(交换)
```

Rust 的所有权系统可以被读作**仿射逻辑**（affine logic）的工程实现：

- **Contraction 被禁止**：默认情况下值不能被隐式复制（`move` 语义）。
- **Weakening 被允许**：值可以被丢弃（`Drop` 自动调用，或 `let _ = x;`）。
- **Exchange 被允许**：变量声明顺序不影响类型正确性。

这与严格线性逻辑（linear logic）不同：线性逻辑禁止 weakening，即资源必须被**恰好使用一次**。Rust 允许丢弃资源，因此更准确地说 Rust 是**仿射类型系统**加上显式 `Copy` 机制来恢复 contraction。

> **来源**: [Girard 1987, *Linear Logic*](https://doi.org/10.1016/0304-3975(87)90045-4) · [Wadler 1990, *Linear Types can Change the World*](https://doi.org/10.1007/3-540-52377-7_30) · [RustBelt POPL 2018](https://doi.org/10.1145/3158154)

---

### 1.2 子结构规则与 Rust 的结构规则

| 结构规则 | 线性逻辑 | 仿射逻辑 | Rust | 工程含义 |
|:---|:---:|:---:|:---:|:---|
| Weakening（丢弃） | ❌ | ✅ | ✅ | `Drop` / 变量离开作用域 |
| Contraction（复制） | ❌ | ❌ | ❌ | 非 `Copy` 值不能隐式复制 |
| Exchange（交换） | ✅ | ✅ | ✅ | 变量顺序可重排 |

Rust 通过 `Clone` trait 提供**显式 contraction**：只有当类型实现 `Clone` 时，程序员才能通过 `.clone()` 复制资源。这相当于把「是否允许 contraction」推迟到类型层面，由类型作者决定。

```rust
#[derive(Clone)]
struct Resource(String);

fn main() {
    let r = Resource(String::from("data"));
    let r2 = r.clone(); // 显式 contraction
    println!("{} {}", r.0, r2.0);
}
```

> **关键洞察**: 借用检查器不是直接实现线性逻辑，而是实现**仿射类型系统 + 受控复制**。`Copy` / `Clone` 是程序员显式「打开 contraction」的接口。

---

### 1.3 乘法合取 ⊗：结构体与资源组合

**乘法合取 `A ⊗ B`** 表示「同时拥有 A 和 B 两种资源，且它们彼此独立」。Rust 的**元组**和**结构体**正是 `⊗` 的工程实现：

```text
⊗-intro:
  Γ ⊢ A    Δ ⊢ B
  ───────────────
  Γ, Δ ⊢ A ⊗ B

⊗-elim:
  Γ ⊢ A ⊗ B
  ───────────────
  Γ ⊢ A    Γ ⊢ B
```

```rust
struct Pair<A, B> { first: A, second: B }

fn split<A, B>(p: Pair<A, B>) -> (A, B) {
    (p.first, p.second) // 把 A ⊗ B 拆成 A 和 B
}

fn main() {
    let s = String::from("hello");
    let n = 42;
    let p = Pair { first: s, second: n }; // A ⊗ B
    let (a, b) = split(p);
    println!("{} {}", a, b);
}
```

> **关键洞察**: `⊗` 的「资源独立」意味着移动 `Pair` 中的一个字段会**部分移动**（partial move）整个结构体。Rust 编译器精确跟踪这种部分移动，确保不会二次使用已移动字段。

---

### 1.4 线性蕴含 ⊸：move 函数与消费

**线性蕴含 `A ⊸ B`** 表示「消费一个 A 资源，产出一个 B 资源」。Rust 中形如 `fn(A) -> B` 且参数被 move 的函数就是 `⊸` 的实现：

```text
⊸-intro:
  Γ, A ⊢ B
  ─────────
  Γ ⊢ A ⊸ B

⊸-elim:
  Γ ⊢ A ⊸ B    Δ ⊢ A
  ───────────────────
  Γ, Δ ⊢ B
```

```rust
fn consume_string(s: String) -> usize {
    s.len() // 消费 String，产出 usize
}

fn main() {
    let s = String::from("linear");
    let n = consume_string(s); // s: String ⊸ n: usize
    println!("{}", n);
    // println!("{}", s); // ❌ s 已被消费
}
```

线性函数类型在 Rust 中没有原生语法，但可以通过**参数按值传递 + 非 Copy** 来模拟。Rust 的类型系统进一步要求：如果 `B` 仍然包含 `A` 的部分资源，这种包含关系必须显式表达（例如返回包含原 String 的结构体）。

---

### 1.5 指数 !：Copy 与共享借用

线性逻辑中的**指数模态 `!A`**（读作「of course A」）表示「A 可以任意复制和丢弃」。Rust 中对应两类机制：

1. **`T: Copy`**：值可以按位复制，隐式 contraction。
2. **`&T` 共享借用**：只读引用可以复制（`Copy`），不消耗原资源。

```text
!A 的规则
  !A ⊢ A      (dereliction: 可以使用一次)
  !A ⊢ !A ⊗ !A (contraction: 可以复制)
  !A ⊢ 1      (weakening: 可以丢弃)
```

```rust
fn main() {
    let n: i32 = 42; // i32: Copy ⇒ n 等价于 !i32
    let a = n;
    let b = n; // 隐式 contraction
    let c = n;
    println!("{} {} {}", a, b, c);

    let s = String::from("shared");
    let r1 = &s; // &String 等价于 !(&String)
    let r2 = r1; // 共享引用可 Copy
    let r3 = r1;
    println!("{} {} {}", r1, r2, r3);
}
```

> **关键洞察**: `!` 是线性逻辑与直觉逻辑之间的**桥梁**。Rust 的 `Copy` trait 和共享借用正是这座桥：它们让一部分资源从「严格线性」回到「自由使用」。

---

### 1.6 加法合取 & 与选择 ⊕：trait 对象与枚举

- **`A & B`（with）**: 外部选择——使用者选择使用 A 还是 B。Rust 中接近**trait 对象**或**同时实现多个 trait 的类型**：调用者决定调用哪个方法。
- **`A ⊕ B`（plus）**: 内部选择——提供者决定给出 A 还是 B。Rust 中对应**枚举** `enum` / `Result<T, E>` / `Option<T>`：值的构造者决定分支，使用者通过 `match` 处理。

```rust
// ⊕: 内部选择，值的创建者决定分支
enum Choice<A, B> { Left(A), Right(B) }

fn make_choice(flag: bool) -> Choice<i32, &'static str> {
    if flag { Choice::Left(42) } else { Choice::Right("no") }
}

fn main() {
    let c = make_choice(true);
    match c {
        Choice::Left(n) => println!("number {}", n),
        Choice::Right(s) => println!("text {}", s),
    }
}
```

```rust
// &: 外部选择，调用者选择使用哪种能力
trait Readable { fn read(&self) -> String; }
trait Writable { fn write(&mut self, s: &str); }

struct File;
impl Readable for File { fn read(&self) -> String { String::new() } }
impl Writable for File { fn write(&mut self, _s: &str) {} }

fn use_readable(r: &dyn Readable) { let _ = r.read(); }

fn main() {
    let mut f = File;
    use_readable(&f); // 调用者选择使用 Readable 能力
}
```

> **关键洞察**: `&` 和 `⊕` 的对偶性解释了 Rust 中「接口选择」与「值构造选择」的区分。`enum` 是值的内部选择，`trait` 是能力的外部选择。

---

### 1.7 仿射 vs 线性：Drop 与 weakening

Rust 允许**丢弃**（weakening）资源，这使其成为仿射逻辑而非严格线性逻辑。线性逻辑要求每个假设必须被使用一次；Rust 允许：

```rust
fn main() {
    let s = String::from("will be dropped");
    // s 未被显式使用，但 Rust 在作用域结束时自动调用 Drop
}
```

这种行为在线性逻辑中是不合法的，但在仿射逻辑中合法。Rust 进一步通过 `std::mem::forget` 允许显式禁用 Drop，但这会引入资源泄漏风险；在线性逻辑视角下，`mem::forget` 相当于**拒绝履行资源消耗义务**，把仿射丢弃变成真正的资源泄漏。

```rust
use std::mem;

fn main() {
    let s = String::from("leaked");
    mem::forget(s); // 显式不调用 Drop；线性/仿射逻辑都不鼓励
}
```

> **关键洞察**: Rust 的 `Drop` 是「weakening 的工程化」：它保证资源在丢弃时被正确终结。`mem::forget` 绕过了这一保证，是线性资源管理中的**反模式**。

---

### 1.8 从单线程到并发：线性资源的线程迁移

线性/仿射资源模型天然适合并发：如果资源只能被唯一所有者持有，那么把它 move 到另一个线程就**自动消除了数据竞争**。Rust 的 `std::thread::spawn` 利用这一性质：

```rust
use std::thread;

fn main() {
    let s = String::from("move to thread");
    let handle = thread::spawn(move || {
        println!("{}", s);
        s.len()
    });
    let len = handle.join().unwrap();
    println!("len = {}", len);
}
```

`move` 闭包把 `s` 线性迁移到新线程；原线程再也无法访问 `s`，因此不存在竞争。这与分离逻辑中的 `own(x, τ) ⊢ own(y, τ)` 一致：权限从一处转移到另一处。

> **来源**: [RustBelt POPL 2018](https://doi.org/10.1145/3158154) · [O'Hearn 2007, *Resources, Concurrency and Local Reasoning*](https://doi.org/10.1016/j.tcs.2006.12.035)

---

## 二、形式化属性矩阵

| 线性逻辑概念 | Rust 工程机制 | 形式化含义 | 权威来源 |
|:---|:---|:---|:---|
| 命题 A | 类型 `A` | 资源断言 | Girard 1987 |
| 上下文 Γ | 变量环境 | 可用资源集合 | Girard 1987 |
| ⊗ (tensor) | `(A, B)` / `struct` | 同时拥有独立资源 | Wadler 1990 |
| ⊸ (lollipop) | `fn(A) -> B` (move) | 消费 A 产出 B | Wadler 1990 |
| ! (of course) | `T: Copy` / `&T` | 可任意复制/丢弃 | Girard 1987 |
| & (with) | `dyn Trait` / 多能力接口 | 外部选择 | Wadler 2012 |
| ⊕ (plus) | `enum` / `Result` | 内部选择 | Wadler 2012 |
| 1 (unit) | `()` | 空资源 | Girard 1987 |
| ⊥ (bottom) | `!` (never type) | 不可能资源 | Girard 1987 |
| weakening | `Drop` / 作用域结束 | 允许丢弃 | Affine logic |
| contraction | `move` 语义 | 禁止隐式复制 | Affine logic |
| exchange | 变量重排 | 声明顺序无关 | Linear logic |

---

## 三、正向示例

### 示例 1：⊗ 作为 struct 字段组合

```rust
struct Line { start: String, end: String }

fn take_both(l: Line) -> (String, String) {
    (l.start, l.end)
}

fn main() {
    let line = Line {
        start: String::from("A"),
        end: String::from("B"),
    };
    let (a, b) = take_both(line);
    println!("{} -> {}", a, b);
}
```

### 示例 2：⊸ 作为消费型函数

```rust
struct Token;

fn consume_token(t: Token) -> String {
    let _ = t;
    String::from("access granted")
}

fn main() {
    let t = Token;
    let msg = consume_token(t);
    println!("{}", msg);
    // consume_token(t); // ❌ t 已消费
}
```

### 示例 3：! 作为 Copy 类型

```rust
fn main() {
    let x: u64 = 7;
    let a = x;
    let b = x;
    let c = x;
    println!("{} {} {} {}", x, a, b, c); // u64: Copy
}
```

### 示例 4：& 与 ⊕ 作为选择器

```rust
enum Action { Run(i32), Stop }

fn dispatch(a: Action) -> String {
    match a {
        Action::Run(n) => format!("run {}", n),
        Action::Stop => String::from("stop"),
    }
}

fn main() {
    let a = Action::Run(10);
    println!("{}", dispatch(a));
}
```

---

## 四、反例与边界测试

### 反例 1：违反 contraction 导致二次释放

```rust,compile_fail,E0382
fn main() {
    let s = String::from("owned");
    let t = s; // move
    println!("{}", s); // ❌ s 已被消费
    println!("{}", t);
}
```

> **错误诊断**: `error[E0382]: borrow of moved value:`s``。Rust 的仿射规则禁止隐式复制非 `Copy` 值；如果允许，`s` 和 `t` 会双重释放同一块堆内存。
> **修正**: 使用 `.clone()` 显式复制，或改用 `&s` 共享引用。

### 反例 2：把非 Copy 值当作 !A 使用

```rust,compile_fail,E0507
fn main() {
    let s = String::from("not copy");
    let r = &s;
    let s2 = *r; // ❌ 不能 move 出共享引用
    drop(s2);
}
```

> **错误诊断**: `error[E0507]: cannot move out of *r which is behind a shared reference`。`&T` 是 `!T` 的只读视角，不代表拥有 `T`；解引用后 move 会破坏共享借用契约。
> **修正**: 使用 `r.clone()` 或保持引用使用。

### 反例 3：线性通道被丢弃导致协议死锁

```rust
use std::sync::mpsc::{channel, Sender};

struct SendOnce<T>(Sender<T>);

impl<T> SendOnce<T> {
    fn send(self, v: T) {
        self.0.send(v).unwrap();
    }
}

fn main() {
    let (tx, rx) = channel::<i32>();
    let once = SendOnce(tx);
    // once.send(42); // 如果忘记调用 send，接收端会永远等待
    drop(once);      // 显式丢弃线性通道；协议未完成
    println!("channel dropped without send");
}
```

> **错误诊断**: 运行时接收端 `recv()` 会返回 `Err(RecvError)`，但 Rust 编译器**不会**在线性协议层面报错。这说明 Rust 的仿射类型系统只能保证「资源不泄露」，不能保证「协议被完整执行」。
> **修正**: 使用 session-type 库或类型状态机把协议步骤编码进类型（参见 [Session Types and Rust Channels](13_session_types_and_rust_channels.md)）。

---

## 五、反命题决策树

### 命题：「Rust 就是线性类型系统」

```text
该命题成立吗？
├── 是 → 不完全。Rust 的核心 ownership 确实受线性逻辑启发：
│   ├── 禁止隐式复制（contraction）
│   ├── 资源必须被明确转移或丢弃
│   └── 借用是线性资源的受控共享
└── 否 → 更准确。Rust 是仿射类型系统：
    ├── 允许 weakening（Drop / 变量离开作用域）
    ├── 通过 Copy/Clone 显式恢复 contraction
    └── 不强制每个资源必须被使用一次
```

### 命题：「Copy 类型打破了线性逻辑」

```text
该命题成立吗？
├── 是 → 表层看。Copy 类型允许隐式复制，似乎违反线性逻辑的「禁止 contraction」。
└── 否 → 更准确。Copy 类型是 !A（of course A）的工程实现：
    ├── 线性逻辑本身就允许 !A 被任意复制
    ├── Rust 把「能否复制」的决策下放到类型作者
    └── 非 Copy 类型仍然遵守仿射规则
```

---

## 六、嵌入式测验（Embedded Quiz）

### 测验 1：Rust 所有权对应哪一种子结构逻辑？

A. 经典逻辑
B. 直觉主义逻辑
C. 线性逻辑
D. 仿射逻辑

<details>
<summary>✅ 答案</summary>

**D. 仿射逻辑**。Rust 允许 weakening（丢弃资源，通过 Drop），但禁止 contraction（隐式复制非 Copy 值）。严格线性逻辑会禁止 weakening。

</details>

### 测验 2：`fn(T) -> U` 中 T 被 move，最接近哪个线性连接词？

A. ⊗
B. ⊸
C. !
D. &

<details>
<summary>✅ 答案</summary>

**B. ⊸（线性蕴含）**。函数消费一个 `T` 资源并产出一个 `U` 资源，正是 `T ⊸ U` 的直觉。

</details>

### 测验 3：共享引用 `&T` 对应线性逻辑的哪个概念？

A. ⊗
B. ⊸
C. !
D. ⊥

<details>
<summary>✅ 答案</summary>

**C. !（of course / 指数模态）**。`&T` 可以被任意复制而不消耗原资源，相当于把 `T` 放入「可自由使用」模态。

</details>

---

## 七、权威来源 / International Authority References

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Girard 1987, *Linear Logic*](https://doi.org/10.1016/0304-3975(87)90045-4) | ✅ 一级 | 线性逻辑奠基论文，⊗/⊸/! 等连接词 |
| [Wadler 1990, *Linear Types can Change the World*](https://doi.org/10.1007/3-540-52377-7_30) | ✅ 一级 | 线性类型在函数式语言中的资源视角 |
| [Pierce 2002, TAPL §15](https://www.cis.upenn.edu/~bcpierce/tapl/) | ✅ 一级 | 子结构类型系统教材 |
| [Wadler 2012, *Propositions as Sessions*](https://doi.org/10.1145/2103656.2103661) | ✅ 一级 | 线性逻辑与会话类型的 Curry-Howard 对应 |
| [Jung et al., RustBelt POPL 2018](https://doi.org/10.1145/3158154) | ✅ 一级 | Rust 所有权系统的 Iris 机械证明 |
| [Rust Reference — Ownership](https://doc.rust-lang.org/reference/ownership.html) | ✅ P0 | Rust 官方所有权语义 |
| [Rust RFC 152 — Copy](https://rust-lang.github.io/rfcs/0152-copied-type.html) | ✅ P0 | Copy trait 设计来源 |

---

## 八、🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((线性逻辑与所有权计算模型))
    线性逻辑作为资源演算
      命题 = 资源
      证明 = 资源变换
      结构规则
    子结构规则
      weakening = Drop
      contraction = move / Copy 控制
      exchange = 变量重排
    连接词映射
      ⊗ = struct / tuple
      ⊸ = fn(A) -> B (move)
      ! = Copy / &T
      & = trait / 外部选择
      ⊕ = enum / 内部选择
    仿射 vs 线性
      Rust = affine
      允许丢弃
      禁止隐式复制
    并发迁移
      move 到线程
      无数据竞争
    权威来源
      Girard 1987
      Wadler 1990 / 2012
      RustBelt POPL 2018
```
