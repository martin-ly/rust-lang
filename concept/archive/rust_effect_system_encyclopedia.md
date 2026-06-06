# Rust 效应系统（Effect System）与其语言边界的全面深化广化分析论证

> **文档性质**：百科全书级形式化分析论证
> **对齐标准**：POPL、PLDI、ICFP、OOPSLA、SOSP、USENIX ATC、ICFP、ESOP、TACAS 国际顶会学术传统
> **核心问题**：Rust 的类型系统是否构成效应系统？其边界在哪里？与代数效应、能力系统、所有权系统的本质差异为何？
> **表征方式**：概念定义总表 · 形式化类型规则 · 操作语义 · 范畴论语义 · 历史演进谱系 · 代码示例对比矩阵 · 反例集 · 属性关系矩阵 · 思维导图 · 多维矩阵热力图 · 定理推理判定树 · 边界语义空间决策树 · 编译器 lowering 路径图 · 形式化验证生态图谱 · 范畴论三元对比图 · unsafe 形式化模型图 · 工程决策雷达图 · 综合架构全景图

---

## 目录

- [Rust 效应系统（Effect System）与其语言边界的全面深化广化分析论证](#rust-效应系统effect-system与其语言边界的全面深化广化分析论证)
  - [目录](#目录)
  - [第一章：概念定义总表（Alphabetical Encyclopedia）](#第一章概念定义总表alphabetical-encyclopedia)
    - [1.1 Algebraic Effects（代数效应）](#11-algebraic-effects代数效应)
    - [1.2 Affine Type（仿射类型）](#12-affine-type仿射类型)
    - [1.3 Borrow Checker（借用检查器）](#13-borrow-checker借用检查器)
    - [1.4 Capability（能力/权能）](#14-capability能力权能)
    - [1.5 Carried Effect（可携带效应）](#15-carried-effect可携带效应)
    - [1.6 Continuation（续延）](#16-continuation续延)
    - [1.7 Effect Generics（效应泛型）](#17-effect-generics效应泛型)
    - [1.8 Effect Handler（效应处理器）](#18-effect-handler效应处理器)
    - [1.9 Effect Mismatch（效应不匹配）](#19-effect-mismatch效应不匹配)
    - [1.10 Lifetime（生命周期）](#110-lifetime生命周期)
    - [1.11 Linear Type（线性类型）](#111-linear-type线性类型)
    - [1.12 Meta-Effect（元效应）](#112-meta-effect元效应)
    - [1.13 Ownership（所有权）](#113-ownership所有权)
    - [1.14 Row Polymorphism（行多态）](#114-row-polymorphism行多态)
    - [1.15 Uncarried Effect（不可携带效应）](#115-uncarried-effect不可携带效应)
    - [1.16 Zero-Cost Abstraction（零成本抽象）](#116-zero-cost-abstraction零成本抽象)
  - [第二章：形式化语义基础](#第二章形式化语义基础)
    - [2.1 操作语义（Operational Semantics）](#21-操作语义operational-semantics)
      - [2.1.1 Rust 的 Oxide 形式化语义](#211-rust-的-oxide-形式化语义)
      - [2.1.2 Koka 的 Evidence Passing 语义](#212-koka-的-evidence-passing-语义)
    - [2.2 类型规则（Typing Rules）](#22-类型规则typing-rules)
      - [2.2.1 Rust 的 async/await 类型规则](#221-rust-的-asyncawait-类型规则)
      - [2.2.2 Koka 的 Effect Handler 类型规则](#222-koka-的-effect-handler-类型规则)
    - [2.3 范畴论语义（Categorical Semantics）](#23-范畴论语义categorical-semantics)
      - [2.3.1 Monad 的 Kleisli 三元组](#231-monad-的-kleisli-三元组)
      - [2.3.2 Algebraic Effects 的 Lawvere 理论](#232-algebraic-effects-的-lawvere-理论)
      - [2.3.3 Ownership 的分离逻辑语义](#233-ownership-的分离逻辑语义)
  - [第三章：历史演进深化谱系](#第三章历史演进深化谱系)
    - [3.1 完整历史时间线（1936-2026）](#31-完整历史时间线1936-2026)
  - [第四章：Rust 五种效应的完整分析](#第四章rust-五种效应的完整分析)
    - [4.1 async —— 控制流效应的典范](#41-async--控制流效应的典范)
    - [4.2 unsafe —— 元效应的独例](#42-unsafe--元效应的独例)
    - [4.3 const —— 阶段效应的困境](#43-const--阶段效应的困境)
    - [4.4 try —— 可失败性的类型化](#44-try--可失败性的类型化)
    - [4.5 generators —— 不稳定的多重性效应](#45-generators--不稳定的多重性效应)
  - [第五章：跨语言代码示例对比矩阵](#第五章跨语言代码示例对比矩阵)
    - [5.1 异常处理对比](#51-异常处理对比)
    - [5.2 异步编程对比](#52-异步编程对比)
    - [5.3 状态管理对比](#53-状态管理对比)
  - [第六章：反例集（Counter-Examples）](#第六章反例集counter-examples)
    - [6.1 反例 1：Rust 无法实现的 Multi-Shot Continuation](#61-反例-1rust-无法实现的-multi-shot-continuation)
    - [6.2 反例 2：Rust 无法实现的 User-Defined Effect](#62-反例-2rust-无法实现的-user-defined-effect)
    - [6.3 反例 3：Rust 无法实现的 Effect Polymorphism](#63-反例-3rust-无法实现的-effect-polymorphism)
    - [6.4 反例 4：C++ 的异常作为反模式](#64-反例-4c-的异常作为反模式)
    - [6.5 反例 5：Java Checked Exceptions 的失败](#65-反例-5java-checked-exceptions-的失败)
  - [第七章：属性关系矩阵（Property Relation Matrix）](#第七章属性关系矩阵property-relation-matrix)
    - [7.1 概念间逻辑关系](#71-概念间逻辑关系)
    - [7.2 Rust 效应系统的属性依赖图](#72-rust-效应系统的属性依赖图)
  - [第八章：工业实践案例深化](#第八章工业实践案例深化)
    - [8.1 Asterinas：Rust OS 内核的形式化验证](#81-asterinasrust-os-内核的形式化验证)
    - [8.2 verify-rust-std：标准库的形式化验证](#82-verify-rust-std标准库的形式化验证)
    - [8.3 Rust for Linux：内核模块的安全标注](#83-rust-for-linux内核模块的安全标注)
    - [8.4 Ferrocene：安全关键 Rust 编译器](#84-ferrocene安全关键-rust-编译器)
  - [第九章：形式化验证工具深化对比](#第九章形式化验证工具深化对比)
    - [9.1 工具能力矩阵](#91-工具能力矩阵)
    - [9.2 验证层次模型](#92-验证层次模型)
  - [第十章：结论与三重边界的最终形式化](#第十章结论与三重边界的最终形式化)
    - [10.1 边界一：Carried vs Uncarried 类型系统断层](#101-边界一carried-vs-uncarried-类型系统断层)
    - [10.2 边界二：零成本抽象与通用效应处理器的不相容性](#102-边界二零成本抽象与通用效应处理器的不相容性)
    - [10.3 边界三：空间安全与行为安全的正交性](#103-边界三空间安全与行为安全的正交性)
    - [10.4 工程哲学总结](#104-工程哲学总结)
  - [参考文献索引（深化版）](#参考文献索引深化版)

## 第一章：概念定义总表（Alphabetical Encyclopedia）

> **说明**：以下每个概念条目包含【定义】【形式化描述】【核心属性】【正例】【反例】【关系网络】六个维度，确保概念的完整对齐。

### 1.1 Algebraic Effects（代数效应）

**【定义】**:
由 Plotkin & Power (2003) 提出的计算效应理论框架。
一个代数效应由**操作签名（effect signature）** Σ = { opᵢ : Aᵢ → Bᵢ } 定义，其中每个操作 opᵢ 是从参数类型 Aᵢ 到返回类型 Bᵢ 的计算。
效应的语义由**自由代数（free algebra）**在范畴论中的构造给出。

**【形式化描述】**
在 Lawvere 理论的框架下，代数效应对应一个 arity 为 (A,B) 的操作族。
对于集合范畴 **Set**，一个 Σ-代数是载体集 C 配上操作族 [opᵢ] : Cᴬ × A → Cᴮ。
Plotkin & Power 证明：计算效应可表示为对自由模型的计算。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 可观察性 | 高 | 操作调用是计算与环境的显式交互 |
| 用户可扩展性 | 是 | 可定义新 effect signature |
| 组合方式 | 自由组合 | 通过 handlers 组合，无需 monad transformer |
| 运行时成本 | 中-高 | 需 continuation 捕获或 evidence passing |
| 类型系统支持 | 需 effect typing | 效应出现在类型签名中 |

**【正例】**:

```koka
// Koka: 用户自定义异常效应
effect raise
  ctl raise(msg : string) : a

fun safe-divide(x : int, y : int) : raise int
  if y == 0 then raise("div-by-zero") else x / y

// Handler 捕获异常
fun catch(action : () -> <raise|e> a, hnd : (string) -> e a) : e a
  with ctl raise(msg) hnd(msg)
  action()
```

**【反例】**:

```rust
// Rust 无法实现用户自定义 raise 效应
// 以下代码不成立：Rust 没有 effect signature 机制
// effect raise { fn raise(msg: String) -> !; }  // ❌ 语法错误
// fn safe_divide(x: i32, y: i32) -> raise i32 {  // ❌ 类型错误
//     if y == 0 { raise("div-by-zero") } else { x / y }
// }
// 必须使用 Result 类型：
fn safe_divide(x: i32, y: i32) -> Result<i32, String> {
    if y == 0 { Err("div-by-zero".to_string()) } else { Ok(x / y) }
}
```

**【关系网络】**:

- **蕴含**：Algebraic Effects ⊃ Effect Handlers（handlers 是实现机制）
- **等价（范畴论）**：Algebraic Effects ≅ Free Monad + Coproduct（在特定条件下）
- **互斥于**：Rust Ownership System（正交维度，见定理三）
- **细化**：Row Polymorphic Effects（Koka 的特定实现）

---

### 1.2 Affine Type（仿射类型）

**【定义】**:

线性类型（Linear Type）的松弛版本：资源可以被使用**零次或一次**，但不能被使用多次。Rust 的所有权系统基于仿射类型纪律，允许值被丢弃（drop）而不使用。

**【形式化描述】**:

在线性逻辑中，仿射逻辑移除 contraction 规则（A ⊢ A ⊗ A），但保留 weakening 规则（A ⊢ 1）。Rust 的 `let _ = x;` 允许丢弃值，对应 weakening；`let y = x; let z = x;` 被禁止（无 Copy trait 时），对应无 contraction。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 使用次数 | ≤ 1 | 最多使用一次 |
| 丢弃许可 | 是 | 可通过 drop 隐式丢弃 |
| 别名限制 | 严格 | &mut T 独占，&T 共享只读 |
| 运行时成本 | 零 | 纯编译期检查 |
| 与线性类型关系 | 超集 | 线性类型要求恰好使用一次 |

**【正例】**:

```rust
// Rust 仿射类型：String 只能 move 一次
fn affine_example() {
    let s = String::from("hello");
    let t = s;          // s 被 move 到 t
    // println!("{}", s); // ❌ 编译错误：s 已失效
    drop(t);            // 显式丢弃（隐式也可）
}
```

**【反例】**:

```rust
// 以下在纯线性类型语言中非法，但在 Rust 中合法（有 Copy trait）
fn not_affine() {
    let x = 42;         // i32 实现 Copy
    let y = x;
    let z = x;          // ✅ 合法：Copy 隐式克隆
    println!("{} {} {}", x, y, z);
}
// 反例说明：Rust 通过 Copy trait 突破了纯仿射纪律
```

**【关系网络】**:

- **父概念**：Substructural Type Systems（子结构类型系统）
- **兄弟概念**：Linear Type（线性类型，更严格）
- **实现于**：Rust Ownership System
- **对立于**：Unrestricted Types（无限制类型，如 Java 引用）

---

### 1.3 Borrow Checker（借用检查器）

**【定义】**:

Rust 编译器的核心组件，通过**流敏感（flow-sensitive）**和**非结构（non-lexical）**的生命周期分析，
在编译期验证所有借用（引用）遵守所有权纪律：任意时刻，对任何数据，要么存在一个可变引用，要么存在任意数量的不可变引用，二者不可兼得。

**【形式化描述】**:

根据 Oxide 形式化语义（Weiss et al., ICFP 2019），借用检查可建模为**分离逻辑（Separation Logic）**中的 frame rule：

```text
{ P } C { Q }
----------------  (Frame)
{ P * R } C { Q * R }
```

其中 `*` 是分离合取（separating conjunction），确保 C 只访问 P 中的资源，R 中的资源不受影响。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 分析粒度 | 流敏感 + 非词法 | 基于 MIR 数据流分析 |
| 别名关系 | 2-Mutable XOR N-Immutable | 核心不变量 |
| 证明机制 | 约束求解 | 生命周期约束图 |
| 错误报告 | 局部化 | 通常指向具体借用点 |
| 可判定性 | 是 | 多项式时间（近似） |

**【正例】**:

```rust
fn borrow_ok() {
    let mut v = vec![1, 2, 3];
    let r1 = &v;        // 不可变借用开始
    let r2 = &v;        // 第二个不可变借用：✅
    println!("{} {}", r1, r2);
    let r3 = &mut v;    // 可变借用：✅，因为 r1, r2 不再使用
    r3.push(4);
}
```

**【反例】**:

```rust
fn borrow_fail() {
    let mut v = vec![1, 2, 3];
    let r1 = &v;
    let r2 = &mut v;    // ❌ 编译错误：不能可变借用，因为 r1 仍有效
    println!("{}", r1); // 如果删除此行，r1 的生命周期提前结束，r2 合法
}
// 反例说明：非词法生命周期（NLL）允许在最后一次使用后重新借用
```

**【关系网络】**:

- **组成部分**：Lifetime System、Ownership System、Move Semantics
- **依赖**：MIR（中级中间表示）
- **验证于**：RustBelt（Iris 分离逻辑）、Oxide 操作语义
- **对比**：Region-Based Memory Management（Cyclone，Rust 的前身思想）

---

### 1.4 Capability（能力/权能）

**【定义】**:

在对象能力安全模型（Object Capability Security Model, Miller 2006）中，能力是对资源的不可伪造引用。
持有能力意味着拥有访问资源的权限；没有能力则无法访问。
Rust 的 `Send`、`Sync`、`'static` 等 auto trait 可视为**编译期能力**。

**【形式化描述】**:

能力模型声明：安全代码不应拥有**环境权威（ambient authority）**。
在 Rust 中，`unsafe` 块获得环境权威（可访问任意内存），而 safe 代码的能力受限于其持有的引用和 trait 实现。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 可传递性 | 是 | 能力可通过参数传递 |
| 不可伪造性 | 是 | 无法从无创建有 |
| 撤销难度 | 高 | 一旦分发难以撤销 |
| Rust 映射 | auto trait | Send/Sync/'static 作为类型级能力 |
| Scala 3 映射 | capture set | `^{Cap}` 显式能力标注 |

**【正例】**:

```rust
// Rust: Send 作为跨线程能力
fn spawn_thread<T: Send>(data: T) {
    std::thread::spawn(move || {
        process(data);  // 只有 T: Send 才能跨线程
    });
}

// Rc 不是 Send，因此不能跨线程
// let rc = Rc::new(42);
// spawn_thread(rc); // ❌ 编译错误：Rc<i32> 未实现 Send
```

**【反例】**:

```java
// Java: 环境权威（Ambient Authority）的反例
// 任何代码都可以访问文件系统，无需显式能力
public void readFile() {
    // 无需任何能力参数，直接获得环境权威
    Files.readString(Path.of("/etc/passwd"));
}
// 对比 Rust：需要显式传递能力（如文件描述符）
```

**【关系网络】**:

- **理论基础**：Object Capability Model (Miller 2006)
- **类型系统实现**：Scala 3 Capture Checking、Rust Auto Traits
- **安全保证**：Capability-safe code has no ambient authority
- **与 unsafe 关系**：unsafe 块获得临时环境权威

---

### 1.5 Carried Effect（可携带效应）

**【定义】**:

在 Rust 中，Carried Effect 是指在类型系统中有**具体 lowering 目标**的效应。
效应信息被"携带"在类型中，可通过 trait bound 进行泛化抽象。
Rust 的 `async` 和 `try` 是 carried effects。

**【形式化描述】**:

设 effect keyword κ，若存在类型构造器 T_κ 使得：

```text
κ fn foo() -> R   ⟹   fn foo() -> impl T_κ<Output = R>
```

则 κ 是 carried effect。typing judgement 为：

```text
Γ ⊢ e : τ @ κ   ⟹   Γ ⊢ e : T_κ<τ>
```

其中 @ 表示 effect annotation，在 Rust 中通过 desugaring 消除。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 类型实体 | 有 | 对应具体类型构造器 |
| 泛化能力 | 是 | 可通过 trait bound 抽象 |
| 组合方式 | trait 组合 | T: Future + Try 等 |
| 示例 | async, try, generators | 均有对应类型 |
| 反例 | const, unsafe | 无类型实体 |

**【正例】**:

```rust
// async 是 carried effect：有 Future 类型
async fn foo() -> i32 { 42 }
// desugaring 为：
// fn foo() -> impl Future<Output = i32> { async { 42 } }

// 可泛化抽象
async fn bar<T: Future>(f: T) -> T::Output {
    f.await
}
```

**【反例】**:

```rust
// const 不是 carried effect：无对应类型
const fn baz() -> i32 { 42 }
// 无法泛化：以下代码非法
// fn generic_const<T: Const>(f: T) -> T::Output { f() } // ❌
// 因为 const 没有 "Const" trait 或类型构造器
```

**【关系网络】**:

- **对立**：Uncarried Effect
- **实现机制**：Keyword Desugaring → Trait
- **组合性**：高（通过 trait bound）
- **与效应泛型关系**：Effect Generics 试图统一 carried/uncarried 的泛化

---

### 1.6 Continuation（续延）

**【定义】**:

计算的未来（the rest of the computation）。在代数效应系统中，当操作被调用时，当前计算的 continuation 被捕获并传递给 handler，handler 可选择恢复（resume）或丢弃（abort）该 continuation。

**【形式化描述】**:

在 CPS（Continuation Passing Style）中，每个表达式 e 的类型不是 τ 而是 (τ → ans) → ans。对于代数效应，操作调用 `op(v)` 捕获 continuation k，其语义为：

```text
op(v)  ⟹  λk. handle_op(v, k)
```

其中 handle_op 是 handler 定义的操作实现。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 捕获成本 | 高 | 需保存栈帧或堆分配 |
| 恢复次数 | 1+ | one-shot（OCaml 5）或 multi-shot（Koka） |
| 实现方式 | 栈复制 / segmented stack / CPS 转换 | 语言相关 |
| Rust 支持 | 无 | 零成本抽象禁止运行时捕获 |
| 与 async 关系 | 表面相似 | async 是编译期状态机，非运行时 continuation |

**【正例】**:

```koka
// Koka: multi-shot continuation
 effect choice
  ctl choice() : bool

fun choice-all(action : () -> <choice|e> a) : e list<a>
  with ctl choice()
    resume(False) ++ resume(True)  // 恢复两次！
  [action()]
```

**【反例】**:

```rust
// Rust: async/await 不是 continuation
async fn not_continuation() {
    let x = async { 42 }.await;  // 这不是捕获 continuation
    // .await 是状态机状态转换，无运行时栈捕获
}

// Rust 无法实现的 continuation 捕获：
// fn call_cc<F, R>(f: F) -> R
//   where F: FnOnce(Box<dyn FnOnce(i32) -> R>) -> R
// { /* 无法在不使用堆分配闭包的情况下实现 */ }
// 且即使实现，也违反零成本抽象
```

**【关系网络】**:

- **实现机制**：Call/cc (Scheme)、Delimited Continuation (shift/reset)、Effect Handlers
- **与 Monad 关系**：Continuation Monad 可表达所有效应，但效率低
- **与 Rust 关系**：被零成本抽象原则排除
- **子概念**：One-shot continuation、Multi-shot continuation

---

### 1.7 Effect Generics（效应泛型）

**【定义】**
Rust 语言设计的实验性提案（Keyword Generics Initiative），允许函数对 effect keyword 进行参数化，从而避免为每种效应组合（async/sync、const/non-const）编写重复代码。

**【形式化描述】**
设 effect keyword 集合 K = {async, const, try, ...}，效应泛型引入 kind 层级：

```text
fn foo<T, #[effect E: K]>() -> T
```

其中 E 是 effect variable，可在调用点实例化。typing rule：

```text
Γ, E: K ⊢ fn foo() -> T   Γ ⊢ foo[async]() : impl Future<Output = T>
```

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 提案状态 | 实验性 / 讨论中 | 非 RFC，属 initiative |
| 覆盖范围 | async, const（计划） | unsafe 被明确排除 |
| 语法形式 | `#[maybe(async)]`、`effect` 子句 | 多种提案竞争 |
| 实现难度 | 高 | 需修改类型系统 kind 层级 |
| 与 C++ 对比 | C++0x concepts 类似 | 但针对 effect keywords |

**【正例】**:

```rust
// 效应泛型提案示例（概念性语法）
fn read_to_string(path: &str) -> io::Result<String>
    effect async, const
{
    if const {
        Ok(include_str!(path).to_string())
    } else if async {
        let mut file = File::open(path).await?;
        let mut s = String::new();
        file.read_to_string(&mut s).await?;
        Ok(s)
    } else {
        let mut file = File::open(path)?;
        let mut s = String::new();
        file.read_to_string(&mut s)?;
        Ok(s)
    }
}
```

**【反例】**:

```rust
// unsafe 被明确排除在效应泛型之外
// 以下不成立：
// fn foo<T>() -> T
//     effect unsafe  // ❌ 语义错误
// { unsafe { ... } }
// 原因：unsafe 不是 effect，它是 meta-effect（解除保证）

// 效应泛型无法解决以下问题：
// async 和 sync 的 trait bound 差异
// async fn 返回 impl Future，普通 fn 不返回
// 这导致 trait 定义需要重复
```

**【关系网络】**:

- **解决目标**：Effect Mismatch Problem（API 重复）
- **依赖**：Carried Effects（仅对 carried 有效）
- **排除**：Uncarried Effects（const 部分支持，unsafe 完全排除）
- **对比**：C++0x Concepts、Haskell Type Classes（多参数）

---

### 1.8 Effect Handler（效应处理器）

**【定义】**:
代数效应的实现机制。handler 为 effect signature 中的每个操作提供具体实现，捕获操作的 continuation，并可选择恢复、丢弃或多次恢复该 continuation。

**【形式化描述】**:
Plotkin & Pretnar (2013) 的形式化：给定 effect theory (Σ, E)，handler 是代数态射 h: T_Σ(A) → B，其中 T_Σ 是 Σ 上的自由 monad。handler 由返回子句（return clause）和操作子句（operation clauses）组成。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 作用域 | 词法界定（delimited） | `with handler { ... }` |
| 组合性 | 高 | 可嵌套组合多个 handlers |
| 捕获类型 | one-shot / multi-shot | 语言设计选择 |
| 运行时成本 | 中 | 需 evidence passing 或栈操作 |
| Rust 等效 | 无 | 无通用 handler 机制 |

**【正例】**:

```koka
// Koka: 组合多个 handlers
fun state-raise(init : int) : div (maybe<int>, int)
  with pstate(init)      // state handler
  with raise-maybe       // exception handler
  no-odds()             // 被双重包裹的代码

// 类型自动推导：
// no-odds : () -> <raise,state<int>,div> int
// state-raise : (init : int) -> div (maybe<int>, int)
```

**【反例】**:

```rust
// Rust: 无 effect handler，只能手动模拟
// 模拟异常 handler（笨拙且不可组合）：
fn manual_handler<T>(
    action: impl FnOnce() -> Result<T, String>,
    handler: impl FnOnce(String) -> T
) -> T {
    match action() {
        Ok(v) => v,
        Err(e) => handler(e)
    }
}

// 对比 Koka：无法嵌套组合多个 handler
// 无法自动推导类型，无法捕获 continuation
```

**【关系网络】**:

- **理论基础**：Plotkin & Pretnar (2013)
- **实现于**：Koka、Eff、OCaml 5、Multicore OCaml
- **编译策略**：Evidence Passing (Koka)、Stack Copying (Leijen C impl)、Segmented Stacks (OCaml 5)
- **与 Monad 关系**：Handler ≅ Free Monad 的解释（interpretation）

---

### 1.9 Effect Mismatch（效应不匹配）

**【定义】**
Rust 中由于效应不可泛化导致的 API 重复问题。同一算法需为 sync/async、const/non-const、try/non-try 分别实现，造成代码膨胀（code duplication）。

**【形式化描述】**
设函数 f 的逻辑与效应无关，但 Rust 的类型系统要求：

```text
f_sync  : T -> R
f_async : T -> impl Future<Output = R>  // 无法从 f_sync 派生
f_const : const fn(T) -> R               // 无法从 f_sync 派生
```

效应不匹配度量：对 n 个独立效应关键字，可能需要 2ⁿ 个 API 变体。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 影响范围 | 标准库、异步生态 | 广泛存在 |
| 根本原因 | Uncarried effects 不可泛化 | 类型系统断层 |
| 临时方案 | 宏（macro）生成 | 如 tokio::pin!、futures::try_join! |
| 长期方案 | Effect Generics | 语言级解决 |
| 严重程度 | 高 | 被社区广泛认为是主要痛点 |

**【正例】**:

```rust
// 标准库中的效应不匹配：Iterator vs AsyncIterator
// 同步迭代器（稳定）
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}

// 异步迭代器（不稳定，单独 trait）
trait AsyncIterator {
    type Item;
    fn next(&mut self) -> impl Future<Output = Option<Self::Item>>;
}

// 同一算法需实现两次：
fn sum_sync<I: Iterator>(iter: I) -> i32 { /* ... */ }
async fn sum_async<I: AsyncIterator>(iter: I) -> i32 { /* 几乎相同逻辑 */ }
```

**【反例】**:

```koka
// Koka: 无效应不匹配，迭代器天然支持异步
fun sum( xs : list<int> ) : total int
  match xs
    Cons(x, xx) -> x + sum(xx)
    Nil         -> 0

// 同一函数可在 async 上下文中使用，无需重写
// 因为 async 只是 effect，不改变函数签名结构
```

**【关系网络】**:

- **症状**：API Duplication、Trait Multiplication
- **原因**：Carried vs Uncarried 断层、缺乏 Effect Polymorphism
- **解决方案**：Effect Generics、Keyword Generics
- **对比**：Koka 的 Row Polymorphism 天然避免此问题

---

### 1.10 Lifetime（生命周期）

**【定义】**:
Rust 中引用有效的作用域标注。生命周期 `'a` 是一个**区域（region）**——程序执行中的一段代码范围。借用检查器通过约束求解验证所有引用在其生命周期内始终有效。

**【形式化描述】**:
在 Oxide 形式化语义中，生命周期是**抽象位置（abstract locations）**的集合。typing rule：

```text
Γ ⊢ &x : &'a T    iff    lifetime(x) ⊇ 'a
```

即引用的生命周期不能超过被引用数据的生命周期。约束求解通过**区域推断图（region inference graph）**实现。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 表示法 | 区域变量 | 'a, 'static |
| 推断方式 | 约束求解 | 基于 Hindley-Milner 扩展 |
| 与所有权关系 | 借用约束 | 借用必须短于所有者 |
| 运行时存在 | 无 | 纯编译期概念 |
| 与 GC 对比 | 静态替代 | 编译期证明而非运行时回收 |

**【正例】**:

```rust
// 显式生命周期标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
// 约束：返回的生命周期 ≤ x 的生命周期 ∩ y 的生命周期

// 隐式生命周期推断
fn implicit() {
    let s1 = String::from("hello");
    let r1 = &s1;  // 自动推断 'a = s1 的作用域
}
```

**【反例】**:

```rust
// 悬垂引用（Dangling Reference）
fn dangle() -> &String {  // ❌ 编译错误
    let s = String::from("hello");
    &s  // s 在函数结束时 drop，但引用试图返回
}

// 反例说明：生命周期系统阻止了 use-after-free
// 在 C++ 中，这是未定义行为：
// std::string& dangle() {
//     std::string s = "hello";
//     return s;  // 悬垂引用，编译器可能仅警告
// }
```

**【关系网络】**:

- **组成部分**：Region Inference、Constraint Solving、Borrow Checker
- **理论基础**：Region-Based Memory Management (Tofte & Talpin, 1994)
- **实现于**：Rust、Cyclone、ATS
- **与 Ownership 关系**：Lifetime 是 Borrowing 的约束条件

---

### 1.11 Linear Type（线性类型）

**【定义】**:
子结构类型系统（substructural type system）的一种，要求资源必须被**恰好使用一次**——既不能被丢弃（无 weakening），也不能被复制（无 contraction）。
Rust 的所有权系统受线性类型启发，但通过 Copy/Drop trait 放松了严格性。

**【形式化描述】**:
在线性逻辑（Girard, 1987）中，线性类型对应逻辑连接词 ⊗（tensor）、⅋（par）、!（exponential）。线性类型系统的 typing rule：

```text
Γ, x: A ⊢ e : B    x 在 e 中恰好出现一次
-----------------------------------------
Γ ⊢ λx.e : A ⊸ B
```

其中 ⊸ 是线性蕴含（lollipop）。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 使用次数 | = 1 | 恰好一次 |
| 丢弃许可 | 否 | 无 weakening |
| 复制许可 | 否 | 无 contraction |
| Rust 映射 | Affine + Copy/Drop | Rust 是线性类型的实用主义松弛 |
| 语言实现 | Clean、Linear Haskell、Granule | 学术研究为主 |

**【正例】**:

```granule
-- Granule 语言：纯线性类型
swap : forall a b. (a, b) -> (b, a)
swap (x, y) = (y, x)
-- x 和 y 各使用一次，符合线性纪律

-- 以下非法：
-- drop : forall a. a -> ()
-- drop x = ()  -- 需要显式线性丢弃操作
```

**【反例】**:

```rust
// Rust 不是纯线性类型：允许丢弃和复制（通过 trait）
fn not_linear() {
    let s = String::from("hello");
    drop(s);        // 显式丢弃：线性类型不允许，但 Rust 允许

    let x = 42;
    let y = x;
    let z = x;      // 复制：线性类型不允许，但 i32: Copy
}
```

**【关系网络】**:

- **父概念**：Substructural Type Systems
- **子概念**：Affine Type（Rust 使用）、Relevant Type
- **理论基础**：Linear Logic (Girard, 1987)
- **与 Ownership 关系**：Ownership 是线性类型的工程松弛版本

---

### 1.12 Meta-Effect（元效应）

**【定义】**:
作用于类型系统本身的效应，而非计算与环境的交互。Rust 的 `unsafe` 是典型元效应：它不追踪某种可观察行为，而是**解除编译器的保证**，允许程序员手动维护不变量。

**【形式化描述】**:
设类型系统保证集合 G = {内存安全、线程安全、类型安全}，meta-effect κ_meta 的语义是：

```text
Γ ⊢ unsafe { e } : τ   iff   Γ ⊢ e : τ  在 G' ⊂ G 下成立
```

其中 G' 是放宽后的保证子集。`unsafe` 将证明责任从编译器转移给程序员。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 作用对象 | 类型系统自身 | 解除保证而非追踪交互 |
| 可观察性 | 无 | 不对应任何运行时行为 |
| 类型实体 | 无 | 无对应类型构造器 |
| 证明责任 | 程序员 | 需手动维护安全不变量 |
| 与 effect 关系 | 正交 | unsafe 不是 effect，是 meta-effect |

**【正例】**:

```rust
// unsafe 作为元效应：解除借用检查器约束
unsafe fn raw_pointer_ops() {
    let mut x = 5;
    let r = &mut x as *mut i32;
    *r.offset(1) = 42;  // 编译器无法验证此操作的安全性
}
// 程序员保证：offset(1) 在有效内存范围内
```

**【反例】**:

```rust
// 错误理解：将 unsafe 视为普通 effect
// 以下思考方式错误：
// "unsafe fn 具有 'unsafe effect'，可以被 handler 捕获"
// 实际上：unsafe 无类型，不可泛化，不可组合

// 对比：如果 unsafe 是普通 effect，以下应成立：
// fn foo<T: Effect>() -> T  // 不适用于 unsafe
// unsafe 被明确排除在 Effect Generics 之外
```

**【关系网络】**:

- **对比**：Algebraic Effects（追踪可观察交互）
- **实现机制**：Compiler Directive（编译器指令）
- **验证工具**：Miri（动态检测）、Kani（模型检查）、Safety-Tags（标注）
- **与 Capability 关系**：unsafe 块获得临时环境权威

---

### 1.13 Ownership（所有权）

**【定义】**:
Rust 的核心内存管理纪律：每个值有且仅有一个所有者（owner）；当所有者离开作用域，值被自动释放（drop）。所有权可通过 move 转移，或通过 borrow 临时共享。

**【形式化描述】**:
根据 RustBelt（Jung et al., POPL 2018），所有权在 Iris 分离逻辑中建模为**资源（resource）**：

```text
own(x, T)  ≜  ∃v. x ↦ v * T(v)
```

其中 `x ↦ v` 表示位置 x 存储值 v，`T(v)` 是值 v 的类型断言。Move 语义对应资源的所有权转移：

```text
own(x, T) ⊢ own(y, T)   // 将 x 的资源转移给 y
```

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 唯一性 | 是 | 任意时刻只有一个所有者 |
| 转移方式 | move | 默认语义 |
| 复制方式 | clone / Copy | 显式或隐式（trait 控制） |
| 释放时机 | 作用域结束 | RAII（Resource Acquisition Is Initialization） |
| 借用许可 | 是 | &T（共享）、&mut T（独占） |

**【正例】**:

```rust
fn ownership_demo() {
    let s1 = String::from("hello");  // s1 是所有者
    let s2 = s1;                      // 所有权 move 到 s2
    // println!("{}", s1);            // ❌ s1 已失效

    let r1 = &s2;                     // 借用 s2（不转移所有权）
    let r2 = &s2;                     // 多个共享借用：✅
    println!("{} {}", r1, r2);        // s2 仍有效

    drop(s2);                         // 显式释放（也可隐式）
}
```

**【反例】**:

```cpp
// C++：所有权不明确的反例
void cpp_ownership() {
    std::string* s1 = new std::string("hello");
    std::string* s2 = s1;  // 仅复制指针，非所有权转移
    delete s1;               // s1 释放内存
    // std::cout << *s2;   // ❌ use-after-free，未定义行为
}
// C++ 无编译期所有权检查，需依赖程序员约定或智能指针

// Rust 中相同模式被阻止：
// let s1 = String::from("hello");
// let s2 = &s1;
// drop(s1);  // ❌ 编译错误：s1 仍被 s2 借用
```

**【关系网络】**:

- **理论基础**：Linear Logic、Region-Based Memory Management、Affine Types
- **实现机制**：Borrow Checker、Move Semantics、RAII
- **验证工具**：RustBelt (Iris)、Oxide、Stacked/Tree Borrows
- **与 GC 对比**：编译期确定性释放 vs 运行时垃圾回收
- **与 Effect System 关系**：正交（定理三）

---

### 1.14 Row Polymorphism（行多态）

**【定义】**:
记录（record）或效应（effect）的类型多态形式，允许类型/效应集合是**开放的（open）**。
Koka 使用行多态表示效应集合：函数类型 `() -> <console,state|e> int` 表示函数需要 `console` 和 `state` 效应，以及任意其他效应 `e`。

**【形式化描述】**:
行多态的类型规则：

```text
Γ ⊢ e : τ @ <l₁:τ₁, ..., lₙ:τₙ | ρ>
-----------------------------------
Γ ⊢ e : τ @ <l₁:τ₁, ..., lₙ:τₙ, lₙ₊₁:τₙ₊₁ | ρ'>
```

其中 ρ 是行变量（row variable），允许扩展。效应组合通过行的并集实现。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 开放性 | 是 | 效应集合可扩展 |
| 组合方式 | 行并集 | <console|e> ∪ <state|e'> = <console,state|e''> |
| 实现语言 | Koka、Eff、Links | 学术研究语言 |
| Rust 支持 | 无 | Rust 无行多态 |
| 与 Trait 对比 | 正交 | Trait 是 nominal subtyping，行多态是 structural |

**【正例】**:

```koka
// Koka: 行多态效应类型
fun hello() : console ()
  println("hello")

fun greet() : <console,state<int>|e> ()
  hello()           // ✅ 合法：console ⊂ <console,state|e>
  val count := 1   // state 操作
```

**【反例】**:

```rust
// Rust: 无行多态，效应不可扩展
// 无法实现以下类型：
// fn hello() -> <console> ()  // ❌ Rust 无 effect 类型语法
// fn greet() -> <console, state> ()  // ❌

// Rust 的替代方案（笨拙）：
trait Console { fn println(&self); }
trait State<T> { fn get(&self) -> T; fn set(&self, v: T); }
// 需要为每种组合定义新 trait，或依赖复杂的 associated type
```

**【关系网络】**:

- **理论基础**：Rémy (1994) 记录多态扩展至效应
- **实现于**：Koka、Eff、Links、Grace
- **与 Effect System 关系**：Row Polymorphism 是 Effect System 的一种实现策略
- **与 Rust 关系**：Rust 的 trait bound 是 nominal，无法表达开放效应集合

---

### 1.15 Uncarried Effect（不可携带效应）

**【定义】**:
在 Rust 中，Uncarried Effect 是指在类型系统中**无具体 lowering 目标**的效应。
效应信息仅作为编译器内部修饰符传递，不进入类型系统的可组合层。
`const` 和 `unsafe` 是 uncarried effects。

**【形式化描述】**
设 effect keyword κ，若不存在类型构造器 T_κ 使得 κ fn 可 desugar 为返回 T_κ 的普通函数，则 κ 是 uncarried。typing judgement 为：

```text
Γ ⊢ e : τ @ κ   ⟹   Γ ⊢ e : τ   (κ 被擦除，不进入类型)
```

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 类型实体 | 无 | 不对应具体类型 |
| 泛化能力 | 否 | 无法通过 trait bound 抽象 |
| 组合方式 | 无 | 不可高阶组合 |
| 示例 | const, unsafe | 仅编译器内部标记 |
| 与 carried 关系 | 互补 | 共同构成 Rust 的效应分类 |

**【正例】**:

```rust
// const 是 uncarried：无 const 类型
const fn add(a: i32, b: i32) -> i32 { a + b }
// 无法抽象：
// fn generic<T: ConstFn>(f: T) -> i32 { f(1, 2) } // ❌

// unsafe 是 uncarried：无 unsafe 类型
unsafe fn raw_read(ptr: *const i32) -> i32 { *ptr }
// 无法抽象：
// fn generic<T: UnsafeFn>(f: T) -> i32 { f(ptr) } // ❌
```

**【反例】**:

```rust
// 如果 const 是 carried，以下应成立：
// trait ConstFn<Args> { type Output; fn call_const(args: Args) -> Self::Output; }
// impl<A,B,R> ConstFn<(A,B)> for fn(A,B) -> R { ... }
// 实际上 Rust 无此机制，const fn 和普通 fn 在类型层面无区别

// 反例说明：const fn 和普通 fn 的类型完全相同：
const fn foo() -> i32 { 42 }
fn bar() -> i32 { 42 }
// foo 和 bar 的类型都是 fn() -> i32，const 信息不在类型中
```

**【关系网络】**:

- **对立**：Carried Effect
- **导致问题**：Effect Mismatch（API 重复）
- **解决方案**：Effect Generics（部分解决，unsafe 被排除）
- **与类型系统关系**：暴露类型系统的表达能力缺口

---

### 1.16 Zero-Cost Abstraction（零成本抽象）

**【定义】**:
Rust 的核心设计原则：高级抽象（如迭代器、闭包、trait 对象、async/await）在编译后应产生与手写底层代码**同等性能**的机器码。
抽象不应引入运行时开销。

**【形式化描述】**:
设抽象 A 和手写实现 M，零成本抽象要求：

```text
∀program P.  time(P[A]) ≈ time(P[M])  ∧  space(P[A]) ≈ space(P[M])
```

其中 "≈" 表示在常数因子内等价。Rust 通过 monomorphization（单态化）、内联（inlining）、LLVM 优化实现此目标。

**【核心属性】**:

| 属性 | 值 | 说明 |
|------|-----|------|
| 运行时开销 | 零 | 无额外分配、无虚函数、无装箱 |
| 编译时开销 | 高 | 单态化导致代码膨胀、编译慢 |
| 优化依赖 | LLVM | 重度依赖编译器优化 |
| 与 C++ 对比 | 类似 | C++ 模板也是零成本 |
| 与 Java 对比 | 根本不同 | Java 泛型擦除引入装箱开销 |

**【正例】**:

```rust
// 迭代器链是零成本抽象
let sum: i32 = (0..100)
    .filter(|x| x % 2 == 0)
    .map(|x| x * 2)
    .sum();
// 编译后等价于手写循环，无中间集合分配

// async/await 是零成本抽象
async fn foo() -> i32 { 42 }
// 编译为状态机，无运行时调度器开销
```

**【反例】**:

```java
// Java：泛型不是零成本
List<Integer> list = new ArrayList<>();
list.add(42);  // 装箱：int -> Integer（堆分配）
// 对比 Rust：Vec<i32> 无装箱

// C++：虚函数不是零成本
class Base { virtual int foo() { return 42; } };
class Derived : public Base { int foo() override { return 43; } };
Base* b = new Derived();
b->foo();  // vtable 间接调用，无法内联
// 对比 Rust：trait bound 单态化可内联
```

**【关系网络】**:

- **与 Effect System 关系**：零成本抽象排除运行时 continuation 捕获
- **与 GC 关系**：零成本抽象要求无 GC 暂停
- **与 Monomorphization 关系**：零成本的实现机制
- **与 C++ 关系**：继承自 C++ 模板哲学，但更安全

---

## 第二章：形式化语义基础

### 2.1 操作语义（Operational Semantics）

#### 2.1.1 Rust 的 Oxide 形式化语义

Oxide（Weiss et al., ICFP 2019）提供了 Rust 的完整操作语义。核心判断形式：

```text
Σ; Δ; Γ ⊢ e : τ ~> ι
```

其中：

- Σ：结构体/枚举声明环境
- Δ：生命周期约束环境
- Γ：变量类型环境
- e：表达式
- τ：Rust 表面类型
- ι：内部类型（包含生命周期信息）

**核心规则：Move**:

```text
Σ; Δ; Γ, x: ι₁ ⊢ x : ι₂ ~> ι₂    (ι₁ = ι₂, x 被消费)
---------------------------------------------------
Σ; Δ; Γ, x: ι₁ ⊢ x : ι₂ ~> ι₂    (x 从环境中移除)
```

**核心规则：Borrow**:

```text
Σ; Δ; Γ, x: ref(ρ, τ) ⊢ &x : &'ρ τ ~> &'ρ τ
---------------------------------------------------
Σ; Δ; Γ, x: ref(ρ, τ) ⊢ &x : &'ρ τ ~> &'ρ τ
```

#### 2.1.2 Koka 的 Evidence Passing 语义

Koka 编译器将 effect handlers 编译为**证据传递（evidence passing）**风格：

```text
with handler { op(v) -> e₁ } e₂
```

编译为：

```text
let h = { op = λv k. e₁ } in
evidence_pass(h, e₂)
```

其中 evidence 是 handler 的指针向量，操作调用通过常量时间查找定位 handler，而非线性搜索。

### 2.2 类型规则（Typing Rules）

#### 2.2.1 Rust 的 async/await 类型规则

```text
Γ ⊢ e : T    T: Future
--------------------------- (Await)
Γ ⊢ e.await : T::Output

Γ ⊢ e : τ
--------------------------- (Async)
Γ ⊢ async { e } : impl Future<Output = τ>
```

#### 2.2.2 Koka 的 Effect Handler 类型规则

```text
Γ ⊢ e : τ @ <op: A → B, E>    Γ, x: A, k: B → τ @ E ⊢ e_h : τ @ E
-------------------------------------------------------------------- (Handle-Op)
Γ ⊢ with { op(x) -> e_h } e : τ @ E

Γ ⊢ e : τ @ E
--------------------------- (Handle-Return)
Γ ⊢ with { return(x) -> e_r } e : τ' @ E    (若 x: τ ⊢ e_r : τ' @ E)
```

### 2.3 范畴论语义（Categorical Semantics）

#### 2.3.1 Monad 的 Kleisli 三元组

在范畴 **C** 上，Monad (T, η, μ) 满足：

- T: C → C（自函子）
- η: Id ⇒ T（单位自然变换）
- μ: T² ⇒ T（乘法自然变换）
- 结合律：μ ∘ Tμ = μ ∘ μT
- 单位律：μ ∘ Tη = μ ∘ ηT = id

Haskell 的 `>>=`（bind）对应 Kleisli 组合：

```text
(>=>) : (A → T B) → (B → T C) → (A → T C)
f >=> g = λa. f a >>= g
```

#### 2.3.2 Algebraic Effects 的 Lawvere 理论

代数效应由**签名（signature）**Σ = { opᵢ: Aᵢ → Bᵢ } 和**方程（equations）**E 组成。
在范畴论中，这是**代数理论（algebraic theory）**的表示：

- 载体对象 C
- 操作 [opᵢ]: Cᴬⁱ × Aᵢ → Cᴮⁱ
- 满足方程 E

Plotkin & Power 证明：计算效应 = 对自由模型的计算。

#### 2.3.3 Ownership 的分离逻辑语义

在 Iris（高阶分离逻辑）中，Rust 的所有权断言：

```text
PointsTo(l, v)  ≜  l ↦ v
Own(x, T)      ≜  ∃v. x ↦ v * T(v)
Borrow(x, 'a)  ≜  ∃v. x ↦ v * (v 在 'a 内只读)
MutBorrow(x, 'a) ≜  ∃v. x ↦ v * (v 在 'a 内独占)
```

**Frame Rule**（框架规则）：

```text
{ P } C { Q }
----------------
{ P * R } C { Q * R }
```

这是局部推理（local reasoning）的基础：可在不改变 C 的情况下扩展资源上下文。

---

## 第三章：历史演进深化谱系

### 3.1 完整历史时间线（1936-2026）

| 年份 | 领域 | 里程碑 | 对 Rust 效应系统的影响 |
|------|------|--------|----------------------|
| 1936 | 计算理论 | Church λ演算 / Turing 机 | 函数式与命令式计算的奠基 |
| 1968 | 结构化编程 | Dijkstra "GOTO Statement Considered Harmful" | 控制流结构化的思想源头 |
| 1973 | 类型理论 | ML 类型推断（Milner） | Hindley-Milner 类型系统 |
| 1987 | 线性逻辑 | Girard 线性逻辑 | 资源敏感类型的理论基础 |
| 1988 | 效应系统 | Lucassen & Gifford, FX 语言 | **效应系统的诞生** |
| 1989 | 范畴论语义 | Moggi "Computational Lambda-Calculus and Monads" | Monad 作为计算效应的数学基础 |
| 1990 | 线性类型 | Wadler 线性类型论文 | Rust Ownership 的直接理论祖先 |
| 1991 | 区域内存 | Tofte & Talpin, Region-Based Memory Management | Rust 生命周期的理论祖先 |
| 1994 | 行多态 | Rémy 记录多态 | Koka 效应类型的基础 |
| 1995 | 异常处理 | Java Checked Exceptions | 效应追踪的工业尝试（反例） |
| 1998 | 能力安全 | Miller 对象能力模型 | Rust unsafe 边界的理论参考 |
| 2003 | 代数效应 | Plotkin & Power, "Algebraic Operations and Generic Effects" | **代数效应理论奠基** |
| 2006 | 对象能力 | Miller, "Robust Composition" | 能力安全模型的完善 |
| 2009 | Eff 语言 | Pretnar, Eff 语言发布 | 第一个纯代数效应语言 |
| 2010 | Rust 诞生 | Rust 0.1 发布 | Graydon Hoare 的 side project |
| 2012 | Koka | Leijen, Koka v1 发布 | 行多态效应类型的工业实现 |
| 2013 | 效应处理器 | Plotkin & Pretnar, "Handling Algebraic Effects" | **效应处理器理论完善** |
| 2015 | Rust 1.0 | 稳定版发布 | 所有权系统进入工业 |
| 2017 | RustBelt | Jung et al., POPL 2018 | Rust 形式化验证的里程碑 |
| 2018 | async/await | Rust 稳定化 async/await | Carried Effect 的工业实现 |
| 2019 | Oxide | Weiss et al., ICFP 2019 | Rust 的完整操作语义 |
| 2020 | OCaml 5 | Multicore OCaml 合并 | 工业语言的代数效应尝试 |
| 2021 | Keyword Generics | Rust 官方 Initiative 提出 | 效应泛型的起点 |
| 2022 | Verus | SOSP 2024 发表 | Rust 实用验证基础 |
| 2023 | Tree Borrows | Villani et al. | 别名模型 v2 |
| 2024 | Scala 3 | Capture Checking 稳定 | 能力系统的另一种工业路径 |
| 2024 | Asterinas | USENIX ATC 2025 | Rust OS 内核验证 |
| 2025 | UnsafeCop | arXiv 2025 | BMC 验证 unsafe 代码 |
| 2025 | Safety-Tags | Rust for Linux Pre-RFC | 内核安全标注 |
| 2025 | TrustInSoft | Rust Analyzer 发布 | 穷尽静态分析 |
| 2026 | Effect Generics | RFC 讨论中 | Rust 效应系统的未来 |

---

## 第四章：Rust 五种效应的完整分析

### 4.1 async —— 控制流效应的典范

**【定义】** 函数可挂起（suspend）并在稍后恢复，通过 Future trait 实现协作式多任务。

**【Lowering 路径】**（详见图3）

```text
async fn foo() -> T
  ↓ desugar
fn foo() -> impl Future<Output = T>
  ↓ state machine generation
enum __Foo { Start, State1, State2, ..., Done }
  ↓ MIR
match self.__state { 0 => ..., 1 => ..., ... }
  ↓ LLVM IR
switch i8 %state, label %Start, label %State1, ...
  ↓ x86_64
jmpq *.LJTI0_0(,%rax,8)
```

**【形式化语义】**

```text
Γ ⊢ e : T
-----------------------------------
Γ ⊢ async { e } : impl Future<Output = T>

Γ ⊢ e : impl Future<Output = T>
-----------------------------------
Γ ⊢ e.await : T
```

**【与 Koka 对比】**

| 维度 | Rust async | Koka async (库实现) |
|------|-----------|---------------------|
| 实现方式 | 编译器内置 | 用户库（数百行代码） |
| 类型 | impl Future | async effect + handler |
| 调度器 | 外部（tokio/async-std） | 内置或用户定义 |
| 零成本 | 是 | 否（evidence passing 开销） |
| 组合性 | 低（Future trait bound） | 高（effect row 组合） |

### 4.2 unsafe —— 元效应的独例

**【定义】** 解除编译器的安全保证，将证明责任转移给程序员。

**【形式化边界】**

```text
unsafe fn foo() -> T   ⟹   fn foo() -> T  (在放宽的保证集 G' 下)
unsafe { e }           ⟹   e  (在 G' 下)
```

**【三层不变量】**（基于 arXiv 2026 系统分析）

| 不变量 | 定义 | 维护责任 | 验证工具 |
|--------|------|----------|----------|
| 有效性（Validity） | 类型实例满足内部约束 | 类型系统 + unsafe 作者 | Miri, Sanitizer |
| 安全性（Safety） | Safe API 调用的前置条件 | unsafe 块作者 | Kani, Verus, Safety-Tags |
| 对齐（Alignment） | 指针指向正确对齐地址 | 硬件/ABI | 所有工具 |

**【反例：unsafe 的误用】**

```rust
// 反例 1：未维护安全不变量
unsafe fn bad_deref(ptr: *const i32) -> i32 {
    *ptr  // 未验证 ptr 非空且对齐
}

// 反例 2：safe API 暴露内部 unsafe 的不变量破坏
pub fn safe_wrapper(v: &mut Vec<i32>) {
    let ptr = v.as_mut_ptr();
    unsafe {
        *ptr.offset(100) = 42;  // 可能越界，但 safe 函数签名不暴露风险
    }
}
```

### 4.3 const —— 阶段效应的困境

**【定义】** 编译期求值（Compile-Time Function Evaluation, CTFE），函数可在编译期执行。

**【形式化描述】**

```text
const fn foo() -> T   ⟹   foo() 在编译期求值为常量值
```

**【与 C++ constexpr 对比】**

| 维度 | Rust const | C++ constexpr |
|------|-----------|---------------|
| 求值时机 | 编译期 | 编译期或运行期 |
| 确定性 | 必须纯函数 | 可包含未定义行为（C++20 前） |
| 递归限制 | 有 | 有（实现定义） |
| trait 支持 | 不稳定 | C++20 concepts |
| 与类型系统关系 | Uncarried | 类似 uncarried |

**【反例：const 的局限性】**

```rust
// const 无法使用 trait 方法（截至 2025 年仍不稳定）
const fn max(a: i32, b: i32) -> i32 {
    // a.max(b)  // ❌ 不稳定：const trait 调用
    if a > b { a } else { b }
}

// const 无法分配堆内存
const fn make_vec() -> Vec<i32> {
    // vec![1, 2, 3]  // ❌ 编译错误：const 上下文禁止堆分配
    unimplemented!()
}
```

### 4.4 try —— 可失败性的类型化

**【定义】** 通过 `?` 运算符和 `Try` trait 传播错误，desugar 为 `Result` 或 `Option` 的组合。

**【Lowering 规则】**

```text
e?   ⟹   match e {
    Ok(v) => v,
    Err(e) => return Err(From::from(e)),
}
```

**【与 Java Checked Exceptions 对比】**

| 维度 | Rust try (`?`) | Java Checked Exceptions |
|------|---------------|------------------------|
| 类型追踪 | 是（Result 类型） | 是（throws 子句） |
| 组合性 | 高（Try trait） | 低（需捕获或声明） |
| 零成本 | 是 | 否（栈展开开销） |
| 与泛型关系 | 良好 | 差（与泛型不兼容） |
| 反模式 | 过度使用 `?` 丢失上下文 | 过度使用 try-catch |

### 4.5 generators —— 不稳定的多重性效应

**【定义】** 通过 `yield` 产生多个值，编译为状态机协程。

**【状态机 lowering】**

```rust
|| {
    yield 1;
    yield 2;
    yield 3;
}
// desugar 为：
enum __Gen {
    Start,
    State1,
    State2,
    Done,
}
```

**【与 async 的关系】**
async/await 本质上是 generator 的特例：Future 是只 yield 一次的 generator。

---

## 第五章：跨语言代码示例对比矩阵

### 5.1 异常处理对比

| 语言 | 代码示例 | 效应模型 | 类型追踪 | 运行时成本 |
|------|---------|----------|----------|-----------|
| **Rust** | `fn div(x: i32, y: i32) -> Result<i32, String> { if y == 0 { Err("div0") } else { Ok(x/y) } }` | Carried (Result) | 是 | 零（无栈展开） |
| **Koka** | `fun safe-divide(x: int, y: int) : raise int { if y == 0 then raise("div0") else x / y }` | Algebraic Effect | 是 | 中（evidence） |
| **Haskell** | `safeDivide :: Int -> Int -> Either String Int; safeDivide x y = if y == 0 then Left "div0" else Right (x`div`y)` | Monad (Either) | 是 | 高（thunk） |
| **Java** | `int divide(int x, int y) throws ArithmeticException { if (y == 0) throw new ArithmeticException("div0"); return x / y; }` | Checked Exception | 是 | 高（栈展开） |
| **C++** | `int divide(int x, int y) { if (y == 0) throw std::runtime_error("div0"); return x / y; }` | Exception | 否（类型签名不强制） | 高（栈展开） |
| **OCaml 5** | `let safe_divide x y = match y with 0 -> raise (Failure "div0") | _ -> x / y` | Dynamic Effect | 否（类型不追踪） | 中（fiber） |

### 5.2 异步编程对比

| 语言 | 代码示例 | 调度模型 | 零成本 | 组合性 |
|------|---------|----------|--------|--------|
| **Rust** | `async fn fetch(url: &str) -> Result<String, Error> { let resp = reqwest::get(url).await?; Ok(resp.text().await?) }` | 外部调度器（tokio） | 是 | 中（Future trait） |
| **Koka** | `fun fetch(url: string) : async string { val resp = await http_get(url); resp.body }` | 用户定义 handler | 否 | 高（effect row） |
| **Haskell** | `fetch :: String -> IO String; fetch url = do { resp <- httpGet url; body <- responseBody resp; return body }` | 绿色线程 + 运行时 | 否 | 高（Monad） |
| **Java** | `CompletableFuture<String> fetch(String url) { return CompletableFuture.supplyAsync(() -> { ... }); }` | 线程池 | 否 | 低（回调地狱） |
| **C++20** | `std::future<std::string> fetch(std::string url) { return std::async(std::launch::async, [=]() { ... }); }` | 线程池 | 否 | 低 |
| **Swift** | `func fetch(url: String) async throws -> String { let resp = try await URLSession.shared.data(from: url); return String(data: resp.0) }` | 结构化并发 | 低 | 中 |

### 5.3 状态管理对比

| 语言 | 代码示例 | 突变追踪 | 别名安全 | 组合性 |
|------|---------|----------|----------|--------|
| **Rust** | `fn counter(start: i32) -> impl FnMut() -> i32 { let mut count = start; move || { count += 1; count } }` | &mut T | 编译期保证 | 低 |
| **Koka** | `fun counter(init: int) : <state<int>> int { val count := init; count := count + 1; count }` | state effect | 效应系统保证 | 高（handler 组合） |
| **Haskell** | `counter :: Int -> State Int Int; counter start = do { modify (+1); get }` | State Monad | 无别名（纯函数） | 高（Monad 组合） |
| **Java** | `Supplier<Integer> counter(int start) { int[] count = {start}; return () -> ++count[0]; }` | 无追踪 | 无保证 | 低 |
| **C++** | `std::function<int()> counter(int start) { int count = start; return [count]() mutable { return ++count; }; }` | 无追踪 | 无保证 | 低 |

---

## 第六章：反例集（Counter-Examples）

### 6.1 反例 1：Rust 无法实现的 Multi-Shot Continuation

**【问题】** 在 Koka 中，handler 可多次恢复 continuation 实现回溯：

```koka
fun choice-all(action) {
  with ctl choice() resume(False) ++ resume(True)
  [action()]
}
```

**【Rust 不可行论证】**:

1. Multi-shot continuation 需复制栈帧或闭包环境
2. 每次 resume 需独立的执行上下文
3. 最低成本是堆分配闭包 + 状态复制
4. 违反零成本抽象原则：无法保证与手写状态机同等性能
5. **结论**：Rust 明确排除 multi-shot continuation

### 6.2 反例 2：Rust 无法实现的 User-Defined Effect

**【问题】** 在 Koka 中，用户可定义全新效应：

```koka
effect emit
  fun emit(msg: string) : ()
```

**【Rust 不可行论证】**:

1. 用户自定义效应需要 effect signature 语法扩展
2. 需要编译器支持 evidence passing 或 CPS 转换
3. 需要运行时 handler 注册机制
4. 或需要类型系统的行多态支持
5. Rust 的 trait 系统是 nominal，无法表达开放效应集合
6. **结论**：Rust 的效应是语言内置的，不可用户扩展

### 6.3 反例 3：Rust 无法实现的 Effect Polymorphism

**【问题】** 在 Koka 中，函数可泛化于未知效应：

```koka
fun map(xs: list<a>, f: a -> e b) : e list<b>
```

**【Rust 不可行论证】**:

1. Rust 无 effect variable 概念
2. `fn map<T, U, E>(xs: Vec<T>, f: impl Fn(T) -> U) -> Vec<U>` 丢失了效应信息
3. 若 f 是 async，map 必须重写为 async_map
4. Effect Generics 试图解决，但仅覆盖内置关键字
5. **结论**：Rust 缺乏真正的效应多态

### 6.4 反例 4：C++ 的异常作为反模式

**【问题】** C++ 异常与 Rust Result 的对比。

**【反例分析】**:

```cpp
// C++：异常不出现在类型签名，无编译期检查
int divide(int x, int y);  // 可能抛出，类型不反映

// 对比 Rust：
fn divide(x: i32, y: i32) -> Result<i32, String>;  // 类型强制处理错误
```

C++ 异常的问题：

1. 类型签名不追踪异常（直到 C++0x contracts TS，仍未标准化）
2. 栈展开（stack unwinding）有运行时成本
3. 与析构函数交互复杂（RAII 依赖异常安全）
4. 跨 ABI 边界异常传播未定义

### 6.5 反例 5：Java Checked Exceptions 的失败

**【问题】** Java 的 checked exceptions 是效应系统的早期工业尝试，但失败了。

**【反例分析】**:

```java
// Java：checked exceptions 与泛型不兼容
public <T> T genericMethod() throws E {  // ❌ 非法：E 未定义
    ...
}

// 实际 workaround：
public <T, E extends Exception> T genericMethod() throws E {
    ...
}
// 但这导致签名膨胀，且无法捕获实际异常类型
```

失败原因：

1. 与泛型不兼容（throws 子句不可参数化）
2. 过度使用导致代码污染（throws 声明传播）
3. 与 lambda/Stream API 不兼容
4. 运行时仍使用栈展开，非零成本

---

## 第七章：属性关系矩阵（Property Relation Matrix）

### 7.1 概念间逻辑关系

以下矩阵展示核心概念之间的逻辑关系：蕴含（⇒）、互斥（⊥）、独立（∥）、细化（<:）。

| | Algebraic Effects | Ownership | Monad | Linear Type | Affine Type | Borrow Checker | Zero-Cost | Effect Handler | Capability |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| **Algebraic Effects** | = | ⊥ | ⇔(范畴) | ∥ | ∥ | ∥ | ⊥ | <:(实现) | ∥ |
| **Ownership** | ⊥ | = | ∥ | <:(松弛) | <:(实现) | <:(实现) | <:(要求) | ⊥ | <:(映射) |
| **Monad** | ⇔(范畴) | ∥ | = | ∥ | ∥ | ∥ | ⊥ | <:(可表达) | ∥ |
| **Linear Type** | ∥ | >:(严格) | ∥ | = | >:(严格) | ∥ | <:(要求) | ∥ | ∥ |
| **Affine Type** | ∥ | >:(实现) | ∥ | <:(松弛) | = | <:(基础) | <:(要求) | ∥ | ∥ |
| **Borrow Checker** | ∥ | >:(实现) | ∥ | ∥ | >:(实现) | = | <:(要求) | ⊥ | ∥ |
| **Zero-Cost** | ⊥ | <:(要求) | ⊥ | <:(要求) | <:(要求) | <:(要求) | = | ⊥ | ∥ |
| **Effect Handler** | >:(实现) | ⊥ | >:(可表达) | ∥ | ∥ | ⊥ | ⊥ | = | ∥ |
| **Capability** | ∥ | <:(映射) | ∥ | ∥ | ∥ | ∥ | ∥ | ∥ | = |

**关系说明**：

- **⇒ / <:**：左侧概念蕴含/细化右侧概念
- **⊥**：正交（不可归约，定理三）
- **⇔**：范畴论等价（在特定条件下）
- **∥**：独立（无直接蕴含关系）

### 7.2 Rust 效应系统的属性依赖图

```
Zero-Cost Abstraction
    ├─⇒ 排除 Runtime Continuation Capture
    ├─⇒ 排除 GC / Green Threads
    ├─⇒ 要求 Compile-Time Lowering
    └─⇒ 限制 Effect 为 Built-in Keywords

Ownership System
    ├─⇒ 基于 Affine Type
    ├─⇒ 实现 via Borrow Checker
    ├─⇒ 依赖 Lifetime System
    └─⇒ 正交于 Effect System (定理三)

Carried Effect (async/try)
    ├─⇒ 有 Type Constructor (Future/Result)
    ├─⇒ 可 Trait Bound 泛化
    └─⇒ 受限于 Built-in（不可用户扩展）

Uncarried Effect (const/unsafe)
    ├─⇒ 无 Type Constructor
    ├─⇒ 不可 Trait Bound 泛化
    ├─⇒ unsafe 是 Meta-Effect（非 Effect）
    └─⇒ 导致 Effect Mismatch

Effect Generics (提案)
    ├─⇒ 仅覆盖 Carried Effects
    ├─⇒ 排除 unsafe（语义不兼容）
    └─⇒ 不改变 Lowering 策略
```

---

## 第八章：工业实践案例深化

### 8.1 Asterinas：Rust OS 内核的形式化验证

**【项目】** Asterinas（USENIX ATC 2025）

**【核心数据】**

- 代码量：~14% unsafe，86% safe Rust
- 支持：210+ Linux syscalls
- 性能：与 Linux 原生性能相当
- 验证：Framekernel 架构，安全区与 unsafe 区严格分离

**【效应边界启示】**

1. OS 内核需要大量硬件直接访问（unsafe）
2. 通过模块化设计将 unsafe 限制在 14%
3. Safe 区通过 Rust 类型系统保证内存安全
4. Unsafe 区依赖人工审查 + 形式化验证

### 8.2 verify-rust-std：标准库的形式化验证

**【项目】** Rust Foundation 形式化验证挑战

**【核心数据】**

- 工具：Kani（BMC）、Verus（定理证明）、Miri（动态检测）
- 覆盖：18+ 验证任务（截至 2025）
- 目标：标准库 unsafe API 的安全契约

**【效应边界启示】**

1. 标准库是 unsafe 边界的"防火墙"
2. 每个 unsafe API 需明确 Safety Invariant
3. Kani 验证边界条件（如 slice::from_raw_parts 的指针有效性）
4. 验证强度从"信任程序员"向"数学证明"演进

### 8.3 Rust for Linux：内核模块的安全标注

**【项目】** Linux 内核的 Rust 支持

**【核心挑战】**

1. 内核上下文无用户空间内存保护
2. 硬件访问必须 unsafe
3. 需要与 C 代码广泛互操作

**【Safety-Tags Pre-RFC】**

```rust
// 安全属性标注提案（概念性）
#[safety::requires("ptr is non-null and aligned")]
#[safety::ensures("return value is valid UTF-8")]
unsafe fn kernel_read(ptr: *const u8, len: usize) -> &[u8] {
    core::slice::from_raw_parts(ptr, len)
}
```

**【效应边界启示】**

1. 内核需要显式安全契约标注
2. Safety-Tags 是人类可读 + 机器可解析的 DSL
3. 降低形式化验证工具的合同编写成本
4. 从"注释文档"向"可验证属性"演进

### 8.4 Ferrocene：安全关键 Rust 编译器

**【项目】** Ferrous Systems 的安全关键 Rust 工具链

**【核心数据】**

- 目标：DO-178C / ISO 26262 / IEC 61508 认证
- 策略：冻结 rustc 版本 + 确定性编译 + 完整测试覆盖
- 效应边界：禁止某些 unsafe 模式（如裸指针算术）

**【效应边界启示】**

1. 安全关键领域需限制效应使用
2. 可通过 lint 规则禁止特定 unsafe 模式
3. 效应系统不仅是"表达能力"，也是"安全约束"
4. 从"通用语言"向"领域特定子集"演进

---

## 第九章：形式化验证工具深化对比

### 9.1 工具能力矩阵

| 工具 | 验证方法 | 空间安全 | 行为安全 | 效应边界 | 自动化 | 工业就绪 |
|------|---------|----------|----------|----------|--------|----------|
| **Miri** | 解释器 + UB 检测 | ✅ | ❌ | 动态检测 | 高 | 中 |
| **Kani** | BMC (CBMC) | ✅ | 部分 | 模型检查 | 高 | 高 |
| **Verus** | 定理证明 (Z3) | ✅ | ✅ | 完整证明 | 中 | 高 |
| **Creusot** | 定理证明 (Why3) | ✅ | ✅ | 完整证明 | 中 | 中 |
| **Prusti** | 定理证明 (Viper) | ✅ | 部分 | 分离逻辑 | 中 | 低 |
| **UnsafeCop** | BMC (优化) | ✅ | ❌ | unsafe 专用 | 高 | 中 |
| **Safety-Tags** | 属性标注 | ❌ | ❌ | 契约规范 | 高 | 低 |
| **TrustInSoft** | 穷尽分析 | ✅ | 部分 | 静态分析 | 高 | 高 |

### 9.2 验证层次模型

```
Level 5: 完整功能正确性 (Functional Correctness)
    └── Verus, Creusot, Prusti
    └── 需手写规约（pre/post condition）
    └── 证明成本：7.5:1 (Atmosphere 微内核)

Level 4: 安全不变量证明 (Safety Invariant)
    └── Kani, UnsafeCop
    └── 自动边界检查 + 用户断言
    └── 证明成本：1:1 ~ 2:1

Level 3: 未定义行为检测 (UB Detection)
    └── Miri, Sanitizer
    └── 动态执行路径覆盖
    └── 无法覆盖所有路径

Level 2: 静态分析 (Static Analysis)
    └── Clippy, Cargo Audit, TrustInSoft
    └── 模式匹配 + 启发式规则
    └── 误报/漏报存在

Level 1: 类型系统保证 (Type System)
    └── rustc Borrow Checker
    └── 内存安全 + 线程安全（safe Rust）
    └── 不保证功能正确性
```

---

## 第十章：结论与三重边界的最终形式化

### 10.1 边界一：Carried vs Uncarried 类型系统断层

**形式化表述**：

```
∄ T_const : Type → Type.  const fn() → τ  ≅  fn() → T_const<τ>
∄ T_unsafe : Type → Type. unsafe fn() → τ ≅ fn() → T_unsafe<τ>
∃ T_async : Type → Type.  async fn() → τ ≅ fn() → T_async<τ>  (T_async = Future)
∃ T_try : Type → Type.    try fn() → τ   ≅ fn() → T_try<τ>    (T_try = Result)
```

**后果**：效应泛型只能覆盖 ∃ 部分，无法覆盖 ∄ 部分。

### 10.2 边界二：零成本抽象与通用效应处理器的不相容性

**形式化表述**：

```
∀ handler H.  cost(H) ≥ cost(stack_copy) + cost(heap_alloc)
ZeroCost(κ) ⇔ cost(κ) ≈ cost(manual_impl)
∴ ZeroCost(κ) ⇒ ¬∃ general_purpose_handler(H)
```

**后果**：Rust 的效应是语法糖 lowering，无运行时 handlers。

### 10.3 边界三：空间安全与行为安全的正交性

**形式化表述**：

```
Ownership : Resource → SpatialSafety
Effect    : Computation → BehavioralSafety
SpatialSafety ∩ BehavioralSafety = ∅
∴ Ownership ⟂ EffectSystem
```

**后果**：所有权系统管理内存拓扑，效应系统管理计算交互，二者不可归约。

### 10.4 工程哲学总结

Rust 的效应系统边界是**有意识的工程哲学选择**，而非技术债务：

> "Rust experimented with all of these concepts at some point in its history, it wasn't out of ignorance that they were excluded."

Rust 在**表达能力**与**性能可控性**之间选择了后者，通过将效应限制为编译期可消除的语法结构，维持了系统编程语言的核心承诺。这一边界使 Rust 区别于：

- **Koka / Eff**：以效应为首要抽象，牺牲运行时可控性
- **Haskell**：以 Monad 为统一框架，依赖 GC 和惰性求值
- **Scala 3**：在托管运行时中融合能力系统，保留 GC 灵活性
- **OCaml 5**：引入动态效应，但类型系统不追踪

Rust 的效应系统是**静态可消除效应的闭包**——一个精心设计、形式化验证、工业就绪，但**不可用户扩展**的边界系统。

---

## 参考文献索引（深化版）

| 引用 | 来源 | 权威性 | 核心贡献 |
|------|------|--------|----------|
| EPFL 博士论文 | 形式化安全语言分类框架 | S | 三类安全机制分类 |
| boats 博客 | "The problem of effects in Rust" | 高 | Rust 五种效应分类 |
| Yoshua Wuyts 博客 | "Extending Rust's Effect System" | 高 | Effect Generics 提案 |
| Abubalay 博客 | "A universal lowering strategy..." | 中 | Rust 控制流效应 lowering |
| Jung et al., POPL 2018 | RustBelt | S | Iris 分离逻辑验证 Rust |
| Plotkin & Power, 2003 | Algebraic Operations... | S | 代数效应理论奠基 |
| Plotkin & Pretnar, 2013 | Handling Algebraic Effects | S | 效应处理器理论 |
| Lucassen & Gifford, 1988 | Polymorphic Effect Systems | S | 效应系统奠基 |
| Leijen, 2014 | Koka: Row Polymorphic Effects | S | 行多态效应类型 |
| Weiss et al., ICFP 2019 | Oxide | S | Rust 完整操作语义 |
| Villani et al., 2023 | Tree Borrows | S | 别名模型 v2 |
| Keyword Generics Initiative | Rust 官方 | S | Effect Generics 官方提案 |
| SafeFFI, arXiv 2025 | SafeFFI | S | unsafe/safe 边界优化 |
| verify-rust-std | Rust Foundation | S | 标准库形式化验证 |
| UnsafeCop, arXiv 2025 | UnsafeCop | S | BMC 验证 unsafe 代码 |
| Safety-Tags Pre-RFC | Rust for Linux | S | 安全属性标注 |
| Asterinas, USENIX ATC 2025 | Asterinas | S | Rust OS 内核验证 |
| Verus, SOSP 2024 | Verus | S | Rust 实用验证基础 |
| Atmosphere, SOSP 2025 | Atmosphere | S | Rust 微内核验证 |
| TrustInSoft 2025.10 | TrustInSoft | A | 穷尽静态分析 |
| Koka 官方文档 | Koka | A | 行多态效应实现 |
| Eff 论文 | Eff in OCaml | S | Eff 语言嵌入 OCaml |
| OCaml 5 Multicore | Retrofitting Effect Handlers | S | OCaml 5 效应处理器 |
| EventHelix | async/await 底层 | B | Rust async lowering 分析 |
| Antithesis 博客 | Rust 形式化方法 | B | 验证工具实践 |
| Wadler, 1990 | Linear Types | S | 线性类型理论 |
| Girard, 1987 | Linear Logic | S | 线性逻辑奠基 |
| Miller, 2006 | Object Capability Model | S | 能力安全模型 |
| Tofte & Talpin, 1994 | Region-Based Memory | S | 区域内存管理 |
| Moggi, 1989 | Computational Lambda-Calculus | S | Monad 语义基础 |
| Rémy, 1994 | Record Polymorphism | S | 行多态理论 |

---

*文档生成时间：2026-06-03*
*对齐标准：POPL / PLDI / ICFP / OOPSLA / SOSP / USENIX ATC / ESOP / TACAS / 学术 arXiv 2025-2026 / Rust 官方 Initiative*
*论证方法：形式化定义 → 历史谱系 → 边界枚举 → 编译器 lowering 分析 → 跨语言代码对比 → 反例集 → 属性关系矩阵 → 定理论证 → 工业实践验证 → 工程哲学总结*
*表征方式：概念定义总表（16个核心概念 × 6维度） · 形式化类型规则 · 操作语义 · 范畴论语义 · 历史演进谱系 · 代码示例对比矩阵（5语言 × 3场景） · 反例集（5个深度反例） · 属性关系矩阵 · 十一幅可视化图表*
