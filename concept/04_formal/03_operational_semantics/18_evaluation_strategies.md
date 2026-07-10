> **内容分级**: [专家级]

# 求值策略：Call-by-Value, Call-by-Name, Call-by-Need
>
> **EN**: Evaluation Strategies
> **Summary**: Evaluation Strategies: formal methods foundations, semantics, and verification techniques relevant to Rust.
> **受众**: [研究者]
> **权威来源**: 本文件为 `concept/` 权威页。
> ⚠️ **声明**: 本文件使用形式化符号辅助直觉理解，所呈现的"定理/引理/推论"为**教学类比**，非经机器验证的严格数学证明。如需严格形式化验证，请参考 [Verus](https://github.com/verus-lang/verus)、[Kani](https://model-checking.github.io/kani/)、[Coq](https://coq.inria.fr/)。
>
> **层级**: L4 形式化 — 通用编程语言机制
> **A/S/P 标记**: **S** — Structure
> **双维定位**: F×Und — 形式化理解程序执行的求值规则
> **前置概念**:
>
> [Lambda Calculus](../00_type_theory/14_lambda_calculus.md) ·
> [Variable Model](../../01_foundation/03_values_and_references/20_variable_model.md) ·
> [Type System](../../01_foundation/02_type_system/04_type_system.md) ·
> [Async/Await](../../03_advanced/01_async/02_async.md)
>
> **后置概念**:
>
> [Ownership Formalization](../01_ownership_logic/03_ownership_formal.md) ·
> [Control Flow](../../01_foundation/04_control_flow/07_control_flow.md)
>
> **主要来源**: · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> [Pierce — TAPL, §5-§11](https://www.cis.upenn.edu/~bcpierce/tapl/) ·
> [Harper — PFPL, Part III](https://www.cs.cmu.edu/~rwh/pfpl/) ·
> [Wadler 1984 — Why Calculating is Better than Scheming](https://doi.org/10.1093/comjnl/27.2.115) ·
> [Plotkin 1975 — Call-by-Name, Call-by-Value and the λ-Calculus](https://doi.org/10.1016/0304-3975(75)90017-1) ·
> [Cambridge — OptComp 2025, Lambda Lifting & Evaluation Strategies](https://www.cl.cam.ac.uk/~na482/pdfs/) ·
> [Nottingham — PL Semantics, Evaluation Strategies](https://people.cs.nott.ac.uk/pszgmh/) ·
> [Wikipedia: Evaluation strategy](https://en.wikipedia.org/wiki/Evaluation_strategy)
>
>
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [RustBelt](https://plv.mpi-sws.org/rustbelt/)
---

> **Bloom 层级**: 分析 → 评价

---

## 认知路径

> **认知路径**: 本节从 "求值策略" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 求值策略 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 求值策略 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与求值策略的适用边界。
5. **迁移应用**: 将 求值策略 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 求值策略 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。
> **过渡**: 在建立 求值策略 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。
> **过渡**: 最后，将 求值策略 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: 求值策略 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 求值策略 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 求值策略 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

## 📑 目录

- [求值策略：Call-by-Value, Call-by-Name, Call-by-Need](#求值策略call-by-value-call-by-name-call-by-need)
  - [认知路径](#认知路径)
  - [📑 目录](#-目录)
  - [一、核心命题](#一核心命题)
  - [二、求值策略谱系](#二求值策略谱系)
    - [2.1 严格 vs 非严格求值](#21-严格-vs-非严格求值)
    - [2.2 四种核心求值策略](#22-四种核心求值策略)
  - [三、Rust 的求值策略定位](#三rust-的求值策略定位)
    - [3.1 默认策略：Call-by-Value + 严格求值](#31-默认策略call-by-value--严格求值)
    - [3.2 显式引用传递：受限的 Call-by-Reference](#32-显式引用传递受限的-call-by-reference)
    - [3.3 短路求值：非严格性的局部表达](#33-短路求值非严格性的局部表达)
    - [3.4 惰性构造：Future 与 Iterator](#34-惰性构造future-与-iterator)
  - [四、Lambda 演算中的归约策略](#四lambda-演算中的归约策略)
    - [4.1 三种归约策略](#41-三种归约策略)
    - [4.2 Rust 的求值顺序](#42-rust-的求值顺序)
  - [五、求值策略与类型系统的交互](#五求值策略与类型系统的交互)
    - [5.1 严格性 vs 类型系统表达能力](#51-严格性-vs-类型系统表达能力)
  - [六、反例与边界测试](#六反例与边界测试)
    - [6.1 反例：严格求值的性能陷阱](#61-反例严格求值的性能陷阱)
    - [6.2 边界测试：求值顺序的确定性验证](#62-边界测试求值顺序的确定性验证)
    - [6.3 边界测试：Move 作为 CBV 的线性扩展](#63-边界测试move-作为-cbv-的线性扩展)
  - [七、跨语言求值策略对比矩阵](#七跨语言求值策略对比矩阵)
  - [八、知识来源关系](#八知识来源关系)
    - [10.3 边界测试：按值传递与 `Copy` 的交互（编译错误）](#103-边界测试按值传递与-copy-的交互编译错误)
    - [10.4 边界测试：惰性迭代器与严格求值的混合（编译错误/逻辑错误）](#104-边界测试惰性迭代器与严格求值的混合编译错误逻辑错误)
    - [10.5 边界测试：惰性求值与 panic 的延迟触发（运行时行为差异）](#105-边界测试惰性求值与-panic-的延迟触发运行时行为差异)
    - [10.3 边界测试：按值传递与大类型的性能陷阱（编译错误/逻辑问题）](#103-边界测试按值传递与大类型的性能陷阱编译错误逻辑问题)
    - [10.3 边界测试：const fn 中的非编译期操作](#103-边界测试const-fn-中的非编译期操作)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：Rust 默认使用什么求值策略？函数参数在调用前还是调用后求值？（理解层）](#测验-1rust-默认使用什么求值策略函数参数在调用前还是调用后求值理解层)
    - [测验 2：Call-by-Name 和 Call-by-Need 有什么共同点和区别？（理解层）](#测验-2call-by-name-和-call-by-need-有什么共同点和区别理解层)
    - [测验 3：`&&` 和 `||` 的短路求值（short-circuit evaluation）属于哪种求值策略的体现？（理解层）](#测验-3-和--的短路求值short-circuit-evaluation属于哪种求值策略的体现理解层)
    - [测验 4：Rust 的 `Iterator` 惰性求值与 Haskell 的全局惰性求值有什么区别？（理解层）](#测验-4rust-的-iterator-惰性求值与-haskell-的全局惰性求值有什么区别理解层)
    - [测验 5：为什么严格求值语言通常比惰性求值语言更容易预测内存和性能行为？（理解层）](#测验-5为什么严格求值语言通常比惰性求值语言更容易预测内存和性能行为理解层)
  - [权威来源对照](#权威来源对照)
  - [总结](#总结)

## 一、核心命题

> **求值策略决定"何时"和"如何"计算表达式。
> Rust 的严格求值（strict evaluation）+ 默认 Call-by-Value 是其性能与可预测性的根基，但 `&&`/`||` 的短路语义、`lazy_static` 的惰性初始化、以及 `Future` 的惰性构造，都是非严格求值在 Rust 中的工程级表达。**

---

## 二、求值策略谱系

### 2.1 严格 vs 非严格求值

| 策略类别 | 核心特征 | 典型语言 |
|:---|:---|:---|
| **严格求值（Strict / Eager）** | 函数参数在函数体执行前求值 | C、C++、Rust、Java、Python |
| **非严格求值（Non-strict / Lazy）** | 函数参数按需求值 | Haskell、Miranda、Lazy K |

> 严格与非严格的区分是 λ 演算语义的基础之一。Pierce 在 *TAPL* §5 中将 CBV 与 CBN 作为两种核心归约策略讨论；Harper 在 *PFPL* 中则用结构化操作语义（SOS）给出其形式化定义。

**关键差异示例**:

```rust,ignore
// Rust: 严格求值 — 参数先求值，再调用函数
fn strict_example() {
    let result = divide(10, 0); // ❌ 运行时 panic: 0 先被求值
}

// Haskell: 非严格求值 — 参数按需求值
-- lazy_example = let result = divide 10 0 in 42
-- 不会 panic！因为 result 从未被使用，0 不会被求值
```

### 2.2 四种核心求值策略

```text
Call-by-Value (CBV)     → 参数求值后再传递（值拷贝/移动）
Call-by-Name (CBN)      → 参数表达式直接代入函数体，每次使用都重新求值
Call-by-Need (CBV-need) → CBN + 记忆化（第一次求值后缓存结果）
Call-by-Reference (CBR) → 传递参数的地址/引用

Plotkin (1975) 的经典论文证明了 CBV 与 CBN 可通过 continuation-passing style (CPS) 相互转换，并奠定了这两种策略在形式语义中的对偶地位。
```

**形式化对比**:

| 策略 | 参数传递 | 副作用行为 | 性能特征 |
|:---|:---|:---|:---|
| **CBV** | 值的副本 | 无副作用传播 | 可预测，可能重复计算参数 |
| **CBN** | 表达式本身 | 副作用可能多次执行 | 避免无用计算，但重复求值 |
| **CBV-need** | 表达式 + 缓存 | 副作用执行一次 | 最优：惰性 + 记忆化 |
| **CBR** | 地址/引用（Reference） | 副作用直接传播 | 高效大对象传递，但别名风险 |

---

## 三、Rust 的求值策略定位

### 3.1 默认策略：Call-by-Value + 严格求值

Rust 默认采用**严格 Call-by-Value**：函数参数在调用前求值，然后以值的形式传递（Rust Reference: [Moved and Copied Types](https://doc.rust-lang.org/reference/expressions.html#moved-and-copied-types)）。

```rust
fn call_by_value(x: i32) {
    // x 是原值的位拷贝（因为 i32 实现了 Copy）
    println!("{}", x);
}

fn call_by_move(s: String) {
    // s 获得原值的所有权（非 Copy 类型的移动语义）
    println!("{}", s);
} // s 在这里 drop

fn main() {
    let n = 42;
    call_by_value(n); // n 被拷贝，n 仍可用

    let text = String::from("hello");
    call_by_move(text); // text 的所有权转移到 s
    // println!("{}", text); // ❌ 编译错误: value moved
}
```

**Rust 对 CBV 的独特扩展**:

| 类型 | CBV 行为 | 等价于经典 PL |
|:---|:---|:---|
| `Copy` 类型（`i32`, `bool`, `f64`） | 位拷贝 | 经典 CBV（值拷贝） |
| `!Copy` 类型（`String`, `Vec<T>`） | 所有权（Ownership）转移（destructive move） | CBV + 线性类型约束 |
| `&T` 参数 | 传递引用（Reference）（只读借用（Borrowing）） | 受限的 CBR |
| `&mut T` 参数 | 传递可变引用（Mutable Reference） | 受限的 CBR + 别名约束 |

> **关键洞察**: Rust 的默认参数传递**不是纯粹的 CBV**，而是 **CBV + 线性所有权（Ownership）** 的混合体。`Copy` 类型 = 经典 CBV；`!Copy` 类型 = CBV 但原变量失效（所有权转移）。[💡 原创分析](../../00_meta/00_framework/methodology.md)

### 3.2 显式引用传递：受限的 Call-by-Reference

Rust 通过 `&T` 和 `&mut T` 实现了**显式的 CBR**，但附加了严格的别名约束：

```rust
fn call_by_reference(y: &mut i32) {
    *y += 1; // 通过引用修改原值
}

fn main() {
    let mut x = 5;
    call_by_reference(&mut x); // 显式传递可变引用
    assert_eq!(x, 6); // ✅ 原值被修改
}
```

**与 C++ 引用（Reference）的对比**:

| 维度 | C++ 引用（Reference） | Rust 引用 |
|:---|:---|:---|
| 语法 | 隐式（`int& y`） | 显式（`&mut x`） |
| 可空性 | 不可为空（必须初始化） | 不可为空（编译器保证） |
| 别名规则 | 无编译期检查 | borrow checker 静态验证 |
| 生命周期（Lifetimes） | 手动管理 | 编译器自动推断 |
| 可变性 | `const` / 非 `const` | `&T`（只读）/ `&mut T`（独占写） |

### 3.3 短路求值：非严格性的局部表达

Rust 的 `&&` 和 `||` 运算符采用**短路求值**（short-circuit evaluation），这是非严格求值的局部表达：

```rust
fn side_effect() -> bool {
    println!("side effect!");
    true
}

fn main() {
    let _ = false && side_effect(); // side_effect 不会被执行！
    let _ = true || side_effect();  // side_effect 不会被执行！
}
```

**形式化描述**:

```text
&& 的语义:
  e1 && e2 ≡ if e1 then e2 else false
  → e1 为 false 时，e2 不求值（非严格）

|| 的语义:
  e1 || e2 ≡ if e1 then true else e2
  → e1 为 true 时，e2 不求值（非严格）
```

> **与 Haskell 的对比**: Haskell 的函数参数**默认**是非严格的；Rust 的函数参数**默认**是严格的，仅在特定运算符（`&&`, `||`, `?:`）中局部引入非严格性。

### 3.4 惰性构造：Future 与 Iterator

Rust 通过**显式类型**实现工程级惰性求值：

```rust,ignore
// Iterator: 惰性构造，消费时才求值
let iter = vec![1, 2, 3].iter().map(|x| x * 2); // 未执行任何计算
let result: Vec<_> = iter.collect(); // 消费时才计算

// Future: 惰性构造，await 时才执行
let fut = async { println!("lazy"); }; // 未执行
// fut.await; // await 时才执行
```

**与 Haskell 惰性的本质差异**:

| 维度 | Haskell 惰性 | Rust 显式惰性 |
|:---|:---|:---|
| 机制 | 语言级，默认行为 | 库级，显式类型（`Iterator`, `Future`） |
|  thunk 管理 | 运行时（Runtime）自动创建和管理 | 编译器将 `async` 脱糖为状态机 |
| 记忆化 | 自动（CBV-need） | 手动（`once_cell::Lazy`, `lazy_static!`） |
| 空间泄漏 | 可能（thunk 累积） | 不可能（惰性显式标注） |

---

## 四、Lambda 演算中的归约策略

### 4.1 三种归约策略

在 λ 演算中，归约策略决定"先归约哪个 redex"：

| 策略 | 规则 | 特征 |
|:---|:---|:---|
| **Normal Order** | 最外层的 redex 先归约 | 对应 CBN，若存在正规形式则必找到 |
| **Applicative Order** | 最内层的 redex 先归约 | 对应 CBV，可能不终止即使存在正规形式 |
| **Call-by-Name** | Normal Order 的变体，不归约函数体内部的 redex | Haskell 的语义基础 |
| **Call-by-Value** | Applicative Order 的变体，参数归约后再代入 | Rust/C/Java 的语义基础 |

**关键定理** [Tier 1]: **正规化定理（Normalization Theorem）**

> 若一个 λ 项存在正规形式（normal form），则 Normal Order 归约必能找到它。Applicative Order 无此保证。
>
> **来源**: [Curry & Feys, Combinatory Logic, 1958] · [Barendregt, The Lambda Calculus, 1984]

**对 Rust 的启示**: Rust 采用 CBV（Applicative Order），牺牲了找到正规形式的保证性，换取了**可预测的性能**和**无副作用的参数求值顺序**。

### 4.2 Rust 的求值顺序

Rust 明确规定了表达式的求值顺序：

```text
1. 函数/方法参数: 从左到右求值
2. 元组/结构体构造: 从左到右求值
3. 数组构造: 从左到右求值
4. 赋值: 右侧先求值，然后左侧 place expression 被赋值
5. 复合赋值（+= 等）: 左侧先求值作为 place，右侧再求值
```

**与 C/C++ 的对比**:

| 场景 | C/C++ | Rust |
|:---|:---|:---|
| 函数参数求值顺序 | **未指定**（编译器决定） | **严格从左到右** |
| 副作用顺序 | 不可预测（UB 风险） | 完全确定 |
| 示例 | `foo(i++, i++)` // 未定义行为 | `foo(i, i)` // 编译错误（若涉及移动）或确定行为 |

> **关键洞察**: Rust 的严格求值顺序消除了 C/C++ 中大量与求值顺序相关的 UB，是 Rust "无未定义行为"承诺的重要组成部分。来源: [Rust Reference §6.2.13](https://doc.rust-lang.org/reference/introduction.html) ✅

---

## 五、求值策略与类型系统的交互

### 5.1 严格性 vs 类型系统表达能力

| 语言 | 求值策略 | 类型系统（Type System）特征 |
|:---|:---|:---|
| Haskell | 非严格 | 需要 Monad 显式管理副作用（IO、State） |
| ML | 严格 CBV | 引用（Reference）类型（`ref`）显式管理可变性 |
| Rust | 严格 CBV + 线性所有权（Ownership） | `&mut T` 在类型层面编码 write effect |

**Rust 的独特设计**: 通过**线性所有权（Ownership）**而非**惰性求值**来管理副作用：

```rust,ignore
// Rust: 可变性通过 &mut T 显式追踪
fn mutate(x: &mut i32) {
    *x += 1; // 编译器知道这是副作用，因为 x 是 &mut
}

// Haskell: 可变性通过 IO Monad 显式追踪
-- mutate :: IORef Int -> IO ()
-- mutate ref = modifyIORef ref (+1)
```

> **形式化命题** [Tier 2]: Rust 的 `&mut T` 在类型系统（Type System）中编码了**局部可变性效果**（local mutation effect），等价于将 CBR 的可变性限制在线性逻辑框架内。
> **证明草图**: `&mut T` 满足线性逻辑的 `⊗`（张量积）规则：创建 `&mut T` 消耗 `T` 的所有权（Ownership），归还 `&mut T` 恢复 `T` 的所有权。在此区间内，存储被独占修改，无别名干扰。来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)

---

## 六、反例与边界测试

### 6.1 反例：严格求值的性能陷阱

```rust,ignore
fn strict_trap() {
    let expensive = compute_expensive(); // 立即求值，即使可能不用
    if condition {
        use_value(expensive);
    } // 若 condition 为 false，expensive 的计算被浪费
}

// 对比: 使用闭包实现惰性
fn lazy_solution() {
    let expensive = || compute_expensive(); // thunk，未求值
    if condition {
        use_value(expensive()); // 按需求值
    }
}
```

> **认知功能**: 此反例展示了 Rust 严格求值的代价。工程上通过 `Fn` 闭包（Closures）、`Iterator` 适配器链、`Future` 等显式惰性机制来弥补。[💡 原创分析](../../00_meta/00_framework/methodology.md)

### 6.2 边界测试：求值顺序的确定性验证

```rust,compile_fail
fn evaluation_order() {
    let mut v = vec![];

    // Rust 保证从左到右求值
    push_three(&mut v, { v.push(1); 1 }, { v.push(2); 2 }, { v.push(3); 3 });
    // v 现在包含 [1, 2, 3]

    // 在 C/C++ 中，上述代码的求值顺序未指定，可能导致未定义行为
}

fn push_three(v: &mut Vec<i32>, a: i32, b: i32, c: i32) {
    v.push(a); v.push(b); v.push(c);
}
```

### 6.3 边界测试：Move 作为 CBV 的线性扩展

```rust,compile_fail
fn linear_move() {
    let s = String::from("hello");
    let t = s; // CBV: s 的值被传递给 t
    // 但 Rust 的线性约束使 s 失效
    println!("{}", s); // ❌ E0382: borrow of moved value
}

// 对比: C++ 的 CBV（拷贝构造）
// std::string s = "hello";
// std::string t = s; // s 仍然有效（深拷贝）

// 对比: Java 的 CBR（引用拷贝）
// String s = "hello"; // 实际: s 指向字符串对象
// String t = s;       // t 指向同一对象（共享）
```

> **边界洞察**: 同样的"赋值"语法在三种语言中表示三种截然不同的语义：C++ = 深拷贝，Java = 引用（Reference）共享，Rust = 所有权（Ownership）转移。这是变量模型差异的最直接体现。

---

## 七、跨语言求值策略对比矩阵

| 语言 | 默认策略 | 严格性 | 引用（Reference）传递 | 惰性机制 | 副作用管理 |
|:---|:---|:---:|:---:|:---|:---|
| **C** | CBV | 严格 | 指针（手动） | 无 | 无约束 |
| **C++** | CBV | 严格 | 引用（Reference）/指针 | 无（库级 `std::function`） | RAII |
| **Java** | CBR（对象）+ CBV（原始类型） | 严格 | 对象引用（Reference）自动 | 无 | GC |
| **Python** | CBR（对象）+ CBV（不可变） | 严格 | 名字绑定 | 生成器（`yield`） | GC |
| **Haskell** | CBV-need | 非严格 | 无（纯函数） | 默认 | Monad |
| **Rust** | CBV + 线性所有权 | 严格 | `&T` / `&mut T`（显式） | `Iterator` / `Future` / 闭包（Closures） | 所有权（Ownership）+借用（Borrowing） |

---

## 八、知识来源关系

| **论断** | **来源** | **可信度** | **Tier** |
|:---|:---|:---:|:---:|
| 严格 vs 非严格求值 | [Harper PFPL] · [Pierce TAPL §11] | ✅ | Tier 1 |
| CBV/CBN/CBV-need 定义 | [Pierce TAPL §11] · [Wadler 1984] | ✅ | Tier 1 |
| Normal Order 正规化定理 | [Curry & Feys 1958] · [Barendregt 1984] | ✅ | Tier 1 |
| Rust 求值顺序 | [Rust Reference §6.2.13](https://doc.rust-lang.org/reference/introduction.html) | ✅ | Tier 1 |
| Rust 参数传递语义 | [Rust Reference §6.2](https://doc.rust-lang.org/reference/introduction.html) | ✅ | Tier 1 |
| Rust 线性所有权（Ownership） = CBV + 线性约束 | [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · 原创分析 | ✅/💡 | Tier 2 |
| `&mut T` 编码局部可变性效果 | [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [Moggi 1989] | ✅ | Tier 2 |
| 跨语言对比矩阵 | [💡 原创分析] | ⚠️ | Tier 3 |

---

> **最后更新**: 2026-05-24
> **状态**: ✅ 新建 — 通用 PL 基座层

### 10.3 边界测试：按值传递与 `Copy` 的交互（编译错误）

```rust,compile_fail
struct Config {
    data: Vec<u8>,
}

fn process(c: Config) {
    println!("{:?}", c.data);
}

fn main() {
    let cfg = Config { data: vec![1, 2, 3] };
    process(cfg);
    // ❌ 编译错误: Config 未实现 Copy，cfg 已被移动
    println!("{:?}", cfg.data);
}
```

> **修正**:
>
> Rust 的默认参数传递是**按值移动**（move semantics）：未实现 `Copy` 的类型在传参时转移所有权（Ownership）。
> 这与 C 的按值复制（`struct` 按位复制）、Java 的按值引用（对象引用复制，对象共享）、Haskell 的惰性求值（thunk 共享）都不同。
> `Config` 包含 `Vec<u8>`（堆分配），按值移动只复制栈上的 `Vec` 头（指针、长度、容量），不复制堆数据——这是 Rust 的零成本移动。
> 但移动后原变量失效，若需保留，应传引用（`&Config`）或 `Clone`。
> Rust 的求值策略可描述为"严格按值 + 移动语义"：参数在调用前求值（严格），传递时移动所有权（非共享）。
> 这与 C++11 的右值引用（`std::move`，显式移动）类似，但 Rust 的移动是默认且自动的。
> (Source: [The Rust Programming Language](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)) ·
> (Source: [Evaluation Strategy](https://en.wikipedia.org/wiki/Evaluation_strategy))

### 10.4 边界测试：惰性迭代器与严格求值的混合（编译错误/逻辑错误）

```rust,ignore
fn main() {
    let v = vec![1, 2, 3];
    let iter = v.iter().map(|x| {
        println!("computing {}", x);
        x * 2
    });

    // ❌ 逻辑错误: map 是惰性的，println 尚未执行
    println!("mapped created");

    // 只有 collect/for 才触发求值
    let collected: Vec<_> = iter.collect();
    println!("{:?}", collected);
}
```

> **修正**:
> Rust 的迭代器（Iterator）适配器（`map`、`filter`、`flat_map`）是**惰性求值**的——它们返回新的迭代器，不立即执行。
> 副作用（`println`、修改外部状态）在迭代器（Iterator）被消费（`collect`、`for_each`、`fold`）时才发生。
> 这是函数式编程的常规模式（Haskell 的惰性列表、Python 的生成器表达式），但 Rust 开发者常误以为 `map` 像 `Vec::map`（立即执行）。
> 严格求值与惰性求值的边界：Rust 的值（非迭代器（Iterator））是严格求值的，`Iterator` trait 的方法链是惰性求值的。
> 混合时的陷阱：
>
> 1) 副作用的顺序不确定；
> 2) 迭代器（Iterator）被 `collect` 前，中间状态不反映副作用；
> 3) 多次 `collect` 同一迭代器导致副作用重复执行。
> 这与 C# 的 LINQ（惰性，`ToList()` 触发）或 Java 的 `Stream`（惰性，`collect` 触发）相同。
>
> (Source: [The Rust Programming Language](https://doc.rust-lang.org/book/ch13-02-iterators.html)) ·
> (Source: [Evaluation Strategy](https://en.wikipedia.org/wiki/Evaluation_strategy))

### 10.5 边界测试：惰性求值与 panic 的延迟触发（运行时行为差异）

```rust,ignore
fn main() {
    let v = vec![1, 2, 3];
    let bad_index = v.get(10).unwrap_or_else(|| panic!("out of bounds"));
    // ❌ 运行时 panic: unwrap_or_else 的闭包在 None 时立即求值
    // 但某些惰性抽象可能延迟 panic 到不可预期时刻
    println!("{}", bad_index);
}
```

> **修正**:
>
> Rust 的核心语言是**严格求值**（eager evaluation），但某些抽象引入惰性：
>
> 1) 迭代器适配器（`map`、`filter`）惰性执行；
> 2) `lazy_static`、`once_cell` 惰性初始化；
> 3) 宏（Macro）展开在编译期惰性。
>
> 惰性求值的风险：副作用（panic、I/O、修改状态）的触发时机不确定。
> `unwrap_or_else(|| panic!(...))` 在 `None` 时立即 panic，因为 `unwrap_or_else` 是严格的（立即调用闭包（Closures））。
> 这与 Haskell 的惰性求值（`error` 可能在不可预期时刻触发）或 Swift 的 `@autoclosure`（延迟求值参数）不同——Rust 的惰性仅限于迭代器和高阶函数，核心表达式是严格的。
> (Source: [The Rust Programming Language](https://doc.rust-lang.org/book/ch13-02-iterators.html)) ·
> (Source: [Evaluation Strategy](https://en.wikipedia.org/wiki/Evaluation_strategy))

### 10.3 边界测试：按值传递与大类型的性能陷阱（编译错误/逻辑问题）

```rust,ignore
struct LargeArray {
    data: [u8; 10000],
}

fn process(arr: LargeArray) -> LargeArray {
    arr // 按值返回
}

fn main() {
    let a = LargeArray { data: [0; 10000] };
    // ❌ 编译问题: 多次按值传递大类型导致隐式 memcpy
    let b = process(a);
    let c = process(b);
    let _d = process(c);
}
```

> **修正**:
> Rust 的**按值传递**（move semantics）对大类型（如 `[u8; 10000]`）可能产生隐式内存复制（memcpy）。
> 虽然 Rust 的所有权系统保证无双重释放，但性能上：
>
> 1) 大数组按值传递 = memcpy；
> 2) `Box<[u8; 10000]>` 只传递指针（8 字节）；
> 3) `&[u8]` 传递 fat pointer（16 字节）。
>
> 优化：
>
> 1) 大类型使用 `Box<T>` 或 `&T`；
> 2) 使用 `#[repr(C)]` 控制布局（但通常无需）；
> 3) 编译器的 NRVO（Named Return Value Optimization）可能消除部分复制。
>
> Rust 的 move 语义在抽象层面是"零成本"（不调用拷贝构造函数），但底层仍是 `memcpy`——这是所有值语义语言的共性。
> 这与 C++ 的 RVO/NRVO（类似优化）或 Go 的接口值（隐式指针+堆分配）不同——Rust 的 move 语义是显式的、可预测的。
> (Source: [The Rust Programming Language](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)) ·
> (Source: [Rust Performance Book](https://nnethercote.github.io/perf-book/))

### 10.3 边界测试：const fn 中的非编译期操作

```rust,compile_fail
const fn foo(x: i32) -> i32 {
    // ❌ 编译错误: Vec::new() 不是 const fn（在旧版本中）
    let v = Vec::new();
    x
}

fn main() {}
```

> **修正**: **Const fn**：
>
> 1) 函数体必须是编译期可计算的；
> 2) `Vec::new()` 在某些 Rust 版本中不是 `const fn`；
> 3) 编译期限制逐步放宽（`const_mut_refs`、`const_vec_string` 等）。

## 嵌入式测验（Embedded Quiz）

### 测验 1：Rust 默认使用什么求值策略？函数参数在调用前还是调用后求值？（理解层）

**题目**: Rust 默认使用什么求值策略？函数参数在调用前还是调用后求值？

<details>
<summary>✅ 答案与解析</summary>

Rust 使用 Call-by-Value（严格求值）。函数参数在进入函数体之前被求值（eager evaluation）。
</details>

---

### 测验 2：Call-by-Name 和 Call-by-Need 有什么共同点和区别？（理解层）

**题目**: Call-by-Name 和 Call-by-Need 有什么共同点和区别？

<details>
<summary>✅ 答案与解析</summary>

共同点：都是惰性求值，参数只在需要时才求值。区别：Call-by-Name 每次使用参数都重新求值；Call-by-Need（如 Haskell）第一次求值后缓存结果，后续直接使用缓存。
</details>

---

### 测验 3：`&&` 和 `||` 的短路求值（short-circuit evaluation）属于哪种求值策略的体现？（理解层）

**题目**: `&&` 和 `||` 的短路求值（short-circuit evaluation）属于哪种求值策略的体现？

<details>
<summary>✅ 答案与解析</summary>

属于非严格/惰性求值的一种受限形式：若左操作数已能决定结果，右操作数不求值。这是大多数严格语言中的例外。
</details>

---

### 测验 4：Rust 的 `Iterator` 惰性求值与 Haskell 的全局惰性求值有什么区别？（理解层）

**题目**: Rust 的 `Iterator` 惰性求值与 Haskell 的全局惰性求值有什么区别？

<details>
<summary>✅ 答案与解析</summary>

Rust 的惰性是局部的（仅在迭代器适配器链中），最终必须通过消耗方法触发。Haskell 的惰性是全局的，所有表达式默认延迟求值直到需要。
</details>

---

### 测验 5：为什么严格求值语言通常比惰性求值语言更容易预测内存和性能行为？（理解层）

**题目**: 为什么严格求值语言通常比惰性求值语言更容易预测内存和性能行为？

<details>
<summary>✅ 答案与解析</summary>

严格求值的求值时机和顺序是显式的（调用时立即执行），便于分析时间/空间复杂度。惰性求值可能因延迟链过长导致空间泄漏（space leak），性能分析更困难。
</details>

## 权威来源对照

| 来源 | 与本节对应的核心论点 |
|:---|:---|
| [Pierce — TAPL, §5-§11](https://www.cis.upenn.edu/~bcpierce/tapl/) | 类型化 λ 演算中的求值策略、类型安全与归约语义 |
| [Harper — PFPL, Part III](https://www.cs.cmu.edu/~rwh/pfpl/) | 结构化操作语义与求值上下文的形式化定义 |
| [Plotkin 1975 — Call-by-Name, Call-by-Value and the λ-Calculus](https://doi.org/10.1016/0304-3975(75)90017-1) | CPS 转换与两种求值策略的等价性 |
| [Wadler 1984 — Why Calculating is Better than Scheming](https://doi.org/10.1093/comjnl/27.2.115) | 惰性求值与等式推理的教学对比 |
| [Cambridge — OptComp 2025, Lambda Lifting & Evaluation Strategies](https://www.cl.cam.ac.uk/~na482/pdfs/) | 编译优化视角下的求值顺序与 lambda lifting |
| [Nottingham — PL Semantics, Evaluation Strategies](https://people.cs.nott.ac.uk/pszgmh/) | 函数式语言语义课程中的求值策略谱系 |
| [Wikipedia: Evaluation strategy](https://en.wikipedia.org/wiki/Evaluation_strategy) | 求值策略术语与跨语言速查 |

## 总结

- **L1**：求值策略决定表达式何时、如何被计算；Rust 默认严格 Call-by-Value，`Copy` 类型按位拷贝、`!Copy` 类型转移所有权。
- **L2**：Rust 通过显式借用（Borrowing） `&T`/`&mut T` 提供受限的 Call-by-Reference；`&&`/`||` 短路、`Future` 惰性构造、`lazy_static` 等是非严格求值的局部工程表达。
- **L3**：Rust 的求值策略选择是性能可预测性与表达力之间的权衡；理解 CBV/CBN/CPS 对形式化验证（如 RustBelt、Kani）和编译优化都有直接影响。

---

> **权威来源**: [Verus](https://github.com/verus-lang/verus) · [Kani](https://model-checking.github.io/kani/) · [Pierce — TAPL, §5-§11](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Harper — PFPL, Part III](https://www.cs.cmu.edu/~rwh/pfpl/) · [Wadler 1984 — Why Calculating is Better than Scheming](https://doi.org/10.1093/comjnl/27.2.115) · [Plotkin 1975 — Call-by-Name, Call-by-Value and the λ-Calculus](https://doi.org/10.1016/0304-3975(75)90017-1) · [Wikipedia: Evaluation strategy](https://en.wikipedia.org/wiki/Evaluation_strategy)
> **权威来源对齐变更日志**: 2026-07-10 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch L4](../../00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-10
**状态**: ✅ 权威来源对齐完成 (Batch L4)
