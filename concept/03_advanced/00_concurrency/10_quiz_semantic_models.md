# 测验：语义模型与跨语言对比（L3）

> **EN**: Semantic Models and Cross-Language Comparisons Quiz
> **Summary**: L3 standalone quiz on algebraic effects, dependent and refinement types, STM, distributed consensus, GPU/HPC compilation targets, and the unified language semantic model matrix spanning Rust vs Haskell/OCaml/Ada/SPARK/F#/D/Nim.
> **受众**: [进阶]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **内容分级**: [专家级]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链

---

> **来源**:
> [代数效应与效应处理器](../../04_formal/07_concurrency_semantics/04_algebraic_effects.md) ·
> [依赖类型与细化类型](../../04_formal/00_type_theory/10_dependent_refinement_types.md) ·
> [STM 形式语义](../../04_formal/07_concurrency_semantics/05_stm_semantics.md) ·
> [分布式共识与不可能性理论](../../04_formal/07_concurrency_semantics/06_distributed_consensus_theory.md) ·
> [统一语言 × 语义模型表达力矩阵](../../05_comparative/00_paradigms/05_language_semantic_model_matrix.md) ·
> [Rust vs Haskell](../../05_comparative/02_managed_languages/09_rust_vs_haskell.md) ·
> [分布式共识](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md) ·
> [语义模型图谱](../../00_meta/knowledge_topology/11_semantic_model_atlas.md) ·
> [Rust Standard Library — std::sync](https://doc.rust-lang.org/std/sync/) · [Rust Async Book](https://rust-lang.github.io/async-book/) ·
> [Plotkin & Pretnar 2009 — Handlers of Algebraic Effects](https://doi.org/10.1007/978-3-642-00590-9_7) ·
> [Harris et al. — Composable Memory Transactions](https://www.microsoft.com/en-us/research/publication/composable-memory-transactions/) ·
> [Ongaro & Ousterhout 2014 — Raft](https://raft.github.io/raft.pdf) ·
> [Fischer, Lynch, Paterson 1985 — FLP](https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf)
>
> **前置概念**:
> **后置概念**: [并发（Concurrency）语义模型](01_concurrency.md) · [Send/Sync 边界](04_send_sync_boundaries.md)
> [代数效应与效应处理器](../../04_formal/07_concurrency_semantics/04_algebraic_effects.md) ·
> [依赖类型与细化类型](../../04_formal/00_type_theory/10_dependent_refinement_types.md) ·
> [STM 形式语义](../../04_formal/07_concurrency_semantics/05_stm_semantics.md) ·
> [分布式共识与不可能性理论](../../04_formal/07_concurrency_semantics/06_distributed_consensus_theory.md) ·
> [语言语义模型矩阵](../../05_comparative/00_paradigms/05_language_semantic_model_matrix.md) ·
> [Rust vs Haskell](../../05_comparative/02_managed_languages/09_rust_vs_haskell.md) ·
> [Rust vs OCaml](../../05_comparative/02_managed_languages/10_rust_vs_ocaml.md) ·
> [Rust vs Ada/SPARK](../../05_comparative/01_systems_languages/07_rust_vs_ada_spark.md) ·
> [分布式共识](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md) ·
> [Const Generics](../../02_intermediate/01_generics/02_const_generics.md) ·
> [Concurrency](01_concurrency.md)
>
> **对应练习**:
> [`exercises/src/concurrency/`](../../../exercises/src/concurrency/) ·
> [`exercises/src/type_system/`](../../../exercises/src/type_system/)

---

> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题（能否编译 / 输出分析）+ 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`）的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: L3 独立测验——验证语义模型（代数效应、依赖/细化类型、STM、分布式共识）与跨语言语义模型矩阵（Rust vs Haskell/OCaml/Ada/SPARK/F#/D/Nim）的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、语言语义模型矩阵与 GPU/HPC 编译目标

本节考查 [统一语言 × 语义模型表达力矩阵](../../05_comparative/00_paradigms/05_language_semantic_model_matrix.md) 的六维度框架、效应系统评级，以及 Rust 在 GPU/HPC 编译目标上的现实路径：Q1 矩阵六维度、Q2 效应系统评级、Q3 GPU 编译目标选型。

### Q1. 🟢【单选】统一语言 × 语义模型表达力矩阵从哪六个维度刻画语言的语义模型？

- A. 语法糖、包管理、构建速度、IDE 支持、社区规模、学习曲线
- B. 内存安全（Memory Safety）模型、类型系统（Type System）表达力、效应系统、并发模型、验证生态系统、编译目标灵活性
- C. 范式数量、标准库大小、第三方库数量、性能基准、公司背书、发布年份
- D. 变量模型、控制流、数据结构、算法、网络协议、数据库

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：矩阵的六个维度彼此**正交**——一种语言可以在内存安全上得低分，却在类型系统或验证生态上得高分（例如 Agda）。特性清单会随版本变化，但底层语义模型（内存、类型、效应、并发、验证、编译目标）决定能力边界。评级标准以**工业可部署性**与**形式化强度**并重，而非纯粹理论表达力。[→ 语言语义模型矩阵 §二](../../05_comparative/00_paradigms/05_language_semantic_model_matrix.md)

</details>

---

### Q2. 🟢【单选】按矩阵的「效应系统」维度评级，下列对应关系哪一项正确？

- A. Rust = **A**（代数效应处理器）
- B. Haskell = **A**（代数效应处理器）
- C. Koka / Eff = **A**（代数效应处理器），Rust = **C+**（关键字效应 `async` / `unsafe`）
- D. OCaml = **D**（无显式效应系统）

<details>
<summary>✅ 答案与解析</summary>

**答案：C**

**解析**：Koka 与 Eff 把效应类型与 handler 集成进语言核心，评级 **A**；Rust 的效应是词法上下文标记（`async` / `const` / `unsafe`），评级 **C+**；Haskell 用 Monad（`IO`）把副作用建模为值，评级 **B**；OCaml 传统上用异常，5.x 引入代数效应处理器，评级 **B-** 而非 D。[→ 语言语义模型矩阵 §2.3](../../05_comparative/00_paradigms/05_language_semantic_model_matrix.md) · [→ 代数效应](../../04_formal/07_concurrency_semantics/04_algebraic_effects.md)

</details>

---

### Q3. 🟡【单选】某团队要用 Rust 编写跨厂商 GPU 计算内核。按矩阵「编译目标灵活性」维度与 Rust 1.97 工具链现状，最准确的路径判断是？

- A. Rust 完全无法编译到 GPU，必须改用 CUDA C++ 重写全部代码
- B. 生产首选 `wgpu` 计算着色器路线（跨厂商）；`nvptx64-nvidia-cuda` 目标与 `rust-gpu` 适合跟踪研究而非押注
- C. 唯一可行路径是 OpenCL 绑定
- D. 必须等待 Rust 2.0 才能触碰 GPU

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：Rust 在矩阵中编译目标灵活性评级 **A**（native / WASM / `no_std` / GPU），但 GPU 一格的现实是**生态路径**而非语言核心能力：`wgpu` 计算路线跨厂商且可用于生产；1.97 提升了 `nvptx64-nvidia-cuda` 目标维护等级（rustc 可直接产出 PTX），但没有 cuBLAS/cuDNN 类库生态，仍依赖非稳定组件，适合研究型 kernel；`rust-gpu`（SPIR-V 路线）是第三条路径。A 错在绝对化（CPU 侧可用 `cudarc` 驱动绑定）；C、D 无依据。[→ 语言语义模型矩阵 §2.6](../../05_comparative/00_paradigms/05_language_semantic_model_matrix.md)

</details>

---

## 二、代数效应与效应处理器

本节考查 [代数效应与效应处理器](../../04_formal/07_concurrency_semantics/04_algebraic_effects.md) 的核心语义：Q4 Rust 效应系统现状、Q5 handler 与异常的本质区别、Q6 `Result`/`?` 的效应解读。

### Q4. 🟢【判断】截至 Rust 1.97.0 stable，Rust 内置了用户可自定义的通用代数效应处理器（effect handler），允许用 `effect` 关键字声明新的效应操作。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：Rust 是**封闭效应系统**（closed effect system）：`async` / `const` / `unsafe` / `try` 等效应由语言预定义，用户不能声明新 effect，语言也不提供通用 `handle` 表达式。Rust 的探索方向是**关键字泛型**（Keyword Generics Initiative）——让既有效应可被统一抽象（如 `with async + throw`），而非引入 Koka 式的开放效应处理器。原因是有意识的设计权衡：零成本抽象（Zero-Cost Abstraction）、类型系统复杂度、向后兼容、所有权（Ownership）与续延的交互。[→ 代数效应 §3.1 / §3.4](../../04_formal/07_concurrency_semantics/04_algebraic_effects.md)

</details>

---

### Q5. 🟡【单选】效应处理器（effect handler）与异常处理（`try`/`catch`）的关键语义区别是？

- A. 效应处理器一定比异常处理慢
- B. 效应处理器可以通过续延（Continuation）**恢复**（resume）被暂停的计算，而异常 handler 只能终止或传播
- C. 异常可以携带值，效应操作不能携带参数
- D. 效应处理器只能在纯函数式语言中实现

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：`perform op` 暂停当前计算并把「操作之后的整个剩余计算」捕获为续延 `k`，handler 分支决定立即 resume、延迟 resume、丢弃续延（异常式）还是多次调用（非确定性）。异常 handler 没有续延，只能终止或向上传播。续延分**一次性**（one-shot：Koka、Rust async、OCaml 5 默认，可零成本实现）与**多次**（multi-shot：Eff，支持回溯但带运行时（Runtime）成本）。[→ 代数效应 §1.3 / §1.4](../../04_formal/07_concurrency_semantics/04_algebraic_effects.md)

</details>

---

### Q6. 🟡 以下代码的输出是什么？用代数效应视角解释 `?` 运算符的语义

```rust
fn may_fail(x: i32) -> Result<i32, &'static str> {
    if x < 0 {
        Err("negative")
    } else {
        Ok(x * 2)
    }
}

fn composed(x: i32) -> Result<i32, &'static str> {
    let y = may_fail(x)?;
    Ok(y + 1)
}

fn main() {
    println!("{:?}", composed(3));
    println!("{:?}", composed(-1));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：依次输出 `Ok(7)` 与 `Err("negative")`。

**解析**：`composed(3)`：`may_fail(3)` 返回 `Ok(6)`，`?` 解包得 `y = 6`，返回 `Ok(7)`。`composed(-1)`：`may_fail(-1)` 返回 `Err("negative")`，`?` 立即短路返回该 `Err`。

**效应视角**：`Result<T, E>` 把「可失败」编码进返回类型，`?` 等价于「若操作返回异常则提前返回，否则解包继续」——这是一次**异常 handler 的受限形式**：它只能**传播**异常，不能**恢复**或**转换**它。对比完整代数效应：调用者只声明「我需要可失败服务」，如何解释（传播 / 重试 / 默认值 / 日志）本应由外层 handler 决定。[→ 代数效应 §3.2](../../04_formal/07_concurrency_semantics/04_algebraic_effects.md)

</details>

---

## 三、依赖类型与细化类型

本节考查 [依赖类型与细化类型](../../04_formal/00_type_theory/10_dependent_refinement_types.md)：Q7 运行时值与类型的边界、Q8 const generics 维度编码、Q9 跨语言能力矩阵。

### Q7. 🟡【判断】在 Rust 1.97 中，函数的运行时参数值可以直接作为数组长度出现在返回类型中，例如 `fn f(n: usize) -> [u8; n]`。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：数组长度位置要求**编译期常量**，而 `n` 是运行时参数——编译器报 `E0435: attempt to use a non-constant value in a constant`。在 trait 签名或泛型（Generics）返回类型中使用关联常量投影（如 `[u8; Self::SIZE]`）同样需要尚未稳定的 `generic_const_exprs`。这正是 Rust 依赖类型片段的核心边界：**运行时值不能构造类型**；完整依赖类型语言（Idris/Agda）中值可以自由进入类型。[→ 依赖类型 §3.2 / §5.1](../../04_formal/00_type_theory/10_dependent_refinement_types.md)

</details>

---

### Q8. 🟡 以下代码能否编译？输出是什么？它体现了 Rust 依赖类型片段的哪种能力？

```rust
struct Matrix<const R: usize, const C: usize> {
    data: [[f64; C]; R],
}

impl<const R: usize, const C: usize> Matrix<R, C> {
    fn zeros() -> Self {
        Matrix { data: [[0.0; C]; R] }
    }
}

fn main() {
    let a = Matrix::<2, 3>::zeros();
    let b = Matrix::<3, 2>::zeros();
    println!("{}x{} {}x{}", a.data.len(), a.data[0].len(), b.data.len(), b.data[0].len());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译，输出 `2x3 3x2`。

**解析**：`Matrix<R, C>` 用 **const generics** 把矩阵维度（编译期常量）编码进类型——这是「值参数化的类型」，即依赖类型的受限片段。权威页中进一步的 `impl<const R, const C, const K> Mul<Matrix<C, K>> for Matrix<R, C>` 使 `Matrix<2,3> * Matrix<3,3> -> Matrix<2,3>` 合法，而维度错配（如 `Matrix<2,3> * Matrix<2,3>`）直接是**编译错误**而非运行时断言失败。这与依赖类型语言中「形状索引的张量」目标一致，区别是 Rust 只能在编译期常量上操作。[→ 依赖类型 §3.1](../../04_formal/00_type_theory/10_dependent_refinement_types.md)

</details>

---

### Q9. 🟡【多选】关于依赖类型与细化类型的跨语言对比，下列说法正确的有？（选出所有正确项）

- A. Idris 与 Agda 支持完整依赖类型（Π 类型 / Σ 类型 / 索引族），值可以进入类型
- B. Liquid Haskell 用细化类型（refinement types）把谓词交给 SMT 求解器自动判定
- C. Rust 的 const generics、关联常量与类型级编程是依赖类型的受限片段，只能操作编译期常量
- D. Rust 编译器内置 SMT 求解器，可自动验证任意用户谓词

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：A 正确——完整依赖类型中类型可以依赖于值（如长度索引向量 `Vect n a`）。B 正确——Liquid Haskell 的 `{v : Int | v >= 0}` 由 SMT 自动验证，属「轻量」细化路线。C 正确——Rust 片段限于编译期常量；Rust 生态的细化类型由外部工具（如 Flux、Prusti、Creusot）承担。D 错——rustc 不做任意谓词验证，借用（Borrowing）检查只覆盖所有权/生命周期（Lifetimes）不变式。[→ 依赖类型 §四](../../04_formal/00_type_theory/10_dependent_refinement_types.md)

</details>

---

## 四、STM 与分布式共识

本节考查软件事务内存（[STM 形式语义](../../04_formal/07_concurrency_semantics/05_stm_semantics.md)，工程对比见 [Rust vs Haskell §5.2](../../05_comparative/02_managed_languages/09_rust_vs_haskell.md)）与 [分布式共识与不可能性理论](../../04_formal/07_concurrency_semantics/06_distributed_consensus_theory.md)：Q10 STM 可组合性、Q11 FLP 不可能性、Q12 容错模型与选型决策树。

### Q10. 🟡【单选】Haskell STM（Software Transactional Memory）相比传统锁模型的核心优势是？

- A. STM 不需要任何运行时支持即可工作
- B. 事务**可组合**：两个独立的 `atomically` 事务可以安全地合并为一个新事务，`retry` / `orElse` 提供可组合的阻塞与选择
- C. STM 在语义上消除了所有竞态条件（race condition）
- D. STM 保证事务内数据零拷贝

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：可组合性是 STM 的设计核心——锁模型下合并两个加锁临界区必须重新设计全局加锁顺序以避免死锁，而 `atomically` 事务可以直接顺序组合。`retry` 阻塞当前事务直至涉及变量变化，`orElse` 在首个事务 retry 时尝试备选分支，两者都是**可组合**的阻塞与选择原语。C 错——STM 解决的是共享可变状态的原子性与死锁回避，逻辑层面的竞态条件仍可能存在。对照：Rust 标准库**没有** STM，共享状态安全靠编译期 `Send`/`Sync` + `Mutex`/无锁结构。[→ STM 形式语义 §2.3 / §2.4](../../04_formal/07_concurrency_semantics/05_stm_semantics.md) · [→ Rust vs Haskell §5.2](../../05_comparative/02_managed_languages/09_rust_vs_haskell.md)

</details>

---

### Q11. 🟡【判断】FLP 不可能结果指出：在纯异步系统（消息延迟无上界）中，即使只有一个进程可能崩溃，也不存在确定性共识算法能同时满足安全性和终止性。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：Fischer、Lynch、Paterson（JACM 1985）证明：纯异步（Async） + 单崩溃故障 ⟹ 无确定性算法同时保证安全性与终止性。工程上绕过 FLP 的经典策略：**故障检测器**（Failure Detectors）、**随机化**（Ben-Or / Rabin）、**部分同步**（Partial Synchrony，PBFT / Tendermint）、**领导者选举超时**（Raft 用随机超时打破对称性）。FLP 否定的不是「共识不可行」，而是「纯异步 + 确定性 + 必终止」三者不可兼得。[→ 分布式共识理论 §2.1 / §2.3](../../04_formal/07_concurrency_semantics/06_distributed_consensus_theory.md) · [→ 分布式共识生态 §1.2](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md)

</details>

---

### Q12. 🟡【多选】按容错模型与 [共识选型决策树](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md)，下列说法正确的有？（选出所有正确项）

- A. Raft 与 Paxos 容忍崩溃停止（Crash-Stop）故障，要求 f < n/2
- B. PBFT 与 HotStuff 容忍拜占庭（Byzantine）故障，要求 f < n/3
- C. 联盟链 / 许可网络且节点数 < 20 时，PBFT 是经典选择
- D. Raft 可以容忍拜占庭故障，因此可直接用于公链

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：A、B 正确——崩溃停止模型要求多数派（f < n/2），拜占庭模型要求三分之二多数（3f+1 法定人数，即 f < n/3）。C 正确——决策树中「联盟链 + 节点数 < 20」指向 PBFT（Hyperledger Fabric）；节点更多时 HotStuff 以线性通信 O(n) 胜出。D 错——Raft 只处理崩溃停止故障，不能容忍恶意节点；公链 / 无许可网络需要拜占庭容错（HotStuff / Tendermint），且 Raft 的即时最终性假设也与公链环境不符。[→ 分布式共识理论 §1.3 / §4.4](../../04_formal/07_concurrency_semantics/06_distributed_consensus_theory.md) · [→ 分布式共识生态 §1.3 / §6.2](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md)

</details>

---

## 五、跨语言语义模型对比

本节综合 Rust vs Haskell/OCaml/Ada/SPARK/F#/D/Nim 各权威页：Q13 并发模型对比、Q14 五语言语义模型辨析、Q15 依赖类型边界实测。

### Q13. 🟡【多选】关于 Rust 与 Haskell 的并发模型，下列说法正确的有？（选出所有正确项）

- A. Rust 标准库线程是 OS 线程（1:1 模型），靠 `Send`/`Sync` 在编译期排除数据竞争
- B. Haskell `forkIO` 创建的是 green threads（M:N 模型），由 GHC RTS 调度，创建成本极低
- C. Haskell 的默认不可变性意味着大部分数据无需同步即可安全共享
- D. Rust 标准库内置 STM 与 MVar 作为共享状态的主要抽象

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：A 正确——Rust 无运行时，线程即 OS 线程，数据竞争安全由类型系统在编译期保证。B 正确——GHC RTS 把海量绿色线程复用到少量 OS 线程上，可创建数百万线程。C 正确——不可变数据天然可共享，共享可变状态才需要 `STM`/`MVar`。D 错——Rust 标准库**没有 green threads**（1.0 之前曾有过，后被移除），也没有 STM/MVar；对应物是 `Mutex`/`RwLock`/channel 与 `async` 执行器。[→ Rust vs Haskell §5.3](../../05_comparative/02_managed_languages/09_rust_vs_haskell.md)

</details>

---

### Q14. 🔴【多选】综合 OCaml 5 / Ada SPARK / D / Nim / F# 的语义模型，下列说法正确的有？（选出所有正确项）

- A. OCaml 5 的效应处理器续延默认是**一次性**（one-shot）的，不允许安全地多次恢复，以兼容语言的命令式特征
- B. SPARK 通过剔除不可验证的 Ada 特性（无约束指针、非结构化控制等）并引入契约 + 自动定理证明，服务安全关键领域
- C. D 默认使用 GC，同时提供 `@safe` / `@trusted` / `@system` 三级安全属性，允许渐进式底层控制
- D. Nim 仅支持全手动内存管理，没有任何自动回收方案

<details>
<summary>✅ 答案与解析</summary>

**答案：A、B、C**

**解析**：A 正确——OCaml 5 默认一次性续延（Dolan et al. 2017），多次恢复与可变状态交互复杂。B 正确——SPARK 是 Ada 的可验证子集，契约由 GNATprove 自动证明，矩阵中验证生态评级 **A**。C 正确——D 的默认 GC + 三级属性对应矩阵中「GC 可选 / 手动」定位。D 错——Nim 提供**可切换**内存策略：默认 ORC（延期引用（Reference）计数 + 循环回收）、ARC（确定性引用计数）、`owned` 唯一引用与 `--mm:none` 全手动。F# 则以**计算表达式**（computation expressions：`async`/`task`/`seq`/`maybe`）统一效应抽象，与 Rust 的关键字效应形成对照。[→ Rust vs OCaml](../../05_comparative/02_managed_languages/10_rust_vs_ocaml.md) · [→ Rust vs Ada/SPARK](../../05_comparative/01_systems_languages/07_rust_vs_ada_spark.md) · [→ Rust vs D](../../05_comparative/01_systems_languages/08_rust_vs_d.md) · [→ Rust vs Nim](../../05_comparative/01_systems_languages/09_rust_vs_nim.md) · [→ Rust vs F#](../../05_comparative/02_managed_languages/11_rust_vs_fsharp.md)

</details>

---

### Q15. 🔴 以下代码能否编译？它揭示了 Rust 类型系统的哪条边界？

```rust,compile_fail,E0435
fn make_vec(n: usize) -> [u8; n] {
    [0u8; n]
}

fn main() {
    let v = make_vec(4);
    println!("{}", v.len());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**实测错误**：`error[E0435]: attempt to use a non-constant value in a constant`——`n` 是运行时参数，而数组长度位置要求常量。

**解析**：这揭示了 Rust 依赖类型片段的根本边界：**运行时值不能进入类型**。数组长度 `[u8; N]` 中的 `N` 必须是编译期已知的常量；完整依赖类型语言（Idris/Agda）允许类型依赖于任意值，代价是类型检查可能需要用户辅助证明。

**修复方案**——用 const 泛型把值提升到编译期：

```rust
fn make_array<const N: usize>() -> [u8; N] {
    [0u8; N]
}

fn main() {
    let v = make_array::<4>();
    assert_eq!(v.len(), 4);
    println!("{}", v.len());
}
```

**边界延伸**：即便在 const 泛型内，1.97 stable 也不允许泛型常量表达式（如 `[u8; N + 1]`，需要 `generic_const_exprs`）；细化谓词（如「非零」「已排序」）则由 Flux / Prusti / Creusot 等外部验证工具承担。[→ 依赖类型 §3.5 / §5.1](../../04_formal/00_type_theory/10_dependent_refinement_types.md)

</details>

---

## 六、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 13–15/15 | 🏆 语义模型与跨语言对比已内化 | 进阶至 [进程代数](../../04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md) 或 [线性化与一致性（Coherence）](../../04_formal/07_concurrency_semantics/02_linearizability_and_consistency.md) |
| 10–12/15 | ✅ 核心概念掌握 | 重读答错题对应的权威页小节，强化决策树应用 |
| 6–9/15 | 🔄 需巩固基础 | 重读 [代数效应](../../04_formal/07_concurrency_semantics/04_algebraic_effects.md) 与 [语言语义模型矩阵](../../05_comparative/00_paradigms/05_language_semantic_model_matrix.md) |
| 0–5/15 | 📚 建议重新开始 | 从 [语义模型图谱](../../00_meta/knowledge_topology/11_semantic_model_atlas.md) 建立全局认知，再逐页深入 |

---

## 嵌入式测验（Embedded Quiz）

本节为关于本测验自身使用方式的元测验（理解层），不计入上方 15 题计分。

### 测验 1：🟢 本文件是「语义模型与跨语言对比」的专项测验集。这类独立测验文件在知识体系中的主要作用是什么？（理解层）

**题目**: 本文件是「语义模型与跨语言对比」的专项测验集。这类独立测验文件在知识体系中的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供针对特定主题簇（语义模型 + 跨语言对比）的分层练习题，帮助学习者系统检验对多个人权威页（代数效应、依赖类型、STM、共识、语义模型矩阵）的综合掌握程度，补充各概念页末尾的嵌入式测验。
</details>

---

### 测验 2：🟢 本测验的题目大量引用 `concept/` 权威页。作答时遇到不确定的题目，最佳学习策略是什么？（理解层）

**题目**: 本测验的题目大量引用 `concept/` 权威页。作答时遇到不确定的题目，最佳学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先独立作答，再对照解析中的权威页链接回到对应概念页重新阅读相关小节，形成「测验—反馈—复习」闭环；语义模型类概念尤其建议对照 [语义模型图谱](../../00_meta/knowledge_topology/11_semantic_model_atlas.md) 定位其在九大模型族中的位置。
</details>

---

### 测验 3：🟢 本测验覆盖了 Rust vs Haskell/OCaml/Ada/SPARK/F#/D/Nim 多个对比页，为什么把这些语言放在同一份测验中？（理解层）

**题目**: 本测验覆盖了 Rust vs Haskell/OCaml/Ada/SPARK/F#/D/Nim 多个对比页，为什么把这些语言放在同一份测验中？

<details>
<summary>✅ 答案与解析</summary>

因为这些语言在 [语言语义模型矩阵](../../05_comparative/00_paradigms/05_language_semantic_model_matrix.md) 中共享同一套六维度坐标系（内存安全、类型表达力、效应、并发、验证、编译目标），放在一起考查可以检验学习者是否真正建立了「按语义模型维度定位语言」的统一视角，而不是孤立记忆每种语言的特性清单。
</details>

---

> **变更记录**: 2026-07-16 新建（语义模型对齐冲刺：L3 独立 quiz，15 题：代码阅读 3 / 单选 5 / 多选 4 / 判断 3；难度 🟢3 / 🟡10 / 🔴2；覆盖代数效应、依赖/细化类型、STM、分布式共识、GPU/HPC、语言语义模型矩阵与 Rust vs Haskell/OCaml/Ada/SPARK/F#/D/Nim）。
