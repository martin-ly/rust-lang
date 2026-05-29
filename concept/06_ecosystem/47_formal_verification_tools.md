# Formal Verification Tools（形式化验证工具生态）

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **A+S+P** — Application + Structure + Procedure
> **双维定位**: C×Eva — 评价 Rust 形式化验证工具的技术能力与适用边界
> **前置依赖**: [类型系统](../01_foundation/04_type_system.md) · [Unsafe Rust](../03_advanced/03_unsafe.md) · [形式化验证](../04_formal/05_verification_toolchain.md) · [生命周期](../01_foundation/03_lifetimes.md)
> **后置延伸**: [编译器内部原理](./45_compiler_internals.md) · [安全与密码学](./43_security_cryptography.md) · [嵌入式系统](./22_embedded_systems.md)

---

> **来源**: [Kani — Rust Verifier](https://github.com/model-checking/kani) ·
> [Prusti — Viper-based Verifier](https://www.pm.inf.ethz.ch/research/prusti.html) ·
> [MIRI — Undefined Behavior Detector](https://github.com/rust-lang/miri) ·
> [Creusot — WhyML-based Verifier](https://github.com/creusot-rs/creusot) ·
> [Verus — SMT-based Verifier](https://github.com/verus-lang/verus) ·
> [Flux — Refinement Types](https://github.com/liquid-rust/flux) ·
> [Aeneas — Rust Verification](https://github.com/AeneasVerif/aeneas) ·
> [RefinedRust — Iris-based](https://gitlab.mpi-sws.org/lgaeher/refinedrust)

## 📑 目录

- [Formal Verification Tools（形式化验证工具生态）](#formal-verification-tools形式化验证工具生态)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 形式化验证的层次模型](#11-形式化验证的层次模型)
    - [1.2 Rust 形式化验证的独特挑战](#12-rust-形式化验证的独特挑战)
  - [二、概念属性矩阵](#二概念属性矩阵)
  - [三、模型检验工具](#三模型检验工具)
    - [3.1 Kani：基于 CBMC 的 Rust 验证器](#31-kani基于-cbmc-的-rust-验证器)
    - [3.2 MIRI：运行时 UB 检测器](#32-miri运行时-ub-检测器)
  - [四、演绎验证工具](#四演绎验证工具)
    - [4.1 Prusti：Viper 分离逻辑验证器](#41-prustiviper-分离逻辑验证器)
    - [4.2 Creusot：Why3/WhyML 验证器](#42-creusotwhy3whyml-验证器)
    - [4.3 Verus：SMT-LIB 验证器](#43-verussmt-lib-验证器)
  - [五、类型系统扩展](#五类型系统扩展)
    - [5.1 Flux：精化类型（Refinement Types）](#51-flux精化类型refinement-types)
    - [5.2 Aeneas：向函数式语言的转换](#52-aeneas向函数式语言的转换)
  - [六、验证工具对比与选型](#六验证工具对比与选型)
    - [6.1 能力矩阵](#61-能力矩阵)
    - [6.2 选型决策树](#62-选型决策树)
  - [七、Rust 形式化验证的前沿](#七rust-形式化验证的前沿)
    - [7.1 RefinedRust：Iris 分离逻辑](#71-refinedrustiris-分离逻辑)
    - [7.2 RustBelt 验证框架](#72-rustbelt-验证框架)
  - [八、反命题与边界](#八反命题与边界)
    - [8.1 反命题树](#81-反命题树)
    - [8.2 边界极限](#82-边界极限)
  - [九、边界测试](#九边界测试)
    - [9.1 边界测试：Kani 数组越界未被 harness 覆盖（验证盲区）](#91-边界测试kani-数组越界未被-harness-覆盖验证盲区)
    - [9.2 边界测试：MIRI 无法检测未执行的 unsafe 路径（运行时盲区）](#92-边界测试miri-无法检测未执行的-unsafe-路径运行时盲区)
    - [9.3 边界测试：Prusti 前置条件过强导致合法调用被拒绝（假阴性）](#93-边界测试prusti-前置条件过强导致合法调用被拒绝假阴性)
  - [相关概念文件](#相关概念文件)

> **Bloom 层级**: 分析 → 评价
> **变更日志**:
>
> - v1.1 (2026-05-26): 补充 Generic Refinement Types (POPL 2025) — Flux 泛型精化类型扩展 [来源: Web Authority Alignment Sprint]
> - v1.0 (2026-05-26): 初始创建——覆盖模型检验（Kani/MIRI）、演绎验证（Prusti/Creusot/Verus）、精化类型（Flux）、前沿框架（RefinedRust/RustBelt）、选型决策矩阵

---

## 一、权威定义（Definition）

### 1.1 形式化验证的层次模型

> **[Hoare 1969 — An Axiomatic Basis for Computer Programming](https://doi.org/10.1145/363235.363259)** 形式化验证是使用数学方法证明程序满足其规范的过程。
> C.A.R. Hoare 提出的**霍尔逻辑**（Hoare Logic）建立了程序正确性的公理化基础：`{P} C {Q}` 表示若前置条件 `P` 成立，执行命令 `C` 后后置条件 `Q` 成立。

Rust 形式化验证生态可按验证方法分层：

```text
形式化验证方法谱系:

┌─────────────────────────────────────────────────────────────┐
│  Level 4 — 完全形式化证明（机器可检查）                      │
│  · 定理证明器: Coq, Isabelle/HOL, Lean                      │
│  · 应用: RustBelt (Iris), RefinedRust                       │
├─────────────────────────────────────────────────────────────┤
│  Level 3 — 自动演绎验证（SMT/分离逻辑求解器）                │
│  · Prusti (Viper), Creusot (Why3), Verus (Z3)              │
│  · 需手动写规范（前置/后置/循环不变式）                     │
├─────────────────────────────────────────────────────────────┤
│  Level 2 — 模型检验（有界验证）                              │
│  · Kani (CBMC), SMACK                                       │
│  · 自动探索状态空间，但受限于状态爆炸                        │
├─────────────────────────────────────────────────────────────┤
│  Level 1 — 运行时验证 / UB 检测                              │
│  · MIRI, AddressSanitizer, Valgrind                         │
│  · 只能检测执行到的代码路径                                  │
├─────────────────────────────────────────────────────────────┤
│  Level 0 — 类型系统（编译期基础保证）                        │
│  · Rust Borrow Checker, Flux (Refinement Types)             │
│  · 零运行时开销，但表达能力有限                              │
└─────────────────────────────────────────────────────────────┘
```

> **来源**: [Hoare 1969](https://doi.org/10.1145/363235.363259) ·
> [Formal Methods in Software Engineering](https://www.cis.upenn.edu/~lee/09cis500/lectures/verification.pdf) ·
> [Rust Formal Methods Working Group](https://rust-lang.github.io/formal-methods/)

### 1.2 Rust 形式化验证的独特挑战

Rust 的所有权、生命周期和借用检查器给形式化验证带来了独特挑战：

| **挑战** | **传统语言** | **Rust** | **影响** |
|:---|:---|:---|:---|
| **别名控制** | 任意指针别名 | 编译期保证无数据竞争 | 验证器可利用别名信息简化证明 |
| **生命周期** | 无（GC 或手动）| 编译期推断 | 验证器需建模生命周期包含关系 |
| **Unsafe 边界** | 全部代码都可能不安全 | 安全/Unsafe 明确分离 | 验证重点集中在 unsafe 块 |
| **Drop 语义** | 手动/ GC | 确定性析构 | 需验证资源释放的完备性 |
| **Panic 安全** | 异常机制 | 恐慌 + 展开/中止 | 需验证恐慌不破坏不变式 |

```rust
// Rust 形式化验证的核心难点示例

// 挑战 1: 生命周期子类型
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
// 验证器需证明: 返回值的生命周期不超过 x 和 y 的生命周期

// 挑战 2: Unsafe 块中的裸指针
unsafe fn raw_pointer_ops(ptr: *mut i32) {
    *ptr = 42;  // 验证器需证明 ptr 是有效且可写的
}

// 挑战 3: Send/Sync 的自动推导
struct MyData(*mut i32);  // 包含裸指针 → 默认不实现 Send/Sync
// 若手动实现 unsafe impl Send for MyData {}，
// 验证器需证明跨线程使用是安全的
```

> **来源**: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) ·
> [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) ·
> [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/)

---

## 二、概念属性矩阵

| **维度** | **Kani** | **MIRI** | **Prusti** | **Creusot** | **Verus** | **Flux** |
|:---|:---|:---|:---|:---|:---|:---|
| **验证方法** | 模型检验 (BMC) | 动态解释执行 | 分离逻辑 | 霍尔逻辑 | SMT + 所有权 | 精化类型 |
| **自动化程度** | 高（全自动）| 高（运行即检测）| 中（需规范）| 中（需规范）| 中（需规范）| 高（推断为主）|
| **Unsafe 支持** | ✅ 完整 | ✅ 完整 | ⚠️ 有限 | ⚠️ 有限 | ⚠️ 有限 | ❌ 不支持 |
| **循环/递归** | 需展开界限 | ✅ 自然支持 | ✅ 不变式 | ✅ 不变式 | ✅ 不变式 | ✅ 类型推导 |
| **性能开销** | 编译期高 | 运行时 10-100x | 编译期中 | 编译期中 | 编译期中 | 编译期低 |
| **学习曲线** | 低 | 低 | 高（分离逻辑）| 高（WhyML）| 中 | 中 |
| **成熟度** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ |
| **学术来源** | CBMC (CProver) | rustc 内部 | Viper (ETH) | Why3 (INRIA) | Ironclad Apps | Liquid Types |

> **来源**: [Kani Documentation](https://model-checking.github.io/kani/) ·
> [Prusti Paper](https://www.pm.inf.ethz.ch/publications/getpdf.php?bibname=Own&id=AstrauskasMuellerPoliSummers22.pdf) ·
> [Creusot Paper](https://hal.inria.fr/hal-03737818) ·
> [Verus Paper](https://www.microsoft.com/en-us/research/publication/verus-verifying-rust-programs-using-linear-ghost-types/)

---

## 三、模型检验工具

### 3.1 Kani：基于 CBMC 的 Rust 验证器

> **[Kani](https://github.com/model-checking/kani)** 是 Amazon Web Services (AWS) 开发的 Rust 代码模型检验器，基于 **CBMC**（C Bounded Model Checker）。
> 核心方法：**有界模型检验**（Bounded Model Checking, BMC）——将程序展开为 SAT/SMT 公式，由求解器自动验证。
> [来源: [Kani Documentation](https://model-checking.github.io/kani/)]

```rust
// Kani 验证示例：证明 Vec::push 不会 panic
#[cfg(kani)]
mod verification {
    use kani::any;

    #[kani::proof]
    fn test_vec_push() {
        let mut vec = Vec::new();
        let val: i32 = kani::any();  // 非确定性值
        vec.push(val);
        assert!(vec.len() == 1);
        assert!(vec[0] == val);
    }

    #[kani::proof]
    #[kani::unwind(10)]  // 循环展开 10 次
    fn test_vec_sum() {
        let len: usize = kani::any();
        kani::assume(len < 10);  // 假设 len < 10

        let mut vec = Vec::with_capacity(len);
        for i in 0..len {
            vec.push(kani::any::<i32>());
        }

        let sum: i64 = vec.iter().map(|&x| x as i64).sum();
        assert!(sum >= i64::MIN);
    }
}
```

**Kani 的核心能力**:

| **能力** | **说明** | **局限** |
| :--- | :--- | :--- |
| **有界验证** | 对所有可能的输入值进行符号执行 | 需限制循环展开次数 |
| **Panic 检测** | 自动检测数组越界、整数溢出、除零 | 仅验证有界路径 |
| **Unsafe 验证** | 可验证包含 unsafe 的代码 | 需信任 unsafe 的规范 |
| **内存安全** | 检测 use-after-free、双重释放 | 复杂数据结构状态爆炸 |

> **来源**: [Kani GitHub](https://github.com/model-checking/kani) ·
> [CBMC Documentation](https://diffblue.github.io/cbmc/) ·
> [Bounded Model Checking](https://en.wikipedia.org/wiki/Model_checking#Bounded_model_checking)

### 3.2 MIRI：运行时 UB 检测器

> **[MIRI](https://github.com/rust-lang/miri)** 是 Rust 的 MIR（中级中间表示）解释器，用于检测**未定义行为**（Undefined Behavior, UB）。
> 与 Kani 的静态验证不同，MIRI 在运行时解释执行 MIR，追踪内存访问的合法性。
> [来源: [MIRI Book](https://github.com/rust-lang/miri)]

```rust
// MIRI 检测到的 UB 示例

// ❌ 错误：违反 Stacked Borrows / Tree Borrows
fn undefined_behavior() {
    let mut x = 5;
    let raw1 = &mut x as *mut i32;
    let raw2 = &mut x as *mut i32;  // 创建第二个可变裸指针

    unsafe {
        *raw1 = 1;
        *raw2 = 2;  // MIRI: UB！两个 &mut 重叠，违反别名规则
    }
}

// ❌ 错误：使用已释放内存
fn use_after_free() {
    let ptr: *const i32;
    {
        let x = Box::new(42);
        ptr = &*x as *const i32;
    }  // x 在此 drop
    // unsafe { println!("{}", *ptr); }  // MIRI: UB！use-after-free
}

// ❌ 错误：未对齐读取
fn unaligned_read() {
    let bytes = [0u8; 8];
    let ptr = bytes.as_ptr() as *const u64;
    // unsafe { let _ = *ptr; }  // MIRI: UB！u64 需 8 字节对齐
}
```

**MIRI 的运行方式**:

```bash
# 安装 Miri
rustup component add miri

# 运行 Miri
cargo +nightly miri run

# 测试整个 crate
cargo +nightly miri test
```

> **来源**: [MIRI README](https://github.com/rust-lang/miri) ·
> [Rustonomicon — Undefined Behavior](https://doc.rust-lang.org/nomicon/what-unsafe-does.html) ·
> [Stacked Borrows Paper](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)

---

## 四、演绎验证工具

### 4.1 Prusti：Viper 分离逻辑验证器

> **[Prusti](https://www.pm.inf.ethz.ch/research/prusti.html)** 是 ETH Zurich 开发的 Rust 验证器，基于 **Viper** 验证基础设施。
> 核心方法：**分离逻辑**（Separation Logic）+ **权限基验证**（Permission-based Verification）。
> 用户通过 `#[requires(...)]` 和 `#[ensures(...)]` 注解写规范。
> [来源: [Prusti Documentation](https://viperproject.github.io/prusti-dev/user-guide/)]

```rust
// Prusti 规范注解示例
use prusti_contracts::*;

// 前置条件: n 必须 >= 0
// 后置条件: 返回值 >= 0
#[requires(n >= 0)]
#[ensures(result >= 0)]
fn factorial(n: i64) -> i64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

// 内存安全的验证：链表 push
struct Node {
    val: i32,
    next: Option<Box<Node>>,
}

impl Node {
    #[pure]  // 纯函数（无副作用）
    #[ensures(result >= 0)]
    fn len(&self) -> usize {
        match &self.next {
            None => 1,
            Some(next) => 1 + next.len(),
        }
    }

    #[requires(index < self.len())]
    #[ensures(result == old(self).lookup(index))]
    fn get_mut(&mut self, index: usize) -> &mut i32 {
        if index == 0 {
            &mut self.val
        } else {
            self.next.as_mut().unwrap().get_mut(index - 1)
        }
    }
}
```

**Prusti 的设计权衡**:

| **优势** | **劣势** |
|:---|:---|
| 分离逻辑天然适合所有权推理 | 学习曲线陡峭（需理解权限、分形）|
| 可验证复杂数据结构（链表、树）| 对泛型和 Trait 支持有限 |
| 与 Rust 所有权系统深度集成 | 编译速度慢（Viper 后端）|
| 自动推理循环不变式（部分）| 工具链维护活跃度下降 |

> **来源**: [Prusti User Guide](https://viperproject.github.io/prusti-dev/user-guide/) · [Viper Project](https://www.pm.inf.ethz.ch/research/viper.html) · [Separation Logic — Reynolds 2002](https://doi.org/10.1007/s001650200018)

### 4.2 Creusot：Why3/WhyML 验证器

> **[Creusot](https://github.com/creusot-rs/creusot)** 是 INRIA 开发的 Rust 验证器，将 Rust 代码翻译为 **WhyML**（Why3 验证语言），利用 Why3 的 SMT 求解器生态进行验证。特色：**浅层嵌入**（Shallow Embedding）—— Rust 类型直接映射到 WhyML 的对应概念。[来源: [Creusot Documentation](https://creusot-rs.github.io/creusot/)]

```rust
// Creusot 规范示例（Pearlite 规范语言）
use creusot_contracts::*;

// 使用 Pearlite（Rust 子集）写规范
#[requires(x@ >= 0)]  // @ 运算符将 Rust 值转为逻辑值
#[ensures(result@ == x@ * x@)]
fn square(x: u32) -> u32 {
    x * x
}

// 向量查找（带规范）
#[requires(0 <= index@ && index@ < vec.len())]
#[ensures(*result@ == vec[index@])]
fn get<T>(vec: &Vec<T>, index: usize) -> &T {
    &vec[index]
}
```

**Creusot 的翻译流水线**:

```text
Rust 源码 → Creusot 前端 → WhyML → Why3 → SMT 求解器 (Alt-Ergo/Z3/CVC4)
              │              │
              └── 浅层嵌入: Rust 的 &T → WhyML 的 borrowed T
                             Rust 的 Option<T> → WhyML 的 option t
                             Rust 的 Vec<T> → WhyML 的 seq t
```

> **来源**: [Creusot Paper — ICFP 2022](https://hal.inria.fr/hal-03737818) · [Why3 Platform](http://why3.lri.fr/) · [Pearlite Specification Language](https://creusot-rs.github.io/creusot/guide/pearlite.html)

### 4.3 Verus：SMT-LIB 验证器

> **[Verus](https://github.com/verus-lang/verus)** 是 Microsoft Research 开发的 Rust 验证器，专注于**系统软件验证**。核心设计：将 Rust 代码和规格翻译为 **SMT-LIB**，由 Z3 求解器验证。特色支持：**可执行规格**（Executable Specifications）和**幽灵类型**（Ghost Types）。[来源: [Verus Documentation](https://verus-lang.github.io/verus/)]

```rust
// Verus 验证示例
use vstd::prelude::*;

verus! {

// 规范函数（exec 模式可执行，proof 模式仅验证）
fn binary_search(v: &Vec<u64>, k: u64) -> (r: usize)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],  // 有序
    ensures
        r < v.len() ==> v[r as int] == k,  // 若找到则正确
        r == v.len() ==> forall|i: int| 0 <= i < v.len() ==> v[i] != k,  // 若未找到则不存在
{
    let mut lo = 0usize;
    let mut hi = v.len();

    while lo < hi
        invariant
            0 <= lo <= hi <= v.len(),
            forall|i: int| 0 <= i < lo ==> v[i] < k,
            forall|i: int| hi <= i < v.len() ==> v[i] > k,
    {
        let mid = lo + (hi - lo) / 2;
        if v[mid] == k {
            return mid;
        } else if v[mid] < k {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    v.len()
}

} // verus!
```

**Verus 的独特设计**:

| **特性** | **说明** |
|:---|:---|
| **幽灵类型 (`Ghost<T>`)** | 仅在验证时存在，运行时零开销 |
| **可执行规格** | 规格代码在编译后保留，可用于运行时检查 |
| **所有权追踪** | 利用 Rust 的所有权系统简化验证条件生成 |
| **线性类型** | 支持线性 ghost 状态，追踪资源使用 |

> **来源**: [Verus Paper — OSDI 2023](https://www.microsoft.com/en-us/research/publication/verus-verifying-rust-programs-using-linear-ghost-types/) · [Verus Guide](https://verus-lang.github.io/verus/guide/) · [Z3 SMT Solver](https://github.com/Z3Prover/z3)

---

## 五、类型系统扩展

### 5.1 Flux：精化类型（Refinement Types）

> **[Flux](https://github.com/liquid-rust/flux)** 是 UC San Diego 开发的 Rust 精化类型系统扩展。精化类型将**逻辑谓词**附加到类型上，例如 `i32{v: 0 <= v && v < 100}` 表示范围在 [0, 100) 的整数。Flux 在编译期自动推断和检查这些谓词。[来源: [Flux Paper — PLDI 2023](https://ranjitjhala.github.io/static/flux-pldi23.pdf)]

```rust
// Flux 精化类型示例
// 使用 #[flux::sig(...)] 注解类型约束

#[flux::sig(fn(x: i32{v: v >= 0}) -> i32{v: v >= 0})]
pub fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}

#[flux::sig(fn(arr: &[i32{v: v >= 0}]) -> i32{v: v >= 0})]
pub fn sum_positive(arr: &[i32]) -> i32 {
    let mut sum = 0;
    for i in 0..arr.len() {
        sum += arr[i];  // Flux 验证: arr[i] >= 0，sum 保持 >= 0
    }
    sum
}

// 向量索引安全
#[flux::sig(fn(vec: &Vec<i32>, i: usize{0 <= i && i < vec.len()}) -> i32)]
pub fn safe_get(vec: &Vec<i32>, i: usize) -> i32 {
    vec[i]  // Flux 保证不会发生越界
}
```

**Flux vs 标准 Rust 类型系统**:

```text
标准 Rust:        Vec<i32>          →  编译期仅保证是 i32 向量
Flux 精化类型:    Vec<i32{v: v>0}>  →  编译期还保证所有元素 > 0

优势:
  · 零运行时开销（谓词在编译期擦除）
  · 自动推断（通常无需手动写谓词）
  · 与 Rust 类型系统无缝集成

局限:
  · 不支持 unsafe 代码
  · 复杂数据结构（如自定义树）的谓词可能难以表达
  · 求解器可能超时
```

> **来源**: [Flux GitHub](https://github.com/liquid-rust/flux) · [Liquid Types — PLDI 2008](https://goto.ucsd.edu/~rjhala/papers/liquid_types_pldi08.pdf) · [Refinement Types Survey](https://arxiv.org/abs/2010.07763)

> **2025 最新进展 — Generic Refinement Types (POPL 2025)**: Flux 团队将精化类型扩展到**泛型上下文**，解决了原始 Flux 无法处理泛型函数（如 `fn max<T: Ord>(a: T, b: T) -> T`）的精化谓词问题。Generic Refinement Types 允许类型参数携带精化约束（如 `T{v: v >= 0}`），并通过**约束抽象**（Constraint Abstraction）在实例化时求解具体谓词。这是精化类型从"特定类型上的轻量验证"向"通用库级验证"的关键跃迁。[来源: [POPL 2025 — Lehmann et al., "Generic Refinement Types"](https://dl.acm.org/doi/10.1145/3704886)]

### 5.2 Aeneas：向函数式语言的转换

> **[Aeneas](https://github.com/AeneasVerif/aeneas)** 是 Inria 和 Microsoft Research 合作开发的项目，将 Rust 代码翻译为**纯函数式语言**（Lean、Coq、F*），利用交互式定理证明器进行验证。核心方法：**基于区域的内存模型**（Region-based Memory Model）——将 Rust 的所有权系统显式建模为区域效应。[来源: [Aeneas Paper — ICFP 2022](https://hal.science/hal-04196909/document)]

```text
Aeneas 翻译流水线:

Rust MIR
   │
   ▼ (Aeneas 前端)
基于区域的纯函数式表示
   │
   ├──→ Lean 4 代码 → 交互式证明
   ├──→ Coq 代码 → 交互式证明
   └──→ F* 代码 → SMT + 交互式证明

关键洞察:
  Rust 的 &mut T  →  函数式表示中的 "更新后返回新状态"
  Rust 的 ownership →  线性类型 / 区域参数
```

> **来源**: [Aeneas GitHub](https://github.com/AeneasVerif/aeneas) · [Aeneas Charon (Rust → LLBC)](https://github.com/AeneasVerif/charon) · [Lean 4](https://lean-lang.org/)

---

## 六、验证工具对比与选型

### 6.1 能力矩阵

| **验证目标** | **Kani** | **MIRI** | **Prusti** | **Creusot** | **Verus** | **Flux** |
|:---|:---|:---|:---|:---|:---|:---|
| **数组越界** | ✅ 自动 | ✅ 运行时 | ✅ 规范+自动 | ✅ 规范+自动 | ✅ 规范+自动 | ✅ 自动推断 |
| **整数溢出** | ✅ 自动 | ✅ 运行时 | ✅ 自动 | ✅ 自动 | ✅ 自动 | ⚠️ 部分 |
| **内存泄漏** | ✅ 自动 | ❌ 不检测 | ✅ 自动 | ✅ 自动 | ✅ 自动 | N/A |
| **并发安全** | ⚠️ 有限 | ⚠️ 有限 | ❌ 不支持 | ❌ 不支持 | ⚠️ 部分 | ❌ 不支持 |
| **功能正确性** | ⚠️ 需断言 | ❌ 不验证 | ✅ 完整规范 | ✅ 完整规范 | ✅ 完整规范 | ⚠️ 部分 |
| **泛型/Trait** | ✅ 支持 | ✅ 支持 | ⚠️ 有限 | ⚠️ 有限 | ✅ 良好 | ⚠️ 有限 |
| **Unsafe 代码** | ✅ 支持 | ✅ 支持 | ❌ 不支持 | ❌ 不支持 | ⚠️ 有限 | ❌ 不支持 |
| **CI 集成** | ✅ cargo kani | ✅ cargo miri | ⚠️ 复杂 | ⚠️ 复杂 | ✅ cargo verus | ⚠️ 实验性 |

> **来源**: [Kani vs MIRI](https://model-checking.github.io/kani/tutorial-kani-rustc.html) · [Verus vs Prusti](https://verus-lang.github.io/verus/guide/compare.html)

### 6.2 选型决策树

```text
是否需要验证功能正确性（而不仅是安全性）？
  ├── 否 → 只需检测 UB/内存错误？
  │         ├── 是 → 有 CI 预算？
  │         │         ├── 是 → Kani（有界模型检验）✅
  │         │         └── 否 → MIRI（定期运行）✅
  │         └── 否 → 需要类型级约束？
  │                   ├── 是 → Flux（精化类型）✅
  │                   └── 否 → 标准 Rust 类型系统 ✅
  └── 是 → 需要验证 unsafe 代码？
            ├── 是 → Kani（唯一支持完整 unsafe 的验证器）✅
            └── 否 → 团队熟悉哪种规范语言？
                      ├── 分离逻辑 / Viper → Prusti ✅
                      ├── WhyML / Coq → Creusot ✅
                      ├── SMT / Z3 → Verus ✅
                      └── 无偏好 → Verus（生态最活跃）✅
```

> **来源**: [Formal Methods for Rust — Rust Lang Blog](https://blog.rust-lang.org/inside-rust/2023/03/17/formal-methods.html) · [Rust Verification Workshop](https://rustverify.com/)

---

## 七、Rust 形式化验证的前沿

### 7.1 RefinedRust：Iris 分离逻辑

> **[RefinedRust](https://gitlab.mpi-sws.org/lgaeher/refinedrust)** 是 MPI-SWS 开发的项目，使用 **Iris** 分离逻辑框架在 Coq 中验证 Rust 程序。与 Prusti 不同，RefinedRust 不依赖自动化求解器，而是生成可在 Coq 中手动证明的验证条件。适合需要**最高可信度**的场景（如密码学、安全关键系统）。[来源: [RefinedRust Paper — OOPSLA 2024](https://dl.acm.org/doi/10.1145/3689738)]

```text
RefinedRust 验证流水线:

Rust 源码
   │
   ▼ (Rust 编译器插件)
Rust 类型 + 用户规范
   │
   ▼ (RefinedRust 翻译)
Iris 分离逻辑公式
   │
   ▼ (Coq 证明)
机器可检查的证明

特点:
  · 最高可信度（Coq 证明 + Iris 逻辑）
  · 可验证 unsafe 代码（需手动写内存模型规范）
  · 工作量巨大（每行代码可能需要数行证明）
  · 目前为研究原型
```

> **来源**: [RefinedRust GitLab](https://gitlab.mpi-sws.org/lgaeher/refinedrust) · [Iris Project](https://iris-project.org/) · [Coq Proof Assistant](https://coq.inria.fr/)

### 7.2 RustBelt 验证框架

> **[RustBelt](https://plv.mpi-sws.org/rustbelt/)** 是 MPI-SWS 的奠基性工作（POPL 2018），首次在数学上证明了 Rust 类型系统的**语义正确性**：如果程序通过借用检查器，则它确实是内存安全的。RustBelt 使用 **Iris** 分离逻辑在 Coq 中形式化了 Rust 核心语言（包括生命周期、借用、共享/独占引用）。[来源: [RustBelt Paper — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)]

```text
RustBelt 的核心定理:

Theorem (RustBelt): 对于任何通过 Rust 借用检查器的程序 P，
  若 P 的所有 unsafe 块满足其声明的规范，
  则 P 不会出现以下未定义行为:
    · use-after-free
    · 双重释放
    · 数据竞争
    · 悬垂指针解引用

技术路线:
  1. 定义 λRust：Rust 核心语言的 λ 演算
  2. 在 Iris 中定义 λRust 的操作语义
  3. 证明类型系统规则在语义上是 sound 的
  4. 将标准库中的 unsafe 原语（Box, Rc, Arc, Vec）建模为 Iris 资源代数
```

**RustBelt 的后续工作**:

| **项目** | **贡献** | **状态** |
|:---|:---|:---|
| **RustBelt** | 证明 λRust 类型系统的 soundness | 已完成（POPL 2018）|
| **Stacked Borrows** | 定义 Rust 的别名模型 | 已完成（POPL 2021）|
| **Tree Borrows** | 改进别名模型，更宽容 | 活跃（PLDI 2025）|
| **RefinedRust** | 用户代码的 Iris 验证 | 研究中（OOPSLA 2024）|

> **来源**: [RustBelt Project](https://plv.mpi-sws.org/rustbelt/) · [RustBelt Logical Relations](https://plv.mpi-sws.org/rustbelt/18/07/types-as-propositions.html) · [Iris Tutorial](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf)

---

## 八、反命题与边界

### 8.1 反命题树

```text
反命题 1: "形式化验证可以消除所有 Rust 程序中的 bug"
├── 前提: 形式化验证比测试更完备
├── 反驳:
│   ├── 验证范围限制：Kani 只验证有界路径，MIRI 只检测执行到的路径
│   ├── 规范错误：验证器只检查"程序是否符合规范"，但规范本身可能有错
│   ├── 工具限制：泛型、高阶函数、复杂 Trait bound 可能超出验证器能力
│   └── 可信计算基（TCB）：验证器本身可能有 bug（Kani 依赖 CBMC，Prusti 依赖 Viper）
└── 根结论: ❌ 形式化验证显著减少特定类别的 bug，但不能替代测试、代码审查和设计验证。

反命题 2: "Unsafe Rust 无法被形式化验证"
├── 前提: Unsafe 代码绕过了借用检查器，验证器无法推理
├── 反驳:
│   ├── Kani 可直接验证包含 unsafe 的代码（通过符号执行）
│   ├── RustBelt/RefinedRust 使用分离逻辑显式建模 unsafe 的内存操作
│   └── Verus 支持 ghost 状态追踪 unsafe 块的资源使用
└── 根结论: ❌ Unsafe Rust 可以被验证，但需要更多的手动规范（尤其是内存模型）。
           标准库中的 unsafe 原语（Box, Vec, Rc）已在 RustBelt 中被验证。

反命题 3: "形式化验证工具已经成熟到可以在生产环境日常使用"
├── 前提: Rust 验证工具与编译器一样可靠
├── 反驳:
│   ├── Prusti 的维护活跃度已下降，不支持最新 Rust 版本
│   ├── Flux 和 Aeneas 仍处于研究阶段，API 不稳定
│   ├── 编译时间开销：验证可能比编译慢 10-100 倍
│   └── 学习曲线：写规范（前置/后置/不变式）需要专门的培训
└── 根结论: ❌ 目前只有 Kani 和 MIRI 达到日常可用水平。演绎验证工具（Prusti/Creusot/Verus）
           适合安全关键模块的定向验证，不适合整个大型项目。
```

> **来源**: [Formal Methods Reality Check](https://www.hillelwayne.com/post/formally-verifying/) · [Kani Production Use](https://model-checking.github.io/kani/publications.html) · [Verus Production Use](https://github.com/verus-lang/verus/blob/main/IMPACT.md)

### 8.2 边界极限

| **边界** | **现状** | **理论极限** | **工程影响** |
|:---|:---|:---|:---|
| **Kani 循环展开** | 默认 0（需手动指定）| 状态爆炸 | 复杂算法需简化或拆分 |
| **MIRI 执行时间** | 10-100x  slowdown | 解释执行固有开销 | CI 中只运行关键 unsafe 模块 |
| **Prusti 支持版本** | Rust 1.70 | 最新 stable | 无法验证使用新特性的代码 |
| **SMT 求解器超时** | Z3 默认 30s | 不可判定问题 | 需简化规范或增加 hints |
| **unsafe 验证覆盖率** | 标准库原语已验证 | 所有 unsafe 代码 | 手动规范工作量巨大 |
| **并发验证** | 几乎不支持 | 状态空间爆炸 | 目前仅支持顺序代码 |

> **来源**: [Kani Limitations](https://model-checking.github.io/kani/limitations.html) · [MIRI Performance](https://github.com/rust-lang/miri#miri-is-slow) · [SMT Solver Complexity](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories#Complexity)

---

## 九、边界测试

### 9.1 边界测试：Kani 数组越界未被 harness 覆盖（验证盲区）

```rust,ignore
// ❌ 错误：Kani 只验证有 harness 的函数，未覆盖的函数仍有 bug

fn unchecked_access(arr: &[i32], idx: usize) -> i32 {
    arr[idx]  // 若 idx >= arr.len()，此处 panic！
}

#[kani::proof]
fn test_safe_access() {
    let arr = vec![1, 2, 3];
    let _ = safe_access(&arr, 1);  // 只验证 safe_access，未验证 unchecked_access
}

fn safe_access(arr: &[i32], idx: usize) -> i32 {
    if idx < arr.len() { arr[idx] } else { 0 }
}
```

> **修正**: Kani 的验证范围仅限于有 `#[kani::proof]` 注解的函数。未被 harness 覆盖的代码仍需通过测试和代码审查保证正确性。
> **来源**: [Kani Tutorial](https://model-checking.github.io/kani/tutorial-first-steps.html) · [Kani Coverage](https://model-checking.github.io/kani/coverage-report.html)

### 9.2 边界测试：MIRI 无法检测未执行的 unsafe 路径（运行时盲区）

```rust,ignore
// ❌ 错误：MIRI 只检测执行到的代码路径
fn conditional_ub(flag: bool) {
    let mut x = 5;
    if flag {
        let raw = &mut x as *mut i32;
        unsafe {
            *raw = 1;
        }
    } else {
        // 此分支没有 unsafe，但也没有被测试覆盖
        let _ = x;
    }
}

fn main() {
    conditional_ub(false);  // MIRI 运行时只执行 false 分支，true 分支的 UB 未被发现！
}
```

> **修正**: MIRI 需要结合**高覆盖率测试**使用。使用 `cargo miri test` 运行所有测试用例，确保尽可能多的代码路径被执行。对于安全关键代码，结合 Kani 进行静态验证。
> **来源**: [MIRI Book](https://github.com/rust-lang/miri) · [Code Coverage in Rust](https://doc.rust-lang.org/rustc/instrument-coverage.html)

### 9.3 边界测试：Prusti 前置条件过强导致合法调用被拒绝（假阴性）

```rust,ignore
// ❌ 错误：前置条件过强
use prusti_contracts::*;

#[requires(x > 0)]  // 过于严格！x == 0 也是合法输入
#[ensures(result >= 0)]
fn sqrt_approx(x: f64) -> f64 {
    x.sqrt()  // sqrt(0) = 0 是合法的
}

fn caller() {
    let _ = sqrt_approx(0.0);  // Prusti 错误: 前置条件不满足！
}
```

> **修正**: 写规范时需仔细考虑边界条件。前置条件应恰好描述函数要求的最小条件：
>
> ```rust
> #[requires(x >= 0)]  // ✅ 正确的最小前置条件
> #[ensures(result >= 0)]
> fn sqrt_approx(x: f64) -> f64 { x.sqrt() }
> ```
>
> **来源**: [Prusti Contracts](https://viperproject.github.io/prusti-dev/user-guide/verify/specifications.html) · [Design by Contract](https://en.wikipedia.org/wiki/Design_by_contract)

---

## 相关概念文件

- [编译器内部原理](./45_compiler_internals.md) — rustc 管线、MIR、借用检查器
- [安全与密码学](./43_security_cryptography.md) — 侧信道防护、常量时间操作
- [Unsafe Rust](../03_advanced/03_unsafe.md) — Miri、UB、别名模型
- [形式化验证](../04_formal/05_verification_toolchain.md) — 定理证明器、SMT、分离逻辑
- [类型系统](../01_foundation/04_type_system.md) — 类型论、泛型、Trait
- [生命周期](../01_foundation/03_lifetimes.md) — 借用规则、NLL、Polonius
- [并发编程](../03_advanced/01_concurrency.md) — Send/Sync、数据竞争
- [嵌入式系统](./22_embedded_systems.md) — `#![no_std]`、资源受限验证
- [版本跟踪](../07_future/05_rust_version_tracking.md) — Rust 语言演进对验证工具的影响

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust Standard Library](https://doc.rust-lang.org/std/)
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)
