> **内容分级**: [专家级]

# 现代 Rust 验证工具生态（2025-2026）
>
> **EN**: Modern Verification Tools
> **Summary**: Modern Verification Tools: formal methods foundations, semantics, and verification techniques relevant to Rust.
> ⚠️ **声明**: 本文件使用形式化符号辅助直觉理解，所呈现的"定理/引理/推论"为**教学类比**，非经机器验证的严格数学证明。如需严格形式化验证，请参考 [Verus](https://github.com/verus-lang/verus)、[Kani](https://model-checking.github.io/kani/)、[Coq](https://coq.inria.fr/)。
>
> **受众**: [研究者]
> **层级**: L4 形式化理论 → L7 前沿
> **A/S/P 标记**: **P** — Procedure
> **双维定位**: F×Eva — 评估现代验证工具的适用性与局限
> **前置概念**: [Verification Toolchain](05_verification_toolchain.md) · [Hoare 逻辑](../03_operational_semantics/15_hoare_logic.md) · [RustBelt](../02_separation_logic/04_rustbelt.md)
> **主要来源**: [AutoVerus arXiv 2025] · [Kani 0.65 Release] · [ESBMC Rust] · [RFC #3842 Safety Tags](https://github.com/rust-lang/rfcs/pull/3842) · [TrustInSoft] · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> **来源**: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) · [RustBelt](https://plv.mpi-sws.org/rustbelt/) · [Verus](https://verus-lang.github.io/verus/) · [Kani](https://model-checking.github.io/kani/) · [Miri](https://github.com/rust-lang/miri)
---

> **后置概念**: [Comparative Studies](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **前置依赖**: [Traits](../../02_intermediate/00_traits/01_traits.md) · [Generics](../../02_intermediate/01_generics/02_generics.md)
> **前置依赖**: [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md)

## 目录

- [现代 Rust 验证工具生态（2025-2026）](#现代-rust-验证工具生态2025-2026)
  - [目录](#目录)
  - [AutoVerus：LLM 辅助自动证明合成](#autoverusllm-辅助自动证明合成)
    - [核心思想](#核心思想)
    - [能力边界](#能力边界)
    - [概念示例（伪代码）](#概念示例伪代码)
  - [Kani 0.65+：循环契约与 Autoharness](#kani-065循环契约与-autoharness)
    - [新特性 1：循环契约](#新特性-1循环契约)
    - [新特性 2：Autoharness](#新特性-2autoharness)
    - [验证示例：安全包装器](#验证示例安全包装器)
  - [ESBMC for Rust：基于 SMT 的符号执行](#esbmc-for-rust基于-smt-的符号执行)
    - [核心能力](#核心能力)
    - [Rust 验证示例](#rust-验证示例)
    - [C/Rust FFI 验证](#crust-ffi-验证)
  - [Safety Tags：机器可读的安全契约](#safety-tags机器可读的安全契约)
    - [语法设计（提案阶段）](#语法设计提案阶段)
    - [工具链集成愿景](#工具链集成愿景)
    - [状态](#状态)
  - [TrustInSoft：C/Rust 混合代码的抽象解释](#trustinsoftcrust-混合代码的抽象解释)
    - [抽象解释原理](#抽象解释原理)
    - [Rust 支持状态](#rust-支持状态)
  - [选型速查表（2026）](#选型速查表2026)
  - [快速开始：工具安装与运行](#快速开始工具安装与运行)
    - [Miri（Rust 官方动态分析器）](#mirirust-官方动态分析器)
    - [Kani（AWS 有界模型检查器）](#kaniaws-有界模型检查器)
    - [BorrowSanitizer（运行时（Runtime）借用（Borrowing）检查 Sanitizer）](#borrowsanitizer运行时借用检查-sanitizer)
    - [Verus（Microsoft 演绎验证器）](#verusmicrosoft-演绎验证器)
  - [嵌入式测验](#嵌入式测验)
  - [相关工具交叉索引](#相关工具交叉索引)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：`cargo-kani` 与 `cargo-fuzz` 在验证方法上有什么区别？（理解层）](#测验-1cargo-kani-与-cargo-fuzz-在验证方法上有什么区别理解层)
    - [测验 2：Miri 能检测哪些类别的未定义行为（UB）？（理解层）](#测验-2miri-能检测哪些类别的未定义行为ub理解层)
    - [测验 3：为什么即使有了形式化验证，仍然需要传统测试？（理解层）](#测验-3为什么即使有了形式化验证仍然需要传统测试理解层)

---

## AutoVerus：LLM 辅助自动证明合成

> **定位**: 利用大语言模型（LLM）自动生成 Verus 证明注解，降低形式化验证的门槛。

### 核心思想

传统形式化验证的最大瓶颈不是编写规范，而是**编写证明**。AutoVerus 通过以下 pipeline 自动化这一过程：

```text
Rust 代码 + 自然语言规范
        ↓
   LLM (GPT-4o / Claude)
        ↓
   生成候选 Verus 注解 (requires/ensures/invariant)
        ↓
   Verus 验证器反馈（成功 / 反例 / 超时）
        ↓
   LLM 迭代修复（错误定位 → 猜测修复 → 重验证）
        ↓
   可编译通过的 Verus 注解
```

### 能力边界

| 场景 | AutoVerus 成功率 | 人工仍需介入 |
|:---|:---:|:---|
| 简单循环不变量 | ~75% | 复杂归纳假设 |
| 递归函数终止性 | ~60% | 良基关系构造 |
| 数据结构不变量 | ~45% | 幽灵状态（ghost state）管理 |
| 并发协议 | ~20% | 原子操作（Atomic Operations）序列的线性化证明 |

> **关键洞察**: AutoVerus 不是取代验证专家，而是将专家的时间从"写证明"重新分配到"审阅 LLM 输出、构造反例、设计归纳策略"。

### 概念示例（伪代码）

```rust
// 人工编写的 Rust 函数
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = arr.len();
    while low < high {
        let mid = low + (high - low) / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => low = mid + 1,
            std::cmp::Ordering::Greater => high = mid,
        }
    }
    None
}

// AutoVerus 生成的 Verus 注解（示例）
// requires: forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
// ensures: match result {
//     Some(idx) => 0 <= idx < arr.len() && arr[idx] == target,
//     None => forall|i: int| 0 <= i < arr.len() ==> arr[i] != target,
// }
// invariant: 0 <= low <= high <= arr.len()
// invariant: forall|i: int| 0 <= i < low ==> arr[i] < target
// invariant: forall|i: int| high <= i < arr.len() ==> arr[i] > target
```

**权威来源**: [AutoVerus — arXiv 2025](https://arxiv.org/abs/2409.13082) · [Verus Lang](https://github.com/verus-lang/verus/guide/)

---

## Kani 0.65+：循环契约与 Autoharness

> **定位**: AWS 开发的 Rust 有界模型检查器，0.65 版本引入循环契约（Loop Contracts）和自动测试 harness 生成（Autoharness），大幅扩展验证范围。
>
> 📚 **深度概念页**: 更系统的 Kani 教程、项目内可运行示例与工具选型对比，参见 [Kani：Rust 有界模型检查器](32_kani.md)。

### 新特性 1：循环契约

Kani 传统上需要**展开循环**（unrolling），对循环次数有上界限制。0.65+ 引入类似 Dafny/Verus 的循环契约：

```rust,ignore
#[kani::modifies(a)]
#[kani::ensures(
    forall|i: usize| (0 <= i && i < a.len()) ==> a[i] == old(a)[i] + 1
)]
fn increment_all(a: &mut [u32]) {
    for i in 0..a.len() {
        a[i] += 1;
    }
}
```

> `#[kani::modifies(...)]` 声明函数修改的内存位置；`#[kani::ensures(...)]` 声明后置条件。循环体内部不再需要展开，验证器通过归纳法处理。

### 新特性 2：Autoharness

传统上，Kani 需要人工编写 `#[kani::proof]` 函数来设置测试场景：

```rust,ignore
#[kani::proof]
fn check_increment() {
    let mut arr = kani::vec::any_vec::<u32, 5>();
    increment_all(&mut arr);
}
```

Autoharness 自动生成这些 harness：

```bash
# 自动生成并运行 harness
kani autoharness --harness-depth 2 --function increment_all
```

| 参数 | 含义 |
|:---|:---|
| `--harness-depth` | 生成 harness 时递归调用其他函数的深度 |
| `--gen-contracts` | 同时生成函数契约（requires/ensures）草案 |

### 验证示例：安全包装器

```rust,ignore
// 验证：Vec::push 不会导致缓冲区溢出
#[kani::proof]
fn verify_vec_push_safety() {
    let mut v: Vec<u32> = kani::vec::any_vec::<u32, 100>();
    let elem: u32 = kani::any();
    v.push(elem); // Kani 验证：capacity 检查 + reallocation 安全
    assert!(v.last() == Some(&elem));
}
```

**权威来源**: [Kani 0.65 Release Notes](https://model-checking.github.io/kani/) · [AWS Kani Blog](https://aws.amazon.com/blogs/aws/)

---

## ESBMC for Rust：基于 SMT 的符号执行

> **定位**: 经典 C 验证工具 ESBMC（Efficient SMT-based Bounded Model Checker）的 Rust 前端，支持跨语言验证（C ↔ Rust FFI）。

### 核心能力

ESBMC 与 Kani 的区别：

| 维度 | Kani | ESBMC |
|:---|:---|:---|
| 后端 | CBMC / SAT | SMT (Z3, Yices, Boolector) |
| 跨语言 | 仅 Rust | C + Rust + 混合 |
| 并发 | 顺序代码为主 | pthread + async |
| 浮点 | 有限支持 | 完整 IEEE-754 建模 |
| 工业部署 | AWS 内部大规模 | 学术研究为主 |

### Rust 验证示例

```rust,ignore
// ESBMC 验证 Rust 中的整数溢出
fn add_with_check(a: i32, b: i32) -> Option<i32> {
    match a.checked_add(b) {
        Some(sum) => Some(sum),
        None => None,
    }
}

// ESBMC 验证：对所有可能的 a, b，函数不会 panic
// 命令：esbmc --rust file.rs --function add_with_check --overflow-check
```

### C/Rust FFI 验证

ESBMC 的独特优势是验证跨语言调用：

```c
// C 代码
int c_compute(int x);
```

```rust,ignore
// Rust FFI
extern "C" {
    fn c_compute(x: i32) -> i32;
}

fn rust_wrapper(x: i32) -> i32 {
    unsafe { c_compute(x) }
}

// ESBMC 可验证：C 代码的内存安全假设与 Rust 的所有权规则是否兼容
```

**权威来源**: [ESBMC GitHub](https://github.com/esbmc/esbmc) · [ESBMC Rust Frontend Paper](https://arxiv.org/)

---

## Safety Tags：机器可读的安全契约

> **定位**: RFC #3842 提出的标准化注解，为 `unsafe` API 提供机器可读的 Safety Contract，使静态分析工具和文档生成器能自动提取安全前置条件。

### 语法设计（提案阶段）

```rust,ignore
// 当前：安全契约仅在文档注释中描述（人工阅读）
/// # Safety
/// `ptr` must be valid and properly aligned.
/// `len` must not exceed the allocation size.
pub unsafe fn read_slice<T>(ptr: *const T, len: usize) -> &[T] {
    std::slice::from_raw_parts(ptr, len)
}

// RFC #3842 提案：机器可读的安全标签
#[safety_tag(
    requires = "ptr.is_aligned() && ptr.is_valid_for(len)",
    ensures = "result.len() == len",
    invariant = "T: Sized",
)]
pub unsafe fn read_slice<T>(ptr: *const T, len: usize) -> &[T] {
    std::slice::from_raw_parts(ptr, len)
}
```

### 工具链集成愿景

```text
Safety Tags
    ├── Clippy: 检查 unsafe 块是否满足 requires 条件
    ├── Miri: 动态验证 ensures 断言
    ├── Kani: 有界验证 requires → ensures 蕴含关系
    ├── rustdoc: 自动生成 # Safety 文档
    └── Verus: 将 requires/ensures 转换为形式化规范
```

### 状态

- **RFC 阶段**: Draft（2025-2026）
- **编译器支持**: 尚未实现，需 `#[feature(...)]`
- **工具支持**: rustdoc 的 Safety Tag 渲染已在设计中

**权威来源**: [RFC #3842](https://github.com/rust-lang/rfcs/pull/3842) · [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)

---

## TrustInSoft：C/Rust 混合代码的抽象解释

> **定位**: 基于抽象解释（Abstract Interpretation）的商业级静态分析工具，专注于证明 C/C++ 代码无运行时（Runtime）错误（内存安全（Memory Safety）、整数溢出、除零等），正在扩展 Rust 支持。

### 抽象解释原理

抽象解释是一种**保守近似**的程序分析方法：

```text
具体语义（Concrete Semantics）
    └── 所有可能的程序状态（无限集）
            ↓ 抽象函数 α
抽象语义（Abstract Semantics）
    └── 区间/多面体/八边形等抽象域（有限可计算）
            ↓ 验证
"无运行时错误"的结论
```

与模型检查（Kani）和演绎验证（Verus）的区别：

| 方法 | 保证 | 误报 | 适用场景 |
|:---|:---|:---:|:---|
| 模型检查 (Kani) | 有界完备 | 无 | 算法验证、协议检查 |
| 演绎验证 (Verus) | 完备 | 无 | 系统代码、数据结构 |
| 抽象解释 (TrustInSoft) | 保守 sound | **有** | 遗留 C 代码审计、合规认证 |

### Rust 支持状态

TrustInSoft 对 Rust 的支持通过以下路径：

1. **MIR 导入**: 将 Rust MIR（中级中间表示）转换为 TrustInSoft 的内部 IR
2. **unsafe 块聚焦**: 优先分析包含 `unsafe` 的函数（safe Rust 由编译器保证）
3. **FFI 边界检查**: 验证 Rust 调用 C 函数时的前置条件

```rust,ignore
// TrustInSoft 分析目标示例
pub fn safe_wrapper(data: &[u8]) -> u32 {
    if data.len() < 4 {
        return 0;
    }
    unsafe {
        // TrustInSoft 验证：ptr 是否对齐？len 是否 ≥ 4？
        let ptr = data.as_ptr() as *const u32;
        ptr.read_unaligned()
    }
}
```

**权威来源**: [TrustInSoft Official](https://trust-in-soft.com/) · [Abstract Interpretation — Cousot 1977](https://doi.org/10.1145/512950.512973)

---

## 选型速查表（2026）

| 场景 | 首选工具 | 备选 | 关键限制 |
|:---|:---|:---|:---|
| 日常 unsafe 代码审查 | **Miri** | Kani (bounded) | Miri 不验证所有执行路径 |
| 安全关键组件（crypto/网络） | **Kani 0.65+** | ESBMC | 循环需契约或展开 |
| 操作系统/驱动/嵌入式 | **Verus** | Kani + 手引公理 | 学习曲线陡峭 |
| LLM 辅助验证入门 | **AutoVerus** | 纯 Verus | 成功率随复杂度下降 |
| C/Rust FFI 混合验证 | **ESBMC** | TrustInSoft | Rust 前端成熟度有限 |
| 遗留 C 代码审计 | **TrustInSoft** | ESBMC | 商业工具，需许可证 |
| unsafe API 标准化文档 | **Safety Tags** (未来) | rustdoc + 手写 | RFC 尚未批准 |
| 生产环境借用（Borrowing）检查（运行时） | **BorrowSanitizer** (BSan) | Miri | 2-5x 性能开销，需 nightly |
| 编译器本身验证 | **a-mir-formality** | — | 研究工具，非程序验证 |

---

## 快速开始：工具安装与运行

### Miri（Rust 官方动态分析器）

> **深度概念页**: [Miri：Rust 未定义行为动态检测器](31_miri.md)

```bash
# 安装 Miri
rustup component add miri

# 运行项目中的 Miri 测试（示例）
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test --package c01_ownership_borrow_scope miri_tests

# 检查单个文件的未定义行为
cargo miri run --manifest-path crates/c01_ownership_borrow_scope/Cargo.toml --bin ts
```

### Kani（AWS 有界模型检查器）

> 📚 **深度概念页**: [Kani：Rust 有界模型检查器](32_kani.md)

```bash
# 安装 Kani
cargo install kani-verifier
cargo kani setup

# 验证单个函数
cargo kani --harness verify_vec_push_safety

# Autoharness 自动生成测试
kani autoharness --function increment_all
```

### BorrowSanitizer（运行时借用检查 Sanitizer）

```bash
# 编译并运行带 BorrowSanitizer 检查的程序
RUSTFLAGS="-Zsanitizer=borrow" cargo run --target x86_64-unknown-linux-gnu

# 注意: BSan 需要 nightly toolchain 和目标平台的 sanitizer 运行时支持
```

**适用场景**: 生产环境部署前的借用（Borrowing）安全检查，Miri 太慢（100-1000x）时的替代方案。

**关键限制**: 仅检测运行时可达路径；静态分析覆盖不如 Miri 全面。

> **与 Miri 的对比**: Miri 解释执行 MIR（100-1000x  slowdown），BSan 编译期插桩（2-5x slowdown）。BSan 适合 CI 集成，Miri 适合深度调试。
> **深度文档**: [BorrowSanitizer 深度解析](../../07_future/02_stabilized_features/borrow_sanitizer.md)

---

### Verus（Microsoft 演绎验证器）

```bash
# 克隆并安装 Verus
git clone https://github.com/verus-lang/verus.git
cd verus/source && ./tools/get-z3.sh && cargo build --release

# 验证 Rust 文件
./target/release/verus your_file.rs
```

---

## 嵌入式测验

<details>
<summary>📝 测验 1：AutoVerus 的主要价值是什么？</summary>

**答案**：AutoVerus 的核心价值是**降低形式化验证的入门门槛**。它自动化了最耗时的"写证明"环节，使开发者只需关注"写规范"和"审阅 LLM 输出"。但它不保证 100% 成功，复杂场景（并发协议、幽灵状态）仍需人工介入。
</details>

<details>
<summary>📝 测验 2：Kani 0.65 的循环契约与旧版循环展开有什么区别？</summary>

**答案**：旧版 Kani 需要**展开循环**（设置 `kani::unwind` 上限），对无限循环或大变量的循环验证能力有限。0.65+ 的**循环契约**（`#[kani::modifies]` / `#[kani::ensures]`）允许验证器通过归纳法处理循环，无需展开，大幅扩展了可验证的代码范围。
</details>

<details>
<summary>📝 测验 3：Safety Tags 与当前文档注释中的 `# Safety` 有什么区别？</summary>

**答案**：当前 `# Safety` 是**纯文本**，仅供人类阅读。Safety Tags（RFC #3842）是**机器可读的标准化注解**（如 `#[safety_tag(requires = "...")]`），可被 Clippy、Miri、Kani、rustdoc 等工具自动解析，实现"写一次契约，多工具复用"。
</details>

---

> **权威来源**: [AutoVerus arXiv 2025] · [Kani 0.65 Release Notes](https://model-checking.github.io/kani/) · [ESBMC GitHub](https://github.com/esbmc/esbmc) · [RFC #3842 Safety Tags](https://github.com/rust-lang/rfcs/pull/3842) · [TrustInSoft](https://trust-in-soft.com/)
> **文档版本**: 1.1
> **对应 Rust 版本**: 1.96.1+ (Edition 2024)
> **最后更新**: 2026-07-09
> **权威来源对齐变更日志**: 2026-07-09 新增 Safety Tags / BorrowSanitizer / AutoVerus / Tree Borrows 交叉引用（Reference） [P2-Q3 形式化工具交叉引用]
> **状态**: ✅ 现代验证工具生态补全

## 相关工具交叉索引

| 工具 / 概念 | 定位 | 权威来源 |
|:---|:---|:---|
| [Kani](32_kani.md) | Rust 有界模型检查器 | [Kani 官方文档](https://model-checking.github.io/kani/) |
| [Miri](31_miri.md) | Rust MIR 解释器，动态检测 UB | [Miri GitHub](https://github.com/rust-lang/miri) |
| [Tree Borrows](../01_ownership_logic/36_tree_borrows_deep_dive.md) | Rust 别名模型演进方向 | [Tree Borrows 论文/博客](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html) |
| [Stacked Borrows](../01_ownership_logic/36_tree_borrows_deep_dive.md) | 早期 Rust 别名模型 | [Stacked Borrows 论文](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) |
| [Safety Tags](../02_separation_logic/33_safety_tags_in_formal.md) | `unsafe` 安全契约机器可读标注（RFC #3842） | [RFC #3842](https://github.com/rust-lang/rfcs/pull/3842) |
| [BorrowSanitizer](../02_separation_logic/34_borrow_sanitizer_in_formal.md) | 运行时别名模型检测 | [Rust Project Goal #624](https://github.com/rust-lang/rust-project-goals/issues/624) |
| [AutoVerus / Verus](24_autoverus.md) | SMT 演绎验证与 LLM 辅助自动证明 | [Verus GitHub](https://github.com/verus-lang/verus) · [AutoVerus 论文](https://arxiv.org/abs/2409.13082) |

## 认知路径

> **认知路径**: 从 L0 基础概念出发，经由本节的 **现代 Rust 验证工具生态（2025-2026）** 核心原理，通向 L2 进阶模式与 L3 工程实践。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| 现代 Rust 验证工具生态（2025-2026） 基础定义 ⟹ 正确用法 | 理解语法与语义 | 能写出符合惯用法的代码 | 高 |
| 现代 Rust 验证工具生态（2025-2026） 正确用法 ⟹ 常见陷阱 | 忽略边界条件 | 编译错误或运行时 bug | 高 |
| 现代 Rust 验证工具生态（2025-2026） 常见陷阱 ⟹ 深度掌握 | 系统学习反模式 | 能进行代码审查与优化 | 高 |

> **过渡**: 掌握 现代 Rust 验证工具生态（2025-2026） 的基础语法后，下一步需要理解其在类型系统（Type System）中的位置与与其他概念的交互关系。
> **过渡**: 在实践中应用 现代 Rust 验证工具生态（2025-2026） 时，务必关注边界条件与异常处理，这是从"能编译"到"能生产"的关键跃迁。
> **过渡**: 现代 Rust 验证工具生态（2025-2026） 的设计理念体现了 Rust 零成本抽象（Zero-Cost Abstraction）与安全保证的核心权衡，理解这一权衡有助于迁移到更高级的并发与形式化验证领域。

### 反命题与边界

> **反命题**: "现代 Rust 验证工具生态（2025-2026） 在所有场景下都是最佳选择" —— 错误。需要根据具体上下文权衡性能、可读性与安全性，某些场景下显式替代方案可能更优。

## 嵌入式测验（Embedded Quiz）

### 测验 1：`cargo-kani` 与 `cargo-fuzz` 在验证方法上有什么区别？（理解层）

**题目**: `cargo-kani` 与 `cargo-fuzz` 在验证方法上有什么区别？

<details>
<summary>✅ 答案与解析</summary>

`cargo-kani` 是模型检测，通过符号执行穷举所有路径证明属性。`cargo-fuzz` 是模糊测试，随机生成输入发现崩溃，不保证穷尽。
</details>

---

### 测验 2：Miri 能检测哪些类别的未定义行为（UB）？（理解层）

**题目**: Miri 能检测哪些类别的未定义行为（UB）？

<details>
<summary>✅ 答案与解析</summary>

悬垂指针解引用（Reference）、越界访问、数据竞争、未对齐访问、类型混淆、未初始化内存读取等。
</details>

---

### 测验 3：为什么即使有了形式化验证，仍然需要传统测试？（理解层）

**题目**: 为什么即使有了形式化验证，仍然需要传统测试？

<details>
<summary>✅ 答案与解析</summary>

形式化验证通常针对特定属性，且受限于规约正确性和验证范围。测试补充验证性能、集成行为和未建模的边界情况。
</details>
