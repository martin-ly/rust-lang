> **内容分级**: [综述级]
>
> **本节关键术语**: Kani · 有界模型检查（Bounded Model Checking） · CBMC · Harness · 函数合约（Function Contracts） · 循环合约（Loop Contracts） · Autoharness — [完整对照表](../00_meta/terminology_glossary.md)
>

# Kani：Rust 有界模型检查器

> **EN**: Kani: Rust Bounded Model Checker
> **Summary**: Kani is an AWS-developed bounded model checker for Rust. It verifies properties over all possible inputs and execution paths within bounds using `#[kani::proof]` harnesses, function contracts, loop contracts, and autoharness generation.
> **受众**: [进阶 / 工程 / 形式化]
> **Bloom 层级**: 理解 → 应用 → 分析
> **A/S/P 标记**: **A** — Application
> **双维定位**: T×Fml — 工具链与形式化验证
> **定位**: 将 Kani 从"AWS 内部工具"还原为日常安全关键代码审查与教学的标准模型检查器。
> **前置概念**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [Borrowing](../01_foundation/02_borrowing.md) · [Ownership](../01_foundation/01_ownership.md) · [现代验证工具生态](22_modern_verification_tools.md)
> **后置概念**: [Miri](31_miri.md) · [BorrowSanitizer](34_borrow_sanitizer_in_formal.md)

---

> **来源**: [Kani 官方文档](https://model-checking.github.io/kani/) · · [Kani — Rust Verification Model Checker](https://github.com/model-checking/kani) · [Clarke et al. — Behavioral Model Checking](https://doi.org/10.1145/876638.876643) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Rust Reference — Unsafe Blocks](https://doc.rust-lang.org/reference/unsafe-blocks.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Kani GitHub](https://github.com/model-checking/kani) ·
> [CBMC](https://github.com/diffblue/cbmc) ·
> [Kani 教程](https://model-checking.github.io/kani/tutorial-first-steps.html)

## 📑 目录

- [Kani：Rust 有界模型检查器](#kanirust-有界模型检查器)
  - [📑 目录](#-目录)
  - [一、Kani 是什么](#一kani-是什么)
    - [与测试、Miri、Verus 的定位差异](#与测试miriverus-的定位差异)
  - [二、安装与基本用法](#二安装与基本用法)
    - [安装](#安装)
    - [验证单个 harness](#验证单个-harness)
    - [验证整个 crate](#验证整个-crate)
  - [三、核心概念](#三核心概念)
    - [Harness：`#[kani::proof]`](#harnesskaniproof)
    - [非确定性输入：`kani::any()`](#非确定性输入kaniany)
    - [假设与断言：`kani::assume` / `assert!`](#假设与断言kaniassume--assert)
    - [函数合约：`#[kani::requires]` / `#[kani::ensures]`](#函数合约kanirequires--kaniensures)
    - [循环合约：`#[kani::loop_invariant]`](#循环合约kaniloop_invariant)
    - [循环展开：`#[kani::unwind(...)]`](#循环展开kaniunwind)
    - [Autoharness](#autoharness)
  - [四、可运行示例](#四可运行示例)
    - [示例 1：简单函数安全证明](#示例-1简单函数安全证明)
    - [示例 2：循环与循环合约](#示例-2循环与循环合约)
    - [示例 3：数据结构边界条件](#示例-3数据结构边界条件)
  - [五、项目内已有 Kani 示例导航](#五项目内已有-kani-示例导航)
  - [六、常见限制](#六常见限制)
  - [七、权威来源索引](#七权威来源索引)

---

## 一、Kani 是什么

**Kani** 是 AWS 开发并开源的 **Rust 有界模型检查器（Bounded Model Checker）**。它基于 [CBMC](https://github.com/diffblue/cbmc)，将 Rust 代码转换为逻辑公式，然后调用 SAT/SMT 求解器验证**在给定边界内**程序是否满足指定属性。

> **关键洞察**: Kani 不是测试框架，而是**符号执行 + 模型检查器**。它回答的问题是："对于所有满足前置条件的输入，该函数是否永远不会 panic、越界、触发断言失败或其他指定错误？"
>
> [来源: Kani 官方文档](https://model-checking.github.io/kani/)

### 与测试、Miri、Verus 的定位差异

| 工具 | 方法 | 覆盖范围 | 能证明什么 | 主要局限 |
|:---|:---|:---|:---|:---|
| `cargo test` | 动态执行 | 人工选定的输入 | 特定输入下行为正确 | 无法穷尽输入空间 |
| **Kani** | 有界模型检查 | 边界内所有路径/输入 | 无 panic、无越界、属性成立 | 有界、循环需合约或展开、不支持 async/并发 |
| **Miri** | MIR 解释执行 | 实际执行到的路径 | 未定义行为（UB） | 不穷尽路径、不支持形式化属性断言 |
| **Verus** | 演绎验证 | 完整（无界） | 函数合约、数据结构不变量、并发协议 | 学习曲线陡峭、需大量注解 |
| `cargo fuzz` | 模糊测试 | 随机/覆盖引导输入 | 发现崩溃 | 不保证穷尽 |

> **选择建议**:
>
> - 需要证明 **unsafe 代码无 UB** → Miri（动态） + Kani（有界形式化）。
> - 需要证明 **算法/协议在所有输入下正确** → Kani（快速上手）或 Verus（完整无界）。
> - 需要 **发现复杂状态机 bug** → 模糊测试 + Kani 互补。

---

## 二、安装与基本用法

### 安装

```bash
# 1. 安装 Kani 命令行工具
cargo install kani-verifier

# 2. 下载并配置 CBMC 等依赖
cargo kani setup
```

验证安装：

```bash
cargo kani --version
```

### 验证单个 harness

```bash
# 在 crate 目录下执行
cargo kani --harness verify_increment_contract
```

### 验证整个 crate

```bash
cargo kani
```

Kani 会自动发现所有标注了 `#[kani::proof]` 的 harness 并逐一验证。

---

## 三、核心概念

### Harness：`#[kani::proof]`

Harness 是 Kani 的入口函数，类似于测试，但它使用**符号值**而非具体值。Kani 会尝试证明 harness 中所有 `assert!` 都不会失败。

```rust,ignore
#[kani::proof]
fn verify_abs_returns_nonnegative() {
    let x: i32 = kani::any();
    let result = x.abs();
    assert!(result >= 0);
}
```

> **注意**: Kani 宏（Macro）只在 `cfg(kani)` 下可用。项目内 crate 的 Kani 示例通常被 `#[cfg(kani)]` 包裹，普通 `cargo build/test` 会跳过它们。

### 非确定性输入：`kani::any()`

`kani::any()` 生成一个符号值，代表该类型的**所有可能取值**。Kani 会针对这些取值的所有组合进行验证。

```rust,ignore
#[kani::proof]
fn verify_saturation_add() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    let result = a.saturating_add(b);
    assert!(result >= a); // 饱和加法不会减小原值
}
```

### 假设与断言：`kani::assume` / `assert!`

- `kani::assume(cond)`：限制验证只考虑满足 `cond` 的输入。
- `assert!(cond)`：Kani 尝试证明 `cond` 对**所有满足假设的输入**恒成立。

```rust,ignore
#[kani::proof]
fn verify_slice_first_when_non_empty() {
    let s: [i32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    kani::assume(s.iter().all(|x| *x >= 0)); // 假设
    let first = s.first().unwrap();
    assert!(*first >= 0); // 断言
}
```

### 函数合约：`#[kani::requires]` / `#[kani::ensures]`

函数合约允许在被测函数上直接声明前置条件和后置条件，无需手写 harness。

```rust,ignore
#[kani::requires(x > 0)]
#[kani::ensures(|result| *result > x)]
fn increment(x: u32) -> u32 {
    x + 1
}
```

> 项目内完整示例: [`crates/c01_ownership_borrow_scope/src/kani_examples.rs`](../../crates/c01_ownership_borrow_scope/src/kani_examples.rs)

### 循环合约：`#[kani::loop_invariant]`

对于循环，Kani 需要知道循环不变量（loop invariant）才能无界地验证。否则需要设置展开深度。

```rust,ignore
#[kani::proof]
fn sum_of_nonnegative_array_is_nonnegative() {
    let arr: [i32; 4] = [kani::any(), kani::any(), kani::any(), kani::any()];
    kani::assume(kani::forall!(|i in 0..4| arr[i] >= 0));

    let mut sum = 0i64;
    #[kani::loop_invariant(sum >= 0)]
    for &x in &arr {
        sum += x as i64;
    }

    assert!(sum >= 0);
}
```

> 项目内完整示例: [`crates/c02_type_system/src/kani_examples.rs`](../../crates/c02_type_system/src/kani_examples.rs)

### 循环展开：`#[kani::unwind(...)]`

如果不能写出循环不变量，可以显式设置展开次数。Kani 会验证循环迭代次数不超过该上界。

```rust,ignore
#[kani::proof]
#[kani::unwind(5)]
fn verify_bounded_sum() {
    let arr: [i32; 4] = [kani::any(); 4];
    let mut sum = 0;
    for &x in &arr {
        sum += x;
    }
    // 仅对 4 个元素有效，展开 5 次足够
}
```

> **警告**: `unwind` 值过小会导致 **UNWINDING ASSERTION** 失败；过大则会指数级增加验证时间。

### Autoharness

Kani 0.65+ 支持自动生成 harness，减少手写验证代码的工作量。

```bash
# 为函数 increment_all 自动生成并运行 harness
kani autoharness --function increment_all --harness-depth 2
```

| 参数 | 含义 |
|:---|:---|
| `--harness-depth` | 生成 harness 时递归调用其他函数的深度 |
| `--gen-contracts` | 同时生成函数契约草案 |

---

## 四、可运行示例

### 示例 1：简单函数安全证明

```rust,ignore
#[kani::proof]
fn verify_checked_add_no_panic() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    // 对 u32 而言，checked_add 永远不会 panic；Kani 会确认这一点
    let _ = a.checked_add(b);
}
```

### 示例 2：循环与循环合约

```rust,ignore
#[kani::proof]
fn verify_increment_all_elements() {
    let mut arr: [u32; 4] = [kani::any(); 4];
    let old_sum: u64 = arr.iter().map(|x| *x as u64).sum();

    #[kani::loop_invariant(
        arr.iter().enumerate().all(|(i, x)| *x >= old_arr[i])
    )]
    // 注意：复杂不变量可能需要 kani::old 或手动保存旧状态
    for x in &mut arr {
        *x += 1;
    }

    let new_sum: u64 = arr.iter().map(|x| *x as u64).sum();
    assert_eq!(new_sum, old_sum + 4);
}
```

> 实际循环合约写法请参考项目内 [`crates/c01_ownership_borrow_scope/src/kani_examples.rs`](../../crates/c01_ownership_borrow_scope/src/kani_examples.rs)。

### 示例 3：数据结构边界条件

验证 `Vec::push` 在任意合法状态下不会越界：

```rust,ignore
#[kani::proof]
fn verify_vec_push_safety() {
    let mut v: Vec<u32> = kani::vec::any_vec::<u32, 100>();
    let elem: u32 = kani::any();
    v.push(elem); // Kani 验证：capacity 检查 + reallocation 安全
    assert!(v.last() == Some(&elem));
}
```

---

## 五、项目内已有 Kani 示例导航

本项目已在多个 crate 中接入 Kani 示例，均使用 `#[cfg(kani)]` 保护，不会干扰普通编译。

| Crate / 文件 | 覆盖主题 | 运行命令 |
|:---|:---|:---|
| [`crates/c01_ownership_borrow_scope/src/kani_examples.rs`](../../crates/c01_ownership_borrow_scope/src/kani_examples.rs) | 所有权（Ownership）/借用（Borrowing）、函数合约、循环合约、切片（Slice）最大值 | `cargo kani --manifest-path crates/c01_ownership_borrow_scope/Cargo.toml` |
| [`crates/c02_type_system/src/kani_examples.rs`](../../crates/c02_type_system/src/kani_examples.rs) | 泛型（Generics）、trait bound、循环不变量、偶数计数 | `cargo kani --manifest-path crates/c02_type_system/Cargo.toml` |
| [`crates/c08_algorithms/src/kani_examples.rs`](../../crates/c08_algorithms/src/kani_examples.rs) | 数组和、二分查找边界条件 | `cargo kani --manifest-path crates/c08_algorithms/Cargo.toml` |

> **提示**: 由于 Kani 示例依赖 `kani` crate 的宏（Macro），普通 `cargo build` 不会编译这些模块（Module）。运行 `cargo kani` 时会自动进入 `cfg(kani)` 模式。

---

## 六、常见限制

| 限制 | 说明 |
|:---|:---|
| **有界验证** | Kani 是 *bounded* model checker，对循环深度、递归深度、输入大小有界。超出边界无法保证结论。 |
| **循环需合约或展开** | 无循环不变量时需要 `#[kani::unwind]`，且需验证展开次数足够。 |
| **未支持 async / 并发** | 当前 Kani 主要验证同步、单线程 Rust 代码。async/await、多线程、原子操作（Atomic Operations）支持有限或实验性。 |
| **标准库支持范围** | 部分 `std` API（如浮点运算、I/O、网络）建模不完整，可能报 "unsupported" 或需要 stub。 |
| **验证复杂度** | 随着状态空间增长，求解时间可能指数级上升，需要合理设置边界或添加假设。 |
| **Kani 版本更新** | 函数合约 / 循环合约 / Autoharness 等特性较新，不同版本语法可能变化。 |

---

## 七、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Kani 官方文档](https://model-checking.github.io/kani/) | ✅ 一级 | 安装、语法、教程、限制说明 |
| [Kani GitHub](https://github.com/model-checking/kani) | ✅ 一级 | 源码、Issue、Release Notes |
| [Kani 教程](https://model-checking.github.io/kani/tutorial-first-steps.html) | ✅ 一级 | 从零开始的 harness 编写 |
| [CBMC GitHub](https://github.com/diffblue/cbmc) | ✅ 二级 | Kani 底层模型检查引擎 |
| [AWS Kani Blog](https://aws.amazon.com/blogs/aws/) | ✅ 二级 | 工业应用案例 |
| [Rust 形式化验证工具对比](22_modern_verification_tools.md) | ✅ 二级 | 项目内 Kani/Miri/Verus 对比 |

---

> **权威来源**: [Kani 官方文档](https://model-checking.github.io/kani/) · [Kani GitHub](https://github.com/model-checking/kani) · [CBMC](https://github.com/diffblue/cbmc)
> **权威来源对齐变更日志**: 2026-06-26 创建，对齐 Kani 0.66+ / Rust 1.96.0

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-26