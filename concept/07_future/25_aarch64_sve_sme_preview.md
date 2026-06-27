> **内容分级**:
>
> [实验级]
> **代码状态**: ✅ 含可编译示例
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.98.0
> **预计稳定**: 待定

# AArch64 SVE / SME：可伸缩向量扩展预览
>
> **EN**: Aarch64 Sve Sme Preview
> **Summary**: Aarch64 Sve Sme Preview: emerging Rust language feature or ecosystem trend.
> **受众**: [专家]
> **内容分级**: [实验级]
> **跟踪版本**: nightly 1.98.0 (2026-06-06)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链

---

> **来源**:
>
> [Tracking Issue #145052 — Scalable Vectors](https://github.com/rust-lang/rust/issues/145052) ·
> [RFC #3838 — Scalable Vectors](https://github.com/rust-lang/rfcs/pull/3838) ·
> [Rust Project Goals 2025H1/H2 #270](https://github.com/rust-lang/rust-project-goals/issues/270) ·
> [ARM Architecture Reference Manual — SVE](https://developer.arm.com/documentation/100986/latest) ·
> [ARM Architecture Reference Manual — SME](https://developer.arm.com/documentation/109246/latest)
>
> **前置概念**:
>
> [SIMD / 向量化](../01_foundation/06_zero_cost_abstractions.md) ·
> [Unsafe Rust](../03_advanced/03_unsafe.md) ·
> 内联汇编（Inline Assembly）

---

> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S** — Structure
> **定位**: 跟踪 Rust 对 ARM AArch64 **SVE（Scalable Vector Extension，可伸缩向量扩展）** 和 **SME（Scalable Matrix Extension，可伸缩矩阵扩展）** 的支持进展。SVE/SME 是 ARMv9-A 的关键特性，代表向量计算从固定长度向硬件自适应长度的范式转变。

---

## 一、核心概念

### 1.1 从固定向量到可伸缩向量

传统 SIMD（如 SSE/AVX/NEON）使用**固定宽度**向量寄存器（128-bit、256-bit、512-bit）。SVE 引入了**可伸缩向量长度（VL）**：

| 特性 | NEON（固定） | SVE（可伸缩） |
|:---|:---|:---|
| 向量长度 | 固定 128-bit | 128-bit 到 2048-bit（以 128-bit 为增量） |
| 运行时（Runtime）确定 | ❌ 编译期固定 | ✅ 硬件决定，运行时暴露 |
| 代码可移植性 | 同一二进制无法跨硬件 | 同一代码可在不同 VL 硬件运行 |
| 循环向量化 | 需手动处理剩余元素 | 通过 `WHILELO` 谓词自动处理 |

### 1.2 SVE 核心机制：谓词（Predicate）

SVE 不依赖传统 SIMD 的"剩余元素处理"，而是通过**谓词寄存器**（`p0-p15`）控制向量通道的活动状态：

```rust,ignore
#![feature(stdarch_aarch64_sve)]
// 注意：以下代码为概念示例，API 尚未稳定

// svwhilelt_b32：生成谓词，标记前 N 个活跃元素
// ptrue_b32：全部活跃
// pfalse_b32：全部非活跃
```

### 1.3 SME：从向量到矩阵

SME 在 SVE 基础上增加**二维可伸缩矩阵运算**：

- **ZA 状态**： Streaming SVE 模式下可用的可伸缩矩阵累加器
- **Streaming SVE（SSVE）**：一种受限的 SVE 执行模式，专为高吞吐矩阵运算优化
- **tile 操作**：以 2D tile 为单位进行矩阵加载/存储/运算

---

## 二、Rust 支持现状（截至 2026-06-06）

### 2.1 Feature Gate

```rust,ignore
#![feature(stdarch_aarch64_sve)]
```

### 2.2 跟踪 Issue

| Issue | 标题 | 状态 | 创建日期 |
|:---|:---|:---:|:---|
| [#145052](https://github.com/rust-lang/rust/issues/145052) | Tracking Issue for Scalable Vectors | open | 2025-08-07 |
| [#157110](https://github.com/rust-lang/rust/issues/157110) | `sve_zeroinitializer` compiler intrinsic | open | 2026-05-29 |

### 2.3 RFC 状态

- [RFC #3838 — Scalable Vectors](https://github.com/rust-lang/rfcs/pull/3838)：**尚未正式接受**（截至 2026-06-06）
- Tracking Issue #145052 在 RFC 接受前已创建，用于记录实现进展

### 2.4 Project Goal 历史

- **2025H1/H2**：Scalable Vectors 被列为 Rust Project Goal（[#270](https://github.com/rust-lang/rust-project-goals/issues/270)）
- **2026 状态**：未进入 Rust Project Goals 2026 正式列表，转为社区持续跟踪

### 2.5 已实现基础设施

| 组件 | 状态 | 说明 |
|:---|:---:|:---|
| `std::arch::aarch64::*` SVE intrinsics | 🧪 Nightly | 大量底层 intrinsic 已暴露 |
| `SVec<T>` / `SVBool` 类型 | 🧪 Nightly | 可伸缩向量类型 |
| `svptrue` / `svpfalse` | 🧪 Nightly | 谓词生成 |
| `sve_zeroinitializer` | 🔧 开发中 | #157110，2026-05-29 新提出 |
| SME / Streaming SVE | 🔴 未开始 | 无公开 RFC 或 tracking issue |

---

## 三、技术挑战

### 3.1 Rust 类型系统适配

SVE 的核心难点在于**向量长度是运行时（Runtime）确定的**，但 Rust 类型系统（Type System）要求编译期确定大小：

```rust
// 传统 SIMD：类型包含宽度信息
pub struct uint8x16_t(pub(crate) [u8; 16]); // NEON，固定 128-bit

// SVE：类型大小在编译期未知
pub struct svuint8_t(/* opaque，硬件决定宽度 */);
```

这意味着：

- `size_of::<svuint8_t>()` 无法在编译期求值
- 栈分配 SVE 类型需要特殊处理（通常通过 `alloca` 或隐式向量寄存器分配）
- Rust 的 `Copy`、`Clone`、`Default` 等 trait 需要特殊实现

### 3.2 ABI 与调用约定

SVE 向量在函数调用时通过 **Z 寄存器**（`z0-z31`）和 **P 寄存器**（`p0-p15`）传递，这要求：

- Rust 的 AArch64 ABI 支持 SVE 寄存器保存/恢复
- `extern "C"` 函数与 C 代码的 SVE 类型互操作
- Miri 等工具对可变长度类型的验证能力扩展

### 3.3 SME 的额外复杂度

SME 引入的 **ZA 状态** 是一种特殊的 CPU 状态（类似浮点单元状态，但更复杂）：

- 进入/退出 Streaming 模式需要系统调用或特殊指令
- ZA 状态在上下文切换时需要保存/恢复
- Linux 内核 6.x 才开始支持 SME 的完整上下文管理

---

## 四、与 Rust 生态的关联

| 领域 | 影响 | 时间线 |
|:---|:---|:---|
| **HPC / 科学计算** | SVE 是 ARM 超算（如 Fugaku 后继机型）的核心，Rust  numerical 生态需要 SVE 支持才能竞争 | 2027+ |
| **AI / ML 推理** | SME 的矩阵运算能力对端侧 AI 推理至关重要，Rust ML 运行时（Runtime）（如 Candle、Burn）长期需要 | 2028+ |
| **嵌入式 / 移动端** | ARMv9-A 手机 SoC 已广泛支持 SVE2，游戏/多媒体 Rust 应用将受益 | 2026–2027 |
| **编译器后端** | LLVM 已支持 SVE/SME，Rust 的 LLVM IR 生成需要对应扩展 | 🔄 进行中 |

---

## 五、时间线与里程碑

| 时间 | 事件 | 状态 |
|:---|:---|:---:|
| 2020 | ARM 发布 SVE2（SVE 的第二代，固定功能扩展） | ✅ 硬件标准 |
| 2022 | ARM 发布 SME（Scalable Matrix Extension） | ✅ 硬件标准 |
| 2023 | Linux 内核初步支持 SME 上下文切换 | ✅ |
| 2025-08 | Rust Tracking Issue #145052 创建 | ✅ |
| 2025H1/H2 | Scalable Vectors 作为 Rust Project Goal | ✅ 已完成周期 |
| 2026-05-29 | `sve_zeroinitializer` compiler intrinsic 提出（#157110） | 🔧 开发中 |
| 2026+ | RFC #3838 正式接受 | 🟡 等待中 |
| 2027+ | SVE 稳定化评估 | 🔮 远期 |
| 2028+ | SME 初步支持 | 🔮 远期 |

---

## 六、参考资源

| 级别 | 资源 | 说明 |
|:---|:---|:---|
| 官方 | [ARM SVE 编程指南](https://developer.arm.com/documentation/102476/latest) | ARM 官方 SVE 编程手册 |
| 官方 | [ARM SME 编程指南](https://developer.arm.com/documentation/109540/latest) | ARM 官方 SME 编程手册 |
| 社区 | [rust-lang/rust#145052](https://github.com/rust-lang/rust/issues/145052) | 主跟踪 issue |
| 社区 | [rust-lang/rfcs#3838](https://github.com/rust-lang/rfcs/pull/3838) | RFC 提案（未接受） |
| 对比 | [AVX-512 vs SVE2](https://www.nextplatform.com/2021/08/24/why-sve2-is-important-and-why-armv9-is-more-than-sve2/) | 架构对比分析 |

---

> **后置概念**: [SIMD / 向量化](../01_foundation/06_zero_cost_abstractions.md) · [Unsafe Rust](../03_advanced/03_unsafe.md) · [Rust for Linux](./19_rust_for_linux.md)

## 嵌入式测验（Embedded Quiz）

### 测验 1：SVE（Scalable Vector Extension）和 SME（Scalable Matrix Extension）是什么？（理解层）

**题目**: SVE（Scalable Vector Extension）和 SME（Scalable Matrix Extension）是什么？

<details>
<summary>✅ 答案与解析</summary>

ARM 的下一代 SIMD 指令集，向量长度在运行时确定（128-2048 位），无需为不同向量大小编译多个版本。SME 扩展了矩阵运算支持。
</details>

---

### 测验 2：SVE/SME 与 x86 的 AVX-512 有什么区别？（理解层）

**题目**: SVE/SME 与 x86 的 AVX-512 有什么区别？

<details>
<summary>✅ 答案与解析</summary>

AVX-512 有固定宽度（512 位），需要编译多个版本。SVE 的向量长度可变，同一代码可在不同硬件上利用最优向量宽度。
</details>

---

### 测验 3：Rust 目前对 SVE/SME 的支持状态如何？（理解层）

**题目**: Rust 目前对 SVE/SME 的支持状态如何？

<details>
<summary>✅ 答案与解析</summary>

通过 `std::simd`（portable SIMD）和 `std::arch::aarch64` 内联函数提供部分支持。完整的自动向量化支持仍在开发中。
</details>

---

### 测验 4：SVE/SME 对 Rust 的高性能计算（HPC）和 ML 推理有什么意义？（理解层）

**题目**: SVE/SME 对 Rust 的高性能计算（HPC）和 ML 推理有什么意义？

<details>
<summary>✅ 答案与解析</summary>

ARM 服务器（AWS Graviton、Apple Silicon）正在普及。SVE/SME 支持使 Rust 可以在这些平台上达到接近 x86 的峰值性能。
</details>

---

### 测验 5：Rust 编译器如何利用 SVE 的可变向量长度？（理解层）

**题目**: Rust 编译器如何利用 SVE 的可变向量长度？

<details>
<summary>✅ 答案与解析</summary>

通过 `std::simd` 的抽象，编译器生成与向量长度无关的代码，由硬件决定实际执行宽度。这简化了跨平台 SIMD 编程。
</details>
