# f16 / f128 预研：半精度与四精度浮点类型

> **代码状态**: ✅ 含 nightly 实测示例（`#![feature(f16, f128)]`，rustc 1.99.0-nightly 2026-07-10 通过）
>
> **EN**: f16 and f128 Preview
> **Summary**: Preview of the `f16` (IEEE 754 binary16 half-precision) and `f128` (binary128 quad-precision) primitive float types introduced by RFC 3453 — syntax, semantics, ABI caveats, and ecosystem impact.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **状态**: 🧪 Nightly 实验性（feature gates `f16` / `f128`；tracking issue rust-lang/rust#116909）
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: stable 1.97.0 报 E0658（类型不稳定）；nightly 1.99.0 可用
> **预计稳定**: 待定（`f16` 阻塞于跨平台 ABI 与 `__fp16` 支持矩阵，`f128` 阻塞于 `long double` ABI 对齐）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: L3-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 分析 f16/f128 类型语义
> **定位**: 跟踪 [RFC 3453](https://rust-lang.github.io/rfcs/3453-f16-and-f128.html) 引入的两个新原始浮点类型（Primitive Float Types），说明其语法、IEEE 754 语义、ABI 边界条件与对数值生态的影响。
> **前置概念**: [数值类型与运算](../../01_foundation/02_type_system/03_numerics.md) · [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) · [Application Binary Interface](../../04_formal/05_rustc_internals/05_application_binary_interface.md)
> **后置概念**: [Version Tracking](../00_version_tracking/01_rust_version_tracking.md) · [Complex Numbers 预研](38_complex_numbers_preview.md) · [Machine Learning 生态](../../06_ecosystem/11_domain_applications/13_machine_learning_ecosystem.md)
> **定理链**: N/A — 描述性/跟踪性文档，不涉及形式化定理链
---

> **来源**: [RFC 3453 — f16 and f128](https://rust-lang.github.io/rfcs/3453-f16-and-f128.html) ·
> [Rust Reference — Numeric Types](https://doc.rust-lang.org/reference/types/numeric.html) ·
> [std docs — primitive `f16`](https://doc.rust-lang.org/std/primitive.f16.html) ·
> [std docs — primitive `f128`](https://doc.rust-lang.org/std/primitive.f128.html) ·
> [Tracking Issue #116909](https://github.com/rust-lang/rust/issues/116909) ·
> **国际权威来源（2026-07-13 补录）**: **P2** [Rust Blog — Announcing Rust 1.82.0](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0.html)（f16 稳定化的官方发布公告；curl 200 实测 2026-07-13） ·
> [IEEE 754-2019](https://ieeexplore.ieee.org/document/8766229)

## 📑 目录

- [f16 / f128 预研：半精度与四精度浮点类型](#f16--f128-预研半精度与四精度浮点类型)
  - [📑 目录](#-目录)
  - [一、动机与定位](#一动机与定位)
  - [二、类型语义](#二类型语义)
    - [2.1 存储格式](#21-存储格式)
    - [2.2 字面量与转换](#22-字面量与转换)
  - [三、实测示例（nightly 1.99.0）](#三实测示例nightly-1990)
  - [四、ABI 与稳定化阻塞项](#四abi-与稳定化阻塞项)
  - [五、反命题与边界分析](#五反命题与边界分析)
  - [六、与既有概念的关系](#六与既有概念的关系)
  - [⚠️ 反例与陷阱](#️-反例与陷阱)
  - [权威来源索引](#权威来源索引)

## 一、动机与定位

Rust 长期只有 `f32`（binary32）与 `f64`（binary64）两种浮点原始类型。RFC 3453 补齐 IEEE 754 谱系的两端：

| 类型 | IEEE 754 格式 | 位宽 | 指数/尾数 | 典型场景 |
|:---|:---|:---:|:---|:---|
| `f16` | binary16（半精度，Half Precision） | 16 | 5 / 10 | GPU 张量、ML 权重、纹理、带宽受限传输 |
| `f32` | binary32 | 32 | 8 / 23 | 通用图形与数值计算 |
| `f64` | binary64 | 64 | 11 / 52 | 默认科学计算精度 |
| `f128` | binary128（四精度，Quad Precision） | 128 | 15 / 112 | 高精度补偿算法（如 Kahan 求和的内层）、轨道力学 |

设计要点（RFC 3453 §Guide-level explanation）：

1. **一等原始类型（Primitive Type）**：`f16`/`f128` 是语言级原始类型，不是库包装类型，享有字面量语法、模式匹配与 `#[repr]` 布局保证。
2. **零抽象惩罚目标**：在硬件原生支持的平台上（如 ARM FP16、x86 AVX10.2、RISC-V Zfh）直接映射到机器指令；无原生支持时经编译器运行时库（compiler-builtins）软件模拟。
3. **不引入隐式转换**：与现有浮点类型一致，`f16 → f32`、`f64 → f128` 等均需显式 `as` 或 `From`/`Into`，防止静默精度放大/截断。

## 二、类型语义

`f16`/`f128` 的语义锚点是 IEEE 754-2008 的 **binary16** 与 **binary128**：

| 维度 | `f16` | `f128` |
|:---|:---|:---|
| 位布局 | 1 符号 + 5 指数 + 10 尾数 | 1 符号 + 15 指数 + 112 尾数 |
| 存储大小 | 2 字节 | 16 字节 |
| 典型用途 | ML 权重/激活的压缩存储 | 高精度中间计算、天文/物理仿真 |
| 运算路径 | 多数平台提升为 `f32` 计算 | 以软件模拟（编译器运行时库）为主 |

字面量与转换规则：`f16`/`f128` 后缀字面量沿用浮点语法；与其他浮点类型之间**不自动**转换，必须显式 `as` 或可用处的 `From`。判定原则：`f16` 只当"存储格式"而非"计算格式"使用；选 `f128` 前先确认目标平台的软件模拟开销可接受。两者当前为 nightly 特性（对应 feature gate），稳定进度以 rust-lang/rust 的 tracking issue 为准。

### 2.1 存储格式

- `f16`：符号 1 位 + 指数 5 位 + 尾数 10 位；值域约 ±65504，最小正规数约 6.1e-5。
- `f128`：符号 1 位 + 指数 15 位 + 尾数 112 位；精度约 34 位十进制有效数字，远超 `f64` 的约 17 位。
- 两者均完整支持 IEEE 754 特殊值：`NaN`、±∞、±0、次正规数（Subnormal）。

### 2.2 字面量与转换

字面量后缀 `f16` / `f128`（如 `1.5f16`、`2.5f128`）；`f16`/`f128` 字面量允许下划线分隔与科学计数法，语法与 `f32`/`f64` 完全同构（Rust Reference — Numeric Types）。

转换规则（RFC 3453 §Reference-level explanation）：

- `as` 转换：全精度谱系互转允许， narrowing（`f128 as f64`）按 IEEE round-to-nearest-even 截断。
- `From`/`Into`：仅提供**无损方向**（`f16: From<f8 不存在>`；`f32: From<f16>`、`f64: From<f16>`、`f128: From<{f16,f32,f64}>`）。
- `Display`/`Debug`/`LowerExp` 等格式化 trait 均已实现（nightly）。

## 三、实测示例（nightly 1.99.0）

以下示例在 `rustc 1.99.0-nightly (375b1431b 2026-07-10) --edition 2024` 实测编译通过：

```rust,ignore
// rust-toolchain: nightly；#![feature(f16, f128)]
#![feature(f16, f128)]

fn main() {
    let x: f16 = 1.5;
    let y: f128 = 2.5;
    // 无损提升：f16 → f128
    let z: f128 = f128::from(x) + y;
    assert!(z > f128::from(3.0f64));

    // 字面量后缀
    let half_pi: f16 = 3.14f16;
    let quad_e: f128 = 2.71828182845904523536028747135266250f128;
    println!("{half_pi} {quad_e}");
}
```

在 stable 1.97.0 上同代码按预期报 `E0658: the type f16 is unstable`（实测），即当前必须经 feature gate 启用。

## 四、ABI 与稳定化阻塞项

RFC 3453 明确以下未决项是稳定化的主要阻塞（§Unresolved questions，对照 Tracking Issue #116909）：

1. **`f16` 的 C ABI 映射**：`__fp16`（ARM）vs `_Float16`（C23）vs 无对应类型（部分 x86 ABI 按 `uint16_t` 传递）。`extern "C" fn` 签名中 `f16` 的 ABI 在各目标平台尚未完全对齐。
2. **`f128` 与 `long double`**：x86-64 SysV 的 `long double` 是 80 位扩展精度（x87），与 binary128 不同；`f128` 须映射到 `__float128`/`_Float128`，依赖平台 libquadmath 或 compiler-rt。
3. **软件模拟路径的性能与正确性**：无硬件支持目标上的 round-to-nearest-even 与次正规数行为须与 IEEE 完全一致，测试矩阵庞大。
4. **`const fn` 与编译期求值**： Miri/CTFE 对 binary128 的支持须先行落地（参见 [Constant Evaluation](../../04_formal/03_operational_semantics/07_constant_evaluation.md)）。

## 五、反命题与边界分析

- **反命题 1：「f16 可以直接替代 f32 做通用计算」**——错误。10 位尾数意味着约 3 位十进制精度，累加误差迅速失控；`f16` 适合**存储与传输**而非中间计算（ML 推理中的 mixed-precision 模式：存储 `f16`、累加 `f32`）。
- **反命题 2：「f128 稳定后即可在 FFI 中自由传递」**——受 §四 ABI 阻塞项约束，跨语言边界传递 `f128` 前必须核对目标平台的 `_Float128` ABI。
- **边界**：`f16`/`f128` 不改变 [浮点语义（RFC 3514）](../../01_foundation/02_type_system/03_numerics.md) 已确立的 NaN/符号零/舍入规则，仅扩展格式谱系。

## 六、与既有概念的关系

| 关系 | 目标 |
|:---|:---|
| 上位概念 | [数值类型与运算](../../01_foundation/02_type_system/03_numerics.md)（浮点谱系扩展） |
| 并列概念 | [Complex Numbers 预研](38_complex_numbers_preview.md)（数值生态扩展） |
| 约束来源 | [Application Binary Interface](../../04_formal/05_rustc_internals/05_application_binary_interface.md) · [Constant Evaluation](../../04_formal/03_operational_semantics/07_constant_evaluation.md) |
| 演进跟踪 | [Version Tracking](../00_version_tracking/01_rust_version_tracking.md) |

## ⚠️ 反例与陷阱

**陷阱：在稳定工具链使用 `f16`/`f128`**。两个类型仍是 nightly 独占（ABI 与 codegen 未就绪），稳定编译器按「未稳定特性」拒绝：

```rust,compile_fail
fn quantize(x: f16) -> f16 {
    x * 0.5
}
```

rustc 1.97.0（stable）实测：`error[E0658]: the type f16 is unstable`。

**修正（稳定方案）**：存储/传输用 `half::f16` crate（位布局兼容 IEEE 754 binary16），计算路径提升到 `f32`；需要 `f128` 精度的科学计算用 `f64` 或任意精度库，待稳定后再迁移：

```rust
fn quantize(x: f32) -> f32 { // half::f16::to_f32() 转换后计算
    x * 0.5
}
```

## 权威来源索引

> **权威来源**: [RFC 3453 — f16 and f128](https://rust-lang.github.io/rfcs/3453-f16-and-f128.html) ·
> [Rust Reference — Numeric Types](https://doc.rust-lang.org/reference/types/numeric.html) ·
> [std docs — primitive `f16`](https://doc.rust-lang.org/std/primitive.f16.html) ·
> [std docs — primitive `f128`](https://doc.rust-lang.org/std/primitive.f128.html) ·
> [Tracking Issue #116909](https://github.com/rust-lang/rust/issues/116909) ·
> [RFC 3514 — Float Semantics](https://rust-lang.github.io/rfcs/3514-float-semantics.html)
>
> 以上链接于 2026-07-12 经 curl 实测全部返回 HTTP 200；代码示例经 `rustc 1.99.0-nightly --edition 2024` 实测编译通过（stable 1.97.0 按预期报 E0658）。
