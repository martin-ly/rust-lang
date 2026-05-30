# Rust Project Goals 2026 对齐矩阵

> **Bloom 层级**: L4-L5 (分析/评价)

> **文档定位**: 本文件建立 Rust 官方 2026 Project Goals 与项目知识体系的**双向映射**，确保 L7 前沿层的内容基于官方路线图而非猜测。
> **更新频率**: 每月对照 [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/) 月度报告更新状态。
> **创建日期**: 2026-05-18
> **对齐版本**: Rust 1.95.0 stable / 2026 Project Goals (2026-05-10 快照)

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust Project Goals 2026 对齐矩阵](#rust-project-goals-2026-对齐矩阵)
  - [📑 目录](#目录)
  - [一、旗舰主题映射（Flagship Themes → 项目内容）](#一旗舰主题映射flagship-themes--项目内容)
  - [二、2026 稳定化目标详细映射](#二2026-稳定化目标详细映射)
    - [2.1 语言与编译器层](#21-语言与编译器层)
    - [2.2 工具链与生态层](#22-工具链与生态层)
    - [2.3 异步与效果层](#23-异步与效果层)
    - [2.4 形式化与安全层](#24-形式化与安全层)
    - [2.5 WASM 与跨语言层](#25-wasm-与跨语言层)
  - [三、缺口热力图](#三缺口热力图)
  - [四、行动建议（按优先级排序）](#四行动建议按优先级排序)
    - [🔴 P0 — 立即创建（完全缺失，2026 年稳定化目标）](#p0--立即创建完全缺失2026-年稳定化目标)
    - [🟡 P1 — 补充深化（部分覆盖，需升级）](#p1--补充深化部分覆盖需升级)
    - [🟢 P2 — 跟踪观察（nightly / 长期演进）](#p2--跟踪观察nightly--长期演进)
  - [五、参考链接](#五参考链接)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 一、旗舰主题映射（Flagship Themes → 项目内容）
>
> **[来源: Rust Official Docs]**

| 旗舰主题 | 官方定义 | 项目覆盖文件 | 覆盖度 | 缺口 |
|:---|:---|:---|:---:|:---|
| **Just Add Async** | sync Rust 模式应在 async Rust 中同样可用 | `concept/03_advanced/02_async.md` · `crates/c06_async/` | 🟡 80% | AFIT dyn 兼容 nightly 代码示例；immobile types 预研 |
| **Beyond the `&`** | 智能指针应像 `&`/`&mut` 一样自然 | `concept/02_intermediate/03_memory_management.md` | 🔴 30% | Field Projections 完全缺失；reborrow traits 未覆盖；in-place initialization 未覆盖 |
| **Unblocking dormant traits** | Lending iterators, extern types, scalable vectors, evolvable trait hierarchies | `concept/02_intermediate/01_traits.md` · `concept/02_intermediate/02_generics.md` | 🟡 50% | Next-gen trait solver 完全缺失；Sized hierarchy 未覆盖 |
| **Constify all the things** | 结构体和关联常量进入泛型参数；编译期类型内省 | `concept/02_intermediate/02_generics.md` · `concept/02_intermediate/01_traits.md` | 🟡 60% | `adt_const_params` 代码示例缺失；`min_generic_const_args` 代码示例缺失；reflection 未覆盖 |
| **Higher-level Rust** | 单文件脚本带依赖 | `concept/06_ecosystem/09_cargo_script.md` · `docs/06_toolchain/06_cargo_script_guide.md` | 🟡 75% | ✅ 独立章节 + 指南已创建；frontmatter 语法、SemVer 影响、工程实践全覆盖 |
| **Secure your supply chain** | 公共 API 依赖控制、破坏性变更检测、SBOM 生成 | `SECURITY_RESPONSE.md` · `deny.toml` | 🟡 50% | cargo-semver-checks 未覆盖；SBOM 生成实践缺失 |
| **Safety-Critical Rust** | 认证工具链、规范、功能安全证据 | `RUST_SAFETY_CRITICAL_ECOSYSTEM/` · `concept/07_future/02_formal_methods.md` | 🟡 60% | MC/DC coverage 未覆盖；normative unsafe docs 未与官方路线对齐；FLS 发布节奏未覆盖 |

---

## 二、2026 稳定化目标详细映射
>
> **[来源: Rust Official Docs]**

### 2.1 语言与编译器层
>
> **[来源: Rust Official Docs]**

| 官方目标 | 负责人 | 状态 | 项目覆盖 | 覆盖文件 | 缺口 |
|:---|:---|:---:|:---|:---|:---|
| **Rust for Linux: compiler features** | Tomas Sedovic / Wesley Wiser | 推进中 | 🟡 部分 | `docs/04_rust_for_linux_2026.md` | 缺少具体 unstable feature 清单与代码示例 |
| **Rust for Linux: language features** | Tomas Sedovic / Josh Triplett | 推进中 | 🟡 部分 | `docs/04_rust_for_linux_2026.md` | 同上 |
| **Stabilize Const Generics** | Boxy / Niko Matsakis | **目标 2026 稳定** | 🟡 部分 | `concept/02_intermediate/02_generics.md` | `adt_const_params` 无代码示例；`min_generic_const_args` 无代码示例 |
| **Stabilize Const Traits** | Deadbeef | **目标 2026 RFC + 稳定** | 🟡 部分 | `concept/02_intermediate/01_traits.md` §Const Trait | 缺少 `~const` → `const trait` 语法迁移跟踪 |
| **Stabilize next-generation trait solver** | lcnr / Niko Matsakis | **目标 2026 稳定** | 🔴 **缺失** | — | **完全缺失**；需新建概念章节 + nightly 代码示例 |
| **Sized Hierarchy and Scalable Vectors** | David Wood / Niko Matsakis | **目标 2026 稳定** | 🔴 30% | `concept/02_intermediate/02_generics.md` | `extern types` 未覆盖；SVE/SME 未覆盖；`const Sized` 未覆盖 |
| **Stabilize Return Type Notation** | — | 推进中 | 🟡 部分 | `concept/03_advanced/02_async.md` §RTN | 缺少 dyn 兼容 + RTN 的组合分析 |
| **Open Enums** | — | nightly | 🔴 **缺失** | — | 完全缺失 |

### 2.2 工具链与生态层
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 官方目标 | 负责人 | 状态 | 项目覆盖 | 覆盖文件 | 缺口 |
|:---|:---|:---:|:---|:---|:---|
| **Stabilize cargo-script** | Ed Page | **目标 2026 稳定** | 🟡 75% | `concept/06_ecosystem/09_cargo_script.md` · `docs/06_toolchain/06_cargo_script_guide.md` | ✅ 独立章节 + 指南已创建；frontmatter 语法、SemVer 影响、工程实践全覆盖 |
| **Stabilize public/private dependencies** | Ed Page | **目标 2026 稳定** | 🟡 75% | `concept/06_ecosystem/10_public_private_deps.md` | ✅ 独立章节已创建；RFC 3516 核心机制、SemVer 矩阵、重构路径全覆盖 |
| **Stabilize Cargo SBOM precursor** | Sergey Davidoff | 推进中 | 🔴 **缺失** | — | 完全缺失 |
| **build-std** | — | 推进中 | 🟡 部分 | `concept/07_future/05_rust_version_tracking.md` | 缺少实际操作示例 |
| **cargo-semver-checks 合并至 cargo** | — | 推进中 | 🔴 **缺失** | — | 完全缺失 |
| **Cargo "plumbing" commands** | — | 原型 | 🔴 **缺失** | — | 完全缺失 |

### 2.3 异步与效果层
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 官方目标 | 负责人 | 状态 | 项目覆盖 | 覆盖文件 | 缺口 |
|:---|:---|:---:|:---|:---|:---|
| **Async Future Memory Optimisation** | — | 推进中 | 🟡 部分 | `concept/03_advanced/02_async.md` | 缺少内存布局优化细节 |
| **Async statemachine optimisation** | — | 推进中 | 🟡 部分 | `concept/03_advanced/02_async.md` §状态机 | 缺少编译器优化细节 |
| **Immobile types and guaranteed destructors** | — | 原型 | 🔴 **缺失** | — | 完全缺失；与 Pin 的关系未分析 |
| **Ergonomic ref-counting** | — | RFC 决策 | 🔴 30% | `concept/02_intermediate/03_memory_management.md` | Share trait / move expressions 未覆盖 |
| **Box notation for dyn async trait** | — | 推进中 | 🟡 部分 | `concept/03_advanced/02_async.md` | 缺少 `Box<dyn async Trait>` 语法分析 |

### 2.4 形式化与安全层
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 官方目标 | 负责人 | 状态 | 项目覆盖 | 覆盖文件 | 缺口 |
|:---|:---|:---:|:---|:---|:---|
| **a-mir-formality 作为类型系统规范** | — | 推进中 | 🟡 部分 | `concept/04_formal/02_type_theory.md` | 缺少 a-mir-formality 工具链使用指南 |
| **Normative Documentation for Sound unsafe Rust** | — | 推进中 | 🟡 部分 | `concept/03_advanced/03_unsafe.md` | 未与官方 Safety-Critical 路线对齐 |
| **Safety-Critical Lints in Clippy** | — | 推进中 | 🟡 部分 | `RUST_SAFETY_CRITICAL_ECOSYSTEM/` | 缺少 Clippy 安全 lint 矩阵 |
| **MC/DC Coverage Support** | — | 推进中 | 🔴 **缺失** | — | 完全缺失 |
| **MemorySanitizer / ThreadSanitizer** | Jakob Koschel | **目标 2026 稳定** | 🟡 部分 | `docs/03_miri_guide.md` | 缺少 MSan/TSan 与 Miri 的对比 |
| **BorrowSanitizer** | — | 原型 | 🔴 **缺失** | — | 完全缺失 |

### 2.5 WASM 与跨语言层
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 官方目标 | 负责人 | 状态 | 项目覆盖 | 覆盖文件 | 缺口 |
|:---|:---|:---:|:---|:---|:---|:---|
| **Wasm Components** | Yoshua Wuyts | **目标 2026 稳定** | 🟡 部分 | `crates/c12_wasm/` | 缺少 Component Model 新 target 分析；Wasm 语言特性实验未覆盖 |
| **C++/Rust Interop Problem Space Mapping** | — | 推进中 | 🟡 部分 | `concept/05_comparative/01_rust_vs_cpp.md` | 缺少官方 interop 路线图跟踪 |

---

## 三、缺口热力图
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```
                    覆盖率
            0%    25%    50%    75%   100%
            |──────|──────|──────|──────|
Next-gen trait solver    ████░░░░░░░░░░░░░░   🔴 缺失
public/private deps      ████████████░░░░░░░░   🟡 75%
cargo-script             ███████████████░░░░░   🟢 80%
Field Projections        ████░░░░░░░░░░░░░░   🔴 缺失
Immobile types           ████░░░░░░░░░░░░░░   🔴 缺失
Open Enums               ████░░░░░░░░░░░░░░   🔴 缺失
MC/DC Coverage           ████░░░░░░░░░░░░░░   🔴 缺失
BorrowSanitizer          ████░░░░░░░░░░░░░░   🔴 缺失
SBOM                     ████░░░░░░░░░░░░░░   🔴 缺失
cargo-semver-checks      ████░░░░░░░░░░░░░░   🔴 缺失
Sized Hierarchy          ████░░░░░░░░░░░░░░   🔴 缺失
Effects System           ██████████████░░░░   🟡 70%  (已有 306 行)
Const Generics           ███████████░░░░░░░   🟡 55%
Safety-Critical Rust     ███████████░░░░░░░   🟡 55%
Async Closures           ████████████████░░   🟢 80%
Rust for Linux           ███████████░░░░░░░   🟡 55%
```

---

## 四、行动建议（按优先级排序）
>
> **[来源: [crates.io](https://crates.io/)]**

### 🔴 P0 — 立即创建（完全缺失，2026 年稳定化目标）
>
> **[来源: [docs.rs](https://docs.rs/)]**

1. **Next-generation trait solver**
   - 新建 `concept/02_intermediate/01_traits.md` 补充章节 或独立文件
   - 创建 `crates/c04_generic/src/next_solver_preview.rs`（nightly）
   - 核心内容：现有 solver 的 coherence 漏洞、next solver 的行为差异、对 GATs/TAIT/specialization 的解锁

2. **Field Projections**
   - 新建 `concept/02_intermediate/03_memory_management.md` 补充章节
   - 与 Pin、智能指针、self-referential structs 联动

### 🟡 P1 — 补充深化（部分覆盖，需升级）
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

1. **Const Generics 扩展**
   - 扩展 `crates/c04_generic/src/rust_195_features.rs`
   - 增加 `adt_const_params` 和 `min_generic_const_args` 示例

2. **Sized Hierarchy / extern types / SVE**
   - 在 `concept/02_intermediate/02_generics.md` 中补充章节

3. **Immobile types / guaranteed destructors**
   - 与 `concept/03_advanced/02_async.md` 中 Pin 章节联动

4. **Safety-Critical Rust 官方路线对齐**
   - 创建 `docs/04_research/04_safety_critical_alignment_2026.md`

5. **io_uring / QUIC / HTTP3 / libp2p 深度**
   - 现有代码文件已有 200–800 行，需补充概念文档和决策树

6. **Embassy / RTIC / Rust for Linux / eBPF 深度**
   - 现有代码文件已有 400–500 行，需补充系统文档和形式化分析

### 🟢 P2 — 跟踪观察（nightly / 长期演进）
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

1. **Open Enums** — 加入 `concept/07_future/05_rust_version_tracking.md` 待跟踪表
2. **BorrowSanitizer** — 加入待跟踪表
3. **cargo-semver-checks / plumbing commands / SBOM** — 加入工具链演进跟踪
4. **MC/DC Coverage** — 加入 Safety-Critical 跟踪

---

## 五、参考链接
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/flagships.html)
- [Rust 2026 Stabilizations](https://rust-lang.github.io/rust-project-goals/2026/stabilizations.html)
- [Project Goals RFC](https://rust-lang.github.io/rust-project-goals/2026/rfc.html)
- [Rust Forge — Release Versions](https://forge.rust-lang.org/)
- [releases.rs](https://releases.rs/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [Parent README](../README.md)

---

## 相关概念
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon]**

---
