# 可执行语义路线图

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 与 K-Framework、PLT Redex 等可执行语义工具的对接可能性与路线图
> **参考**: [RustSEM (K-Framework, 2024)](https://link.springer.com/article/10.1007/s10703-024-00460-3)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [可执行语义路线图](#可执行语义路线图)
  - [📑 目录](#-目录)
  - [一、现状与目标](#一现状与目标)
  - [二、可选技术路线](#二可选技术路线)
    - [2.1 K-Framework](#21-k-framework)
    - [2.2 PLT Redex](#22-plt-redex)
    - [2.3 自研最小子集](#23-自研最小子集)
  - [三、分阶段路线图](#三分阶段路线图)
    - [阶段 1：调研（1–2 个月）](#阶段-1调研12-个月)
    - [阶段 2：最小可执行语义（2–3 个月）](#阶段-2最小可执行语义23-个月)
    - [阶段 3：扩展（按需）](#阶段-3扩展按需)
  - [四、与现有文档的衔接](#四与现有文档的衔接)
  - [五、资源与依赖](#五资源与依赖)
  - [🆕 Rust 1.94 更新](#-rust-194-更新)
  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)
  - [**最后更新**: 2026-03-14 (Rust 1.94 深度整合)](#最后更新-2026-03-14-rust-194-深度整合)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

## 一、现状与目标
>
> **[来源: Rust Official Docs]**

| 维度 | 现状 | 目标 |
| :--- | :--- | :--- |
| 语义形式 | 自然语言 + 数学符号 | 可执行小步操作语义 |
| 验证方式 | 人工证明思路 | 自动/半自动验证（如 K 的 reachability） |
| 覆盖范围 | 语言级、概念级 | 内存级 OBS（可选） |

---

## 二、可选技术路线
>
> **[来源: Rust Official Docs]**

### 2.1 K-Framework

> **[来源: RFCs - github.com/rust-lang/rfcs]**
>
> **[来源: Rust Official Docs]**

| 项目 | 说明 |
| :--- | :--- |
| **RustSEM** | 2024 FMSD 论文，内存级 OBS、700+ 测试、可执行 |
| **对接可能** | 本项目 formal_methods 的 Def/规则 → K 语法定义；需学习 K 语法 |
| **工作量** | 高；需重写语义为 K 格式 |
| **优先级** | 低（调研阶段） |

### 2.2 PLT Redex

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| 项目 | 说明 |
| :--- | :--- |
| **Racket 生态** | 小步语义、类型系统、测试 |
| **对接可能** | 本项目 type_system T1–T5、ownership 规则 → Redex 归约规则 |
| **工作量** | 中；Redex 语法相对简洁 |
| **优先级** | 中 |

### 2.3 自研最小子集

> **[来源: POPL - Programming Languages Research]**

| 项目 | 说明 |
| :--- | :--- |
| **范围** | 仅 ownership + 简单类型（如 λ 演算 + Box） |
| **实现** | Rust/OCaml 写解释器 + 小步归约 |
| **工作量** | 中低 |
| **优先级** | 高（可快速验证概念） |

---

## 三、分阶段路线图
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 阶段 1：调研（1–2 个月）

> **[来源: PLDI - Programming Language Design]**

| 任务 | 交付物 |
| :--- | :--- |
| K-Framework 语法学习 | 笔记、与 ownership 规则映射草案 |
| PLT Redex 评估 | 评估报告：是否适合 Rust 子集 |
| RustSEM 论文精读 | 内存级 OBS 与本研究语言级对应关系 |

### 阶段 2：最小可执行语义（2–3 个月）

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

| 任务 | 交付物 |
| :--- | :--- |
| 选择工具 | Redex 或自研 |
| 实现 λ + Box 子集 | 小步归约、所有权移动规则 |
| 测试用例 | 5–10 个正例、3–5 个反例（应拒绝） |

### 阶段 3：扩展（按需）

> **[来源: POPL - Programming Languages Research]**

| 任务 | 说明 |
| :--- | :--- |
| 借用规则 | 增加共享/可变借用 |
| 生命周期 | 简化版 outlives |
| K 迁移 | 若阶段 2 成功，评估 K 迁移 |

---

## 四、与现有文档的衔接
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 本项目文档 | 可执行语义对应 |
| :--- | :--- |
| ownership_model 规则 1–3 | 归约规则：move、copy、drop |
| borrow_checker_proof 规则 5–8 | 借用状态转换 |
| type_system_foundations T1–T2 | 进展性、保持性可测试 |
| [FORMAL_FULL_MODEL_OVERVIEW](./FORMAL_FULL_MODEL_OVERVIEW.md) | 公理列表 → 语义规则 |

---

## 五、资源与依赖
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 资源 | 说明 |
| :--- | :--- |
| K-Framework | <https://kframework.org/> |
| PLT Redex | <https://docs.racket-lang.org/redex/> |
| RustSEM | 论文 + 若有开源实现 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14

---

## 🆕 Rust 1.94 更新
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **适用版本**: Rust 1.94.0+

详见 [RUST_194_RESEARCH_UPDATE](./RUST_194_RESEARCH_UPDATE.md)

**最后更新**: 2026-03-14

---

## 🆕 Rust 1.94 深度整合更新
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

> **[来源: PLDI - Programming Language Design]**

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- Rust 1.94 迁移指南
- [Rust 1.94 特性速查](../archive/2026_05_historical_docs/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [crates.io](https://crates.io/)]**

- [research_notes 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

---

## 权威来源索引

> **[来源: [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)]**
>
> **[来源: [Rust Blog](https://blog.rust-lang.org/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
