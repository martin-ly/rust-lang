> **内容分级**: [综述级]
> **Rust 版本**: 1.96.0+ (Edition 2024)

# L4 形式化理论层索引（Formal Methods Layer Index）

> **受众**: [研究者]
> **定位**: Rust 概念体系的**数学根基**与形式化验证。为 L1-L3 的所有安全保证提供严格的数学证明，是知识体系的"地基"。
> **Bloom 层级**: 分析 → 评价
> **核心功能**: 为上层概念提供**可机械验证的**安全性证明
> **规范文件**: [`04_formal/README.md`](04_formal/README.md)
> **[来源: Wikipedia - Linear Logic]** · **[来源: Wikipedia - Type Theory]** · **[来源: POPL 2018 - RustBelt: Securing the Foundations of the Rust Programming Language]** · **[来源: Iris Project - iris-project.org]**

---

## 📑 目录

- [L4 形式化理论层索引（Formal Methods Layer Index）](#l4-形式化理论层索引formal-methods-layer-index)
  - [📑 目录](#-目录)
  - [核心四理论速查](#核心四理论速查)
  - [L4 → L1-L3 核心映射链](#l4--l1-l3-核心映射链)
  - [映射精度评估](#映射精度评估)
  - [变更日志](#变更日志)
  - [权威来源索引](#权威来源索引)

## 核心四理论速查
>

| 理论 | 规范文件 | 核心内容 | 状态 |
|:---|:---|:---|:---|
| **线性/仿射逻辑** | [`04_formal/01_linear_logic.md`](04_formal/01_linear_logic.md) | 资源敏感逻辑、⊗/⅋/⊸、Girard 1987、weakening | ✅ v1.0 |
| **类型论基础** | [`04_formal/02_type_theory.md`](04_formal/02_type_theory.md) | ADT、HM 推断、子类型、Variance、System F / Fω | ✅ v1.0 |
| **所有权形式化** | [`04_formal/03_ownership_formal.md`](04_formal/03_ownership_formal.md) | COR、区域类型、分数权限、Stacked/Tree Borrows | ✅ v1.0 |
| **RustBelt 验证** | [`04_formal/04_rustbelt.md`](04_formal/04_rustbelt.md) | Iris 分离逻辑、验证工具链（Creusot/Verus/Kani）、工业应用 | ✅ v1.0 |
| **子类型与变型** | [`04_formal/06_subtype_variance.md`](04_formal/06_subtype_variance.md) | 协变/逆变/不变、生命周期子类型、形式化推导 | ✅ v1.0 |
| **分离逻辑** | [`04_formal/07_separation_logic.md`](04_formal/07_separation_logic.md) | * 算子、帧规则、CSL、Iris 框架、RustBelt 应用映射 | ✅ v1.0 |
| **类型推断** | [`04_formal/08_type_inference.md`](04_formal/08_type_inference.md) | HM 算法、统一、Rust 扩展、Trait 约束推断 | ✅ v1.0 |
| **操作语义** | [`04_formal/09_operational_semantics.md`](04_formal/09_operational_semantics.md) | 小步/大步语义、求值上下文、Rust 形式化 | ✅ v1.0 |

---

## L4 → L1-L3 核心映射链
>

```text
[线性逻辑] ⊗ ───────→ [所有权] ───────→ Move 语义安全
[区域类型] 'a ──────→ [生命周期] ────→ 无悬垂指针
[分数权限] ─────────→ [借用规则] ────→ AXM 规则
[分离逻辑] ─────────→ [并发安全] ────→ Send/Sync 证明
[代数类型] ─────────→ [enum/struct] ─→ 模式匹配
[System F] ─────────→ [泛型] ────────→ 单态化零成本
        │
        └────────────────────────────────→ [RustBelt: 机械验证上述所有定理]
```

---

## 映射精度评估
>

| L4 理论 | L1-L3 概念 | 映射类型 | 精度 |
|:---|:---|:---|:---|
| 线性逻辑 ⊗ | 所有权唯一性 | 双射 | **精确** |
| 仿射逻辑 weakening | `Copy` trait | 特化 | **精确** |
| 区域类型 | 生命周期 `'a` | 嵌入 | **精确** |
| 分数权限 | 借用 `&/&mut` | 同态 | **近似** |
| 分离逻辑 | 并发安全 | 同态 | **近似** |
| 代数类型 | `enum`/`struct` | 双射 | **精确** |

---

## 变更日志
>

| 版本 | 日期 | 变更 |
|:---|:---|:---|
| v1.0 | 2026-05-13 | 创建层级入口索引 |

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引

>
>
>

---

---

> **补充来源**
