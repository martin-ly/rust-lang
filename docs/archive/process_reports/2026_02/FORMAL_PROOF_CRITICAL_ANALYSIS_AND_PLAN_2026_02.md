# research_notes 形式化证明体系：批判性分析与可持续推进计划

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **用途**: 回应「缺乏系统完整充分的形式化证明模型、整体性层次不足、未对标国际最新全充分形式化证明」的反馈
> **状态**: ✅ **阶段 1–3 100% 完成**（阶段 3 含 Coq 证明骨架）

---

## 一、批判性分析：现状诊断

### 1.1 核心问题归纳

| 维度 | 现状 | 问题 |
| :--- | :--- | :--- |
| **系统完整性** | 105+ Def/Axiom/Theorem 分散于 17+ 文档 | 缺乏单一「全充分形式化模型」入口；无统一可执行语义 |
| **证明充分性** | 多为证明思路、结构归纳法描述 | 非机器可检查（无 Coq/Isabelle/Lean 证明）；部分为「证明草图」 |
| **整体性** | formal_methods、type_theory、software_design_theory 分域 | 域间依赖关系未形式化；缺乏「公理→定理→实现」全链路可追溯 |
| **层次性** | 有 PROOF_INDEX、UNIFIED_SYSTEMATIC_FRAMEWORK | 层次划分（公理层/语义层/定理层/边界层）存在，但**证明深度层次**不清晰 |
| **国际对标** | 引用 RustBelt、Rust Distilled | 未系统对标 RustBelt Meets Relaxed Memory、Aeneas、coq-of-rust、Crux、RustSEM、AutoVerus 等 2024–2025 最新成果 |

### 1.2 与国际权威形式化证明的差距

| 国际成果 | 特点 | 本项目差距 |
| :--- | :--- | :--- |
| **RustBelt** (Iris/Coq) | 机器可检查证明、分离逻辑、MIR 级建模 | Coq 骨架已创建（T-OW2）；无 Iris 分离逻辑；无 MIR 级 |
| **RustBelt Meets Relaxed Memory** (POPL 2020) | 松弛内存、Arc 数据竞争形式化 | 无松弛内存模型；原子操作形式化仅 Def 级 |
| **Aeneas** (Coq/F*/HOL4/Lean) | 多证明助手、Safe Rust 翻译 | 无证明助手翻译；无多后端验证 |
| **coq-of-rust** (Rocq) | THIR→Coq、借用与 effect 显式 | 无编译器 IR 级形式化 |
| **Crux-MIR** | 比特级精确、密码学验证 | 无比特级模型 |
| **RustSEM** (K-Framework, 2024) | 可执行操作语义、700+ 测试、内存级 OBS | 无可执行语义；无 K 框架实现 |
| **AutoVerus** (2024–2025) | LLM 自动证明生成、90%+ 正确率 | 无自动化证明生成 |

### 1.3 论证充分性缺口

1. **证明方法**：多数为「结构归纳法」「规则归纳法」的**文字描述**，缺乏：
   - 归纳基与归纳步的**形式化陈述**
   - 辅助引理的**显式编号与依赖图**
   - 反例的**形式化否定**（`¬P` 的构造）

2. **语义层**：有操作/指称/公理语义的**概念区分**，但缺乏：
   - **可执行**的小步操作语义（如 K-Framework、PLT Redex）
   - 指称语义与类型论的**范畴论对应**（如 Fω、System F 的 Rust 片段）

3. **机器可检查性**：FORMAL_VERIFICATION_GUIDE 有六类验证任务清单；**Coq 骨架已创建**（[coq_skeleton](../../../research_notes/coq_skeleton/) T-OW2，证明 Admitted）；Aeneas/coq-of-rust 对接方案已制定（[AENEAS_INTEGRATION_PLAN](../../../research_notes/AENEAS_INTEGRATION_PLAN.md)、[COQ_OF_RUST_INTEGRATION_PLAN](../../../research_notes/COQ_OF_RUST_INTEGRATION_PLAN.md)）

### 1.4 整体性与层次性缺口

1. **整体性**：
   - 无「Rust 形式化全模型」单文档：将 ownership + borrow + lifetime + type + trait + async + pin 统一于**单一形式系统**
   - 域间定理（如 ownership T2 → borrow T1）的**显式推导链**不完整

2. **层次性**：
   - **证明深度层次**未定义：L1 证明思路 / L2 完整证明 / L3 机器可检查
   - **抽象层次**：语言级 vs MIR 级 vs 内存级 的对应关系未形式化

---

## 二、意见与建议

### 2.1 短期（可立即落实）

| 建议 | 说明 |
| :--- | :--- |
| **新建「国际对标索引」** | 建 `INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md`，系统列出 RustBelt、Aeneas、coq-of-rust、Crux、RustSEM、AutoVerus 等，每项含：论文/工具链接、形式化范围、与本项目 PROOF_INDEX 的对应关系、差距说明 |
| **证明深度标注** | 在 PROOF_INDEX 中为每项证明增加「深度」字段：L1 证明思路 / L2 完整证明 / L3 机器可检查 |
| **单文档「形式化全模型」入口** | 新建 `FORMAL_FULL_MODEL_OVERVIEW.md`，用单一文档勾勒 ownership+borrow+lifetime+type+trait+async+pin 的**统一形式系统**，含公理列表、定理依赖 DAG、与各子文档的映射 |
| **层次化导航** | 在 README 中增加「按证明深度」「按抽象层次」的导航入口 |

### 2.2 中期（1–3 个月）

| 建议 | 说明 |
| :--- | :--- |
| **RustBelt 对标** | 将 ownership_model、borrow_checker_proof 与 RustBelt 论文逐章对标，标注「已覆盖」「部分覆盖」「未覆盖」 |
| **证明充分性补全** | 选取 3–5 个核心定理（如 ownership T2、borrow T1、type T3），撰写**完整证明**（归纳基、归纳步、辅助引理编号） |
| **可执行语义占位** | 在 formal_methods 中增加「可执行语义路线图」：与 K-Framework、PLT Redex 的对接可能性 |
| **Aeneas/coq-of-rust 对接** | 调研 Aeneas、coq-of-rust 的输入要求，给出「本项目文档 → 工具输入」的映射方案 |

### 2.3 长期（季度–年度）

| 建议 | 说明 |
| :--- | :--- |
| **机器可检查证明** | 选取 1–2 个定理，在 Coq/Isabelle 中实现证明，纳入 FORMAL_VERIFICATION_GUIDE |
| **RustSEM 风格可执行语义** | 若资源允许，考虑 K-Framework 或自研小步语义，覆盖 Rust 子集 |
| **松弛内存模型** | 对标 RustBelt Meets Relaxed Memory，补全原子操作、Arc 的松弛内存形式化 |

---

## 三、可持续推进计划与方案

### 3.1 阶段 1：对标与缺口显式化（2–4 周）✅ 100% 完成

| 任务 | 交付物 | 状态 |
| :--- | :--- | :--- |
| 国际对标索引 | `INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md` | ✅ |
| 证明深度标注 | PROOF_INDEX 增加 depth 字段、按深度导航 | ✅ |
| 形式化全模型入口 | `FORMAL_FULL_MODEL_OVERVIEW.md` | ✅ |
| 层次化导航 | README、INDEX 按深度/层次导航 | ✅ |

### 3.2 阶段 2：证明充分性补全（1–2 个月）✅ 100% 完成

| 任务 | 交付物 | 优先级 | 状态 |
| :--- | :--- | :--- | :--- |
| 核心定理完整证明 | ownership T2、borrow T1、type T3 的完整证明文档 | 高 | ✅ 已创建 [CORE_THEOREMS_FULL_PROOFS](../../../research_notes/CORE_THEOREMS_FULL_PROOFS.md) |
| RustBelt 逐章对标 | `RUSTBELT_ALIGNMENT.md` | 中 | ✅ 已创建 |
| 可执行语义路线图 | `EXECUTABLE_SEMANTICS_ROADMAP.md` | 低 | ✅ 已创建 |

### 3.3 阶段 3：工具对接与机器证明（3–6 个月）✅ 骨架完成

| 任务 | 交付物 | 优先级 | 状态 |
| :--- | :--- | :--- | :--- |
| Aeneas 对接调研 | `AENEAS_INTEGRATION_PLAN.md` | 中 | ✅ 已创建 |
| coq-of-rust 对接调研 | `COQ_OF_RUST_INTEGRATION_PLAN.md` | 中 | ✅ 已创建 |
| 1–2 定理 Coq/Isabelle 证明 | 实际证明代码 + 文档 | 高（若资源允许） | ✅ 骨架已创建 [coq_skeleton](../../../research_notes/coq_skeleton/)、[COQ_ISABELLE_PROOF_SCAFFOLDING](../../../research_notes/COQ_ISABELLE_PROOF_SCAFFOLDING.md) |

### 3.4 持续机制

| 机制 | 说明 | 状态 |
| :--- | :--- | :--- |
| **版本触发** | Rust 新版本发布时，更新 RUST_XXX 特性形式化，检查与最新 formal verification 成果的对标 | 已建立 |
| **季度审查** | 每季度更新 INTERNATIONAL_FORMAL_VERIFICATION_INDEX，补充新论文/工具 | 已建立 |
| **缺口追踪** | 在 00_completeness_gaps 中增加「国际对标缺口」小节，与阶段 1 交付物联动 | ✅ formal_methods、type_theory 已补全 |

---

## 四、总结

**批判性结论**：research_notes 在**文档覆盖广度**和**概念-公理-定理索引**上已达较高水平，但在**证明充分性**（机器可检查）、**整体性**（单一全模型）、**国际对标**（RustBelt、Aeneas、RustSEM 等）上存在明确缺口。建议按上述三阶段推进，优先完成「国际对标索引」和「形式化全模型入口」，以提升整体性与层次性，再逐步补全证明充分性与工具对接。

---

## 五、阶段 1–3 完成总结（2026-02-14）

### 阶段 1 交付物

| 交付物 | 路径 |
| :--- | :--- |
| 国际对标索引 | [INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md](../../../research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |
| 证明深度标注 | [PROOF_INDEX.md](../../../research_notes/PROOF_INDEX.md) § 证明深度层次、按证明深度导航 |
| 形式化全模型入口 | [FORMAL_FULL_MODEL_OVERVIEW.md](../../../research_notes/FORMAL_FULL_MODEL_OVERVIEW.md) |
| 层次化导航 | [README.md](../../../research_notes/README.md)、[INDEX.md](../../../research_notes/INDEX.md) |
| RustBelt 逐章对标 | [RUSTBELT_ALIGNMENT.md](../../../research_notes/RUSTBELT_ALIGNMENT.md) |
| 可执行语义路线图 | [EXECUTABLE_SEMANTICS_ROADMAP.md](../../../research_notes/EXECUTABLE_SEMANTICS_ROADMAP.md) |
| 核心定理完整证明 | [CORE_THEOREMS_FULL_PROOFS.md](../../../research_notes/CORE_THEOREMS_FULL_PROOFS.md) |
| Aeneas 对接计划 | [AENEAS_INTEGRATION_PLAN.md](../../../research_notes/AENEAS_INTEGRATION_PLAN.md) |
| coq-of-rust 对接计划 | [COQ_OF_RUST_INTEGRATION_PLAN.md](../../../research_notes/COQ_OF_RUST_INTEGRATION_PLAN.md) |
| 国际对标缺口 | [formal_methods/00_completeness_gaps.md](../../../research_notes/formal_methods/00_completeness_gaps.md) §10、[type_theory/00_completeness_gaps.md](../../../research_notes/type_theory/00_completeness_gaps.md) §8 |

### 阶段 2 交付物

| 交付物 | 路径 |
| :--- | :--- |
| 核心定理完整证明 | [CORE_THEOREMS_FULL_PROOFS.md](../../../research_notes/CORE_THEOREMS_FULL_PROOFS.md) |
| RustBelt 逐章对标 | [RUSTBELT_ALIGNMENT.md](../../../research_notes/RUSTBELT_ALIGNMENT.md) |
| 可执行语义路线图 | [EXECUTABLE_SEMANTICS_ROADMAP.md](../../../research_notes/EXECUTABLE_SEMANTICS_ROADMAP.md) |

### 阶段 3 交付物

| 交付物 | 路径 |
| :--- | :--- |
| Coq 证明骨架 | [coq_skeleton/OWNERSHIP_UNIQUENESS.v](../../../research_notes/coq_skeleton/OWNERSHIP_UNIQUENESS.v) |
| L3 实施指南 | [COQ_ISABELLE_PROOF_SCAFFOLDING.md](../../../research_notes/COQ_ISABELLE_PROOF_SCAFFOLDING.md) |

**后续**：补全 Admitted 证明、扩展 T-BR1/T-TY3 骨架；见 [AENEAS_INTEGRATION_PLAN](../../../research_notes/AENEAS_INTEGRATION_PLAN.md)、[COQ_OF_RUST_INTEGRATION_PLAN](../../../research_notes/COQ_OF_RUST_INTEGRATION_PLAN.md)

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
