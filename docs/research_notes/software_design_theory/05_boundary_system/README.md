# 边界体系统一分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 100% 完成

---

## 宗旨

本目录提供软件设计理论体系的三维边界分析。**层次推进**：先读本 README 与 Def B1–B3，再查各矩阵决策树，最后按 [03_semantic_boundary_map](../02_workflow_safe_complete_models/03_semantic_boundary_map.md) 模式选取示例实践。

1. **安全 vs 非安全**：模式/模型在 Rust 中的安全子集边界
2. **支持 vs 不支持**：语言/库的原生支持程度
3. **充分表达 vs 非充分表达**：相对 OOP/GoF 的语义等价性

---

## 形式化定义

设 $D$ 为设计模式或执行模型，$B_s$、$B_p$、$B_e$ 分别为安全、支持、表达边界函数（定义见各矩阵文档）：

- **Def B1**：$B_s(D) \in \{\mathrm{Safe},\, \mathrm{Unsafe},\, \mathrm{Inexpr}\}$（见 [safe_unsafe_matrix](safe_unsafe_matrix.md) Def 1.1）
- **Def B2**：$B_p(D) \in \{\mathrm{Native},\, \mathrm{Lib},\, \mathrm{FFI}\}$（见 [supported_unsupported_matrix](supported_unsupported_matrix.md) Def 1.1）
- **Def B3**：$B_e(D) \in \{\mathrm{Same},\, \mathrm{Approx},\, \mathrm{NoExpr}\}$（见 [expressive_inexpressive_matrix](expressive_inexpressive_matrix.md) Def 1.1）

**Axiom B1**：三维边界独立；任一维度可单独判定；组合使用时需同时满足各维约束。

**定理 B-T1（边界一致性）**：对任意模式 $D$，$B_s(D)$、$B_p(D)$、$B_e(D)$ 由各矩阵文档的 Def 与定理唯一确定；与 [02_workflow_safe_complete_models](../02_workflow_safe_complete_models/) 的 23/43 分类一致。

*证明*：由各矩阵 Def 1.1；23 安全、43 完全的分类与 safe_unsafe、supported_unsupported、expressive_inexpressive 三矩阵对应。∎

**定理 B-T2（三维边界独立性）**：对任意 $D$，$B_s(D)$、$B_p(D)$、$B_e(D)$ 可独立判定；$\mathit{SafeB}(D) = \mathrm{Safe}$ 不蕴涵 $\mathit{ExprB}(D) = \mathrm{Same}$。

*证明*：由 Axiom B1；安全边界仅依赖 unsafe 使用，表达边界依赖 OOP 语义等价，二者独立。例：Singleton 为 Safe（OnceLock）但 Approx（无全局可变）。∎

---

## 文档索引

| 文档 | 内容 |
| :--- | :--- |
| [safe_unsafe_matrix](safe_unsafe_matrix.md) | 安全 vs 非安全边界矩阵 |
| [supported_unsupported_matrix](supported_unsupported_matrix.md) | 支持 vs 不支持边界矩阵 |
| [expressive_inexpressive_matrix](expressive_inexpressive_matrix.md) | 充分表达 vs 非充分表达边界矩阵 |

---

## 三维边界快速参考

| 维度 | 取值 | 含义 |
| :--- | :--- | :--- |
| 安全 | 纯 Safe / 需 unsafe / 无法表达 | 是否依赖 unsafe |
| 支持 | 原生 / 库 / FFI | 语言/标准库 vs 第三方 |
| 表达 | 等价 / 近似 / 不可表达 | 相对 GoF/OOP 语义 |

## 使用流程

1. 查模式：在 [04_boundary_matrix](../01_design_patterns_formal/04_boundary_matrix.md) 或对应模式文档
2. 判安全：用 [safe_unsafe_matrix](safe_unsafe_matrix.md) 决策树
3. 判支持：用 [supported_unsupported_matrix](supported_unsupported_matrix.md) 判定
4. 查表达：用 [expressive_inexpressive_matrix](expressive_inexpressive_matrix.md) 了解差异

---

## 快速决策

| 问题 | 查文档 |
| :--- | :--- |
| 某模式是否纯 Safe？ | [safe_unsafe_matrix](safe_unsafe_matrix.md) |
| 需哪个 crate？ | [supported_unsupported_matrix](supported_unsupported_matrix.md) |
| 与 GoF 有无差异？ | [expressive_inexpressive_matrix](expressive_inexpressive_matrix.md) |
| 从 OOP 迁移？ | expressive_inexpressive_matrix § 从 OOP 迁移建议 |

---

## 模式选取决策依据（实质指南）

| 需求类型 | 决策依据 | 推荐矩阵 |
| :--- | :--- | :--- |
| **安全优先** | 需零 unsafe、无 FFI | safe_unsafe_matrix；排除 Inexpr |
| **零依赖** | 仅 std、无第三方 crate | supported_unsupported_matrix；选 Native |
| **语义等价** | 与 GoF/OOP 一致 | expressive_inexpressive_matrix；选 Same |
| **组合约束** | 子模式 Safe 则组合 Safe | 定理 B-T1、SBM-C2；见 [04_compositional_engineering](../04_compositional_engineering/02_effectiveness_proofs.md) CE-T1–T3 |
| **执行模型** | 同步/异步/并发/并行/分布式 | [03_execution_models/06_boundary_analysis](../03_execution_models/06_boundary_analysis.md) 决策树 |

**选型流程**：需求 → [03_semantic_boundary_map](../02_workflow_safe_complete_models/03_semantic_boundary_map.md) 模式选取示例 → 查 Safe/支持/表达 → 确定实现路径。

---

## 模式选取与边界判定完整示例（实质内容）

**场景**：需跨平台 UI 组件族（按钮、文本框）；运行时根据平台选择。

**步骤 1**：按需求查模式 → [03_semantic_boundary_map](../02_workflow_safe_complete_models/03_semantic_boundary_map.md) 按需求反向查 → **Abstract Factory**。

**步骤 2**：判安全 → [safe_unsafe_matrix](safe_unsafe_matrix.md) 创建型表 → **纯 Safe**。

**步骤 3**：判支持 → [supported_unsupported_matrix](supported_unsupported_matrix.md) → **原生**（trait + 枚举）。

**步骤 4**：判表达 → [expressive_inexpressive_matrix](expressive_inexpressive_matrix.md) → **等价**。

**结论**：可零依赖、纯 Safe、等价实现。代码见 [03_semantic_boundary_map 示例 1](../02_workflow_safe_complete_models/03_semantic_boundary_map.md#示例-1跨平台-ui-组件族)。

---

## 场景化 Safe 决策示例（实质内容）

### 示例 1：需全局唯一配置

**需求**：应用启动时加载配置，全局访问。

**步骤**：查模式 → Singleton；判安全 → [safe_unsafe_matrix](safe_unsafe_matrix.md) 创建型 → **OnceLock 为纯 Safe**；判支持 → 原生 `std::sync::OnceLock`。

**结论**：`OnceLock<Config>`，零 unsafe。

### 示例 2：需跨线程共享缓存

**需求**：多线程可读共享缓存，偶有更新。

**步骤**：查模式 → Flyweight + 缓存；判安全 → 共享用 `Arc`；跨线程需 `Sync` → **Arc\<RwLock\<HashMap>>** 为纯 Safe。

**结论**：`Arc<RwLock<HashMap<K, V>>>` 或 `dashmap`，零 unsafe。

### 示例 3：需 FFI 调用 C 库

**需求**：调用 C 的 `malloc`/`free`。

**步骤**：判安全 → 需 `unsafe`；可封装为 Safe API（`Box::from_raw` 等）→ **需 unsafe、可安全抽象**。

**结论**：内部 `unsafe`；对外 `pub fn` 为 Safe 抽象；见 [borrow_checker_proof](borrow_checker_proof.md) Def UNSAFE1。

---

## 与顶层衔接

本边界体系与 [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) 衔接，扩展至设计模式与执行模型维度。
