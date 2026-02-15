# 可执行语义路线图

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 与 K-Framework、PLT Redex 等可执行语义工具的对接可能性与路线图
> **参考**: [RustSEM (K-Framework, 2024)](https://link.springer.com/article/10.1007/s10703-024-00460-3)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)

---

## 一、现状与目标

| 维度 | 现状 | 目标 |
| :--- | :--- | :--- |
| 语义形式 | 自然语言 + 数学符号 | 可执行小步操作语义 |
| 验证方式 | 人工证明思路 | 自动/半自动验证（如 K 的 reachability） |
| 覆盖范围 | 语言级、概念级 | 内存级 OBS（可选） |

---

## 二、可选技术路线

### 2.1 K-Framework

| 项目 | 说明 |
| :--- | :--- |
| **RustSEM** | 2024 FMSD 论文，内存级 OBS、700+ 测试、可执行 |
| **对接可能** | 本项目 formal_methods 的 Def/规则 → K 语法定义；需学习 K 语法 |
| **工作量** | 高；需重写语义为 K 格式 |
| **优先级** | 低（调研阶段） |

### 2.2 PLT Redex

| 项目 | 说明 |
| :--- | :--- |
| **Racket 生态** | 小步语义、类型系统、测试 |
| **对接可能** | 本项目 type_system T1–T5、ownership 规则 → Redex 归约规则 |
| **工作量** | 中；Redex 语法相对简洁 |
| **优先级** | 中 |

### 2.3 自研最小子集

| 项目 | 说明 |
| :--- | :--- |
| **范围** | 仅 ownership + 简单类型（如 λ 演算 + Box） |
| **实现** | Rust/OCaml 写解释器 + 小步归约 |
| **工作量** | 中低 |
| **优先级** | 高（可快速验证概念） |

---

## 三、分阶段路线图

### 阶段 1：调研（1–2 个月）

| 任务 | 交付物 |
| :--- | :--- |
| K-Framework 语法学习 | 笔记、与 ownership 规则映射草案 |
| PLT Redex 评估 | 评估报告：是否适合 Rust 子集 |
| RustSEM 论文精读 | 内存级 OBS 与本研究语言级对应关系 |

### 阶段 2：最小可执行语义（2–3 个月）

| 任务 | 交付物 |
| :--- | :--- |
| 选择工具 | Redex 或自研 |
| 实现 λ + Box 子集 | 小步归约、所有权移动规则 |
| 测试用例 | 5–10 个正例、3–5 个反例（应拒绝） |

### 阶段 3：扩展（按需）

| 任务 | 说明 |
| :--- | :--- |
| 借用规则 | 增加共享/可变借用 |
| 生命周期 | 简化版 outlives |
| K 迁移 | 若阶段 2 成功，评估 K 迁移 |

---

## 四、与现有文档的衔接

| 本项目文档 | 可执行语义对应 |
| :--- | :--- |
| ownership_model 规则 1–3 | 归约规则：move、copy、drop |
| borrow_checker_proof 规则 5–8 | 借用状态转换 |
| type_system_foundations T1–T2 | 进展性、保持性可测试 |
| [FORMAL_FULL_MODEL_OVERVIEW](./FORMAL_FULL_MODEL_OVERVIEW.md) | 公理列表 → 语义规则 |

---

## 五、资源与依赖

| 资源 | 说明 |
| :--- | :--- |
| K-Framework | <https://kframework.org/> |
| PLT Redex | <https://docs.racket-lang.org/redex/> |
| RustSEM | 论文 + 若有开源实现 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
