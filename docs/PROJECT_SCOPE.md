# 项目定位与范围

本项目定位为：基于Rust语言的学习项目，专注于Rust语言的语法、语义、设计模式和最佳实践的系统性学习与实践。

## 1. 目标与边界

- 学习目标：系统学习Rust语言的语法、语义和最佳实践
- 内容边界：以语言语法/语义、类型系统、所有权/借用/生命周期、宏/模块、并发/异步、FFI、内存/性能安全等为核心
- 交付方式：学习文档 + 代码示例 + 实践项目，提供渐进式学习路径

## 2. 核心交付

- 知识梳理索引：`formal_rust/language/00_index.md`
- 类型系统证明：
  - 文档：`formal_rust/language/02_type_system/22_formal_type_system_proofs.md`
  - 骨架：
    - Coq：`formal_rust/framework/proofs/coq/type_system_progress_preservation.v`
    - Lean：`formal_rust/framework/proofs/lean/TypeSystem/ProgressPreservation.lean`
- HM 推断映射与义务：
  - 文档：`formal_rust/language/02_type_system/02_type_inference.md`
  - 骨架：
    - Coq：`formal_rust/framework/proofs/coq/hm_inference_soundness_completeness.v`
    - Lean：`formal_rust/framework/proofs/lean/TypeSystem/HMInference.lean`
- 生命周期省略：`formal_rust/language/21_lifetime_elision_theory.md`
- 符号体系标准化：`formal_rust/MATHEMATICAL_NOTATION_STANDARD_V2.md`
- 验证框架索引与使用：`formal_rust/framework/verification_index.md`、`formal_rust/framework/proofs/README.md`

## 3. 验证与质量

- 结构与交叉引用：`tools/crossref_check.py`、`formal_rust/framework/verify_integrity.py`
- 证明骨架校验（本地/CI 建议）：确保 Coq/Lean 骨架存在且非空；占位允许（Admitted/sorry）用于收敛期；后续逐步替换为完整证明。

## 4. 非目标（Out of Scope）

- Rust 1.90+ 的新特性与变更（如需对比，仅在附注中说明差异，不纳入主体系）。
- 与语法/语义无直接关系的生态盘点、教程型内容与泛泛指南。

## 5. 面向人群

- 语言理论研究者：获取 Rust ≤1.89 的可验证语法/语义与形式化基线。
- 工程实践者：理解类型系统、所有权/借用等机制的严谨边界与工程映射。
- 工具链开发者：为编译器/验证工具提供一致的理论与证明参照。

---

> 说明：本文件为单一事实来源（SSOT）声明项目范围。若未来扩展至 1.90+，将新建对应版本的范围文件与分支（不影响 ≤1.89 主体系）。
