# 类型系统验证

本文件描述类型系统的验证范围、最小可验证示例（MVE）与证明义务映射。

## 证明义务与骨架映射（新增）

- 进展性/保持性（Type Safety）
  - Coq: `formal_rust/framework/proofs/coq/type_system_progress_preservation.v`
  - Lean: `formal_rust/framework/proofs/lean/TypeSystem/ProgressPreservation.lean`
- HM 推断：可靠性/完备性/最一般性
  - Coq: `formal_rust/framework/proofs/coq/hm_inference_soundness_completeness.v`
  - Lean: `formal_rust/framework/proofs/lean/TypeSystem/HMInference.lean`
  - 义务：
    - O-HM-SND: `hm_soundness`
    - O-HM-CMP: `hm_completeness`
    - O-HM-PT: `principal_types`
- Generics / Trait / Associated Types（占位义务）
  - O-TR-BND: Trait 约束一致性（映射 HM 合一与边界）
  - O-AT-PROJ: 关联类型投影一致性（映射 HM 合一与进展/保持）
  - O-GEN-MONO: 单态化正确性（后续阶段补充专用脚本）
- Ownership / Borrowing（占位义务）
  - O-OB-UNI: 可变借用唯一性（无并发别名）
  - O-OB-IMM: 不可变借用多别名但只读（无写）
  - O-OB-LIF: 生命周期不超越owner（无悬垂）

> 要求：依照文档 `language/02_type_system/22_formal_type_system_proofs.md` 的定理编号，逐条补全证明。

---

## 范围

- Rust ≤1.89 的类型规则与操作语义的可验证子集
- 目标：类型安全（进展性/保持性）、HM 推断正确性、型变安全的可验证骨架

## MVE（最小可验证示例）

- 函数抽象/应用，代数数据类型构造/匹配，引用与解引用
- 约束收集 + 合一的 HM 算法原型

## 质量门禁

- 每个证明义务需有对应的 Coq/Lean 脚本文件
- 脚本内保留 TODO/注释，后续迭代逐步去除 admit/sorry
