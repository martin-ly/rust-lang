# RustBelt 逐章对标

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 将 ownership_model、borrow_checker_proof 与 RustBelt 论文逐章对标，标注「已覆盖」「部分覆盖」「未覆盖」
> **参考**: [RustBelt: Logical Foundations for the Future of Safe Systems Programming](https://plv.mpi-sws.org/rustbelt/) (POPL 2018)

---

## 一、RustBelt 论文结构（附录形式化）

| 章节/主题 | RustBelt 内容 | 本项目对应 | 覆盖度 |
| :--- | :--- | :--- | :--- |
| **λRust 语法** | 形式化语言子集语法 | ownership_model、borrow_checker_proof 的 Def/规则 | 部分 |
| **操作语义** | 小步归约 $e \to e'$ | type_system 进展性/保持性；无显式 MIR 级 | 部分 |
| **类型系统** | typing rules | type_system_foundations T1–T5 | 部分 |
| **生命周期逻辑** | lifetime 证明规则 | lifetime_formalization LF1–LF3 | 部分 |
| **借用证明规则** | 分离逻辑、borrowing | borrow_checker_proof T1–T2 | 部分 |
| **owned pointers** | Box 语义 | ownership_model Def BOX1、BOX-T1 | 已覆盖 |
| **&mut T** | 可变引用 | borrow 规则 6、A-BR2 | 已覆盖 |
| **&T** | 共享引用 | borrow 规则 5、A-BR1 | 已覆盖 |
| **Copy** | 复制语义 | ownership 规则、Copy trait | 已覆盖 |
| **Send/Sync** | 并发 trait | async_state_machine T6.2、SPAWN-T1 | 已覆盖 |
| **Iris 分离逻辑** | 机器可检查证明框架 | [coq_skeleton](coq_skeleton/)（T-OW2 骨架，证明 Admitted） | 部分 |
| **MIR 级建模** | 中间表示级语义 | 无 | 未覆盖 |
| **unsafe 库验证** | 每库验证条件 | borrow UNSAFE1、UNSAFE-T1/T2 | 部分 |

---

## 二、逐章对标详情

### 2.1 所有权与借用（RustBelt 核心）

| RustBelt 概念 | 本项目 | 差距 |
| :--- | :--- | :--- |
| 唯一所有者 | ownership T2、A-OW1、[coq_skeleton](coq_skeleton/) | Coq 骨架已创建，证明待补全 |
| 移动语义 | ownership 规则 2、A-OW2 | 语言级有，MIR 级无 |
| 借用互斥 | borrow T1、A-BR2/3 | Coq 骨架待扩展（见 [COQ_ISABELLE_PROOF_SCAFFOLDING](COQ_ISABELLE_PROOF_SCAFFOLDING.md)） |
| 生命周期 outlives | lifetime LF-T1–T3 | 无 Iris lifetime 逻辑 |

### 2.2 类型系统

| RustBelt 概念 | 本项目 | 差距 |
| :--- | :--- | :--- |
| 进展性 | type_system T1 | L2 完整证明；Coq 骨架待扩展 |
| 保持性 | type_system T2 | 同上 |
| 类型安全 | type_system T3 | 同上；见 [CORE_THEOREMS_FULL_PROOFS](CORE_THEOREMS_FULL_PROOFS.md) §4 |

### 2.3 扩展（RustBelt Meets Relaxed Memory, POPL 2020）

| 主题 | RustBelt | 本项目 | 覆盖度 |
| :--- | :--- | :--- | :--- |
| 松弛内存 | synchronized ghost state | 无 | 未覆盖 |
| Arc 数据竞争 | 形式化发现 Arc bug | Def ATOMIC1、ARC1；无松弛内存 | 部分 |
| 原子操作 | 内存序形式化 | Def ATOMIC1 | 部分 |

---

## 三、覆盖度汇总

| 维度 | 已覆盖 | 部分覆盖 | 未覆盖 |
| :--- | :--- | :--- | :--- |
| 所有权语义 | ✓ | - | - |
| 借用规则 | ✓ | - | - |
| 生命周期 | ✓ | - | - |
| 类型系统 | - | ✓ | - |
| Iris/Coq 证明 | - | ✓（coq_skeleton T-OW2 骨架） | - |
| MIR 级 | - | - | ✓ |
| 松弛内存 | - | - | ✓ |

---

## 四、补全路线图

1. **短期**：保持语言级形式化与 RustBelt 概念对齐；在 PROOF_INDEX 中标注 RustBelt 对应章节
2. **中期**：补全 [coq_skeleton](coq_skeleton/) Admitted 证明；扩展 T-BR1/T-TY3 骨架（见 [COQ_ISABELLE_PROOF_SCAFFOLDING](./COQ_ISABELLE_PROOF_SCAFFOLDING.md)、[AENEAS_INTEGRATION_PLAN](./AENEAS_INTEGRATION_PLAN.md)、[COQ_OF_RUST_INTEGRATION_PLAN](./COQ_OF_RUST_INTEGRATION_PLAN.md)）
3. **长期**：若资源允许，对标 RustBelt Meets Relaxed Memory，补全原子操作与 Arc 松弛内存形式化

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
