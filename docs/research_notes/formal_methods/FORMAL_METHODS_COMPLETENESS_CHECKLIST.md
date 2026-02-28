# formal_methods 完备性检查表

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 六篇形式化文档 × 六维（概念定义、属性关系、解释论证、形式证明、反例、思维表征四类）自检，确保充分完整完备
> **上位**: [README](README.md)、[SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md)、[QUALITY_CHECKLIST](../QUALITY_CHECKLIST.md)

---

## 六篇 × 六维 完备性矩阵

每篇需具备：
**概念定义**（Def/公理）、**属性关系**（与它机制依赖）、**解释论证**（动机、设计理由）、
**形式证明**（定理与证明思路）、**反例**（违反即编译错误或 UB）、
**思维表征四类**（思维导图、多维矩阵、决策树、推理证明树）入口。

| 文档 | 概念定义 | 属性关系 | 解释论证 | 形式证明 | 反例 | 思维表征四类 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| [ownership_model](ownership_model.md) | ✅ 规则 1–3, Def 1.1–1.5 | ✅ 与 borrow/变量 | ✅ 理论基础、设计理由 | ✅ T2, T3 | ✅ 使用已移动、双重释放 | ✅ 导图/矩阵/证明树/决策树 |
| [borrow_checker_proof](borrow_checker_proof.md) | ✅ 规则 5–8 | ✅ 与 ownership/lifetime/Send | ✅ 数据竞争定义、理论 | ✅ T1, T2 | ✅ 双重可变借用、悬垂 | ✅ 同上 |
| [lifetime_formalization](lifetime_formalization.md) | ✅ LF1–LF2, Def 1.4, $\ell \subseteq \text{lft}$ | ✅ 与 borrow、型变 | ✅ 区域类型、NLL | ✅ LF-T1–T3 | ✅ 返回局部引用、存短命 | ✅ 矩阵/证明树 |
| [async_state_machine](async_state_machine.md) | ✅ Def 4.1–5.2（Future、Poll） | ✅ 与 Pin、Send/Sync | ✅ 状态机、并发安全 | ✅ T6.1–T6.3, SPAWN-T1 | ✅ 非 Send 跨线程、未 Pin | ✅ 导图/矩阵/证明树/决策树 |
| [pin_self_referential](pin_self_referential.md) | ✅ Def 1.1–2.2（位置稳定、自引用） | ✅ 与 async、Unpin | ✅ 堆/栈固定、设计理由 | ✅ T1–T3 | ✅ 未 Pin 自引用、栈 !Unpin | ✅ 矩阵/证明树/决策树 |
| [send_sync_formalization](send_sync_formalization.md) | ✅ Def SEND1, SYNC1, SYNC-L1 | ✅ $T:\text{Sync} \Leftrightarrow \&T:\text{Send}$；与 spawn/Future/Arc | ✅ 跨线程安全、FLS Ch.17.1 | ✅ SEND-T1, SYNC-T1, SEND-SYNC-T1 | ✅ Rc !Send、Cell !Sync、非 Send spawn | ✅ 导图/矩阵/决策树/证明树 |

---

## 维度说明

- **概念定义**：文档内显式 Def 或等价公理；可追溯至 README 六篇并表。
- **属性关系**：与其它机制（ownership/borrow/lifetime/async/pin/send_sync）的依赖或等价关系。
- **解释论证**：设计动机、为何可判定、与 FLS/RustBelt 等权威对应（见 README 国际权威对标）。
- **形式证明**：定理编号 + 证明思路或完整证明；与 [PROOF_INDEX](../PROOF_INDEX.md) 衔接。
- **反例**：至少一例违反导致编译错误或 UB；可集中见 [FORMAL_PROOF_SYSTEM_GUIDE](../FORMAL_PROOF_SYSTEM_GUIDE.md) 反例索引。
- **思维表征四类**：各篇末尾「相关思维表征」表含思维导图、概念多维矩阵、决策树、推理证明树四类入口；见 [HIERARCHICAL_MAPPING_AND_SUMMARY](../HIERARCHICAL_MAPPING_AND_SUMMARY.md) §3.1。

---

## 与安全可判定机制总览的对应

本表与 [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](../SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) §二、§三 一致：总览按「机制」列出形式化文档与反例，本表按「文档」核对六维是否齐全。二者互为完备性检查。

---

## 维护约定

- 新增 formal_methods 文档时：在本表增加一行，六维逐项填写并保持 ✅。
- 某篇补充定义/定理/反例/思维表征时：更新对应单元格说明，保持 ✅。
- 季度维护：与 [MAINTENANCE_GUIDE](../MAINTENANCE_GUIDE.md) 协同，核对本表与 README 六篇并表、00_completeness_gaps 一致。

---

**维护者**: Rust Formal Methods Research Group
**最后更新**: 2026-02-14
**状态**: ✅ 六篇 × 六维 已全覆盖
