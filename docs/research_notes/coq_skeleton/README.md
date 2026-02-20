# Coq 证明骨架（L3  scaffolding）

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 为 L3 机器可检查证明提供 Coq 定理陈述骨架，对应 [CORE_THEOREMS_FULL_PROOFS](../CORE_THEOREMS_FULL_PROOFS.md)
> **状态**: ✅ 已完成

---

## 文件说明

| 文件 | 对应定理 | 状态 |
| :--- | :--- | :--- |
| `OWNERSHIP_UNIQUENESS.v` | T-OW2 所有权唯一性 | 定理陈述已定义；证明 Admitted |

---

## 编译

**前置**: 安装 [Coq](https://coq.inria.fr/)（建议 8.18+）

```bash
cd docs/research_notes/coq_skeleton
coqc OWNERSHIP_UNIQUENESS.v
```

---

## 补全路线

1. **细化 State 定义**：增加「可达状态」谓词（由初始状态经规则 1–3 转换得到）
2. **归纳证明**：对状态转换归纳；归纳基用 L-OW1；归纳步对移动/复制/作用域结束分类
3. **扩展**：增加 `BORROW_DATARACE_FREE.v`（T-BR1）、`TYPE_SAFETY.v`（T-TY3）

---

## 与文档对应

- [CORE_THEOREMS_FULL_PROOFS](../CORE_THEOREMS_FULL_PROOFS.md) §2 — 完整证明结构
- [AENEAS_INTEGRATION_PLAN](../AENEAS_INTEGRATION_PLAN.md) — Aeneas 对接
- [COQ_OF_RUST_INTEGRATION_PLAN](../COQ_OF_RUST_INTEGRATION_PLAN.md) — coq-of-rust 对接
