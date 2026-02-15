# Coq/Isabelle 证明骨架与 L3 实施指南

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 阶段 3「1–2 定理 Coq/Isabelle 证明」的骨架交付物与实施指南
> **上位文档**: [FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](./FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md)

---

## 一、已创建骨架

| 骨架 | 路径 | 定理 | 状态 |
| :--- | :--- | :--- | :--- |
| Coq 所有权唯一性 | [coq_skeleton/OWNERSHIP_UNIQUENESS.v](./coq_skeleton/OWNERSHIP_UNIQUENESS.v) | T-OW2 | 定理陈述 + Admitted |
| Coq 借用数据竞争自由 | [coq_skeleton/BORROW_DATARACE_FREE.v](./coq_skeleton/BORROW_DATARACE_FREE.v) | T-BR1 | 定理陈述 + Admitted |
| Coq 类型安全 | [coq_skeleton/TYPE_SAFETY.v](./coq_skeleton/TYPE_SAFETY.v) | T-TY3 | 定理陈述 + Admitted |

---

## 二、定理陈述与 Coq 对应

### T-OW2 所有权唯一性

**文档陈述**：$\forall v, t: |\{x \mid \Omega_t(x)=\text{Owned} \land \Gamma_t(x)=v\}| \leq 1$

**Coq 骨架**：见 [OWNERSHIP_UNIQUENESS.v](./coq_skeleton/OWNERSHIP_UNIQUENESS.v)

### T-BR1 数据竞争自由

**文档陈述**：$\text{BorrowCheck}(P)=\text{OK} \rightarrow \text{DataRaceFree}(P)$

**Coq 骨架**：见 [BORROW_DATARACE_FREE.v](./coq_skeleton/BORROW_DATARACE_FREE.v)；`Parameter` 占位 `Program`、`BorrowCheck`、`DataRaceFree`；L-BR1/L-BR2 引理占位。

### T-TY3 类型安全

**文档陈述**：$\Gamma \vdash e : \tau \rightarrow \neg\exists e': e \to^* e' \land \text{type\_error}(e')$

**Coq 骨架**：见 [TYPE_SAFETY.v](./coq_skeleton/TYPE_SAFETY.v)；`Parameter` 占位 `Expr`、`has_type`、`step`、`type_error`；可参考 TAPL 形式化补全。

---

## 三、实施步骤

### 步骤 1：验证骨架可编译

```bash
cd docs/research_notes/coq_skeleton
coqc OWNERSHIP_UNIQUENESS.v
coqc BORROW_DATARACE_FREE.v
coqc TYPE_SAFETY.v
```

### 步骤 2：补全 T-OW2 证明

1. 定义 `reachable : State -> Prop`（从初始状态经规则 1–3 可达）
2. 将定理改为 `forall S, reachable S -> ownership_unique S`
3. 对 `reachable` 归纳；归纳基由规则 1；归纳步对移动/复制/drop 分类

### 步骤 3：补全 T-BR1、T-TY3 骨架

- **T-BR1**：将 `Parameter` 替换为具体定义；实现 L-BR1/L-BR2；见 [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md) §3
- **T-TY3**：定义 `Expr`、`has_type`、`step`、`type_error`；实现 L-TY1；见 §4

### 步骤 4：与 Aeneas/coq-of-rust 对接

完成 Coq 证明后，按 [AENEAS_INTEGRATION_PLAN](./AENEAS_INTEGRATION_PLAN.md)、[COQ_OF_RUST_INTEGRATION_PLAN](./COQ_OF_RUST_INTEGRATION_PLAN.md) 评估与工具链的衔接。

---

## 四、与 FORMAL_VERIFICATION_GUIDE 的衔接

本骨架对应 [FORMAL_VERIFICATION_GUIDE](./FORMAL_VERIFICATION_GUIDE.md) 六类验证中的**所有权模型验证**。补全证明后，可勾选该指南任务清单中的相应项。

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
