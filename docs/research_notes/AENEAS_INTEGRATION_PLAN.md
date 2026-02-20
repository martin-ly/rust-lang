# Aeneas 对接调研与集成计划

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 调研 Aeneas（Safe Rust → Coq/F*/HOL4/Lean）的输入要求，给出「本项目文档 → 工具输入」的映射方案
> **参考**: [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)
> **状态**: 📋 规划中；步骤 1–4 可执行

---

## 一、Aeneas 概述

| 维度 | 说明 |
| :--- | :--- |
| **功能** | 将 Safe Rust 程序翻译到证明助手（Coq、F*、HOL4、Lean） |
| **输入** | Rust 源码（MIR/THIR 级） |
| **输出** | 证明助手可验证的代码 |
| **形式化范围** | Safe Rust 子集 |

---

## 二、本项目文档 → Aeneas 映射

### 2.1 输入要求

| Aeneas 需求 | 本项目对应 | 映射方式 |
| :--- | :--- | :--- |
| Rust 源码 | 无直接对应；需编写示例程序 | 从 [practical_applications](./practical_applications.md)、各文档代码示例提取 |
| Safe 子集 | [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](./SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) | 选无 unsafe 的示例 |
| 类型注解 | type_system、trait 形式化 | 确保示例满足本项目定理（如 ownership T2、borrow T1） |

### 2.2 验证目标对应

| 本项目定理 | Aeneas 验证目标 |
| :--- | :--- |
| ownership T2（唯一性） | 证明无双重所有者 |
| ownership T3（内存安全） | 证明无悬垂、无双重释放 |
| borrow T1（数据竞争自由） | 证明借用规则满足 |
| type T3（类型安全） | 类型保持 |

---

## 三、集成步骤

### 步骤 1：环境搭建（1–2 周）

| 任务 | 说明 |
| :--- | :--- |
| 安装 Aeneas | 按官方文档 |
| 选择后端 | Coq / F* / HOL4 / Lean 之一 |
| 运行示例 | 验证工具链可用 |

### 步骤 2：示例程序选取（1 周）

| 任务 | 说明 |
| :--- | :--- |
| 从 practical_applications 选 2–3 个 Safe 案例 | 满足 ownership、borrow 定理 |
| 从 ownership_model、borrow_checker_proof 代码示例选 3–5 个 | 简单所有权转移、借用 |
| 编写最小可验证程序 | 如：Box 创建、移动、drop |

**首个示例规格（Aeneas 优先）**：[c01/examples/aeneas_first.rs](../../crates/c01_ownership_borrow_scope/examples/aeneas_first.rs)

```rust
fn main() {
    let x = String::from("hello");
    let y = x;  // 移动；x 不再可用
    let _ = y.len();
}
```

对应定理：T-OW2（所有权唯一性）；验证目标：移动后无双重所有者。

### 步骤 3：翻译与验证（2–4 周）

| 任务 | 说明 |
| :--- | :--- |
| 将示例翻译到证明助手 | Aeneas 自动 |
| 编写/补全证明 | 对应本项目定理 |
| 记录映射 | 本项目 Def/定理 ↔ 证明助手命题 |

### 步骤 4：文档化（持续）

| 任务 | 说明 |
| :--- | :--- |
| 更新 FORMAL_VERIFICATION_GUIDE | 增加 Aeneas 任务 |
| 更新 PROOF_INDEX | 标注 L3（若成功） |
| 更新 INTERNATIONAL_FORMAL_VERIFICATION_INDEX | 对接状态 |

---

## 四、风险与限制

| 风险 | 缓解 |
| :--- | :--- |
| Aeneas 支持 Rust 子集有限 | 选最简示例；查阅 Aeneas 支持列表 |
| 证明助手学习曲线 | 优先 Coq（Iris/RustBelt 生态） |
| 工具链不稳定 | 记录版本、环境 |

---

## 五、成功标准

- [ ] 至少 1 个示例程序经 Aeneas 翻译并验证通过
- [ ] 本项目至少 1 个定理（如 ownership T2）在证明助手中对应命题成立
- [x] 映射文档更新至 FORMAL_VERIFICATION_GUIDE（✅ 已添加入口与工具链扩展任务）

---

## 六、与 Rust 1.93 的对应

- 本项目文档与 **Rust 1.93.0+ (Edition 2024)** 对齐；Aeneas 输入为 Rust 源码，工具链版本建议与 [00_ORGANIZATION § 六 权威来源与版本约定](./00_ORGANIZATION_AND_NAVIGATION.md#六权威来源与版本约定) 一致。
- 示例程序（如 `aeneas_first.rs`）应在 1.93 下编译通过；1.93 相关反例见 [RUST_193_COUNTEREXAMPLES_INDEX](./RUST_193_COUNTEREXAMPLES_INDEX.md)。

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
**状态**: 📋 规划中；步骤 1–4 可执行
