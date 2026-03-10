# coq-of-rust 对接调研与集成计划

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 调研 coq-of-rust（THIR → Rocq/Coq）的输入要求，给出「本项目文档 → 工具输入」的映射方案
> **参考**: [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)

---

## 一、coq-of-rust 概述

| 维度 | 说明 |
| :--- | :--- |
| **功能** | 从 Rust THIR（Typed HIR）生成 Rocq（Coq 方言）代码 |
| **输入** | Rust 源码 → 编译器 THIR |
| **输出** | Rocq 代码，含显式借用与 effect 序列 |
| **特点** | 编译器 IR 级；显式处理借用、effect |

---

## 二、本项目文档 → coq-of-rust 映射

### 2.1 输入要求

| coq-of-rust 需求 | 本项目对应 | 映射方式 |
| :--- | :--- | :--- |
| Rust 源码 | 各文档代码示例 | 从 ownership_model、borrow_checker_proof、practical_applications 提取 |
| THIR 可用 | 需 rustc 支持 | 使用与 coq-of-rust 兼容的 rustc 版本 |
| 借用显式化 | borrow 规则 5–8 | 生成代码将体现借用状态 |

### 2.2 验证目标对应

| 本项目定理 | coq-of-rust 生成代码中的对应 |
| :--- | :--- |
| borrow T1（数据竞争自由） | 借用 effect 序列无冲突 |
| borrow T2（规则正确性） | 生成 Rocq 类型反映借用规则 |
| lifetime LF-T2（引用有效性） | 生命周期在 Rocq 中显式 |

---

## 三、集成步骤

### 步骤 1：环境搭建（1–2 周）

| 任务 | 说明 |
| :--- | :--- |
| 安装 coq-of-rust | 按官方文档（通常需特定 rustc） |
| 安装 Rocq | Coq 的 Rust 语义扩展 |
| 运行示例 | 验证 THIR → Rocq 流程 |

### 步骤 2：示例程序选取（1 周）

| 任务 | 说明 |
| :--- | :--- |
| 选简单借用示例 | 如：`fn foo(x: &i32) -> i32 { *x }` |
| 选所有权转移示例 | 如：`fn take(v: Vec<i32>) { }` |
| 避免复杂 trait、泛型 | 优先 monomorphic 代码 |

### 步骤 3：生成与验证（2–4 周）

| 任务 | 说明 |
| :--- | :--- |
| 生成 Rocq 代码 | coq-of-rust 自动 |
| 分析生成结构 | 借用、effect 如何编码 |
| 编写 Coq 命题 | 对应本项目定理 |
| 尝试证明 | 若可行，标注 L3 |

### 步骤 4：文档化（持续）

| 任务 | 说明 |
| :--- | :--- |
| 更新 FORMAL_VERIFICATION_GUIDE | 增加 coq-of-rust 任务 |
| 更新 PROOF_INDEX | 标注 L3（若成功） |
| 与 Aeneas 对比 | 两工具适用场景 |

---

## 四、与 Aeneas 的对比

| 维度 | Aeneas | coq-of-rust |
| :--- | :--- | :--- |
| 输入级 | MIR/源码 | THIR |
| 借用处理 | 依赖后端 | 显式 effect 序列 |
| 多后端 | Coq/F*/HOL4/Lean | Rocq（Coq） |
| 适用场景 | 高层验证 | 借用/生命周期精确建模 |

---

## 五、成功标准

- [ ] 至少 1 个示例经 coq-of-rust 成功生成 Rocq
- [ ] 分析生成代码与 borrow_checker_proof 规则的对应关系
- [ ] 若可行，至少 1 个命题在 Rocq 中验证
- [ ] 映射文档更新至 FORMAL_VERIFICATION_GUIDE

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
