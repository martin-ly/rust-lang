# Aeneas 对接调研与集成计划

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **用途**: 调研 Aeneas（Safe Rust → Coq/F*/HOL4/Lean）的输入要求，给出「本项目文档 → 工具输入」的映射方案
> **参考**: [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../../research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)
> **状态**: 📋 规划中；步骤 1–4 可执行

---

## Aeneas 介绍

- **开发**: EPFL (École Polytechnique Fédérale de Lausanne)
- **网址**: <https://github.com/AeneasVerif/aeneas>
- **论文**: ICFP 2022 - "Aeneas: Rust Verification by Functional Translation"

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
| Rust 源码 | 无直接对应；需编写示例程序 | 从 [practical_applications](../../research_notes/practical_applications.md)、各文档代码示例提取 |
| Safe 子集 | [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) | 选无 unsafe 的示例 |
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

## Aeneas 理论基础

### Characteristic Prophecy Variables (CPV)

Aeneas使用**预言变量(Prophecy Variables)**来模拟Rust的可变引用(`&mut T`)。在函数式翻译中，可变引用难以直接表示，因为函数式语言通常不支持可变性。

**核心思想**:

- 预言变量用于**预测未来的值**(predict future values)
- 当创建可变借用 `&mut x` 时，引入一个预言变量 `π` 代表 `x` 在借用结束后的最终值
- 这允许在纯函数式设置中模拟可变的副作用

**形式化表示**:

```text
let r = &mut x;  // 创建预言变量 π，r 指向 (current, π)
*r = new_val;    // 更新当前值，π 保持不变
// 借用结束: x 的值变为 π
```

**与所有权模型的联系**:

- 预言变量保持了借用规则的形式化语义
- 与 [ownership_model](./formal_methods/ownership_model.md) 中的规则 6-8 兼容

### borrow_generated_from 关系

**borrow_generated_from** 是Aeneas中用于追踪借用来源的形式化关系。

**定义**:

- `borrow_generated_from(b, x)` 表示借用 `b` 是从变量 `x` 生成的
- 这是一个**形式化借用依赖**关系，用于验证借用的有效性

**性质**:

1. **传递性**: 若 `borrow_generated_from(b1, b2)` 且 `borrow_generated_from(b2, x)`，则 `borrow_generated_from(b1, x)`
2. **有效性**: `borrow_generated_from(b, x)` 蕴含 `x` 在借用创建点存活
3. **唯一性**: 每个借用有唯一的生成源

**形式化与本文档的对应**:

- 与 [borrow_checker_proof](./formal_methods/borrow_checker_proof.md) 中的 Def 1.3（借用有效性）对应
- 与 Axiom 3（借用有效性保持）兼容

### 函数式翻译

Aeneas的核心贡献是将Rust代码**翻译到纯函数式语言**：

**翻译过程**:

```text
Rust MIR/THIR → Aeneas IL → Coq/HOL4/Lean
```

**关键转换**:

| Rust 特性 | 函数式表示 | 说明 |
| :--- | :--- | :--- |
| `let x = v;` | `let x = v in ...` | 标准 let-binding |
| `let y = x;` (移动) | `let y = x in (x = ⊥; ...)` | 原变量标记为未定义 |
| `&mut x` | `(x, π)` 对 | 当前值 + 预言变量 |
| `*r = v` | 返回更新后的状态 | 函数式状态传递 |
| 函数调用 | 显式状态传递 | 输入状态 → 输出状态 |

**类型保持**:

- 翻译保持Rust的类型结构
- 所有权信息编码在类型中
- 借用规则通过类型系统强制执行

### 支持的验证后端

Aeneas支持多个定理证明器后端：

| 后端 | 特点 | 适用场景 |
| :--- | :--- | :--- |
| **Coq** | 成熟的生态系统，Iris框架 | 与RustBelt集成 |
| **HOL4** | 经典高阶逻辑 | 教育、研究 |
| **Lean** | 现代证明助手，元编程强 | 新兴项目 |
| **F\*** | 依赖类型，SMT自动化 | 自动化验证 |

**推荐选择**:

- 对于与 [RustBelt](./formal_methods/ownership_model.md#rustbelt) 对比研究：选择 **Coq**
- 对于自动化验证：选择 **F\***
- 对于现代证明开发：选择 **Lean**

### 与RustBelt的对比

| 特性 | RustBelt | Aeneas |
| :--- | :--- | :--- |
| **方法** | 分离逻辑 (Iris) | 函数式翻译 |
| **工具** | Coq (Iris) | Coq/HOL4/Lean/F\* |
| **范围** | Unsafe安全验证 | Safe Rust功能正确性 |
| **重点** | 内存安全 | 功能正确性 |
| **证明负担** | 较高（手动分离逻辑） | 较低（自动化翻译） |
| **处理借用** | 复杂分离逻辑推理 | 预言变量简化 |
| **处理Unsafe** | 支持 | 不支持（Safe Rust子集） |
| **适用场景** | 标准库验证 | 应用代码验证 |

**互补性**:

- RustBelt 验证 Unsafe 代码的**安全抽象**
- Aeneas 验证 Safe Rust 代码的**功能正确性**
- 两者结合覆盖 Rust 全生态

---

## 与项目文档的整合

### 形式化方法整合

#### 与 ownership_model.md 的整合

需要在 [ownership_model.md](./formal_methods/ownership_model.md) 中添加Aeneas引用：

1. **理论基础章节**: 添加"Aeneas 函数式翻译方法"
2. **所有权规则**: 对比 CPV 与所有权环境 Ω
3. **移动语义**: 与函数式状态传递对应
4. **参考文献**: 添加 ICFP 2022 论文

具体添加内容见 [ownership_model.md](./formal_methods/ownership_model.md) §Aeneas 函数式翻译方法。

#### 与 borrow_checker_proof.md 的整合

需要在 [borrow_checker_proof.md](./formal_methods/borrow_checker_proof.md) 中添加：

1. **对比分析**: Aeneas 借用处理 vs 传统借用检查
2. **borrow_generated_from**: 与 Def 1.3（借用有效性）的关系
3. **预言变量**: 与 Axiom 3（借用有效性保持）的对应
4. **数据竞争自由**: 两种方法的路径对比

具体添加内容见 [borrow_checker_proof.md](./formal_methods/borrow_checker_proof.md) §与Aeneas对比。

### 类型理论整合

**函数式翻译与类型保持**:

Aeneas的翻译保持类型结构，与 [type_system_foundations](./type_theory/type_system_foundations.md) 的形式化对应：

| 类型理论概念 | Rust 形式 | Aeneas 翻译 |
| :--- | :--- | :--- |
| 线性类型 | `String`, `Vec<T>` | 单射函数参数 |
| 仿射类型 | 大多数 Owned 类型 | 消耗性参数 |
| 相关类型 | `Copy` trait 类型 | 普通函数参数 |
| 引用类型 | `&T`, `&mut T` | 值对 + 预言变量 |
| 生命周期 | `'a` | 隐式在借用关系中 |

**整合建议**:

- 在 [type_system_foundations](./type_theory/type_system_foundations.md) 添加"函数式视角"小节
- 对比 Rust 类型系统与函数式翻译的对应
- 参考 Aeneas ICFP 2022 论文的类型系统章节

### 验证工具链整合

**与现有工具链的关系**:

```text
┌─────────────────────────────────────────────────────────────┐
│                    Rust 验证工具链                           │
├─────────────┬─────────────┬─────────────┬───────────────────┤
│   Miri      │   Kani      │  Prusti     │     Aeneas        │
│  (运行时)    │  (模型检查)  │ (演绎验证)   │  (函数式翻译)      │
├─────────────┼─────────────┼─────────────┼───────────────────┤
│ UB检测      │  属性验证   │  契约验证   │  定理证明器验证   │
│ 借用检查    │  内存安全   │  预/后置条件 │  功能正确性       │
├─────────────┴─────────────┴─────────────┴───────────────────┤
│ 与本文档整合:                                               │
│ • ownership_model.md: 所有权语义 → Miri/Kani/Prusti/Aeneas │
│ • borrow_checker_proof.md: 借用规则 → 所有工具             │
│ • type_system_foundations.md: 类型系统 → 所有工具          │
└─────────────────────────────────────────────────────────────┘
```

**推荐工作流**:

1. 使用 **Miri** 检测 UB 和借用违规
2. 使用 **Kani** 验证关键属性（如边界检查）
3. 使用 **Prusti** 验证函数契约
4. 使用 **Aeneas** 验证功能正确性（高保证需求）

---

## 六、与 Rust 1.93 的对应

- 本项目文档与 **Rust 1.93.0+ (Edition 2024)** 对齐；Aeneas 输入为 Rust 源码，工具链版本建议与 [00_ORGANIZATION § 六 权威来源与版本约定](./00_ORGANIZATION_AND_NAVIGATION.md#六权威来源与版本约定) 一致。
- 示例程序（如 `aeneas_first.rs`）应在 1.93 下编译通过；1.93 相关反例见 [RUST_193_COUNTEREXAMPLES_INDEX](./RUST_193_COUNTEREXAMPLES_INDEX.md)。

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
**状态**: 📋 规划中；步骤 1–4 可执行
