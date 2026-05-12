# Formal Methods Industrialization（形式化方法工业化）

> **层级**: L7 前沿趋势
> **前置概念**: [RustBelt](../04_formal/04_rustbelt.md) · [Ownership Formalization](../04_formal/03_ownership_formal.md) · [Concurrency](../03_advanced/01_concurrency.md)
> **主要来源**: [AWS Kani] · [Microsoft Verus] · [TLA+] · [P Language] · [POPL/PLDI 2024-2026]

---

**变更日志**:

- v1.0 (2026-05-12): 初始版本

---

## 一、权威定义

### 1.1 Wikipedia 权威定义

> **[Wikipedia: Formal verification]** Formal verification is the act of proving or disproving the correctness of intended algorithms underlying a system with respect to a certain formal specification or property, using formal methods of mathematics.

> **[Wikipedia: Model checking]** Model checking is a method for checking whether a finite-state model of a system meets a given specification. It uses exhaustive enumeration of states to determine if the specification holds.

> **[Wikipedia: Theorem proving]** Automated theorem proving is a subfield of automated reasoning and mathematical logic dealing with proving mathematical theorems by computer programs.

### 1.2 五层扩展模型

```text
L0: Rust 编译器     → 所有权/生命周期/并发  ✅ 原生完成
L1: Code-Level      → 功能正确性            🚧 Creusot/Verus/Kani
L2: Interface-Level → 契约/版本代数          🚧 Filament/Schema Lattice
L3: Protocol-Level  → 状态机/一致性          🚧 TLA+/P
L4: System-Level    → 故障模型/容错          🚧 CALM/FizzBee
L5: Runtime-Level   → 轨迹比对/持续验证       🚧 PObserve/MongoDB Trace
```

---

## 二、工业实践矩阵

| **层级** | **工具/标准** | **工业用户** | **成熟度** |
|:---|:---|:---|:---|
| L1 | Kani | AWS | ✅ 生产级 |
| L1 | Verus | Microsoft | 🚧 内部推广 |
| L3 | TLA+ | AWS, MongoDB, Kafka | ✅ 工业标准 |
| L3 | P + PObserve | AWS | 🚧 运行时验证 |
| L5 | Schema Registry + Buf | 多家企业 | ✅ CI 集成 |

---

## 三、持续验证趋势

```text
设计时验证 ──→ 测试时验证 ──→ 生产时监控
   (TLA+)        (Trace-Check)      (PObserve)
```

---

## 四、与 L4 形式化层的衔接

| 工业工具 | 理论基础 | 对应 L4 文件 | 成熟度 |
|:---|:---|:---|:---|
| Kani | 模型检测 + 符号执行 | `04_formal/04_rustbelt.md` (扩展) | 生产可用 |
| Creusot | Why3 / MLCFG | `04_formal/04_rustbelt.md` | 研究→工业 |
| Verus | SMT + 所有权逻辑 | `04_formal/03_ownership_formal.md` | 研究→工业 |
| Miri | Stacked/Tree Borrows | `04_formal/03_ownership_formal.md` | 生产可用 |
| TLA+ | 时序逻辑 | —（系统级） | 成熟 |

## 五、知识来源

| **论断** | **来源** | **可信度** |
|:---|:---|:---|
| AWS 使用 Kani 验证 Rust | [AWS Blog] | ✅ |
| TLA+ 用于 S3/DynamoDB | [AWS CACM 2015] | ✅ |
| PObserve 运行时对齐 | [AWS P Language] | ✅ |

## 三、扩展内容：验证工具详细对比与工业案例

### 3.1 验证工具能力矩阵

| 工具 | 验证类型 | 自动化程度 | 覆盖范围 | 成熟度 | 工业应用 |
|:---|:---|:---|:---|:---|:---|
| **Kani** | 模型检测 | 高（全自动） | unsafe、并发 | ⭐⭐⭐⭐ | AWS 生产 |
| **Creusot** | 演绎验证 | 中（需规格） | safe 代码 | ⭐⭐⭐ | 研究→工业 |
| **Verus** | SMT 验证 | 中（需规格） | 系统软件 | ⭐⭐⭐ | Microsoft |
| **Aeneas** | 函数式翻译 | 中（需证明） | safe 核心 | ⭐⭐ | 研究 |
| **Prusti** | 分离逻辑 | 中（需规格） | safe 代码 | ⭐⭐ | 研究 |
| **RefinedRust** | 自动化分离逻辑 | 高（类型驱动） | safe 代码 | ⭐⭐ | PLDI 2024 |
| **Miri** | 动态检测 | 高（运行时） | UB 检测 | ⭐⭐⭐⭐ | 社区标准 |

### 3.2 CI/CD 集成方案

```yaml
# .github/workflows/verify.yml
name: Formal Verification
on: [push, pull_request]
jobs:
  kani:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: model-checking/kani-github-action@v1
        with:
          args: "--tests"
  creusot:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - run: cargo creusot --span-mode=absolute
```

### 3.3 工业案例

| 公司 | 项目 | 工具 | 成果 |
|:---|:---|:---|:---|
| **AWS** | Firecracker / Bottlerocket | Kani | 关键模块模型检测 |
| **Microsoft** | Windows Rust 组件 | Verus | 系统代码验证 |
| **MongoDB** | 存储引擎 | TLA+ | 分布式一致性 |
| **Linux Foundation** | Rust for Linux | Miri + 手动审计 | 内核代码安全 |
| **Google** | Android Rust | 多种工具 | 内存安全迁移 |

---

## 六、相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| RustBelt | [`../04_formal/04_rustbelt.md`](../04_formal/04_rustbelt.md) | 理论基础 |
| 所有权形式化 | [`../04_formal/03_ownership_formal.md`](../04_formal/03_ownership_formal.md) | 验证对象 |
| Unsafe | [`../03_advanced/03_unsafe.md`](../03_advanced/03_unsafe.md) | 验证边界 |
| 工具链 | [`../06_ecosystem/01_toolchain.md`](../06_ecosystem/01_toolchain.md) | CI 集成 |
| AI × Rust | [`./01_ai_integration.md`](./01_ai_integration.md) | 协同趋势 |
| 语言演进 | [`./03_evolution.md`](./03_evolution.md) | 验证需求驱动 |
| 安全边界 | [`../05_comparative/safety_boundaries.md`](../05_comparative/safety_boundaries.md) | 验证目标 |

## 五、待补充

- [ ] **TODO**: 补充具体 TLA+ 规约示例
- [ ] **TODO**: 补充 CI/CD 集成方案
