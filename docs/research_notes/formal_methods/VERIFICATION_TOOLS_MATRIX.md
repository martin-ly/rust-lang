# 验证工具矩阵

> **创建日期**: 2026-02-24
> **最后更新**: 2026-02-28
> **状态**: ✅ 已扩展
> **版本**: Rust 1.93.0+ (Edition 2024)

---

## 概述

验证工具矩阵全面梳理Rust生态中的形式化验证工具、静态分析工具和测试工具，为不同验证需求提供工具选型参考。

---

## 一、形式化验证工具

### 定理证明器

| 工具 | 类型 | 学习曲线 | 成熟度 | 适用场景 |
| :--- | :--- | :--- | :--- | :--- |
| **Coq** | 交互式证明 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 通用数学证明、程序验证 |
| **Isabelle/HOL** | 交互式证明 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 通用证明、教育系统 |
| **Lean 4** | 交互式证明 | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 数学、程序验证 |
| **Agda** | 依赖类型 | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | 类型论研究 |

### Rust专用验证工具

| 工具 | 技术 | 自动化 | 覆盖范围 | 状态 |
| :--- | :--- | :--- | :--- | :--- |
| **Aeneas** | 特征化翻译到Lean | 半自动 | Safe Rust子集 | 活跃开发 |
| **Creusot** | Why3中间层 | 半自动 | Safe Rust | 活跃 |
| **Kani** | 模型检测(CBMC) | 自动 | Unsafe Rust | 成熟 |
| **Prusti** | Viper框架 | 半自动 | Safe Rust+规范 | 研究 |
| **MIRAI** | 抽象解释 | 自动 | 数据分析 | 维护中 |
| **Crux** | Galois工具 | 半自动 | LLVM IR | 活跃 |
| **coq-of-rust** | Coq翻译 | 手动 | 教育 | 概念 |

---

## 二、静态分析工具

### 代码质量与lint

| 工具 | 类型 | 用途 | 集成 |
| :--- | :--- | :--- | :--- |
| **Clippy** | Lint | 代码风格、常见错误 | Cargo内置 |
| **Rustc warnings** | 编译器 | 基础检查 | 编译时 |
| **Miri** | 解释器 | UB检测、运行时检查 | 命令行 |
| **cargo-audit** | 安全 | 依赖漏洞扫描 | CI/CD |
| **cargo-deny** | 策略 | 许可/安全策略 | CI/CD |

### 高级静态分析

| 工具 | 技术 | 能力 | 性能 |
| :--- | :--- | :--- | :--- |
| **MIRAI** | 抽象解释 | 数值分析、不变式 | 中等 |
| **Lockbud** | 锁分析 | 死锁检测 | 快 |
| **Rudra** | 模式扫描 | Unsafe代码bug | 快 |
| **RAP** | 数据流 | 内存/并发bug | 中等 |

---

## 三、测试工具

### 单元与集成测试

| 工具 | 类型 | 特性 | 生态 |
| :--- | :--- | :--- | :--- |
| **cargo test** | 内置 | 标准测试框架 | ⭐⭐⭐⭐⭐ |
| **rstest** | 参数化 | 参数化测试 | ⭐⭐⭐⭐ |
| **mockall** | Mock | 模拟对象 | ⭐⭐⭐⭐ |
| **tokio-test** | 异步 | 异步测试工具 | ⭐⭐⭐⭐ |

### 模糊测试与属性测试

| 工具 | 类型 | 能力 | 使用场景 |
| :--- | :--- | :--- | :--- |
| **cargo-fuzz** | 覆盖引导 | 自动输入生成 | 解析器、协议 |
| **proptest** | 属性测试 | 失败最小化 | 函数正确性 |
| **quickcheck** | 属性测试 | 随机输入 | 代数性质 |
| **bolero** | 混合 | fuzz+属性 | 深度验证 |

### 性能测试

| 工具 | 类型 | 能力 |
| :--- | :--- | :--- |
| **criterion** | 微基准 | 统计显著性 |
| **iai** | 指令计数 | 稳定的性能指标 |
| **cargo-bench** | 内置 | 简单基准 |
| **flamegraph** | 分析 | 火焰图生成 |

---

## 四、工具选型决策树

```text
需要形式化验证?
│
├─ 是 → 有形式化背景?
│  ├─ 是 → 使用 Coq/Isabelle + Aeneas/Creusot
│  └─ 否 → 使用 Kani (自动化程度高)
│
└─ 否 → 需要检测未定义行为?
   ├─ 是 → 使用 Miri
   │
   └─ 否 → 代码质量检查?
      ├─ 是 → Clippy + Rustc warnings
      │
      └─ 安全审计?
         ├─ 是 → cargo-audit + cargo-deny
         └─ 否 → 基础测试足够
```

---

## 五、工具详细对比

### Kani vs MIRAI vs Prusti

| 维度 | Kani | MIRAI | Prusti |
| :--- | :--- | :--- | :--- |
| 验证方式 | 模型检测 | 抽象解释 | 演绎验证 |
| 自动化 | 高 | 高 | 中 |
| 需规范 | 否(断言) | 否 | 是(契约) |
| Unsafe支持 | 是 | 是 | 否 |
| 学习曲线 | 低 | 中 | 高 |
| 适用场景 | 快速检查 | 数据分析 | 精确验证 |

### Coq vs Lean vs Isabelle

| 维度 | Coq | Lean 4 | Isabelle |
| :--- | :--- | :--- | :--- |
| 语法 | 复杂 | 现代 | 简洁 |
| 生态 | 丰富 | 增长中 | 丰富 |
| Rust支持 | coq-of-rust | Aeneas | 无直接 |
| 教育材料 | 多 | 增长中 | 多 |
| IDE支持 | CoqIDE, VSC | Lean 4 IDE | Isabelle/jEdit |

---

## 六、与形式化方法层次的对应

| 层次 | 工具 | 输出 |
| :--- | :--- | :--- |
| L1 概念理解 | Clippy, Miri | 代码质量/UB检测 |
| L2 完整证明 | Coq骨架 | 手写证明 |
| L3 机器检查 | Coq Qed, Kani | 验证证书 |
| L4 自动验证 | Creusot, Prusti | 条件证明 |

---

## 七、验证工具链集成

### CI/CD 集成示例

```yaml
# .github/workflows/verify.yml
name: Verification

jobs:
  static-analysis:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Clippy
        run: cargo clippy --all-targets -- -D warnings
      - name: Audit
        run: cargo audit

  testing:
    runs-on: ubuntu-latest
    steps:
      - name: Unit Tests
        run: cargo test
      - name: Miri
        run: cargo +nightly miri test

  formal-verification:
    runs-on: ubuntu-latest
    steps:
      - name: Kani
        run: cargo kani
```

---

## 八、国际项目对比

| 项目 | 工具 | 规模 | 成果 |
| :--- | :--- | :--- | :--- |
| RustBelt | Coq/Iris | 大型 | Rust核心语义 |
| rustc_formal | Coq | 中型 | 类型系统 |
| Verus | Z3 | 大型 | 系统代码验证 |
| CRustS | Coq | 小型 | C-Rust转换 |

---

## 九、选择建议

### 按场景推荐

| 场景 | 推荐工具 | 理由 |
| :--- | :--- | :--- |
| 快速UB检测 | Miri | 易于使用，检测全面 |
| 安全关键代码 | Kani + Creusot | 自动化+精确性 |
| 教学/研究 | Coq + Aeneas | 灵活性强 |
| 生产代码质量 | Clippy + MIRAI | 集成简单 |
| 密码学代码 | Kani | bit精确验证 |

---

## 十、扩展阅读

- [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)
- [coq_skeleton](../coq_skeleton/) - Coq证明骨架
- [L3_MACHINE_PROOF_GUIDE](../L3_MACHINE_PROOF_GUIDE.md)

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-28
**状态**: ✅ 已扩展 - 验证工具矩阵完整版
