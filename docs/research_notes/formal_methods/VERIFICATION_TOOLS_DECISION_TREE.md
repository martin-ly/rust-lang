# 验证工具选型决策树

> **创建日期**: 2026-02-24
> **状态**: ✅ 新建 (9/10决策树)
> **任务ID**: P1-W8-T6

---

## 决策树

```text
需要形式化验证？
│
├── 验证目标？
│   ├── 内存安全
│   │   ├── 纯Safe Rust → Miri (已内置)
│   │   ├── 包含unsafe
│   │   │   ├── 小规模 → Kani (模型检测)
│   │   │   └── 大规模 → RustBelt (分离逻辑)
│   │   └── 并发安全
│   │       ├── 数据竞争 → ThreadSanitizer
│   │       └── 死锁检测 → 自定义分析
│   │
│   ├── 功能正确性
│   │   ├── 有规格注释 → Prusti (SMT)
│   │   ├── 无注释 → Creusot (Why3)
│   │   └── 复杂不变式 → Verus (SMT+线性)
│   │
│   └── 特定属性
│       ├── 不溢出 → Kani (内置检查)
│       ├── 终止性 → 自定义证明
│       └── 实时性 → Tock OS工具
│
├── 验证阶段？
│   ├── 开发期 → 快速反馈工具
│   │   ├── Miri (解释器)
│   │   ├── Clippy (静态分析)
│   │   └── Kani (针对属性)
│   │
│   ├── CI/CD → 自动化验证
│   │   ├── cargo-kani
│   │   ├── cargo-creusot
│   │   └── 自定义脚本
│   │
│   └── 发布前 → 深度验证
│       ├── 完整Kani证明
│       ├── Coq机器证明
│       └── 第三方审计
│
├── 团队能力？
│   ├── 形式化专家 → Coq/Iris
│   ├── 有验证经验 → Prusti/Creusot
│   └── 新手 → Kani/Miri
│
└── 预算与时间？
    ├── 充足 → RustBelt + Coq
    ├── 中等 → Prusti/Creusot
    └── 有限 → Kani/Miri
```

---

## 工具对比矩阵

| 工具 | 方法 | 内存安全 | 功能正确 | 并发 | unsafe | 学习曲线 | 成熟度 | 适用场景 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Miri** | 解释器 | ✅ | ⚠️ | ⚠️ | ✅ | 低 | 高 | 开发期检查 |
| **Kani** | 模型检测 | ✅ | ✅ | ⚠️ | ✅ | 低 | 中 | 属性验证 |
| **Prusti** | SMT | ✅ | ✅ | ⚠️ | ❌ | 中 | 中 | 合同验证 |
| **Creusot** | Why3 | ✅ | ✅ | ⚠️ | ❌ | 中 | 中 | 功能证明 |
| **Verus** | SMT+线性 | ✅ | ✅ | ⚠️ | ⚠️ | 中 | 新 | 系统代码 |
| **RustBelt** | 分离逻辑 | ✅ | ⚠️ | ✅ | ✅ | 高 | 研究 | 核心库验证 |
| **Aeneas** | 翻译验证 | ✅ | ✅ | 🔄 | 🔄 | 中 | 新 | 自动化证明 |

---

## 推荐配置

### 开发期

```bash
# Miri - 检测未定义行为
cargo +nightly miri test

# Clippy - 静态分析
cargo clippy -- -D warnings

# Kani - 针对特定属性
cargo kani --harness my_function
```

### CI/CD

```yaml
# GitHub Actions示例
- name: Run Kani
  uses: model-checking/kani-github-action
  with:
    args: "--harness verify_*"
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 验证工具选型决策树 (9/10)

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
