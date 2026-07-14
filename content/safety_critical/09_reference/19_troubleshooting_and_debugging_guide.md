# Rust安全关键系统故障排除与调试

**EN**: Troubleshooting And Debugging Guide
**Summary**: Rust安全关键系统故障排除与调试入口；通用 Rust 编译器错误、生命周期与泛型问题排错请见 `concept/` 权威页。

> **权威来源**: 本文件为安全关键领域专题入口；通用 Rust 概念解释请见：
> - [所有权系统](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md)
> - [借用与生命周期](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)、[生命周期深入](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md)
> - [错误处理基础](../../concept/01_foundation/08_error_handling/01_error_handling_basics.md)
> - [泛型](../../concept/02_intermediate/01_generics/01_generics.md)
> - [Trait](../../concept/02_intermediate/00_traits/01_traits.md)
> - [Unsafe Rust](../../concept/03_advanced/02_unsafe/01_unsafe.md)
> - [异步 Rust](../../concept/03_advanced/01_async/01_async.md)
> - [FFI](../../concept/03_advanced/04_ffi/01_rust_ffi.md)
>
> 若 `concept/` 已覆盖相同主题，本文仅保留安全关键系统场景下的调试要点与决策树，不重复通用概念推导。

> **Bloom 层级**: L4-L6
>
> 本文内容迁移自历史归档，已按 `AGENTS.md` 规则保留为安全关键领域专题实践。

---

## 安全关键系统调试要点

在安全关键系统中，调试不仅是定位错误，更是确保**可审计性、确定性与可追溯性**：

- **优先使用 Miri**：对任何 `unsafe` 边界或 FFI 交互，先用 `cargo miri test` 检测未定义行为。
- **冻结工具链**：记录并锁定 `rust-toolchain.toml`，确保调试结果可复现。
- **保留证据**：将缺陷、根因分析与修复措施写入安全案例（Safety Case）与变更记录。
- ** worst-case 思维**：在实时/嵌入式场景中，结合 WCET 分析与硬件调试器（probe-rs、OpenOCD）验证。

---

## 快速决策树

```
遇到编译错误？
├── 借用/生命周期错误 (E0499, E0597, E0507...)
│   └── 参考 concept/01_foundation/01_ownership_borrow_lifetime/
├── 泛型/trait 约束错误 (E0277, E0599, E0283...)
│   └── 参考 concept/02_intermediate/01_generics/ 与 concept/02_intermediate/00_traits/
├── 错误处理与 ? 操作符问题
│   └── 参考 concept/01_foundation/08_error_handling/
├── unsafe / FFI 段错误/UB
│   └── 先跑 cargo miri test，再审查 SAFETY 注释
├── 异步运行时问题
│   └── 参考 concept/03_advanced/01_async/
└── 性能/确定性问题
    └── 参考 [性能优化指南](10_performance_optimization_guide.md) 与 concept/06_ecosystem/10_performance/
```

---

## 常用工具速查

| 场景 | 命令/工具 | 说明 |
|------|-----------|------|
| 未定义行为检测 | `cargo miri test` | 对 `unsafe` 与原始指针交互尤其重要 |
| 属性验证 | `cargo kani` | 关键函数形式化验证 |
| 覆盖率 | `cargo llvm-cov` | ASIL D 通常要求 MC/DC |
| 依赖审计 | `cargo audit` / `cargo deny` | 安全关键项目必须定期执行 |
| 嵌入式调试 | `probe-rs debug` / `cargo embed` | 硬件级调试 |

---

**文档版本**: 2.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-15
**状态**: ✅ 已按 AGENTS.md §2 规范化为专题入口 stub；通用排错内容已链接至 `concept/` 权威页

---

- [Parent README](../README.md)

---

## 相关概念

- [性能优化指南](10_performance_optimization_guide.md)
- [FFI 集成指南](07_ffi_integration_guide.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Rust Reference](https://doc.rust-lang.org/reference/)**
> **[来源: The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **[来源: Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
