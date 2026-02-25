# 链接修复计划 2026-02-12

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已归档
---

## 1. docs/UNSAFE_RUST_GUIDE.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |

---

## 2. crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 98 | `tier3_advanced/3.2_零成本抽象.md` | `tier_03_references/07_零成本抽象参考.md` |
| 99 | `tier3_advanced/3.4_性能优化.md` | `tier_03_references/09_性能优化参考.md` |
| 119 | `tier3_advanced/README.md` | `tier_03_references/README.md` 或 `tier_04_advanced/README.md` |
| 485 | `tier3_advanced/3.2_零成本抽象.md` | `tier_03_references/07_零成本抽象参考.md` |
| 505 | `tier3_advanced/3.3_内存安全最佳实践.md` | `tier_03_references/08_内存安全参考.md` |

---

## 3. docs/WASM_USAGE_GUIDE.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 324 | `03_javascript_互操作.md` | 正确，无需修改 |

---

## 4. docs/THREADS_CONCURRENCY_USAGE_GUIDE.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 398 | `02_并发控制指南.md` | `02_同步原语实践.md` |
| 399 | `03_无锁数据结构参考.md` | `tier_03_references/02_无锁编程参考.md` |

---

## 5. docs/MACRO_SYSTEM_USAGE_GUIDE.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 306 | `02_过程宏指南.md` | `02_Derive宏开发指南.md`（或 03_属性宏、04_函数宏）

---

## 6. docs/DESIGN_PATTERNS_USAGE_GUIDE.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 355 | `02_Rust特有模式.md` | `05_最佳实践与反模式.md` |

---

## 7. docs/quick_reference/ownership_cheatsheet.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |

---

## 8. docs/quick_reference/type_system.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |

---

## 9. docs/quick_reference/network_programming_cheatsheet.md

| 行 | 原内容 | 修正为 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 360 | `02_TCP_UDP指南.md` | `04_TCP_UDP编程.md` |
| 361 | `03_WebSocket指南.md` | `03_WebSocket实时通信.md` |

---

## 10. 其他需核对的引用

- `docs/STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md` 中的 `./docs/` 路径（可能为 `./` 取决于文档位置）
- `docs/RUST_RELEASE_TRACKING_CHECKLIST.md` 中 `08_rust_version_evolution_1.89_to_1.93.md` 应为 `08_rust_version_evolution_1.89_to_1.93.md`（文件名为 `08_rust_version_evolution_1.89_to_1.93.md`，需确认）

---

## 执行检查

修复完成后执行：

```bash
# 若已安装 cargo-deadlinks
cargo deadlinks

# 或使用 markdown-link-check 等工具
find . -name "*.md" -exec markdown-link-check {} \;
```

---

**创建日期**: 2026-02-12
**关联**: [PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md](./PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md)