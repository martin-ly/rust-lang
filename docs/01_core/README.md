> **权威来源**: 本文件为 `docs/` 核心概念学习索引，通用 Rust 概念解释统一维护在 `concept/` 权威页。
> 根据 AGENTS.md §3.4，`docs/` 仅保留学习路径、导航与速查，不重复概念定义。
>
> **核心权威页**:
> - [所有权](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md)
> - [借用](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)
> - [生命周期](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md)
> - [类型系统](../../concept/01_foundation/02_type_system/01_type_system.md)
> - [错误处理](../../concept/01_foundation/08_error_handling/01_error_handling_basics.md)
> - [并发基础](../../concept/03_advanced/00_concurrency/01_concurrency.md)
> - [异步基础](../../concept/03_advanced/01_async/01_async.md)
> - [Unsafe Rust](../../concept/03_advanced/02_unsafe/01_unsafe.md)

# Rust 核心概念 (Core Concepts) {#rust-核心概念-core-concepts}

> **EN**: Core Concepts
> **Summary**: `docs/` 核心概念学习索引，链接到 `concept/` 权威页、练习与示例。
> **Bloom 层级**: L1-L2
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **难度**: 初级 → 中级
> **预计学习时间**: 4-6 小时

---

## 概念索引 {#概念索引}

| 主题 | 权威页 | 练习 / 示例 |
|:---|:---|:---|
| 所有权 | [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | [`crates/c01_ownership_borrow_scope/`](../../crates/c01_ownership_borrow_scope/) |
| 借用 | [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | [`exercises/rustlings_style/`](../../exercises/rustlings_style/) |
| 生命周期 | [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | [`crates/c01_ownership_borrow_scope/`](../../crates/c01_ownership_borrow_scope/) |
| 类型系统 | [`concept/01_foundation/02_type_system/01_type_system.md`](../../concept/01_foundation/02_type_system/01_type_system.md) | [`crates/c02_type_system/`](../../crates/c02_type_system/) |
| 错误处理 | [`concept/01_foundation/08_error_handling/01_error_handling.md`](../../concept/01_foundation/08_error_handling/01_error_handling_basics.md) | [`crates/c03_control_fn/`](../../crates/c03_control_fn/) |
| 泛型与 Trait | [`concept/02_intermediate/01_generics/01_generics.md`](../../concept/02_intermediate/01_generics/01_generics.md) · [`concept/02_intermediate/00_traits/01_traits.md`](../../concept/02_intermediate/00_traits/01_traits.md) | [`crates/c04_generic/`](../../crates/c04_generic/) |
| 并发 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../concept/03_advanced/00_concurrency/01_concurrency.md) | [`crates/c05_threads/`](../../crates/c05_threads/) |
| 异步 | [`concept/03_advanced/01_async/01_async.md`](../../concept/03_advanced/01_async/01_async.md) | [`crates/c06_async/`](../../crates/c06_async/) |
| Unsafe | [`concept/03_advanced/02_unsafe/01_unsafe.md`](../../concept/03_advanced/02_unsafe/01_unsafe.md) | [`crates/c13_embedded/`](../../crates/c13_embedded/) |

## 学习路径 {#学习路径}

```text
初学者
├── 1. 所有权三规则
├── 2. 移动 vs 复制
├── 3. 不可变引用 &T
├── 4. 可变引用 &mut T
├── 5. 借用规则（编译器错误理解）
└── 6. 基础生命周期概念

进阶
├── 7. 生命周期标注语法
├── 8. 生命周期省略规则
├── 9. 结构体中的引用生命周期
├── 10. trait 对象与生命周期
└── 11. 'static 的准确含义

高级
├── 12. 自引用结构体与 Pin
├── 13. 协变/逆变/不变 (Variance)
├── 14. Higher-Ranked Trait Bounds (for<'a>)
└── 15. 形式化语义理解 (Stacked Borrows / Tree Borrows)
```

## 相关资源 {#相关资源}

- [所有权、借用与生命周期：学习路径与易错点索引](01_ownership_borrowing_lifetimes.md) — `docs/` 学习路径入口
- [MVP 学习路径](../../concept/00_meta/04_navigation/08_learning_mvp_path.md) — 35-45 小时系统学习
- [Rust 官方文档](https://doc.rust-lang.org/book/)
- [Rust Reference](https://doc.rust-lang.org/reference/)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)

---

> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Reference](https://doc.rust-lang.org/reference/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **权威来源对齐变更日志**: 2026-05-19 新增 TRPL、Rust Reference、Rustonomicon 来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 2.0
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-14
**状态**: ✅ 已按 AGENTS.md §3.4 去重，改为 `docs/` 索引
