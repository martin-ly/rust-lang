# 06 - 生态系统与工具

> **Bloom 层级**: 理解
> **Rust 生态系统的核心工具、框架和新特性**
>
> **受众**: [专家] / [研究者]
> **内容分级**: [研究者级]

## 🎯 本模块学习目标
>
> **[来源: Rust Official Docs]**

完成本模块后，你将能够：

- [ ] 熟练使用 Cargo 管理复杂项目和工作空间
- [ ] 理解 Rust Edition 2024 的关键变更并迁移代码
- [ ] 使用 Tokio 构建高性能异步应用
- [ ] 了解 Rust 前沿不稳定特性和未来方向

## 📚 内容
>
> **[来源: Rust Official Docs]**

### 核心工具
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [cargo_basics.md](01_cargo_basics.md) | Cargo 基础与工作空间 | ⭐⭐ |
| [edition_2024.md](02_edition_2024.md) | Edition 2024 迁移指南 | ⭐⭐⭐ |
| [emerging/rust_1_95.md](./emerging/03_rust_1_95.md) | Rust 1.95 新特性 | ⭐⭐⭐ |
| [emerging/rust_1_96.md](./emerging/05_rust_1_96.md) | Rust 1.96 稳定特性 | ⭐⭐⭐ |

### 深度解析
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [deep_dives/tokio_deep_dive.md](./deep_dives/02_tokio_deep_dive.md) | Tokio 运行时深度解析 | ⭐⭐⭐⭐ |
| [deep_dives/axum_deep_dive.md](./deep_dives/01_axum_deep_dive.md) | Axum Web 框架深度解析 | ⭐⭐⭐⭐ |
| [databases/sqlx_deep_dive.md](./databases/02_sqlx_deep_dive.md) | SQLx 数据库访问 | ⭐⭐⭐ |
| [databases/sea_orm_deep_dive.md](./databases/01_sea_orm_deep_dive.md) | SeaORM ORM 框架 | ⭐⭐⭐ |
| [deployment/kubernetes_deployment_guide.md](./deployment/01_kubernetes_deployment_guide.md) | Kubernetes 部署指南 | ⭐⭐⭐⭐ |

### 前沿特性
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [emerging/generic_const_exprs.md](./emerging/02_generic_const_exprs.md) | 泛型常量表达式 | ⭐⭐⭐⭐ |
| [emerging/async_closures.md](./emerging/01_async_closures.md) | 异步闭包 | ⭐⭐⭐⭐ |
| [emerging/rust_1_95.md](./emerging/03_rust_1_95.md) | Rust 1.95 新特性 | ⭐⭐⭐ |

## ⏱️ 预计时间

- Cargo 基础: 2-3 小时
- Edition 2024: 1-2 小时
- Tokio 深度: 4-6 小时
- 其他 deep dives: 各 2-4 小时
- **总计**: 约 15-25 小时（按需选择）

## 🎓 前置要求

- [02_intermediate/](../02_intermediate/) 的 Trait、泛型、错误处理
- [03_advanced/](../03_advanced/) 的 async/await、线程、unsafe

## ✅ 完成检查清单

- [ ] 能独立创建和管理多 crate 工作空间
- [ ] 能评估项目是否适合迁移到 Edition 2024
- [ ] 能使用 Tokio 构建并发网络服务
- [ ] 了解至少一个前沿不稳定特性的使用限制

## 🚀 下一步

- 深入 [04_expert/](../04_expert/) 的专家级主题
- 查阅 [05_reference/](../05_reference/) 的速查资料
- 结合实际项目应用所学

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [Cargo 基础](01_cargo_basics.md)

---

## 相关概念

- [Rust for Linux (concept)](../../concept/07_future/19_rust_for_linux.md) — 操作系统内核中的内存安全
- [Cranelift 后端 (concept)](../../concept/07_future/16_cranelift_backend_preview.md) — 快速调试编译
- [并行前端 (concept)](../../concept/07_future/09_parallel_frontend_preview.md) — SALSA 3.0 与多核编译加速
