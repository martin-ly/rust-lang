# Databases 数据库

> **Bloom 层级**: 理解

> **Rust 数据库访问：ORM 与查询构建器**

## 📚 内容
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [sqlx_deep_dive.md](02_sqlx_deep_dive.md) | SQLx 编译时检查查询 | ⭐⭐⭐ |
| [sea_orm_deep_dive.md](01_sea_orm_deep_dive.md) | SeaORM 异步 ORM | ⭐⭐⭐ |

## 🎯 选型建议
>
> **[来源: Rust Official Docs]**

| 需求 | 推荐 |
|------|------|
| 编译时 SQL 验证 | SQLx |
| 全功能 ORM + 迁移 | SeaORM |
| 高性能 + 复杂查询 | SQLx + 手写 SQL |
| 快速 CRUD 开发 | SeaORM |

## 🚀 相关层
>
> **[来源: Rust Official Docs]**

- [03_advanced/async/async_await.md](../../03_advanced/async/01_async_await.md) - 异步基础
- [02_intermediate/error_handling.md](../../02_intermediate/02_error_handling.md) - 错误处理

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
