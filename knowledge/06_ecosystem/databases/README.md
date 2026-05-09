# Databases 数据库

> **Rust 数据库访问：ORM 与查询构建器**

## 📚 内容

| 文档 | 主题 | 难度 |
|------|------|------|
| [sqlx_deep_dive.md](sqlx_deep_dive.md) | SQLx 编译时检查查询 | ⭐⭐⭐ |
| [sea_orm_deep_dive.md](sea_orm_deep_dive.md) | SeaORM 异步 ORM | ⭐⭐⭐ |

## 🎯 选型建议

| 需求 | 推荐 |
|------|------|
| 编译时 SQL 验证 | SQLx |
| 全功能 ORM + 迁移 | SeaORM |
| 高性能 + 复杂查询 | SQLx + 手写 SQL |
| 快速 CRUD 开发 | SeaORM |

## 🚀 相关层

- [03_advanced/async/async_await.md](../../03_advanced/async/async_await.md) - 异步基础
- [02_intermediate/error_handling.md](../../02_intermediate/error_handling.md) - 错误处理

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09
