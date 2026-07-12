> **EN**: Production-Grade Macro Development
> **Summary**: Engineering practices for shipping Rust macro crates: MSRV and edition compatibility, span-aware diagnostics, documentation and doc tests, semantic versioning, changelog management, CI/CD, security auditing, and long-term maintenance.
>
> **权威来源**: [concept/03_advanced/03_proc_macros/05_production_grade_macro_development.md](../../../../concept/03_advanced/03_proc_macros/05_production_grade_macro_development.md)

# 05 生产级宏开发

> 本文档已由 `crates/*/docs/` 合规整改迁移。原始详细内容现已纳入 `concept/` 权威页；本页仅保留主题索引与入口链接。

---

## 主题索引

- 版本兼容性
  - MSRV 管理
  - Edition 兼容
  - 依赖版本策略
  - 弃用和迁移
- 错误诊断最佳实践
  - Span 感知错误
  - 帮助消息
  - 多错误聚合
  - 友好错误文案
- 文档生成
  - 宏文档最佳实践
  - 示例代码
  - 隐藏实现细节
  - Doc Tests
- 发布策略
  - 语义化版本
  - Changelog 管理
  - Breaking Changes 处理
  - CI/CD 集成
- 维护策略
  - 问题追踪
  - 安全更新
  - 社区支持
  - 长期维护
- 实战案例
  - Serde 的版本策略
  - Tokio 宏的错误诊断

---

> **权威来源**: [concept/03_advanced/03_proc_macros/05_production_grade_macro_development.md](../../../../concept/03_advanced/03_proc_macros/05_production_grade_macro_development.md)
