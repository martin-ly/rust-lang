> **EN**: Advanced Macro Debugging
> **Summary**: Advanced debugging techniques for Rust macros: cargo expand, compiler plugin development, macro expansion tracing, breakpoint debugging, performance profiling, and improving diagnostic messages with Span management.
>
> **权威来源**: [concept/03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md](../../../../concept/03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md)

# 04 宏调试深化

> 本文档已由 `crates/*/docs/` 合规整改迁移。原始详细内容现已纳入 `concept/` 权威页；本页仅保留主题索引与入口链接。

---

## 主题索引

- 高级 cargo expand 用法
  - 基础展开与格式化
  - 按测试、示例、feature 过滤
  - 差异比较与自动化脚本
  - CI 集成与 pre-commit hook
- 编译器插件开发
  - rustc 驱动器
  - 自定义 Lint
  - 编译器回调
- 宏展开追踪
  - 日志追踪
  - 断点调试（lldb/gdb / VS Code）
  - 可视化工具
- 性能分析
  - 编译时性能
  - 宏展开开销
  - 火焰图与 perf
- 错误诊断
  - 错误消息改进
  - Span 管理
  - `proc-macro-error`
- 实战案例
  - 调试复杂宏展开
  - 性能瓶颈定位

---

> **权威来源**: [concept/03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md](../../../../concept/03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md)
