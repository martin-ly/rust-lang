> **EN**: Procedural Macro Code Generation Optimization
> **Summary**: Optimizing the output of procedural and declarative macros in Rust: readable token generation, compile-time overhead reduction, monomorphization bloat control, const folding, dead-code elimination, loop unrolling, SIMD hints, and measurement tooling.
>
> **权威来源**: [concept/03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md](../../../../concept/03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md)

# 03 代码生成优化

> 本文档已由 `crates/*/docs/` 合规整改迁移。原始详细内容现已纳入 `concept/` 权威页；本页仅保留主题索引与入口链接。

---

## 主题索引

- 生成代码质量（可读性、文档、可调试性、Clippy 规范）
- 编译时间优化
  - 避免宏递归爆炸
  - 减少单态化开销
  - 增量编译友好
  - 并行编译与依赖链
- 代码膨胀控制
  - 泛型特化（`min_specialization`）
  - 条件编译与 feature flags
  - 共享代码路径
  - 静态 vs 动态分发
- 高级优化技术
  - 常量折叠与常量传播
  - 死代码消除
  - 循环展开
  - SIMD 优化
- 性能测量
  - `cargo build --timings`
  - `cargo-llvm-lines`
  - `cargo-bloat`
  - Criterion 基准测试
- 实战案例
  - 序列化代码生成优化
  - 减少泛型膨胀

---

> **权威来源**: [concept/03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md](../../../../concept/03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md)
