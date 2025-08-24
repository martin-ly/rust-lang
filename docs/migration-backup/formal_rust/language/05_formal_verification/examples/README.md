# 05 形式化验证 示例导航

本目录收录Rust形式化验证相关的典型代码示例，涵盖类型安全、所有权、分离逻辑、并发安全、自动化工具等主题。每个示例均配有形式化注释，便于理解理论与工程联系。

## 示例导航

- type_safety.rs —— 类型安全与进展/保持定理示例
- ownership_correctness.rs —— 所有权、借用、生命周期安全性示例
- separation_logic.rs —— 分离逻辑与内存分离、帧规则示例
- concurrency_safety.rs —— 并发安全、Send/Sync、原子性示例
- prusti_example.rs —— Prusti自动化验证注解示例
- kani_example.rs —— Kani模型检查示例
- creusot_example.rs —— Creusot高阶验证示例

## 示例结构与说明

每个示例文件包含：

- Rust核心代码片段
- 形式化注释（如前置/后置条件、不变式、分离逻辑断言等）
- 工程意义与适用场景说明
- 推荐适用的验证工具

## 工程意义

- 便于开发者结合理论与实际代码理解形式化验证要点
- 支持自动化工具（Prusti/Kani/Creusot等）直接验证
- 可作为工程项目安全性验证的参考模板

## 工具适用建议

- 类型安全/借用/生命周期：Prusti、Creusot
- 并发安全/边界条件：Kani、Prusti
- 高阶trait/复杂不变式：Creusot、Coq/Isabelle

---

如需添加新示例，请保持注释风格与理论联系，便于后续自动化验证与工程落地。
