# Criterion 基线

- 约定：基准位于各 crate 的 `benches/`，命名规则按功能域
- 执行：`cargo bench` 或 `cargo criterion`（若使用插件）
- 输出：HTML 报告归档为 CI 工件；建立趋势图
- 门槛：关键用例设定性能预算与波动阈值（如 ±5%）
