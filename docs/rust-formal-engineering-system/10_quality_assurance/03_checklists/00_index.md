# 质量检查清单（Checklists）索引

## 目的

- 提供 Rust 项目开发过程中的质量检查清单。
- 确保代码提交、发布、维护过程中的质量标准。

## 代码提交检查清单

- [ ] 代码通过 `cargo fmt` 格式化
- [ ] 代码通过 `cargo clippy -- -D warnings` 检查
- [ ] 所有测试通过 `cargo test`
- [ ] 新增功能包含相应的测试
- [ ] 公共 API 包含文档注释
- [ ] 提交信息遵循 Conventional Commits 规范

## 发布检查清单

- [ ] 版本号正确更新
- [ ] CHANGELOG 更新
- [ ] 所有测试通过
- [ ] 基准测试通过
- [ ] 文档更新
- [ ] 依赖项检查

## 性能检查清单

- [ ] 关键路径性能测试
- [ ] 内存使用分析
- [ ] 并发性能测试
- [ ] 基准测试基线更新
- [ ] 性能回归检查

## 安全检查清单

- [ ] 无 `unsafe` 代码（除非必要）
- [ ] 输入验证完整
- [ ] 错误处理完善
- [ ] 依赖项安全扫描
- [ ] 敏感信息保护

## 实践与样例

- 检查清单应用：参见 [crates/c03_control_fn](../../../crates/c03_control_fn/)
- 性能检查：[crates/c05_threads](../../../crates/c05_threads/)
- 安全检查：[crates/c10_networks](../../../crates/c10_networks/)

## 相关索引

- 质量标准：[`../01_standards/00_index.md`](../01_standards/00_index.md)
- 质量指南：[`../02_guidelines/00_index.md`](../02_guidelines/00_index.md)
- 自动化：[`../08_automation/00_index.md`](../08_automation/00_index.md)

## 导航

- 返回质量保障：[`../00_index.md`](../00_index.md)
- 质量标准：[`../01_standards/00_index.md`](../01_standards/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
