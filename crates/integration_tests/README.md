# 集成测试 (Integration Tests)

## 概述

本 crate 存放跨 crate 的集成测试，验证多个学习模块之间的协作与兼容性。

## 测试范围

- **跨模块 API 兼容性**: 确保 crate 间接口一致
- **端到端工作流**: 模拟真实使用场景
- **特性组合测试**: 验证不同 feature flag 组合下的行为

## 运行测试

```bash
cargo test -p integration_tests
```
## 注意事项

本 crate 的测试可能依赖于其他 crate 的特定 feature 组合，运行前请确保工作区已完整编译。
