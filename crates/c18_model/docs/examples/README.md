# 示例目录

> 返回索引：`../README.md`

包含可运行的端到端示例，便于快速验证与学习。

## 运行方式

```bash
cargo run --example system_modeling_examples
cargo run --example machine_learning_examples
cargo run --example formal_methods_examples
```

## 示例清单

- 系统建模：`system_modeling_examples`（关联：`guides/system-modeling.md`）
- 机器学习：`machine_learning_examples`（关联：`guides/ml-preprocess-eval.md`、`api-reference/ml-models.md`）
- 形式化方法：`formal_methods_examples`（关联：`guides/fsm-to-protocol.md`、`api-reference/formal-models.md`）

## 提交要求

- 示例需最小可复现、带注释与 README 链接
- 输出稳定、避免依赖不确定的随机性（或固定 seed）
