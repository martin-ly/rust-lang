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

### 并发与异步（多运行时）

- CSP 风格：`concurrency_csp`
- Actor 风格：`concurrency_actor`
- 结构化并发：`concurrency_structured`

运行方式（Tokio）：

```bash
cargo run -p c18_model --example concurrency_csp --features tokio-adapter
cargo run -p c18_model --example concurrency_actor --features tokio-adapter
cargo run -p c18_model --example concurrency_structured --features tokio-adapter
```

运行方式（async-std）：

```bash
cargo run -p c18_model --example concurrency_csp --features async-std-adapter
cargo run -p c18_model --example concurrency_actor --features async-std-adapter
cargo run -p c18_model --example concurrency_structured --features async-std-adapter
```

## 提交要求

- 示例需最小可复现、带注释与 README 链接
- 输出稳定、避免依赖不确定的随机性（或固定 seed）
