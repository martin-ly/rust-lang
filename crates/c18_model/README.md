# c18_model

聚焦核心：排队论、机器学习、形式化方法、数学建模与性能模型的 Rust 实现。

- 文档入口：`docs/README.md`
- API 参考：`docs/api-reference/`
- 使用指南：`docs/guides/`
- 入门指南：`docs/getting-started/`
- 贡献指南：`docs/development/contributing.md`

## 快速开始

```bash
# 编译检查
cargo check -p c18_model

# 运行示例
cargo run -p c18_model --example system_modeling_examples
cargo run -p c18_model --example machine_learning_examples
cargo run -p c18_model --example formal_methods_examples

# 运行测试
cargo test -p c18_model
```

## 设计说明

项目已去除异步/并行/可视化/基准测试及相关依赖，聚焦最小稳定内核，便于学习与集成。
