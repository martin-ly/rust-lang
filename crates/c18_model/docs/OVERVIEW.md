# 概览：建模与形式方法（c18_model）

本模块汇聚系统建模、形式化方法、性能/排队/并发模型与机器学习模型的交叉工程实践。

---

## 目录导航

- 总览与导航
  - [docs/README.md](./README.md)
  - [docs/SUMMARY.md](./SUMMARY.md)

- 入门与指南
  - [getting-started/README.md](./getting-started/README.md)
  - [getting-started/installation.md](./getting-started/installation.md)
  - [getting-started/quick-start.md](./getting-started/quick-start.md)

- 专题目录
  - [formal/README.md](./formal/README.md)
  - [concurrency/README.md](./concurrency/README.md)
  - [architecture/README.md](./architecture/README.md)
  - [patterns/README.md](./patterns/README.md)
  - [domain/README.md](./domain/README.md)
  - [iot/README.md](./iot/README.md)
  - [guides/README.md](./guides/README.md)
  - [development/README.md](./development/README.md)

- API 参考
  - [api-reference/formal-models.md](./api-reference/formal-models.md)
  - [api-reference/ml-models.md](./api-reference/ml-models.md)
  - [api-reference/queueing-models.md](./api-reference/queueing-models.md)

- 源码与示例
  - `src/*.rs`
  - `examples/*.rs`

---

## 快速开始

1) 按 `getting-started/*` 配置环境
2) 运行 `examples/` 的并发/形式化示例
3) 对照 `api-reference/*` 进行二次开发

---

## 待完善

- 补充模型验证工具链与 CI 集成示例
- 与 `c14_workflow` 的状态机/编排互链

### 模型验证工具链与 CI 集成（补全）

- 本地工具链
  - 性质测试：`proptest`/`quickcheck` 定义不变量与代数律
  - 模型检查（可选）：`kani`/`prusti`/`crest` 等工具按需引入
  - 负载与性能：`criterion` 微基准；`tokio-console`/`tracing` 观测并发性质

- 目录与约定
  - `tests/properties/*.rs`：不变量/等价性/幂等性测试
  - `benches/*.rs`：关键算子与状态机步进的基准
  - `models/*.md`：形式化规范与可检验断言的映射

- CI 集成（GitHub Actions 示例片段）

```yaml
name: model-ci
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo test --all --all-features --locked
      - run: cargo clippy --all --all-features -- -D warnings
      - run: cargo fmt --all -- --check
  benches:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: dtolnay/rust-toolchain@stable
      - run: cargo bench --all || true # 基准不作为阻断
```

- 互链
  - 与 `c14_workflow`：将状态机规范转化为属性测试与模型检查约束
  - 与 `c20_distributed`：共享一致性与时序不变量的测试基元
