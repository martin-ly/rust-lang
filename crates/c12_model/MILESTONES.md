# c12_model 里程碑


## 📊 目录

- [c12\_model 里程碑](#c12_model-里程碑)
  - [📊 目录](#-目录)
  - [M1 并发/异步对标与文档骨架](#m1-并发异步对标与文档骨架)
  - [M2 统一运行时能力 Traits 草案](#m2-统一运行时能力-traits-草案)
  - [M3 Tokio 适配占位与 feature 开关](#m3-tokio-适配占位与-feature-开关)
  - [M4 示例与验证](#m4-示例与验证)
  - [M5 文档对标与发布](#m5-文档对标与发布)


## M1 并发/异步对标与文档骨架

- 文档：并发/异步总览、Rust 1.89 对标、模型映射、工程范式
- 接入：`docs/SUMMARY.md` 与根 `README.md` 链接

## M2 统一运行时能力 Traits 草案

- `Spawner/Timer/Channel/Cancellation/Observability` 接口草案与示例

## M3 Tokio 适配占位与 feature 开关

- 不引入运行时强依赖；可选 feature 启用适配层

## M4 示例与验证

- CSP/Actor/结构化并发示例；`loom`/`criterion` 脚手架

## M5 文档对标与发布

- 国际资料映射与索引；README 与 CHANGELOG 更新；版本发布
