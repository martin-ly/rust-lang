# 概览：人工智能（c19_ai）

本模块聚焦传统机器学习、深度学习、图网络、强化学习、时序与多模态等主题，并整合推理/训练/监控链路。

---

## 目录导航

- 顶层与说明
  - 顶层说明：`README.md`
  - 项目总结：`PROJECT_COMPLETION_REPORT_2025.md`

- 示例与场景
  - `examples/{basic_ml,deep_learning,nlp_pipeline,graph_neural_network,reinforcement_learning,vector_search,...}.rs`

- 源码结构
  - `src/machine_learning/*`、`src/deep_learning/*`、`src/llm/*`
  - `src/model_management/*`、`src/monitoring/*`、`src/pipelines/*`
  - `src/time_series/*`、`src/graph_neural_networks/*`、`src/vector_search/*`

---

## 快速开始

1) 运行 `examples/basic_ml.rs` 与 `examples/deep_learning.rs`
2) 查看 `src/llm/*` 下的聊天/补全/嵌入接口
3) 使用 `src/monitoring/*` 观察性能/指标

---

## 🔗 快速导航

- 模型理论：`../../formal_rust/language/18_model/01_model_theory.md`
- 分布式系统：`../c20_distributed/docs/FAQ.md`
- WebAssembly：`../../formal_rust/language/16_webassembly/FAQ.md`
- IoT系统：`../../formal_rust/language/17_iot/FAQ.md`
- 区块链：`../../formal_rust/language/15_blockchain/FAQ.md`

## 待完善

- 增补模型注册与部署端到端示例
- 与 `c18_model` 的建模与验证互链
