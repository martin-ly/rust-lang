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

### 模型注册与部署（端到端示例，补全）

- 注册流程
  - 模型产物：架构/权重/版本/签名；元数据：任务、指标、依赖
  - 存储：对象存储（版本化）、索引数据库（标签/检索）

- 部署与路由
  - 推理服务：多副本、健康检查、灰度/金丝雀；路由按标签/版本/权重
  - 观测：QPS、P95/P99、错误率、SLO 警报

- 伪代码骨架

```rust
struct ModelMeta { name: String, version: String, task: String }

fn register(meta: &ModelMeta, artifact_uri: &str) -> anyhow::Result<()> {
    // 写入索引与版本存储，生成可追溯指纹
    Ok(())
}

async fn route_infer(req: InferenceReq) -> anyhow::Result<InferenceResp> {
    // 依据标签/权重选择副本，转发并聚合指标
    Ok(InferenceResp::default())
}
```

- 与 `c18_model` 互链
  - 将形式化性质（幂等、单调、上界时延）映射为属性测试与 CI 门禁
  - 部署前跑通 `c18_model` 的验证用例，生成合规报告
