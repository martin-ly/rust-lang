> **Summary**: A systems-level guide to deploying and serving AI/ML models with Rust — covering ONNX Runtime, Candle, quantization strategies, batching, caching, and latency/throughput trade-offs in production inference pipelines.
> **内容分级**: [专家级]

# Rust 在 AI 模型服务与推理系统中的应用

**EN**: Rust for AI Model Serving and Inference Systems

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L5-L7
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 聚焦**模型服务层**（model serving / inference serving），把 LLM system architecture 中的推理部分下沉到工程实现，对齐国际 ML 系统工程实践与 Rust 生态。
> **前置概念**: [LLM System Architecture](08_llm_system_architecture.md) · [MLOps and LLMOps](09_mlops_and_llmops.md) · [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) · [Async/Await](../../03_advanced/01_async/01_async.md) · [Performance Optimization](../../06_ecosystem/10_performance/01_performance_optimization.md)
> **后置概念**: [Rust in AI](05_rust_in_ai.md) · [AI Safety and Alignment](10_ai_safety_and_alignment.md) · [Custom Allocators](../../03_advanced/06_low_level_patterns/01_custom_allocators.md)

---

> **来源**: [Huyen — *Designing Machine Learning Systems*](https://www.oreilly.com/library/view/designing-machine-learning/9781098107956/) · [MLCommons Inference Benchmarks](https://mlcommons.org/benchmarks/inference/) · [MLCommons Inference Rules](https://mlcommons.org/inference/) · [NVIDIA Triton Inference Server](https://docs.nvidia.com/deeplearning/triton-inference-server/user-guide/docs/index.html) · [Hugging Face Inference API docs](https://huggingface.co/docs/api-inference/index) · [Seldon Core](https://docs.seldon.io/seldon-core-2/) · [ONNX Runtime docs](https://onnxruntime.ai/docs/) · [Hugging Face Candle](https://github.com/huggingface/candle) · [LLM Inference Survey (arXiv)](https://arxiv.org/abs/2401.00066) · [vLLM / PagedAttention](https://arxiv.org/abs/2309.06180) · [TensorRT-LLM](https://developer.nvidia.com/tensorrt-llm)

---

## 🧠 知识结构图

```mermaid
mindmap
  root((Rust AI Serving))
    运行时
      ONNX Runtime
      Candle
      TensorRT-LLM
      llama.cpp / ggml
    优化
      量化 INT8/INT4
      连续批处理
      KV Cache / PagedAttention
      投机解码
    服务层
      gRPC/REST
      Batching scheduler
      Prefix caching
      Load balancing
    语义边界
      请求级语义
      引擎抽象
      观测语义
    Rust 优势
      零成本抽象
      内存安全
      异步并发
      无 GC 停顿
```

---

## 一、模型服务层核心组件

生产级模型服务不是简单加载 `.pt` 文件并调用 `forward`，而是一个多阶段流水线：

```text
Client Request
    ↓
[Tokenizer] → token ids
    ↓
[Scheduler] → batch / prefill / decode
    ↓
[Inference Engine] → logits / embeddings
    ↓
[Post-processing] → detokenize / filter
    ↓
Response
```

Rust 在 **Scheduler、网络层、缓存层、量化工具链** 中优势最大；核心算子通常仍依赖 CUDA/ROCm 内核。

---

## 二、Rust 生态中的推理运行时

| 运行时 | 定位 | Rust 绑定/实现 | 适用场景 |
|---|---|---|---|
| **ONNX Runtime** | 通用模型格式 | `ort` crate | 图像/语音/小模型 |
| **Candle** | 纯 Rust ML 框架 | `candle-core` | LLM、Embedding、训练 |
| **llama.cpp** | GGUF/GGML 量化模型 | `llama-cpp-rs` | 本地/边缘 LLM |
| **TensorRT-LLM** | NVIDIA 高性能推理 | 官方 Rust 绑定有限 | 数据中心 GPU |
| **burn** | 深度学习框架 | `burn` | 训练 + 推理 |

### 2.1 Candle 最小示例（概念骨架）

```rust,ignore
// 概念示例：Candle 加载模型并执行前向推理。
// 真实代码需对应 model files 与 tokenizer。
use candle_core::{Device, Tensor};
use candle_nn::VarMap;

fn inference_skeleton() -> anyhow::Result<()> {
    let device = Device::Cpu;
    // 占位：加载权重与 tokenizer
    let input_ids = Tensor::new(&[101u32, 2023, 2003, 1037, 3231, 102u32], &device)?;
    let _logits = model_forward(&input_ids, &device)?;
    Ok(())
}

fn model_forward(_input_ids: &Tensor, _device: &Device) -> anyhow::Result<Tensor> {
    todo!("load real weights and run forward")
}
```

> 本示例为骨架，真实运行需下载模型文件；使用 `ignore` 避免 CI 依赖外部权重。

---

## 三、推理优化策略

### 3.1 量化（Quantization）

```text
FP32  →  FP16  →  INT8  →  INT4 / GPTQ / AWQ
  ↓        ↓        ↓           ↓
精度最高   常用      精度损失可控   极致压缩
```

Rust 生态已支持 GGUF 格式（llama.cpp）和 Candle 的量化张量。量化选择是**精度、延迟、显存**的权衡。

### 3.2 连续批处理（Continuous Batching）

传统静态批处理等待所有请求到达固定 batch size；连续批处理允许在**每次 forward 之间**替换已完成的序列，提高 GPU 利用率。

```rust,ignore
// 概念骨架：Scheduler 在每次解码步决定 batch 内容
pub struct Scheduler {
    requests: Vec<Request>,
    kv_cache: KvCacheManager,
}

impl Scheduler {
    pub fn schedule(&mut self) -> Vec<&Request> {
        // 按优先级、长度、SLA 选择可合并的请求
        self.requests.iter().filter(|r| self.kv_cache.can_fit(r)).collect()
    }
}
```

### 3.3 KV Cache 与 PagedAttention

PagedAttention 把 KV cache 分成固定大小的 block，像虚拟内存一样按需分配，减少显存碎片。Rust 的精确内存控制使其适合实现类似的 cache manager。

---

## 四、服务架构模式

### 4.1 Rust 推理服务骨架

```rust,ignore
use axum::{extract::Json, response::IntoResponse, routing::post, Router};
use serde::Deserialize;

#[derive(Deserialize)]
struct GenerateRequest {
    prompt: String,
    max_tokens: usize,
}

async fn generate(Json(req): Json<GenerateRequest>) -> impl IntoResponse {
    // 提交到异步推理队列，等待结果
    let output = INFERENCE_QUEUE.submit(req.prompt, req.max_tokens).await;
    Json(output)
}

// async runtime + 独立推理线程/进程池是常见部署形态
```

> 使用 `ignore` 避免引入 axum/tokio 等依赖到 concept 代码块检查。

### 4.2 与 Python 服务对比

| 维度 | Python (FastAPI + vLLM/TGI) | Rust (Candle/ORT + tokio) |
|---|---|---|
| 启动延迟 | 中等 | 低 |
| GC 停顿 | 有 | 无 |
| 内存安全 | 依赖运行时 | 编译期保证 |
| 生态成熟度 | 极高 | 快速增长 |
| 适合场景 | 快速迭代、研究 | 高吞吐、低延迟、边缘 |

---

## 五、模型服务语义与系统边界

模型服务系统不仅要“跑起来”，还必须精确定义请求在系统边界上的语义行为：请求如何被接收、编解码、调度、执行与观测。下面从请求级语义、推理引擎抽象和观测语义三个维度展开。

### 5.1 请求级语义

- **Batching（静态批处理）**：将形状兼容的请求拼成固定大小的张量一次性送入推理引擎，可提升吞吐，但同批次内较快的请求需等待最慢者完成，尾部延迟会恶化。适用于输入输出长度相对固定的 CV / Encoder 场景。
- **Dynamic Batching（动态批处理 / in-flight batching）**：调度器在最大等待时间或最大 batch size 到达前聚合到达的请求，再统一 dispatch。它是在**吞吐**与**TTFT（首 token 时间）**之间的核心权衡；最大等待时间本身就是 SLO 旋钮。
- **序列化 / 反序列化**：用户文本 → token IDs → 引擎张量 → 输出 logits → 文本/结构化输出。开销包括 tokenizer CPU 计算、张量布局转换、网络负载（gRPC/Protobuf 或 JSON）。使用 Safetensors、零拷贝张量缓冲、gRPC streaming 可降低这部分开销。
- **Token 限制**：`max_input_tokens`、`max_total_tokens`、`max_new_tokens` 定义了请求在模型上下文窗口内的合法范围。超出限制时需截断或拒绝；更长的序列会占用更多 KV cache 与显存，且 prefill 阶段算力密集、decode 阶段显存带宽密集。

### 5.2 推理引擎抽象

不同推理引擎在模型格式、优化阶段、调度能力和 Rust 绑定成熟度上差异显著：

| 引擎 | 定位 | 官方文档 | Rust 绑定/实现 | 核心语义差异 |
|---|---|---|---|---|
| **ONNX Runtime** | 跨平台 ONNX 模型推理引擎 | [ONNX Runtime docs](https://onnxruntime.ai/docs/) | `ort` crate | 图级优化 + Execution Provider 插件化；适合 CV、语音、传统小模型 |
| **TensorRT / TensorRT-LLM** | NVIDIA 高性能推理 SDK | [TensorRT-LLM](https://developer.nvidia.com/tensorrt-llm) | 官方 Rust 绑定有限 | 将模型编译为优化 engine，支持 plugin/fusion；显存与 kernel 高度优化 |
| **llama.cpp** | GGUF/GGML 量化 LLM 推理 | [llama.cpp GitHub](https://github.com/ggerganov/llama.cpp) | `llama-cpp-rs` 等 | 以 GGUF 文件格式和量化为核心，CPU/GPU 后端多样；边缘部署友好 |
| **Candle** | Hugging Face 纯 Rust ML 框架 | [Candle docs](https://huggingface.co/docs/candle/index) | `candle-core` | Rust-first，无 Python 依赖；张量 API 接近 PyTorch，生态仍在快速演进 |

**关键语义差异**：

- **模型格式**：ONNX（通用计算图） vs TensorRT engine（NVIDIA 专用优化产物） vs GGUF（llama.cpp 量化容器） vs Safetensors（Candle 常用）。
- **优化阶段**：ONNX Runtime 在加载时做图优化；TensorRT 通常离线/在线编译；llama.cpp 聚焦量化和 KV cache；Candle 强调 Rust 原生人体工学。
- **调度能力**：Triton/TensorRT-LLM、vLLM 内置连续批处理 / PagedAttention；Candle 与 llama.cpp 通常暴露较低层 API，需要服务层自行实现 scheduler。

### 5.3 观测语义

可观测性不只是“打日志”，而是把延迟拆分到可干预的组件：

- **SLI / SLO**：常见 SLI 包括 TTFT、TPOT（每个输出 token 的时间）、端到端延迟、吞吐（tokens/s、requests/s）、错误率、GPU 显存利用率；SLO 如 P99 TTFT < 200 ms、P95 TPOT < 50 ms、可用性 > 99.9%。
- **Latency Histogram 与百分位**：将延迟按桶收集后计算 p50、p95、p99、p999。LLM 输出长度差异极大，均值延迟容易掩盖尾部延迟，百分位才是 SLO 的核心。
- **吞吐与并发度关系**：并发度增加时吞吐先上升，直至 GPU 算力或显存带宽饱和；超过饱和点后排队延迟占主导，端到端延迟上升（Little's Law：`L = λW`）。Rust 的异步运行时能在无 GC 停顿的情况下维持高并发，但真正的瓶颈通常是底层 CUDA/ROCm 推理引擎。

### 5.4 Rust 服务骨架：tokio + axum 端点

```rust,ignore
// 概念骨架：用 axum + tokio 暴露异步模型服务 HTTP 端点。
// 真实运行需将 axum、tokio、serde 加入 Cargo.toml。
use axum::{
    extract::Json,
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::post,
    Router,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::{mpsc, oneshot};

#[derive(Deserialize)]
struct GenerateRequest {
    prompt: String,
    max_tokens: usize,
}

#[derive(Serialize)]
struct GenerateResponse {
    text: String,
}

// 异步提交到推理队列，解耦 HTTP worker 与模型执行线程/进程
async fn generate(
    Json(req): Json<GenerateRequest>,
    tx: axum::extract::State<Arc<mpsc::UnboundedSender<InferenceJob>>>,
) -> Response {
    let (resp_tx, resp_rx) = oneshot::channel();
    let job = InferenceJob {
        prompt: req.prompt,
        max_tokens: req.max_tokens,
        respond_to: resp_tx,
    };
    if tx.send(job).is_err() {
        return (StatusCode::SERVICE_UNAVAILABLE, "inference queue closed").into_response();
    }
    match resp_rx.await {
        Ok(text) => (StatusCode::OK, Json(GenerateResponse { text })).into_response(),
        Err(_) => (StatusCode::INTERNAL_SERVER_ERROR, "inference failed").into_response(),
    }
}

struct InferenceJob {
    prompt: String,
    max_tokens: usize,
    respond_to: oneshot::Sender<String>,
}

#[tokio::main]
async fn main() {
    let (tx, _rx) = mpsc::unbounded_channel::<InferenceJob>();
    let app = Router::new()
        .route("/generate", post(generate))
        .with_state(Arc::new(tx));
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

> 使用 `ignore` 避免 CI 编译缺少 axum/tokio 依赖；真实部署应放在 workspace crate 或独立服务中管理依赖。

## 六、生产部署与治理

### 6.1 SLO / SLI 与可观测性

生产模型服务需要明确的**服务水平目标（SLO）**和**服务水平指标（SLI）**：

| SLI | 说明 | Rust 生态工具 |
|---|---|---|
| **延迟（Latency）** | TTFT / TPOT / P99 latency | `tokio::time`、`metrics`、OpenTelemetry |
| **吞吐（Throughput）** | tokens/s、requests/s | `prometheus`、自定义 histogram |
| **可用性（Availability）** | 成功请求比例 | `axum` health check、kube probes |
| **成本（Cost）** | $ / 1M tokens、GPU 利用率 | DCGM、NVML 绑定 |
| **能效（Energy）** | W / token、CO₂ / inference | MLCommons Power、NVIDIA Triton 能效指标 |

> **关键洞察**: Rust 的无 GC 停顿和零成本抽象使其在**延迟敏感**和**高吞吐**场景下更容易达成严格的 SLO。

### 6.2 模型版本管理与 A/B 测试

```text
模型注册表（如 MLflow / Hugging Face Hub）
    ↓
版本化模型工件（GGUF、ONNX、Safetensors）
    ↓
金丝雀部署 → A/B 测试 → 全量 rollout
    ↓
回滚策略（蓝绿 / 影子流量）
```

Rust 服务可通过 feature flag（如 `launchdarkly`、`unleash`）或配置文件实现模型版本路由。

### 6.3 安全与隐私边界

- **模型窃取**：限制 prompt 日志、限制输出 tokens 采样。
- **数据泄露**：避免在日志中记录 PII；使用差分隐私或联邦学习时明确边界。
- **提示注入**：对输入进行过滤、沙箱化工具调用。
- **供应链**：使用 `cargo vet` / `cargo audit` 审查推理运行时依赖。

### 6.4 国际权威来源对齐

| 来源 | URL | 对齐内容 |
|---|---|---|
| MLCommons Inference | <https://mlcommons.org/inference/> | 推理性能、能效与公平性基准规则 |
| Hugging Face Inference API | <https://huggingface.co/docs/api-inference/index> | 托管模型服务请求语义与限制 |
| NVIDIA Triton | <https://docs.nvidia.com/deeplearning/triton-inference-server/user-guide/docs/index.html> | 数据中心推理服务架构与调度 |
| Seldon Core | <https://docs.seldon.io/seldon-core-2/> | Kubernetes 上 ML 部署、A/B 测试与监控 |
| Model Cards | <https://arxiv.org/abs/1810.03993> | 模型透明度与限制报告 |
| LLM System Survey | <https://arxiv.org/abs/2303.18223> | LLM 训练与推理系统栈 |

---

## 七、反命题与边界

### 反例 1：用 Rust 重写所有训练代码

Rust 在**训练框架**生态（autograd、分布式训练、实验工具）仍远不如 PyTorch/JAX。当前更合理的策略是：Python 训练，Rust 服务。

### 反例 2：认为量化总是无代价

INT4 量化可能显著降低模型能力；对于需要高精度推理的任务（如代码生成、数学推理），应保留 FP16 或采用 QLoRA 等精细量化。

### 反例 3：认为“模型服务只是 HTTP 转发”

这是一个常见的设计误解。模型服务远不止把请求路由到模型；它隐藏了大量系统复杂度：

- **延迟层次**：网络 RTT、序列化/反序列化、tokenizer 预处理、队列等待、GPU 内核启动、KV cache 访问、解码步迭代、后处理均会贡献端到端延迟；忽略任何一层都难以达成 SLO。
- **批处理权衡**：动态批处理需要在等待更多请求与最大等待时间之间做调度决策；batch size 过大导致 TTFT 恶化，过小则 GPU 利用率不足。
- **缓存策略**：Prefix caching、KV cache 复用、embedding cache 能显著降低重复计算，但需要管理显存生命周期与一致性。
- **GPU 内存管理**：模型权重、激活值、KV cache、连续批处理的中间状态共享有限显存；OOM 可能在长序列或高并发时突然出现。
- **自动扩缩容**：GPU 节点冷启动慢、显存不可超分、请求长度变化大，导致 CPU/GPU 混部扩缩容远比无状态 HTTP 服务困难。

### 边界：Rust 不是 CUDA 内核开发首选

虽然 Rust 有 `cust`/`cudarc` 等 CUDA 绑定，但高性能 kernel 开发仍以 CUDA C++/Triton 为主。Rust 更适合编排这些 kernel。

---

## 八、国际权威参考

- **P0 官方/生态**
  - [MLCommons Inference Rules](https://mlcommons.org/inference/) — 推理性能、能效与公平性基准规则
  - [NVIDIA Triton Inference Server Architecture](https://docs.nvidia.com/deeplearning/triton-inference-server/user-guide/docs/index.html) — 数据中心推理服务架构与调度
  - [Hugging Face Inference API docs](https://huggingface.co/docs/api-inference/index) — 托管模型服务 API 语义
  - [Seldon Core docs](https://docs.seldon.io/seldon-core-2/) — Kubernetes 上 ML 部署、A/B 测试与可观测性
  - [ONNX Runtime docs](https://onnxruntime.ai/docs/)
  - [TensorRT / TensorRT-LLM](https://developer.nvidia.com/tensorrt-llm)
  - [llama.cpp](https://github.com/ggerganov/llama.cpp)
  - [Candle docs](https://huggingface.co/docs/candle/index)

- **P1 学术/系统**
  - [Huyen — *Designing Machine Learning Systems*](https://www.oreilly.com/library/view/designing-machine-learning/9781098107956/)
  - [vLLM / PagedAttention (SOSP 2023)](https://arxiv.org/abs/2309.06180)
  - [LLM Inference Survey](https://arxiv.org/abs/2401.00066)
  - [LLM Serving Survey](https://arxiv.org/abs/2312.15234)

- **P2 社区**
  - [Hugging Face Rust](https://huggingface.co/docs/candle/index)
  - [Rust ML](https://www.arewelearningyet.com/)
  - [ort crate docs](https://docs.rs/ort) — ONNX Runtime Rust 绑定
  - [candle-core crate docs](https://docs.rs/candle-core) — Hugging Face 纯 Rust ML 框架
  - [burn crate on crates.io](https://crates.io/crates/burn) — Rust 深度学习框架
  - [llama-cpp-rs crate on crates.io](https://crates.io/crates/llama-cpp-rs) — llama.cpp 的 Rust 绑定

---

## 嵌入式测验

> **Q1**. PagedAttention 主要解决什么问题？
>
> - A. 模型训练速度
> - B. KV Cache 显存碎片与浪费
> - C. Tokenizer 精度
> - D. 数据加载
>
> <details><summary>答案</summary>B. 通过分页管理 KV cache，提高显存利用率。</details>

> **Q2**. Rust 在 AI 服务中的主要优势不包括？
>
> - A. 无 GC 停顿
> - B. 内存安全
> - C. 训练生态最成熟
> - D. 零成本并发抽象
>
> <details><summary>答案</summary>C. Rust 训练生态仍在追赶 Python。</details>

> **Q3**. 连续批处理相比静态批处理的主要收益是？
>
> - A. 提高模型精度
> - B. 提高 GPU 利用率
> - C. 减少模型参数量
> - D. 简化代码
>
> <details><summary>答案</summary>B. 允许在解码步之间动态替换已完成序列。</details>
