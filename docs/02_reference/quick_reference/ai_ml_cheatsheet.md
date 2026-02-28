# 🤖 Rust AI/ML 速查卡 {#-rust-aiml-速查卡}

> **快速参考** | [AI+Rust 生态指南](../../05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) | [AI 辅助编程](../../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [🤖 Rust AI/ML 速查卡 {#-rust-aiml-速查卡}](#-rust-aiml-速查卡--rust-aiml-速查卡)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [框架选型](#框架选型)
  - [Burn 快速入门](#burn-快速入门)
    - [示例 1: 张量基础操作](#示例-1-张量基础操作)
    - [示例 2: 简单神经网络](#示例-2-简单神经网络)
    - [示例 3: 模型推理](#示例-3-模型推理)
  - [Candle 快速入门](#candle-快速入门)
    - [示例 4: 张量操作](#示例-4-张量操作)
    - [示例 5: 加载 Hugging Face 模型](#示例-5-加载-hugging-face-模型)
  - [LLM 推理](#llm-推理)
    - [示例 6: 使用 llm crate 进行本地推理](#示例-6-使用-llm-crate-进行本地推理)
    - [框架选型表](#框架选型表)
  - [与 C01–C12 关联](#与-c01c12-关联)
  - [🎯 使用场景 {#-使用场景}](#-使用场景--使用场景)
    - [场景 1: 图像分类服务](#场景-1-图像分类服务)
    - [场景 2: 实时文本生成](#场景-2-实时文本生成)
  - [📐 形式化方法链接 {#-形式化方法链接}](#-形式化方法链接--形式化方法链接)
    - [理论基础](#理论基础)
    - [形式化定理](#形式化定理)
  - [🚫 反例速查 {#-反例速查}](#-反例速查--反例速查)
    - [反例 1: 混淆不同框架的 API](#反例-1-混淆不同框架的-api)
    - [反例 2: 未根据场景选择后端](#反例-2-未根据场景选择后端)
    - [反例 3: 忽略依赖版本兼容性](#反例-3-忽略依赖版本兼容性)
    - [反例 4: 内存泄漏 - 循环引用张量缓存](#反例-4-内存泄漏---循环引用张量缓存)
    - [反例 5: 边界情况 - 空张量操作](#反例-5-边界情况---空张量操作)
  - [相关文档](#相关文档)
  - [相关示例代码](#相关示例代码)

---

## 框架选型

| 框架 | 适用场景 | 依赖 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Candle** | 简洁 API、Hugging Face、推理 | candle-core, candle-nn |
| **llm** | 本地 LLM、CPU 推理 | llm |
| **tch-rs** | PyTorch 生态、LibTorch | tch |

---

## Burn 快速入门

### 示例 1: 张量基础操作

```toml
# Cargo.toml
[dependencies]
burn = "0.20"
burn-ndarray = "0.20"
```

```rust
use burn::tensor::{Tensor, backend::NdArray};

fn main() {
    type B = NdArray<f32>;

    // 创建张量
    let x = Tensor::<B, 2>::from_floats([
        [1.0, 2.0],
        [3.0, 4.0],
    ]);
    let y = Tensor::<B, 2>::from_floats([
        [5.0, 6.0],
        [7.0, 8.0],
    ]);

    // 张量运算
    let z = x + y;           // 加法
    let w = x.matmul(y);     // 矩阵乘法
    let s = x.sum();         // 求和

    println!("Sum: {:?}", s.into_scalar());
}
```

### 示例 2: 简单神经网络

```rust
use burn::{
    module::Module,
    nn::{Linear, ReLU, Softmax},
    tensor::{Tensor, backend::NdArray},
};

#[derive(Module, Debug)]
struct Net<B: burn::tensor::backend::Backend> {
    linear1: Linear<B>,
    activation: ReLU,
    linear2: Linear<B>,
    softmax: Softmax,
}

impl<B: burn::tensor::backend::Backend> Net<B> {
    fn new(device: &B::Device) -> Self {
        Self {
            linear1: Linear::new(device, 784, 128),
            activation: ReLU::new(),
            linear2: Linear::new(device, 128, 10),
            softmax: Softmax::new(1),
        }
    }

    fn forward(&self, input: Tensor<B, 2>) -> Tensor<B, 2> {
        let x = self.linear1.forward(input);
        let x = self.activation.forward(x);
        let x = self.linear2.forward(x);
        self.softmax.forward(x)
    }
}
```

### 示例 3: 模型推理

```rust
use burn::tensor::{Tensor, backend::NdArray};

fn inference<B: burn::tensor::backend::Backend>(
    model: &impl burn::module::Module<B>,
    input: Tensor<B, 2>,
) -> Tensor<B, 2> {
    // 前向传播
    let output = model.forward(input);

    // 获取预测结果
    let predictions = output.argmax(1);
    predictions
}
```

**文档**: [burn.dev](https://burn.dev/)

---

## Candle 快速入门

### 示例 4: 张量操作

```toml
# Cargo.toml
[dependencies]
candle-core = "0.8"
candle-nn = "0.8"
```

```rust
use candle_core::{Device, Result, Tensor};

fn main() -> Result<()> {
    let device = Device::Cpu;

    // 创建张量
    let a = Tensor::new(&[[1.0f32, 2.0], [3.0, 4.0]], &device)?;
    let b = Tensor::new(&[[5.0f32, 6.0], [7.0, 8.0]], &device)?;

    // 基本运算
    let c = (&a + &b)?;           // 加法
    let d = a.matmul(&b)?;        // 矩阵乘法
    let e = a.mean(1)?;           // 按维度求均值

    println!("Shape: {:?}", c.shape());
    println!("Values: {:?}", c.to_vec2::<f32>()?);

    Ok(())
}
```

### 示例 5: 加载 Hugging Face 模型

```rust
use candle_core::{Device, Result};
use candle_nn::VarBuilder;
use hf_hub::{api::sync::Api, Repo, RepoType};

fn load_model(model_id: &str) -> Result<()> {
    let api = Api::new()?;
    let repo = api.repo(Repo::new(
        model_id.to_string(),
        RepoType::Model,
    ));

    // 下载模型文件
    let weights = repo.get("model.safetensors")?;

    // 加载权重
    let device = Device::Cpu;
    let vb = unsafe {
        VarBuilder::from_mmaped_safetensors(&[weights], candle_core::DType::F32, &device)?
    };

    println!("Model loaded successfully!");
    Ok(())
}
```

**文档**: [Candle GitHub](https://github.com/huggingface/candle)

---

## LLM 推理

### 示例 6: 使用 llm crate 进行本地推理

```rust
use llm::Model;

fn llm_inference() -> anyhow::Result<()> {
    // 加载模型
    let model_path = "path/to/model.gguf";
    let model = llm::load::<llm::models::Llama>(
        std::path::Path::new(model_path),
        llm::TokenizerSource::Embedded,
        Default::default(),
        llm::load_progress_callback_stdout,
    )?;

    // 创建推理会话
    let mut session = model.start_session(Default::default());

    // 推理
    let prompt = "The capital of France is";
    let mut response = String::new();

    session.infer(
        model.as_ref(),
        &mut rand::thread_rng(),
        &llm::InferenceRequest {
            prompt: prompt.into(),
            parameters: &llm::InferenceParameters::default(),
            play_back_previous_tokens: false,
            maximum_token_count: Some(50),
        },
        &mut Default::default(),
        |t| {
            if let llm::InferenceResponse::GeneratedToken(token) = t {
                response.push_str(&token);
            }
            Ok(llm::InferenceFeedback::Continue)
        },
    )?;

    println!("Response: {}", response);
    Ok(())
}
```

### 框架选型表

| 库 | 用途 | 适用场景 |
| :--- | :--- | :--- |
| **llm** | 多架构、InferenceSession | 本地 CPU 推理 |
| **mistral.rs** | 高性能、量化、Vision | 生产环境 |
| **lm.rs** | 轻量、CPU 优化 | 嵌入式设备 |

---

## 与 C01–C12 关联

| 模块 | AI/ML 中的关联 |
| :--- | :--- |
| C01 所有权 | 张量生命周期、零拷贝 |
| C02 类型系统 | 泛型张量、Trait 抽象 |
| C05 线程 | 多线程训练、数据并行 |
| C06 异步 | 流式推理 |
| C11 宏 | 模型定义 DSL |

---

## 🎯 使用场景 {#-使用场景}

### 场景 1: 图像分类服务

```rust
// 使用 Candle 构建图像分类微服务
use candle_core::{Device, Tensor};
use candle_nn::Module;

pub struct ImageClassifier {
    model: Box<dyn Module>,
    device: Device,
}

impl ImageClassifier {
    pub fn classify(&self, image_data: &[f32]) -> anyhow::Result<Vec<f32>> {
        let input = Tensor::from_slice(image_data, &[1, 3, 224, 224], &self.device)?;
        let output = self.model.forward(&input)?;
        let probs = candle_nn::ops::softmax(&output, 1)?;
        Ok(probs.to_vec1::<f32>()?)
    }
}
```

### 场景 2: 实时文本生成

```rust
// 使用 Burn 实现流式文本生成
use burn::tensor::backend::Backend;

async fn stream_generate<B: Backend>(
    model: &impl LanguageModel<B>,
    prompt: &str,
) -> impl Stream<Item = String> {
    // 异步流式生成文本
    stream! {
        let mut tokens = tokenize(prompt);
        for _ in 0..100 {
            let next_token = model.predict_next(&tokens).await;
            tokens.push(next_token);
            yield detokenize(&[next_token]);
        }
    }
}
```

---

## 📐 形式化方法链接 {#-形式化方法链接}

### 理论基础

| 概念 | 形式化文档 | 描述 |
| :--- | :--- | :--- |
| **所有权与内存安全** | [ownership_model](../../research_notes/formal_methods/ownership_model.md) | 张量内存管理的形式化保证 |
| **类型系统** | [type_system_foundations](../../research_notes/type_theory/type_system_foundations.md) | 泛型张量的类型安全 |
| **Send/Sync** | [send_sync_formalization](../../research_notes/formal_methods/send_sync_formalization.md) | 多线程训练的安全性 |
| **生命周期** | [lifetime_formalization](../../research_notes/formal_methods/lifetime_formalization.md) | 模型引用有效性 |

### 形式化定理

**定理 ML-T1（张量内存安全）**: 若张量操作满足所有权规则 1-8 和借用规则 5-8，则张量内存访问安全。

*证明*: 由 [ownership_model](../../research_notes/formal_methods/ownership_model.md) 定理 T2/T3 和 [borrow_checker_proof](../../research_notes/formal_methods/borrow_checker_proof.md) 定理 T1，张量作为复合类型，其内存安全由内部元素的所有权保证。∎

---

## 🚫 反例速查 {#-反例速查}

### 反例 1: 混淆不同框架的 API

**错误示例**:

```rust
// ❌ Burn 与 Candle 的 Tensor 创建方式不同，不可混用
use burn::tensor::Tensor as BurnTensor;
use candle_core::Tensor as CandleTensor;

fn bad() {
    // 两者类型不兼容，无法直接转换
    let burn_t: BurnTensor<_, 2> = BurnTensor::zeros([3, 3]);
    // let candle_t: CandleTensor = burn_t;  // 编译错误！
}
```

**原因**: Burn、Candle、tch-rs 各自有独立 API 和类型系统，不能混用。

**修正**: 选定一个框架后统一使用其 API，或通过 trait 抽象隔离。

```rust
// ✅ 使用 trait 抽象
pub trait TensorOps {
    fn add(&self, other: &Self) -> Self;
    fn matmul(&self, other: &Self) -> Self;
}

// 为不同框架实现
impl<B: Backend, const D: usize> TensorOps for Tensor<B, D> { ... }
```

---

### 反例 2: 未根据场景选择后端

**错误示例**:

```rust
// ❌ 大模型推理在 CPU 上运行，未考虑 GPU 加速
use candle_core::Device;

fn slow_inference() {
    let device = Device::Cpu;  // CPU 推理极慢
    let model = load_model("llama-7b", &device).unwrap();
    // 7B 参数模型在 CPU 上推理可能需数分钟
}
```

**原因**: 大模型在 CPU 上推理延迟高，生产环境应使用 GPU 或量化。

**修正**: 使用 `Device::Cuda(0)` 或 `llm` 的量化模型。

```rust
// ✅ 选择合适后端
use candle_core::Device;

fn fast_inference() {
    // 优先使用 GPU
    let device = Device::new_cuda(0)
        .unwrap_or(Device::Cpu);

    // 或使用量化模型
    let model = load_quantized_model("llama-7b-q4.gguf").unwrap();
}
```

---

### 反例 3: 忽略依赖版本兼容性

**错误示例**:

```toml
# ❌ 混用不兼容的 burn 与 burn-ndarray 版本
[dependencies]
burn = "0.18"
burn-ndarray = "0.20"  # 版本不一致易导致编译错误
```

**原因**: burn 与 burn-ndarray 需同版本，否则编译失败。

**修正**: 保持主库与后端扩展版本一致。

```toml
# ✅ 使用 workspace 统一版本
[workspace.dependencies]
burn = "0.20"
burn-ndarray = "0.20"
burn-cuda = "0.20"

[dependencies]
burn = { workspace = true }
burn-ndarray = { workspace = true }
```

---

### 反例 4: 内存泄漏 - 循环引用张量缓存

**错误示例**:

```rust
// ❌ 循环引用导致内存泄漏
use std::rc::Rc;
use std::cell::RefCell;

struct TensorCache {
    tensors: RefCell<Vec<Rc<TensorCache>>>,  // 循环引用
}

// a -> b -> a 导致内存无法释放
```

**原因**: Rc 循环引用导致引用计数永不为零。

**修正**: 使用 Weak 打破循环。

```rust
// ✅ 使用 Weak 打破循环
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct TensorCache {
    tensors: RefCell<Vec<Weak<TensorCache>>>,  // Weak 不增加引用计数
}
```

---

### 反例 5: 边界情况 - 空张量操作

**错误示例**:

```rust
// ❌ 未处理空张量
fn normalize(tensor: &Tensor) -> Tensor {
    tensor / tensor.sum()  // 空张量 sum 为 0，导致除零
}
```

**原因**: 空张量或零和导致除零错误。

**修正**: 添加边界检查。

```rust
// ✅ 边界检查
fn normalize(tensor: &Tensor) -> Option<Tensor> {
    let sum = tensor.sum().into_scalar();
    if sum == 0.0 {
        None
    } else {
        Some(tensor / sum)
    }
}
```

---

## 相关文档

- [AI+Rust 生态指南](../../05_guides/AI_RUST_ECOSYSTEM_GUIDE.md)
- [AI 辅助编程](../../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
- [Burn](https://burn.dev/) | [Candle](https://github.com/huggingface/candle) | [llm](https://docs.rs/llm)

## 相关示例代码

AI/ML 示例代码位于指南与外部仓库，可直接参考：

- [AI_RUST_ECOSYSTEM_GUIDE 入门示例](../../05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) - Burn/Candle 最小示例（见「四、入门示例」）
- [Candle examples](https://github.com/huggingface/candle/tree/main/candle-examples)
- [llm 示例](https://github.com/rust-ml/llm/tree/main/examples)
