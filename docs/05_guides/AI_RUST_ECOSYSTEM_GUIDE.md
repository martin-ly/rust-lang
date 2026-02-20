# AI + Rust 生态指南

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 文档定位

本指南涵盖「AI 辅助 Rust 开发」与「用 Rust 构建 AI/ML 应用」两类场景，帮助开发者选择合适工具并规划学习路径。

---

## 一、AI 辅助 Rust 开发

使用 AI 工具（Cursor、Copilot、Claude 等）高效学习 Rust 与构建项目。

| 主题 | 入口 | 说明 |
| :--- | :--- | :--- |
| **提示词模板** | [AI_ASSISTED_RUST_PROGRAMMING_GUIDE](../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md) | 概念解释、代码审查、错误修复 |
| **RAG 与项目结合** | 同上 | 速查卡、00_MASTER_INDEX、决策树纳入检索 |
| **错误码上下文** | [ERROR_CODE_MAPPING](../02_reference/ERROR_CODE_MAPPING.md) | 编译错误 → 文档映射 |
| **练习推荐** | [RUSTLINGS_MAPPING](../../exercises/RUSTLINGS_MAPPING.md) | 模块 ↔ 习题对应 |

---

## 二、Rust 构建 AI/ML 应用

### 2.1 深度学习框架

| 框架 | 用途 | 特点 | 链接 |
| :--- | :--- | :--- | :--- |
| **Burn** | 动态深度学习 | 多后端、JIT 优化、跨平台 | [burn.dev](https://burn.dev/) |
| **Candle** | 神经网络推理/训练 | 简洁 API、Hugging Face 集成 | [GitHub](https://github.com/huggingface/candle) |
| **tch-rs** | PyTorch 绑定 | Rust 调用 LibTorch | [docs.rs](https://docs.rs/crate/tch) |

### 2.2 LLM 推理

| 项目 | 用途 | 特点 |
| :--- | :--- | :--- |
| **llm** | 本地 LLM 推理 | 多架构（Llama、GPT-J 等）、CPU 友好 |
| **mistral.rs** | 高性能推理 | 模块化、量化、Vision 支持 |
| **lm.rs** | 轻量推理 | CPU 优化、SIMD、rayon |

### 2.3 与 C01–C12 的关联

| 本项目模块 | AI/ML 应用中的关联 |
| :--- | :--- |
| **C01 所有权** | 张量生命周期、零拷贝、内存管理 |
| **C02 类型系统** | 泛型张量、Trait 抽象 |
| **C05** | 多线程训练、数据并行 |
| **C06 异步** | 流式推理、异步 I/O |
| **C11 宏** | 模型定义 DSL |

---

## 三、推荐学习路径

### 路径 A：AI 辅助学 Rust（先 AI 后 Rust）

1. 使用 [AI_ASSISTED_RUST_PROGRAMMING_GUIDE](../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md) 的提示词模板
2. 结合 [RUSTLINGS_MAPPING](../../exercises/RUSTLINGS_MAPPING.md) 让 AI 推荐习题
3. 遇到错误时附带 [ERROR_CODE_MAPPING](../02_reference/ERROR_CODE_MAPPING.md)

### 路径 B：Rust 构建 AI（先 Rust 后 AI）

1. 掌握 C01–C03、C04 泛型
2. 学习 Candle 或 Burn 入门教程
3. 实践：用 Candle 加载简单模型做推理

### 路径 C：AI + Rust 双轨

1. 用 AI 辅助学习 Rust 核心
2. 用 Rust 实现 AI 推理/训练脚本
3. 集成到生产：WASM 部署、边缘推理

---

## 四、入门示例

### 4.1 Candle 最小示例

```toml
# 新建项目: cargo new candle_demo && cd candle_demo
[dependencies]
candle-core = "0.8"
candle-nn = "0.8"
```

```rust
use candle_core::{Device, Tensor};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let device = Device::Cpu;
    let a = Tensor::new(&[[1.0f32, 2.0], [3.0, 4.0]], &device)?;
    let b = a.matmul(&a)?;
    println!("{:?}", b.to_vec2::<f32>()?);
    Ok(())
}
```

### 4.2 Candle 神经网络推理

```rust
use candle_core::{DType, Device, Tensor};
use candle_nn::{Module, Linear, VarBuilder, VarMap};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let device = Device::Cpu;
    let varmap = VarMap::new();
    let vb = VarBuilder::from_varmap(&varmap, DType::F32, &device);
    
    // 创建一个简单的线性层
    let linear = Linear::new(
        vb.get((784, 10), "weight")?,
        Some(vb.get(10, "bias")?),
    );
    
    // 创建输入数据 (batch_size=1, features=784)
    let input = Tensor::zeros((1, 784), DType::F32, &device)?;
    
    // 前向传播
    let output = linear.forward(&input)?;
    println!("输出形状: {:?}", output.shape());
    
    Ok(())
}
```

### 4.3 Burn 最小示例

```toml
[dependencies]
burn = { version = "0.20", features = ["train"] }
burn-ndarray = "0.20"
```

```rust
use burn::tensor::Tensor;
use burn_ndarray::NdArrayBackend;

type Backend = NdArrayBackend<f32>;

fn main() {
    let device = Default::default();
    
    // 创建张量
    let tensor1: Tensor<Backend, 2> = Tensor::from_floats([
        [1.0, 2.0, 3.0],
        [4.0, 5.0, 6.0],
    ], &device);
    
    let tensor2: Tensor<Backend, 2> = Tensor::from_floats([
        [7.0, 8.0, 9.0],
        [10.0, 11.0, 12.0],
    ], &device);
    
    // 张量运算
    let sum = tensor1.clone() + tensor2.clone();
    let product = tensor1.matmul(tensor2.transpose());
    
    println!("Sum: {:?}", sum.to_data());
    println!("Product: {:?}", product.to_data());
}
```

### 4.4 使用 Candle 加载预训练模型

```rust
use candle_core::{Device, Tensor};
use candle_nn::Module;
use candle_transformers::models::bert::{BertModel, Config, DTYPE};
use tokenizers::Tokenizer;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let device = Device::Cpu;
    
    // 加载 tokenizer
    let tokenizer = Tokenizer::from_file("tokenizer.json")?;
    
    // 编码文本
    let encoding = tokenizer.encode("Hello, world!", true)?;
    let input_ids = Tensor::new(&encoding.get_ids(), &device)?;
    
    // 加载模型配置和权重
    let config = Config::from_file("config.json")?;
    let weights = candle_core::safetensors::load("model.safetensors", &device)?;
    
    // 创建模型
    let model = BertModel::load(weights, &config)?;
    
    // 推理
    let embeddings = model.forward(&input_ids.unsqueeze(0)?, None)?;
    println!("嵌入形状: {:?}", embeddings.shape());
    
    Ok(())
}
```

### 4.5 本地 LLM 推理 (llm crate)

```toml
[dependencies]
llm = { git = "https://github.com/rustformers/llm" }
```

```rust
use llm::Model;

fn main() -> Result<(), Box<dyn std::error::Error>> {
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
    let prompt = "Once upon a time,";
    let mut output = String::new();
    
    session.infer::<std::convert::Infallible>(
        model.as_ref(),
        &mut rand::thread_rng(),
        &llm::InferenceRequest {
            prompt: prompt.into(),
            parameters: &llm::InferenceParameters::default(),
            play_back_previous_tokens: false,
            maximum_token_count: Some(100),
        },
        &mut Default::default(),
        |r| match r {
            llm::InferenceResponse::PromptToken(t) | llm::InferenceResponse::InferredToken(t) => {
                output.push_str(&t);
                Ok(llm::InferenceFeedback::Continue)
            }
            _ => Ok(llm::InferenceFeedback::Continue),
        },
    )?;
    
    println!("{}", output);
    Ok(())
}
```

### 4.6 并发数据加载器

```rust
use std::sync::{Arc, Mutex};
use std::thread;

struct DataLoader {
    data: Arc<Mutex<Vec<Vec<f32>>>>,
    batch_size: usize,
    current_index: Arc<Mutex<usize>>,
}

impl DataLoader {
    fn new(data: Vec<Vec<f32>>, batch_size: usize) -> Self {
        DataLoader {
            data: Arc::new(Mutex::new(data)),
            batch_size,
            current_index: Arc::new(Mutex::new(0)),
        }
    }
    
    fn next_batch(&self) -> Option<Vec<Vec<f32>>> {
        let mut idx = self.current_index.lock().ok()?;
        let data = self.data.lock().ok()?;
        
        if *idx >= data.len() {
            return None;
        }
        
        let end = (*idx + self.batch_size).min(data.len());
        let batch: Vec<Vec<f32>> = data[*idx..end].to_vec();
        *idx = end;
        
        Some(batch)
    }
}

// 并行预处理
fn parallel_preprocess(data: Vec<String>) -> Vec<Vec<f32>> {
    use rayon::prelude::*;
    
    data.par_iter()
        .map(|text| tokenize_and_embed(text))
        .collect()
}

fn tokenize_and_embed(text: &str) -> Vec<f32> {
    // 简化的 tokenization
    text.chars()
        .map(|c| c as u8 as f32 / 255.0)
        .take(100)
        .collect()
}
```

---

## 五、RAG 索引建议

将本项目文档纳入 AI 检索时，建议优先索引：

| 文档类型 | 路径 | 用途 |
| :--- | :--- | :--- |
| 速查卡 | docs/02_reference/quick_reference/*.md | 语法、模式、反例 |
| 主索引 | crates/*/docs/00_MASTER_INDEX.md | 模块导航 |
| 决策树 | docs/04_thinking/DECISION_GRAPH_NETWORK.md | 技术选型 |
| 错误码映射 | docs/02_reference/ERROR_CODE_MAPPING.md | 错误→文档 |
| 官方映射 | docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md | 权威源引用 |

**Embedding 建议**: 按段落或章节分块，chunk size 512–1024 tokens。

---

## 六、最佳实践

### 6.1 内存管理

```rust
use candle_core::{Device, Tensor};

fn process_large_tensor() -> candle_core::Result<()> {
    let device = Device::Cpu;
    
    // 使用 no_grad 上下文避免保存梯度
    {
        let input = Tensor::zeros((1000, 1000), candle_core::DType::F32, &device)?;
        let output = input.matmul(&input)?;
        println!("输出: {:?}", output.shape());
    } // 张量在这里被释放
    
    Ok(())
}
```

### 6.2 批量处理

```rust
fn batch_inference(model: &dyn Model, inputs: &[Tensor]) -> Vec<Tensor> {
    const BATCH_SIZE: usize = 32;
    
    inputs
        .chunks(BATCH_SIZE)
        .map(|batch| {
            let batched = Tensor::stack(batch, 0).unwrap();
            model.forward(&batched)
        })
        .collect()
}
```

### 6.3 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
enum AIError {
    #[error("模型加载错误: {0}")]
    ModelLoad(String),
    
    #[error("推理错误: {0}")]
    Inference(String),
    
    #[error("张量错误: {0}")]
    Tensor(#[from] candle_core::Error),
}

type Result<T> = std::result::Result<T, AIError>;
```

---

## 七、后续计划（扩展方向）

| 方向 | 说明 | 优先级 |
| :--- | :--- | :--- |
| **Candle 入门示例** | 在 examples/ 或新 crate 中增加 Candle 推理示例 | P2 |
| **Burn 入门示例** | 同上 | P2 |
| **LLM 推理速查** | 新增 ai_ml_cheatsheet.md | ✅ 已完成 |
| **AI 工具链集成** | RAG 索引、文档嵌入、语义检索 | P3 |

---

## 八、相关文档

- [AI 辅助编程指南](../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
- [guides/README](../../guides/README.md)
- [官方资源映射](../01_learning/OFFICIAL_RESOURCES_MAPPING.md)
- [Burn](https://burn.dev/) | [Candle](https://github.com/huggingface/candle) | [llm](https://docs.rs/llm)
- [BEST_PRACTICES.md](./BEST_PRACTICES.md)
- [PERFORMANCE_TUNING_GUIDE.md](./PERFORMANCE_TUNING_GUIDE.md)
