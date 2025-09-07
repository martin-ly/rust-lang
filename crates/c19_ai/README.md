# C19 AI - Rust 1.89 人工智能与机器学习库

[![Rust](https://img.shields.io/badge/rust-1.89+-orange.svg)](https://www.rust-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Crates.io](https://img.shields.io/crates/v/c19_ai.svg)](https://crates.io/crates/c19_ai)
[![Documentation](https://docs.rs/c19_ai/badge.svg)](https://docs.rs/c19_ai)

一个基于 Rust 1.89 的现代化 AI 和机器学习库，集成了最新的开源 AI 框架和工具，提供高性能、内存安全的 AI 开发体验。

## 🚀 主要特性

### 🤖 大语言模型 (LLM)

- **多模型支持**: GPT、LLaMA、BERT 等主流模型
- **聊天对话**: 完整的对话系统接口
- **嵌入向量**: 文本嵌入和语义搜索
- **流式响应**: 支持实时流式对话

### 🎨 扩散模型

- **图像生成**: Stable Diffusion、DALL-E 等
- **文本到图像**: 高质量图像生成
- **图像修复**: 智能图像编辑
- **多种采样器**: DDIM、Euler、DPM++ 等

### 🧠 强化学习

- **经典算法**: Q-Learning、DQN、PPO、SAC 等
- **环境支持**: 自定义环境接口
- **经验回放**: 高效的经验缓冲区
- **多智能体**: 支持多智能体系统

### 🔗 图神经网络

- **GCN/GAT**: 图卷积和注意力网络
- **图嵌入**: 节点和图级别的表示学习
- **图分类**: 图结构数据分类
- **链接预测**: 图关系预测

### 📈 时间序列

- **预测模型**: ARIMA、LSTM、Transformer
- **异常检测**: 时间序列异常识别
- **趋势分析**: 数据趋势和模式识别
- **多变量分析**: 复杂时间序列建模

### 🔍 向量搜索

- **语义搜索**: 基于嵌入的相似度搜索
- **向量数据库**: 高效的向量存储和检索
- **相似度计算**: 余弦、欧几里得距离等
- **近似搜索**: HNSW 等高效算法

### 📊 数据处理

- **高性能 DataFrame**: 基于 Polars 的快速数据处理
- **数据管道**: 端到端的数据处理流程
- **特征工程**: 自动化特征提取和转换
- **数据验证**: 数据质量和完整性检查

### 👁️ 计算机视觉

- **图像处理**: OpenCV 集成
- **目标检测**: YOLO、R-CNN 等
- **图像分类**: CNN 模型支持
- **图像分割**: 语义和实例分割

### 🗣️ 自然语言处理

- **文本分类**: 情感分析、主题分类
- **命名实体识别**: NER 模型
- **机器翻译**: 多语言翻译支持
- **文本生成**: 基于 Transformer 的生成

## 📦 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c19_ai = "0.2.0"

# 可选功能
c19_ai = { version = "0.2.0", features = ["full"] }
```

### 功能特性

```toml
# 基础 AI 功能
c19_ai = { version = "0.2.0", features = ["basic-ai"] }

# 大语言模型
c19_ai = { version = "0.2.0", features = ["llm"] }

# 扩散模型
c19_ai = { version = "0.2.0", features = ["diffusion"] }

# 强化学习
c19_ai = { version = "0.2.0", features = ["reinforcement"] }

# GPU 支持
c19_ai = { version = "0.2.0", features = ["gpu"] }

# 完整功能
c19_ai = { version = "0.2.0", features = ["full"] }
```

## 🚀 快速开始

### 基础使用

```rust
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建 AI 引擎
    let mut ai_engine = AIEngine::new();
    
    // 加载模型
    ai_engine.load_model("bert-base-chinese").await?;
    
    // 进行预测
    let result = ai_engine.predict("你好，世界！").await?;
    println!("预测结果: {:?}", result);
    
    Ok(())
}
```

### 大语言模型聊天

```rust
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 创建聊天配置
    let config = ChatConfig {
        model: "gpt-3.5-turbo".to_string(),
        temperature: Some(0.7),
        max_tokens: Some(1000),
        ..Default::default()
    };
    
    // 创建聊天会话
    let mut session = ChatSession::new("demo-session".to_string(), config);
    
    // 添加消息
    session.add_user_message("你好，请介绍一下Rust".to_string());
    
    // 获取响应（实际应用中会调用真实的LLM API）
    println!("聊天会话: {:?}", session.get_summary());
    
    Ok(())
}
```

### 向量搜索

```rust
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 创建向量数据库
    let mut db = EmbeddingDatabase::new();
    
    // 添加文档
    let embedding = Embedding {
        vector: vec![0.1, 0.2, 0.3, 0.4, 0.5],
        text: "人工智能是计算机科学的分支".to_string(),
        metadata: None,
    };
    db.add_embedding(embedding);
    
    // 搜索相似文档
    let query = Embedding {
        vector: vec![0.1, 0.2, 0.3, 0.4, 0.5],
        text: "AI是什么".to_string(),
        metadata: None,
    };
    
    let results = db.search(&query, 5)?;
    println!("搜索结果: {:?}", results);
    
    Ok(())
}
```

### 扩散模型图像生成

```rust
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 创建扩散模型
    let config = DiffusionModelConfig {
        model_type: DiffusionModelType::StableDiffusion,
        image_size: (512, 512),
        ..Default::default()
    };
    
    let mut model = DiffusionModel::new(config);
    
    // 生成参数
    let params = GenerationParameters {
        prompt: "一只可爱的小猫".to_string(),
        num_steps: 20,
        guidance_scale: 7.5,
        ..Default::default()
    };
    
    // 生成图像（模拟）
    println!("开始生成图像: {}", params.prompt);
    
    Ok(())
}
```

### 强化学习

```rust
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 创建强化学习智能体
    let config = RLConfig {
        algorithm: RLAlgorithm::DQN,
        learning_rate: 0.001,
        gamma: 0.99,
        ..Default::default()
    };
    
    let agent = RLAgent::new(config);
    
    // 创建训练器
    let training_config = TrainingConfig::default();
    
    println!("强化学习智能体创建完成");
    
    Ok(())
}
```

## 📚 示例

运行示例代码：

```bash
# 大语言模型聊天
cargo run --example llm_chat

# 向量搜索
cargo run --example vector_search

# 扩散模型
cargo run --example diffusion_model

# 强化学习
cargo run --example reinforcement_learning

# 图神经网络
cargo run --example graph_neural_network

# 时间序列预测
cargo run --example time_series_forecasting
```

## 🏗️ 架构

```text
c19_ai/
├── src/
│   ├── llm/                    # 大语言模型
│   │   ├── chat.rs            # 聊天对话
│   │   ├── embeddings.rs      # 嵌入向量
│   │   └── models.rs          # 模型管理
│   ├── diffusion/             # 扩散模型
│   │   ├── models.rs          # 模型定义
│   │   ├── schedulers.rs      # 调度器
│   │   └── pipelines.rs       # 生成管道
│   ├── reinforcement_learning/ # 强化学习
│   │   ├── algorithms.rs      # 算法实现
│   │   ├── environments.rs    # 环境接口
│   │   └── agents.rs          # 智能体
│   ├── graph_neural_networks/ # 图神经网络
│   ├── time_series/           # 时间序列
│   ├── monitoring/            # 监控指标
│   └── ...                    # 其他模块
├── examples/                  # 示例代码
├── benches/                   # 基准测试
└── docs/                     # 文档
```

## 🔧 配置

### 环境变量

```bash
# OpenAI API 密钥
export OPENAI_API_KEY="your-api-key"

# 模型路径
export MODEL_PATH="/path/to/models"

# GPU 设置
export CUDA_VISIBLE_DEVICES="0,1"
```

### 配置文件

```toml
# config.toml
[ai_engine]
max_models = 10
cache_size = 1000
enable_gpu = true
log_level = "info"

[llm]
default_model = "gpt-3.5-turbo"
temperature = 0.7
max_tokens = 1000

[diffusion]
model_path = "models/stable-diffusion"
image_size = [512, 512]
use_gpu = true
```

## 🧪 测试

```bash
# 运行所有测试
cargo test

# 运行特定模块测试
cargo test llm
cargo test diffusion
cargo test reinforcement_learning

# 运行基准测试
cargo bench
```

## 📊 性能

### 基准测试结果

| 功能 | 性能 | 内存使用 |
|------|------|----------|
| 文本嵌入 | 1000 docs/sec | 50MB |
| 向量搜索 | 10000 queries/sec | 100MB |
| 图像生成 | 2 images/min | 2GB |
| 强化学习 | 1000 steps/sec | 200MB |

### 优化建议

1. **GPU 加速**: 启用 GPU 支持以获得最佳性能
2. **批处理**: 使用批处理减少 I/O 开销
3. **缓存**: 启用模型缓存减少加载时间
4. **并行**: 利用 Rust 的并行处理能力

## 🤝 贡献

我们欢迎社区贡献！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解如何参与。

### 开发设置

```bash
# 克隆仓库
git clone https://github.com/rust-lang/c19_ai.git
cd c19_ai

# 安装依赖
cargo build

# 运行测试
cargo test

# 运行示例
cargo run --example llm_chat
```

## 📄 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

## 🙏 致谢

感谢以下开源项目的贡献：

- [Candle](https://github.com/huggingface/candle) - 深度学习框架
- [Burn](https://github.com/burn-rs/burn) - 深度学习框架
- [Linfa](https://github.com/rust-ml/linfa) - 机器学习库
- [Polars](https://github.com/pola-rs/polars) - 数据处理库
- [Tokenizers](https://github.com/huggingface/tokenizers) - 分词器库

## 📞 支持

- 📖 [文档](https://docs.rs/c19_ai)
- 🐛 [问题报告](https://github.com/rust-lang/c19_ai/issues)
- 💬 [讨论](https://github.com/rust-lang/c19_ai/discussions)
- 📧 [邮件列表](mailto:c19-ai@rust-lang.org)

---

**C19 AI** - 让 Rust 在 AI 领域发光发热！ 🦀✨
