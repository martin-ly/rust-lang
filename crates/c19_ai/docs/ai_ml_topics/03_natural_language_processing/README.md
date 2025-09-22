# 自然语言处理 (Natural Language Processing)

## 概述

本文件夹包含Rust 1.90版本中最成熟和最新的自然语言处理库相关内容。

## 主要库

### 1. llm-chain

- **版本**: 0.13.0 (2025年最新)
- **特点**: 大语言模型链式处理框架
- **功能**:
  - 多模型支持 (OpenAI, LLaMA, 本地模型)
  - 流式处理
  - 工具调用和函数调用
  - 对话管理
  - 提示工程
- **优势**:
  - 统一的API接口
  - 支持多种LLM提供商
  - 灵活的链式处理
- **文档**: [llm-chain官方文档](https://github.com/sobelio/llm-chain)
- **示例**: 见 `examples/` 文件夹

### 2. rust-bert

- **版本**: 0.23.0 (2025年最新)
- **特点**: BERT模型Rust实现
- **功能**:
  - 预训练模型支持
  - 文本分类
  - 情感分析
  - 命名实体识别
  - 问答系统
  - 文本摘要
- **优势**:
  - 高性能推理
  - 丰富的预训练模型
  - 完整的NLP任务支持
- **文档**: [rust-bert官方文档](https://github.com/guillaume-be/rust-bert)
- **示例**: 见 `examples/` 文件夹

### 3. tokenizers

- **版本**: 0.22.1 (2025年最新)
- **特点**: 高性能分词器
- **功能**:
  - 多种分词算法 (BPE, WordPiece, SentencePiece)
  - 快速处理
  - 多语言支持
  - 自定义词汇表
- **优势**:
  - 与Hugging Face生态集成
  - 高性能实现
  - 丰富的配置选项
- **文档**: [tokenizers官方文档](https://github.com/huggingface/tokenizers)
- **示例**: 见 `examples/` 文件夹

### 4. 其他NLP库

#### whatlang

- **版本**: 0.16.1 (2025年最新)
- **功能**: 语言检测
- **特点**: 快速、准确的语言识别

#### rust-stemmers

- **版本**: 1.2.0 (2025年最新)
- **功能**: 词干提取
- **特点**: 支持多种语言的词干算法

#### regex

- **版本**: 1.10.3 (2025年最新)
- **功能**: 正则表达式
- **特点**: 高性能文本匹配和处理

## 主要任务

### 1. 文本分类

- **情感分析**: 正面/负面情感识别
- **主题分类**: 文档主题自动分类
- **垃圾邮件检测**: 邮件和消息过滤
- **语言检测**: 自动识别文本语言

### 2. 命名实体识别 (NER)

- **人名识别**: 识别文本中的人名
- **地名识别**: 识别地理位置信息
- **机构名识别**: 识别公司、组织名称
- **时间识别**: 识别日期和时间表达

### 3. 文本生成

- **摘要生成**: 自动文本摘要
- **翻译**: 多语言翻译
- **对话生成**: 聊天机器人回复
- **内容创作**: 文章和内容生成

### 4. 问答系统

- **阅读理解**: 基于文档回答问题
- **知识问答**: 基于知识库的问答
- **多轮对话**: 上下文相关的对话
- **事实核查**: 信息真实性验证

## 库对比

| 库 | 成熟度 | 功能范围 | 性能 | 生态 | 推荐场景 |
|----|--------|----------|------|------|----------|
| llm-chain | 高 | 广泛 | 高 | 丰富 | LLM应用开发 |
| rust-bert | 高 | 专业 | 高 | 完善 | 传统NLP任务 |
| tokenizers | 高 | 专业 | 极高 | 丰富 | 文本预处理 |
| whatlang | 中 | 单一 | 高 | 简单 | 语言检测 |
| rust-stemmers | 中 | 单一 | 高 | 简单 | 词干提取 |

## 使用建议

### 生产环境

- **LLM应用**: llm-chain + tokenizers
- **传统NLP**: rust-bert + tokenizers
- **文本处理**: regex + whatlang + rust-stemmers

### 学习环境

- **入门**: tokenizers + whatlang
- **进阶**: rust-bert + llm-chain
- **实践**: 完整的NLP管道

### 研究环境

- **实验**: llm-chain (灵活性)
- **基准测试**: rust-bert (性能)
- **新算法**: 自定义实现

## 文件结构

```text
03_natural_language_processing/
├── README.md                    # 本文件
├── llm_chain/                   # llm-chain相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── providers/              # 提供商集成
│   └── tools/                  # 工具调用
├── rust_bert/                  # rust-bert相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── models/                 # 预训练模型
│   └── tasks/                  # NLP任务
├── tokenizers/                 # tokenizers相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── algorithms/             # 分词算法
│   └── benchmarks/             # 性能测试
├── text_processing/            # 文本处理
│   ├── language_detection/     # 语言检测
│   ├── stemming/               # 词干提取
│   ├── regex/                  # 正则表达式
│   └── normalization/          # 文本标准化
├── nlp_tasks/                  # NLP任务
│   ├── classification/         # 文本分类
│   ├── ner/                    # 命名实体识别
│   ├── generation/             # 文本生成
│   └── qa/                     # 问答系统
└── pipelines/                  # NLP管道
    ├── preprocessing/          # 预处理管道
    ├── inference/              # 推理管道
    └── evaluation/             # 评估管道
```

## 快速开始

### llm-chain示例

```rust
use llm_chain::prelude::*;
use llm_chain_openai::chatgpt::ChatGPT;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建ChatGPT客户端
    let client = ChatGPT::new("your-api-key".to_string());
    
    // 创建对话
    let mut conversation = Conversation::new();
    conversation.add_message(Message::user("你好，请介绍一下Rust".to_string()));
    
    // 获取回复
    let response = client.chat(&conversation).await?;
    println!("回复: {}", response.content);
    
    Ok(())
}
```

### rust-bert示例

```rust
use rust_bert::pipelines::sentiment::SentimentModel;
use rust_bert::pipelines::ner::NERModel;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 情感分析
    let sentiment_model = SentimentModel::new(Default::default())?;
    let input = ["I love Rust programming language!"];
    let output = sentiment_model.predict(&input);
    
    for sentiment in output {
        println!("情感: {:?}", sentiment);
    }
    
    // 命名实体识别
    let ner_model = NERModel::new(Default::default())?;
    let input = ["My name is John and I live in New York."];
    let output = ner_model.predict(&input);
    
    for entities in output {
        for entity in entities {
            println!("实体: {} - {}", entity.word, entity.label);
        }
    }
    
    Ok(())
}
```

### tokenizers示例

```rust
use tokenizers::Tokenizer;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 加载预训练分词器
    let tokenizer = Tokenizer::from_pretrained("bert-base-uncased", None)?;
    
    // 分词
    let encoding = tokenizer.encode("Hello, world!", false)?;
    println!("Token IDs: {:?}", encoding.get_ids());
    println!("Tokens: {:?}", encoding.get_tokens());
    
    // 批量处理
    let texts = vec!["Hello, world!", "How are you?"];
    let encodings = tokenizer.encode_batch(texts, false)?;
    
    for encoding in encodings {
        println!("Tokens: {:?}", encoding.get_tokens());
    }
    
    Ok(())
}
```

## 性能优化

1. **批处理**: 使用批量处理提高吞吐量
2. **缓存**: 缓存分词结果和模型输出
3. **并行处理**: 使用多线程处理多个文档
4. **模型优化**: 使用量化模型减少内存使用
5. **GPU加速**: 利用GPU加速推理

## 最佳实践

1. **文本预处理**: 标准化、清理、分词
2. **模型选择**: 根据任务选择合适的预训练模型
3. **提示工程**: 优化提示词提高LLM性能
4. **错误处理**: 处理网络错误和模型错误
5. **资源管理**: 合理管理内存和计算资源

## 相关资源

- [Rust NLP生态](https://github.com/rust-ai/awesome-rust-nlp)
- [NLP最佳实践](https://github.com/rust-ai/nlp-best-practices)
- [LLM应用开发指南](https://github.com/rust-ai/llm-app-guide)
