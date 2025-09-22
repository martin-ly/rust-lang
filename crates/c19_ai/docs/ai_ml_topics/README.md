# AI/ML 主题文件夹总览

## 概述

本文件夹包含Rust 1.90版本中AI/ML领域的完整技术栈，按主题组织，便于学习和使用。

## 文件夹结构

### 01. 深度学习框架 (Deep Learning Frameworks)

- **Candle**: Hugging Face的极简ML框架
- **Burn**: 纯Rust深度学习框架
- **Tch**: PyTorch Rust绑定
- **DFDx**: 类型安全的深度学习框架

### 02. 机器学习库 (Machine Learning Libraries)

- **Linfa**: Rust的scikit-learn等价物
- **SmartCore**: 纯Rust机器学习库
- **ndarray**: 多维数组库
- **nalgebra**: 线性代数库

### 03. 自然语言处理 (Natural Language Processing)

- **llm-chain**: 大语言模型链式处理框架
- **rust-bert**: BERT模型Rust实现
- **tokenizers**: 高性能分词器
- **whatlang**: 语言检测

### 04. 计算机视觉 (Computer Vision)

- **Kornia-rs**: 高性能3D计算机视觉库
- **OpenCV**: 成熟的计算机视觉库
- **image**: 纯Rust图像处理库
- **imageproc**: 图像处理算法库

### 05. 数据处理 (Data Processing)

- **Polars**: 高性能DataFrame库
- **DataFusion**: 查询执行引擎
- **Arrow**: 列式内存格式
- **Serde**: 序列化和反序列化

### 06. 向量搜索 (Vector Search)

- **Qdrant**: 向量数据库客户端
- **Tantivy**: 全文搜索引擎
- **HNSW-rs**: 分层导航小世界图算法
- **Faiss-rs**: Facebook AI相似性搜索

### 07. 新兴技术 (Emerging Technologies)

- **多模态AI**: 融合多种模态的AI技术
- **联邦学习**: 分布式隐私保护学习
- **边缘AI**: 边缘设备AI部署
- **量子机器学习**: 量子计算与ML结合

### 08. 性能优化 (Performance Optimization)

- **编译优化**: LTO、CPU指令集优化
- **内存优化**: 零拷贝、内存池
- **并行优化**: 多线程、SIMD、GPU加速
- **算法优化**: 高效算法和数据结构

### 09. 安全与隐私 (Security & Privacy)

- **模型安全**: 对抗攻击防护
- **数据安全**: 加密、访问控制
- **隐私保护**: 差分隐私、联邦学习
- **合规性**: GDPR、CCPA等法规遵循

### 10. 生产部署 (Production Deployment)

- **容器化**: Docker、Kubernetes
- **云原生**: AWS、Azure、GCP
- **监控**: 指标收集、日志管理
- **部署策略**: 蓝绿部署、滚动更新

## 技术栈推荐

### 生产环境

```text
深度学习: Candle + Burn
传统ML: Linfa + SmartCore
NLP: llm-chain + rust-bert
计算机视觉: Kornia-rs + OpenCV
数据处理: Polars + DataFusion
向量搜索: Qdrant + HNSW-rs
```

### 研究环境

```text
深度学习: Burn + DFDx
传统ML: SmartCore
NLP: tokenizers + rust-bert
计算机视觉: Kornia-rs
数据处理: Polars
向量搜索: HNSW-rs + Faiss-rs
```

### 学习环境

```text
深度学习: Tch (文档丰富)
传统ML: SmartCore (纯Rust)
NLP: tokenizers + whatlang
计算机视觉: image + imageproc
数据处理: Polars
向量搜索: HNSW-rs (简单)
```

## 快速开始

### 1. 选择技术栈

根据你的需求选择合适的技术栈：

- **生产应用**: 选择成熟稳定的库
- **研究项目**: 选择灵活的研究库
- **学习目的**: 选择文档完善的库

### 2. 安装依赖

在`Cargo.toml`中添加所需依赖：

```toml
[dependencies]
# 深度学习
candle-core = "0.9.1"
candle-nn = "0.9.1"

# 机器学习
linfa = "0.7.1"
smartcore = "0.4.2"

# NLP
llm-chain = "0.13.0"
rust-bert = "0.23.0"

# 计算机视觉
opencv = "0.95.1"
image = "0.25.8"

# 数据处理
polars = "0.50.0"
datafusion = "49.0.2"

# 向量搜索
qdrant-client = "1.15.0"
tantivy = "0.25.0"
```

### 3. 运行示例

每个主题文件夹都包含详细的示例代码：

```bash
# 深度学习示例
cargo run --example deep_learning

# NLP示例
cargo run --example nlp_pipeline

# 计算机视觉示例
cargo run --example computer_vision

# 向量搜索示例
cargo run --example vector_search
```

## 学习路径

### 初学者

1. **基础**: 02_机器学习库 → 05_数据处理
2. **进阶**: 01_深度学习框架 → 03_自然语言处理
3. **应用**: 04_计算机视觉 → 06_向量搜索

### 中级开发者

1. **深度**: 01_深度学习框架 → 07_新兴技术
2. **优化**: 08_性能优化 → 10_生产部署
3. **安全**: 09_安全与隐私

### 高级开发者

1. **研究**: 07_新兴技术 → 01_深度学习框架
2. **架构**: 10_生产部署 → 08_性能优化
3. **创新**: 07_新兴技术 → 09_安全与隐私

## 贡献指南

### 添加新库

1. 在相应主题文件夹中添加库信息
2. 提供示例代码和文档
3. 更新本README文件

### 改进现有内容

1. 更新库版本信息
2. 添加新的示例代码
3. 改进文档和说明

### 报告问题

1. 在GitHub上创建Issue
2. 提供详细的错误信息
3. 包含复现步骤

## 相关资源

- [Rust AI生态](https://github.com/rust-ai/awesome-rust-ai)
- [机器学习最佳实践](https://github.com/rust-ai/ml-best-practices)
- [性能优化指南](https://github.com/rust-ai/performance-guide)
- [安全最佳实践](https://github.com/rust-ai/security-guide)

## 更新日志

### 2025年1月

- 初始版本发布
- 包含10个主要主题
- 支持Rust 1.90
- 集成最新AI/ML库

---

**注意**: 本文件夹内容会持续更新，请定期查看最新版本。如有问题或建议，欢迎提交Issue或Pull Request。
