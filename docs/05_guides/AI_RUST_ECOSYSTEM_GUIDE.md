# AI + Rust 生态指南

> **创建日期**: 2026-02-13
> **用途**: Rust 在 AI/ML 领域的生态概览、工具选型与学习路径
> **关联**: [AI 辅助编程指南](../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)

---

## 文档定位

本指南涵盖「AI 辅助 Rust 开发」与「用 Rust 构建 AI/ML 应用」两类场景，帮助开发者选择合适工具并规划学习路径。

---

## 一、AI 辅助 Rust 开发

使用 AI 工具（Cursor、Copilot、Claude 等）高效学习 Rust 与构建项目。

| 主题 | 入口 | 说明 |
| :--- | :--- | :--- || **提示词模板** | [AI_ASSISTED_RUST_PROGRAMMING_GUIDE](../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md) | 概念解释、代码审查、错误修复 |
| **RAG 与项目结合** | 同上 | 速查卡、00_MASTER_INDEX、决策树纳入检索 |
| **错误码上下文** | [ERROR_CODE_MAPPING](../02_reference/ERROR_CODE_MAPPING.md) | 编译错误 → 文档映射 |
| **练习推荐** | [RUSTLINGS_MAPPING](../../exercises/RUSTLINGS_MAPPING.md) | 模块 ↔ 习题对应 |

---

## 二、Rust 构建 AI/ML 应用

### 2.1 深度学习框架

| 框架 | 用途 | 特点 | 链接 |
| :--- | :--- | :--- | :--- || **Burn** | 动态深度学习 | 多后端、JIT 优化、跨平台 | [burn.dev](https://burn.dev/) |
| **Candle** | 神经网络推理/训练 | 简洁 API、Hugging Face 集成 | [GitHub](https://github.com/huggingface/candle) |
| **tch-rs** | PyTorch 绑定 | Rust 调用 LibTorch | [docs.rs](https://docs.rs/crate/tch) |

### 2.2 LLM 推理

| 项目 | 用途 | 特点 |
| :--- | :--- | :--- || **llm** | 本地 LLM 推理 | 多架构（Llama、GPT-J 等）、CPU 友好 |
| **mistral.rs** | 高性能推理 | 模块化、量化、Vision 支持 |
| **lm.rs** | 轻量推理 | CPU 优化、SIMD、rayon |

### 2.3 与 C01–C12 的关联

| 本项目模块 | AI/ML 应用中的关联 |
| :--- | :--- || **C01 所有权** | 张量生命周期、零拷贝、内存管理 |
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

## 四、入门示例（Candle/Burn）

以下代码需在**独立项目**中运行（添加对应依赖）：

### Candle 最小示例

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

### Burn 最小示例

```toml
[dependencies]
burn = { version = "0.20", features = ["train"] }
burn-ndarray = "0.20"
```

详见 [Burn 文档](https://burn.dev/book/) 与 [Candle 示例](https://github.com/huggingface/candle/tree/main/candle-examples)。

---

## 五、RAG 索引建议

将本项目文档纳入 AI 检索时，建议优先索引：

| 文档类型 | 路径 | 用途 |
| :--- | :--- | :--- || 速查卡 | docs/02_reference/quick_reference/*.md | 语法、模式、反例 |
| 主索引 | crates/*/docs/00_MASTER_INDEX.md | 模块导航 |
| 决策树 | docs/04_thinking/DECISION_GRAPH_NETWORK.md | 技术选型 |
| 错误码映射 | docs/02_reference/ERROR_CODE_MAPPING.md | 错误→文档 |
| 官方映射 | docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md | 权威源引用 |

**Embedding 建议**: 按段落或章节分块，chunk size 512–1024 tokens。

---

## 六、后续计划（扩展方向）

| 方向 | 说明 | 优先级 |
| :--- | :--- | :--- || **Candle 入门示例** | 在 examples/ 或新 crate 中增加 Candle 推理示例 | P2 |
| **Burn 入门示例** | 同上 | P2 |
| **LLM 推理速查** | 新增 ai_ml_cheatsheet.md | ✅ 已完成 |
| **AI 工具链集成** | RAG 索引、文档嵌入、语义检索 | P3 |

---

## 七、相关文档

- [AI 辅助编程指南](../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
- [guides/README](../../guides/README.md)
- [官方资源映射](../01_learning/OFFICIAL_RESOURCES_MAPPING.md)
- [Burn](https://burn.dev/) | [Candle](https://github.com/huggingface/candle) | [llm](https://docs.rs/llm)
