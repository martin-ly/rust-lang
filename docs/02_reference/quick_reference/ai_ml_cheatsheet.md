# 🤖 Rust AI/ML 速查卡

> **快速参考** | [AI+Rust 生态指南](../../05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) | [AI 辅助编程](../../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
> **最后更新**: 2026-02-13 | **Rust 版本**: 1.93.0+

---

## 📋 目录

- [🤖 Rust AI/ML 速查卡](#-rust-aiml-速查卡)
  - [📋 目录](#-目录)
  - [框架选型](#框架选型)
  - [Burn 快速入门](#burn-快速入门)
  - [Candle 快速入门](#candle-快速入门)
  - [LLM 推理](#llm-推理)
  - [与 C01–C12 关联](#与-c01c12-关联)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 混淆不同框架的 API](#反例-1-混淆不同框架的-api)
    - [反例 2: 未根据场景选择后端](#反例-2-未根据场景选择后端)
    - [反例 3: 忽略依赖版本兼容性](#反例-3-忽略依赖版本兼容性)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)

---

## 框架选型

| 框架 | 适用场景 | 依赖 |
| :--- | :--- | :--- || **Burn** | 动态图、多后端、训练+推理 | burn, burn-ndarray |
| **Candle** | 简洁 API、Hugging Face、推理 | candle-core, candle-nn |
| **llm** | 本地 LLM、CPU 推理 | llm |
| **tch-rs** | PyTorch 生态、LibTorch | tch |

---

## Burn 快速入门

```toml
# Cargo.toml
[dependencies]
burn = "0.20"
burn-ndarray = "0.20"
```

```rust
// 张量创建（需 burn 依赖）
// use burn::tensor::{Tensor, backend::NdArray};
// let t = Tensor::from_floats([[1.0, 2.0], [3.0, 4.0]]);
```

**文档**: [burn.dev](https://burn.dev/)

---

## Candle 快速入门

```toml
# Cargo.toml
[dependencies]
candle-core = "0.8"
candle-nn = "0.8"
```

```rust
// 张量创建（需 candle 依赖）
// use candle_core::Tensor;
// let t = Tensor::new(&[[1.0f32, 2.0], [3.0, 4.0]], &Device::Cpu)?;
```

**文档**: [Candle GitHub](https://github.com/huggingface/candle)

---

## LLM 推理

| 库 | 用途 |
| :--- | :--- || **llm** | 多架构、InferenceSession |
| **mistral.rs** | 高性能、量化、Vision |
| **lm.rs** | 轻量、CPU 优化 |

---

## 与 C01–C12 关联

| 模块 | AI/ML 中的关联 |
| :--- | :--- || C01 所有权 | 张量生命周期、零拷贝 |
| C02 类型系统 | 泛型张量、Trait 抽象 |
| C05 线程 | 多线程训练、数据并行 |
| C06 异步 | 流式推理 |
| C11 宏 | 模型定义 DSL |

---

## 🚫 反例速查

### 反例 1: 混淆不同框架的 API

**错误示例**:

```rust
// ❌ Burn 与 Candle 的 Tensor 创建方式不同，不可混用
// use burn::tensor::Tensor;  // Burn
// use candle_core::Tensor;   // Candle
// let t = Tensor::from_floats(...);  // 不同 crate 的 API 不兼容
```

**原因**: Burn、Candle、tch-rs 各自有独立 API，不能混用。

**修正**: 选定一个框架后统一使用其 API，或通过 trait 抽象隔离。

---

### 反例 2: 未根据场景选择后端

**错误示例**:

```rust
// ❌ 大模型推理在 CPU 上运行，未考虑 GPU 加速
// let model = load_model("llama-7b")?;  // 默认 CPU，推理极慢
```

**原因**: 大模型在 CPU 上推理延迟高，生产环境应使用 GPU 或量化。

**修正**: 使用 `Device::Cuda(0)` 或 `llm` 的量化模型，参考 [AI_RUST_ECOSYSTEM_GUIDE](../../05_guides/AI_RUST_ECOSYSTEM_GUIDE.md)。

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

**修正**: 保持主库与后端扩展版本一致，如 `burn = "0.20"` 与 `burn-ndarray = "0.20"`。

---

## 📚 相关文档

- [AI+Rust 生态指南](../../05_guides/AI_RUST_ECOSYSTEM_GUIDE.md)
- [AI 辅助编程](../../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md)
- [Burn](https://burn.dev/) | [Candle](https://github.com/huggingface/candle) | [llm](https://docs.rs/llm)

## 🧩 相关示例代码

AI/ML 示例代码位于指南与外部仓库，可直接参考：

- [AI_RUST_ECOSYSTEM_GUIDE 入门示例](../../05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) - Burn/Candle 最小示例（见「四、入门示例」）
- [Candle examples](https://github.com/huggingface/candle/tree/main/candle-examples)
- [llm 示例](https://github.com/rust-ml/llm/tree/main/examples)
