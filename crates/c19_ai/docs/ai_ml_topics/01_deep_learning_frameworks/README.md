# 深度学习框架 (Deep Learning Frameworks)

## 概述

本文件夹包含Rust 1.90版本中最成熟和最新的深度学习框架相关内容。

## 主要框架

### 1. Candle (Hugging Face)

- **版本**: 0.9.1 (2025年最新)
- **特点**: 极简主义机器学习框架
- **优势**:
  - 专为LLM推理和生产代码设计
  - 支持CPU和GPU推理
  - 与Hugging Face生态系统深度集成
- **文档**: [Candle官方文档](https://github.com/huggingface/candle)
- **示例**: 见 `examples/` 文件夹

### 2. Burn

- **版本**: 0.13 (2025年最新)
- **特点**: 完全用Rust编写的深度学习框架
- **优势**:
  - 零成本抽象
  - 支持多种后端 (CPU, CUDA, Metal)
  - 灵活的神经网络模块设计
- **文档**: [Burn官方文档](https://github.com/burn-rs/burn)
- **示例**: 见 `examples/` 文件夹

### 3. Tch (PyTorch绑定)

- **版本**: 0.17.0 (2025年最新)
- **特点**: Rust的PyTorch绑定
- **优势**:
  - 完整的PyTorch功能支持
  - 成熟的生态系统
  - 丰富的预训练模型
- **文档**: [Tch官方文档](https://github.com/LaurentMazare/tch-rs)
- **示例**: 见 `examples/` 文件夹

### 4. DFDx

- **版本**: 0.13.0 (2025年最新)
- **特点**: 纯Rust深度学习框架
- **优势**:
  - 类型安全的张量操作
  - 自动微分
  - 编译时优化
- **文档**: [DFDx官方文档](https://github.com/coreylowman/dfdx)
- **示例**: 见 `examples/` 文件夹

## 框架对比

| 框架 | 成熟度 | GPU支持 | 生态 | 学习曲线 | 推荐场景 |
|------|--------|---------|------|----------|----------|
| Candle | 高 | 是 | 丰富 | 中等 | 生产环境、LLM推理 |
| Burn | 中 | 是 | 发展中 | 中等 | 研究、新项目 |
| Tch | 高 | 是 | 非常丰富 | 低 | 需要PyTorch生态 |
| DFDx | 中 | 部分 | 发展中 | 高 | 类型安全要求高 |

## 使用建议

### 生产环境

- **首选**: Candle (稳定、性能好)
- **备选**: Tch (生态丰富)

### 研究环境

- **首选**: Burn (灵活、现代化)
- **备选**: DFDx (类型安全)

### 学习环境

- **首选**: Tch (文档丰富、社区活跃)
- **备选**: Candle (简单易用)

## 文件结构

```text
01_deep_learning_frameworks/
├── README.md                    # 本文件
├── candle/                      # Candle相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   └── benchmarks/             # 性能测试
├── burn/                       # Burn相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   └── benchmarks/             # 性能测试
├── tch/                        # Tch相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   └── benchmarks/             # 性能测试
├── dfdx/                       # DFDx相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   └── benchmarks/             # 性能测试
└── comparison/                 # 框架对比
    ├── performance.md          # 性能对比
    ├── features.md             # 功能对比
    └── use_cases.md            # 使用场景对比
```

## 快速开始

### Candle示例

```rust
use candle_core::{Device, Tensor};
use candle_nn::{linear, Linear, Module};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let device = Device::Cpu;
    let input = Tensor::randn(0f32, 1., (1, 10), &device)?;
    let linear = linear(10, 5, Default::default(), &device)?;
    let output = linear.forward(&input)?;
    println!("输出形状: {:?}", output.shape());
    Ok(())
}
```

### Burn示例

```rust
use burn::{
    config::Config,
    module::{Module, Param},
    nn::{Linear, LinearConfig},
    tensor::{backend::Backend, Tensor},
};

#[derive(Module, Debug)]
pub struct Model<B: Backend> {
    linear: Param<Linear<B>>,
}

impl<B: Backend> Model<B> {
    pub fn new() -> Self {
        Self {
            linear: LinearConfig::new(10, 5).init(),
        }
    }

    pub fn forward(&self, input: Tensor<B, 2>) -> Tensor<B, 2> {
        self.linear.forward(input)
    }
}
```

## 性能优化

1. **GPU加速**: 使用CUDA或Metal后端
2. **批处理**: 合理设置batch size
3. **内存管理**: 使用内存池和缓存
4. **编译优化**: 启用LTO和CPU指令集优化

## 相关资源

- [Rust深度学习生态概览](https://github.com/rust-ai/awesome-rust-ai)
- [深度学习最佳实践](https://github.com/rust-ai/deep-learning-best-practices)
- [性能优化指南](https://github.com/rust-ai/performance-guide)
