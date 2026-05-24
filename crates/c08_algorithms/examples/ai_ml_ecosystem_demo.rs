//! # AI/ML 生态实战演示 —— Candle 极简主义 ML 框架
//!
//! 本示例使用 [Hugging Face Candle](https://github.com/huggingface/candle) 核心库，
//! 演示 Rust 中的张量计算、神经网络前向传播和基础推理模式。
//!
//! ## 运行
//!
//! ```bash
//! cargo run -p c08_algorithms --example ai_ml_ecosystem_demo --features with-candle
//! ```
//!
//! ## 依赖
//!
//! - `candle-core`: 张量运算与自动微分后端
//! - `candle-nn`: 神经网络层与优化器
//!
//! [来源: Candle GitHub / Hugging Face](https://github.com/huggingface/candle)

#![allow(dead_code)]

use anyhow::Result;
use candle_core::{DType, Device, Tensor};
use candle_nn::ops::softmax;
use candle_nn::{Linear, Module};

fn main() -> Result<()> {
    println!("🤖 AI/ML 生态实战演示 —— Candle 框架\n");

    let device = Device::Cpu;

    demo_01_tensor_basics(&device)?;
    demo_02_matrix_operations(&device)?;
    demo_03_simple_neural_network(&device)?;
    demo_04_softmax_classification(&device)?;
    demo_05_linear_regression(&device)?;

    println!("\n✅ AI/ML 演示完成！");
    Ok(())
}

/// ## 演示 1: 张量基础操作
///
/// 展示张量创建、形状变换和索引。
fn demo_01_tensor_basics(device: &Device) -> Result<()> {
    println!("📦 演示 1: 张量基础操作");
    println!("--------------------------");

    // 从切片创建 2x3 张量
    let data: &[f32] = &[1.0, 2.0, 3.0, 4.0, 5.0, 6.0];
    let tensor = Tensor::new(data, device)?.reshape((2, 3))?;
    println!("2x3 张量:\n{}", tensor);

    // 零张量与一张量
    let zeros = Tensor::zeros((2, 2), DType::F32, device)?;
    let ones = Tensor::ones((2, 2), DType::F32, device)?;
    println!("\n零张量:\n{}", zeros);
    println!("一张量:\n{}", ones);

    // 随机张量（正态分布）
    let randn = Tensor::randn(0.0f32, 1.0, (3, 3), device)?;
    println!("\n正态分布随机张量 (3x3):\n{}", randn);

    println!();
    Ok(())
}

/// ## 演示 2: 矩阵运算
///
/// 矩阵乘法、转置和逐元素运算。
fn demo_02_matrix_operations(device: &Device) -> Result<()> {
    println!("🧮 演示 2: 矩阵运算");
    println!("--------------------");

    let a = Tensor::new(&[1.0f32, 2.0, 3.0, 4.0], device)?.reshape((2, 2))?;
    let b = Tensor::new(&[5.0f32, 6.0, 7.0, 8.0], device)?.reshape((2, 2))?;

    println!("矩阵 A:\n{}", a);
    println!("矩阵 B:\n{}", b);

    // 矩阵乘法
    let c = a.matmul(&b)?;
    println!("A × B =\n{}", c);

    // 转置
    let a_t = a.t()?;
    println!("\nA^T:\n{}", a_t);

    // 逐元素乘法和加法
    let elem_mul = (&a * &b)?;
    let elem_add = (&a + &b)?;
    println!("\n逐元素乘法 (A .* B):\n{}", elem_mul);
    println!("逐元素加法 (A .+ B):\n{}", elem_add);

    println!();
    Ok(())
}

/// ## 演示 3: 简单神经网络前向传播
///
/// 使用 `candle_nn::Linear` 构建两层 MLP，执行前向传播。
fn demo_03_simple_neural_network(device: &Device) -> Result<()> {
    println!("🧠 演示 3: 简单神经网络前向传播");
    println!("---------------------------------");

    // 输入: 4 个样本，每个 3 维特征
    let input = Tensor::new(
        &[
            0.5f32, 0.2, 0.1, 0.9, 0.7, 0.3, 0.1, 0.4, 0.8, 0.3, 0.6, 0.2,
        ],
        device,
    )?
    .reshape((4, 3))?;

    println!("输入 (4 samples × 3 features):\n{}", input);

    // 第一层: 3 -> 5
    let weight_1 = Tensor::new(
        &[
            0.1f32, 0.2, 0.3, 0.4, 0.5, 0.2, 0.3, 0.4, 0.5, 0.6, 0.3, 0.4, 0.5, 0.6, 0.7,
        ],
        device,
    )?
    .reshape((3, 5))?;
    let bias_1 = Tensor::new(&[0.1f32, 0.1, 0.1, 0.1, 0.1], device)?;
    let linear_1 = Linear::new(weight_1, Some(bias_1));

    let hidden = linear_1.forward(&input)?;
    println!("\n隐藏层输出 (4 × 5):\n{}", hidden);

    // ReLU 激活: max(0, x)
    let relu = hidden.relu()?;
    println!("\nReLU 激活后:\n{}", relu);

    // 第二层: 5 -> 2
    let weight_2 = Tensor::new(
        &[0.1f32, 0.2, 0.2, 0.3, 0.3, 0.4, 0.4, 0.5, 0.5, 0.6],
        device,
    )?
    .reshape((5, 2))?;
    let bias_2 = Tensor::new(&[0.05f32, 0.05], device)?;
    let linear_2 = Linear::new(weight_2, Some(bias_2));

    let output = linear_2.forward(&relu)?;
    println!("\n最终输出 (4 × 2):\n{}", output);

    println!();
    Ok(())
}

/// ## 演示 4: Softmax 分类
///
/// 将原始 logits 转换为概率分布。
fn demo_04_softmax_classification(device: &Device) -> Result<()> {
    println!("📊 演示 4: Softmax 分类");
    println!("-----------------------");

    // 模拟 3 个样本、4 个类别的 logits
    let logits = Tensor::new(
        &[
            2.0f32, 1.0, 0.1, 0.5, 0.5, 2.5, 1.0, 0.2, 1.0, 0.5, 2.0, 0.3,
        ],
        device,
    )?
    .reshape((3, 4))?;

    println!("原始 logits (3 samples × 4 classes):\n{}", logits);

    let probs = softmax(&logits, 1)?;
    println!("\nSoftmax 概率分布:\n{}", probs);

    // 验证概率和为 1
    let sum_probs = probs.sum(1)?;
    println!("\n每行概率之和 (应接近 1.0):\n{}", sum_probs);

    println!();
    Ok(())
}

/// ## 演示 5: 线性回归
///
/// 手动实现梯度下降训练一个简单的线性模型。
fn demo_05_linear_regression(device: &Device) -> Result<()> {
    println!("📈 演示 5: 线性回归训练");
    println!("------------------------");

    // 合成数据: y = 2x + 1 + noise
    let x = Tensor::new(&[1.0f32, 2.0, 3.0, 4.0, 5.0], device)?.reshape((5, 1))?;
    let y_true = Tensor::new(&[3.1f32, 5.0, 6.9, 9.2, 10.8], device)?.reshape((5, 1))?;

    println!("输入 x:\n{}", x);
    println!("目标 y:\n{}", y_true);

    // 初始化参数
    let mut weight = Tensor::new(&[0.0f32], device)?.reshape((1, 1))?;
    let mut bias = Tensor::new(&[0.0f32], device)?;

    let learning_rate = 0.05f64;
    let epochs = 100;

    for epoch in 0..epochs {
        // 前向传播: y_pred = x * w + b
        let y_pred = x.matmul(&weight)?.broadcast_add(&bias)?;

        // 计算 MSE 损失
        let diff = (&y_pred - &y_true)?;
        let loss = (&diff * &diff)?.mean(0)?.mean(0)?;

        if epoch % 20 == 0 {
            println!("Epoch {:3}: loss = {:.4}", epoch, loss.to_scalar::<f32>()?);
        }

        // 手动梯度计算（简化版）
        // dw = (2/n) * x^T * (y_pred - y_true)
        // db = (2/n) * sum(y_pred - y_true)
        let n = x.dim(0)? as f32;
        let scale = Tensor::new(&[2.0 / n * learning_rate as f32], device)?;

        let grad_w = x.t()?.matmul(&diff)?;
        let grad_w = grad_w.broadcast_mul(&scale)?;

        let grad_b_temp = diff.sum(0)?;
        let grad_b = grad_b_temp.broadcast_mul(&scale)?;

        // 参数更新
        weight = (&weight - &grad_w)?;
        bias = (&bias - &grad_b)?;
    }

    println!("\n训练完成!");
    println!("学习到的权重 w ≈ 2.0: {:.4}", weight.to_scalar::<f32>()?);
    println!("学习到的偏置 b ≈ 1.0: {:.4}", bias.to_scalar::<f32>()?);

    // 预测
    let y_pred = x.matmul(&weight)?.broadcast_add(&bias)?;
    println!("\n预测值:\n{}", y_pred);

    println!();
    Ok(())
}
