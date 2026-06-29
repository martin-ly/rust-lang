//! tract 基础推理示例
//!
//! 本示例演示如何使用 `tract-onnx` 加载 ONNX 模型并执行一次前向推理。
//! 运行时需要有效的 ONNX 模型文件路径，可通过 `TRACT_MODEL` 环境变量指定；
//! 默认查找当前目录下的 `model.onnx`。
//!
//! 本示例主要用于编译检查，若未提供模型文件将在运行时跳过实际推理。

use tract_onnx::prelude::*;

fn main() -> TractResult<()> {
    let model_path = std::env::var("TRACT_MODEL").unwrap_or_else(|_| "model.onnx".into());

    if !std::path::Path::new(&model_path).exists() {
        println!(
            "⚠️  未找到 ONNX 模型文件: {}。请设置 TRACT_MODEL 环境变量后重试。",
            model_path
        );
        return Ok(());
    }

    // 加载并优化模型，生成可执行计划。
    let model = tract_onnx::onnx()
        .model_for_path(&model_path)?
        .into_optimized()?
        .into_runnable()?;

    // 构造一个 1 维 f32 占位输入张量。
    // 实际场景中应根据模型输入 metadata 构造正确形状。
    let input = tensor1(&[1.0_f32]);

    let result = model.run(tvec![input.into()])?;
    let output = result[0].to_plain_array_view::<f32>()?;

    println!(
        "✅ 推理成功，输出前 10 个元素: {:?}",
        &output.iter().take(10).collect::<Vec<_>>()
    );

    Ok(())
}
