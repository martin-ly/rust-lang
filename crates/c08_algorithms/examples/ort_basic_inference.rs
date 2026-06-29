//! ort 基础推理示例
//!
//! 本示例演示如何使用 `ort` 加载 ONNX 模型并执行一次前向推理。
//! 运行时需要有效的 ONNX 模型文件路径，可通过 `ORT_MODEL` 环境变量指定；
//! 默认查找当前目录下的 `model.onnx`。
//!
//! 本示例主要用于编译检查，若未提供模型文件将在运行时跳过实际推理。

use ort::session::Session;
use ort::session::builder::GraphOptimizationLevel;
use ort::value::Tensor;

fn main() -> ort::Result<()> {
    let model_path = std::env::var("ORT_MODEL").unwrap_or_else(|_| "model.onnx".into());

    if !std::path::Path::new(&model_path).exists() {
        println!(
            "⚠️  未找到 ONNX 模型文件: {}。请设置 ORT_MODEL 环境变量后重试。",
            model_path
        );
        return Ok(());
    }

    let mut session = Session::builder()?
        .with_optimization_level(GraphOptimizationLevel::Level3)?
        .with_intra_threads(4)?
        .commit_from_file(&model_path)?;

    // 构造一个 1×1×1×1 的 f32 占位输入张量。
    // 实际场景中应根据模型输入 metadata 构造正确形状。
    let input = Tensor::from_array(([1usize, 1, 1, 1], vec![1.0_f32].into_boxed_slice()))?;

    let outputs = session.run(ort::inputs!["input" => input])?;
    let (_shape, data) = outputs[0].try_extract_tensor::<f32>()?;

    println!(
        "✅ 推理成功，输出前 10 个元素: {:?}",
        &data[..data.len().min(10)]
    );

    Ok(())
}
