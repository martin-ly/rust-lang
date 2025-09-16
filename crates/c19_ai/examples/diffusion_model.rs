//! 扩散模型示例
//!
//! 展示如何使用扩散模型进行图像生成

use anyhow::Result;
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🎨 扩散模型图像生成示例");
    println!("========================");

    // 创建扩散模型配置
    let config = DiffusionModelConfig {
        model_type: DiffusionModelType::StableDiffusion,
        model_path: "models/stable-diffusion-v1-5".to_string(),
        image_size: (512, 512),
        channels: 3,
        use_gpu: true,
        precision: Precision::Float32,
    };

    // 创建扩散模型
    let mut model = DiffusionModel::new(config);

    println!("🤖 扩散模型配置:");
    println!("  模型类型: {:?}", model.get_config().model_type);
    println!("  图像尺寸: {:?}", model.get_config().image_size);
    println!("  使用GPU: {}", model.get_config().use_gpu);

    // 模拟加载模型权重
    model.load_weights("models/stable-diffusion-v1-5.safetensors")?;
    println!("✅ 模型权重加载完成");

    // 定义生成参数
    let generation_params = vec![
        GenerationParameters {
            prompt: "一只可爱的小猫坐在花园里".to_string(),
            negative_prompt: Some("模糊，低质量".to_string()),
            num_steps: 20,
            guidance_scale: 7.5,
            seed: Some(42),
            sampler: SamplerType::Ddim,
        },
        GenerationParameters {
            prompt: "未来主义的城市景观，霓虹灯，赛博朋克风格".to_string(),
            negative_prompt: Some("黑暗，恐怖".to_string()),
            num_steps: 30,
            guidance_scale: 8.0,
            seed: Some(123),
            sampler: SamplerType::Euler,
        },
        GenerationParameters {
            prompt: "梵高风格的向日葵画作".to_string(),
            negative_prompt: None,
            num_steps: 25,
            guidance_scale: 7.0,
            seed: Some(456),
            sampler: SamplerType::DpmPlusPlus,
        },
    ];

    // 生成图像
    for (i, params) in generation_params.iter().enumerate() {
        println!("\n🎨 生成图像 {}: {}", i + 1, params.prompt);
        println!("  步数: {}", params.num_steps);
        println!("  引导强度: {}", params.guidance_scale);
        println!("  采样器: {:?}", params.sampler);

        // 模拟图像生成过程
        let generated_image = simulate_image_generation(params)?;

        println!("✅ 图像生成完成");
        println!("  图像尺寸: {:?}", generated_image.size);
        println!(
            "  生成时间: {:.2}秒",
            generated_image.metadata["generation_time"]
        );

        // 模拟保存图像
        let filename = format!("generated_image_{}.png", i + 1);
        println!("💾 图像已保存为: {}", filename);
    }

    // 演示不同的采样器
    println!("\n🔄 采样器比较");
    let samplers = vec![
        SamplerType::Ddim,
        SamplerType::Euler,
        SamplerType::Heun,
        SamplerType::DpmPlusPlus,
    ];

    for sampler in samplers {
        let params = GenerationParameters {
            prompt: "测试图像".to_string(),
            num_steps: 20,
            guidance_scale: 7.5,
            sampler: sampler.clone(),
            ..Default::default()
        };

        let start_time = std::time::Instant::now();
        let _image = simulate_image_generation(&params)?;
        let duration = start_time.elapsed();

        println!("  {:?}: {:.2}秒", sampler, duration.as_secs_f64());
    }

    println!("\n✅ 扩散模型示例完成！");
    Ok(())
}

/// 模拟图像生成过程
fn simulate_image_generation(params: &GenerationParameters) -> Result<GeneratedImage> {
    let start_time = std::time::Instant::now();

    // 模拟生成过程
    std::thread::sleep(std::time::Duration::from_millis(100));

    let generation_time = start_time.elapsed().as_secs_f64();

    // 创建模拟的图像数据
    let image_data = ndarray::Array3::zeros((512, 512, 3));

    let metadata = serde_json::json!({
        "generation_time": generation_time,
        "model_version": "stable-diffusion-v1-5",
        "parameters": params
    });

    Ok(GeneratedImage {
        data: image_data,
        size: (512, 512),
        parameters: params.clone(),
        metadata,
    })
}
