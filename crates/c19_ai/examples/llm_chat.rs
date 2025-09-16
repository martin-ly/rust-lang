//! 大语言模型聊天示例
//!
//! 展示如何使用 LLM 进行对话

use anyhow::Result;
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🤖 大语言模型聊天示例");
    println!("========================");

    // 创建聊天配置
    let config = ChatConfig {
        model: "gpt-3.5-turbo".to_string(),
        temperature: Some(0.7),
        max_tokens: Some(1000),
        system_prompt: Some("你是一个有用的AI助手，请用中文回答问题。".to_string()),
        ..Default::default()
    };

    // 创建聊天会话
    let mut session = ChatSession::new("demo-session".to_string(), config);

    // 添加系统消息
    session.add_system_message("你好！我是你的AI助手，有什么可以帮助你的吗？".to_string());

    // 模拟对话
    let user_messages = vec![
        "你好，请介绍一下Rust编程语言",
        "Rust在AI领域有什么优势？",
        "能给我一个简单的Rust AI代码示例吗？",
    ];

    for (i, user_msg) in user_messages.iter().enumerate() {
        println!("\n👤 用户: {}", user_msg);

        // 添加用户消息
        session.add_user_message(user_msg.to_string());

        // 模拟AI响应（实际应用中会调用真实的LLM API）
        let ai_response = generate_ai_response(user_msg, i);
        println!("🤖 AI: {}", ai_response);

        // 添加AI响应
        session.add_assistant_message(ai_response);

        // 显示会话摘要
        let summary = session.get_summary();
        println!("📊 会话摘要: {} 条消息", summary.message_count);
    }

    println!("\n✅ 聊天示例完成！");
    Ok(())
}

/// 生成AI响应（模拟）
fn generate_ai_response(user_message: &str, index: usize) -> String {
    match index {
        0 => "Rust是一种系统编程语言，专注于安全性、速度和并发性。它通过所有权系统在编译时防止内存错误，同时提供零成本抽象。Rust特别适合构建高性能、安全的系统软件。".to_string(),
        1 => "Rust在AI领域的优势包括：1) 内存安全，避免数据竞争；2) 高性能，接近C/C++的速度；3) 优秀的并发支持；4) 丰富的生态系统，如Candle、Burn等深度学习框架；5) 与Python的良好互操作性。".to_string(),
        2 => "这里是一个简单的Rust AI代码示例：\n\n```rust\nuse candle_core::{Device, Tensor};\nuse candle_nn::{linear, Linear, Module};\n\nfn main() -> Result<(), Box<dyn std::error::Error>> {\n    let device = Device::Cpu;\n    let input = Tensor::randn(0f32, 1., (1, 784), &device)?;\n    let linear = linear(784, 10, &device)?;\n    let output = linear.forward(&input)?;\n    println!(\"输出形状: {:?}\", output.shape());\n    Ok(())\n}\n```".to_string(),
        _ => "感谢你的问题！如果你还有其他问题，我很乐意帮助你。".to_string(),
    }
}
