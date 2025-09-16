//! 向量搜索示例
//!
//! 展示如何使用向量搜索进行语义相似度匹配

use anyhow::Result;
use c19_ai::prelude::*;

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🔍 向量搜索示例");
    println!("================");

    // 创建嵌入向量数据库
    let mut db = EmbeddingDatabase::new();

    // 模拟一些文档和它们的嵌入向量
    let documents = vec![
        (
            "人工智能是计算机科学的一个分支",
            vec![0.8, 0.2, 0.1, 0.9, 0.3],
        ),
        ("机器学习是AI的核心技术", vec![0.7, 0.3, 0.2, 0.8, 0.4]),
        ("深度学习使用神经网络", vec![0.6, 0.4, 0.3, 0.7, 0.5]),
        ("自然语言处理处理文本数据", vec![0.5, 0.5, 0.4, 0.6, 0.6]),
        ("计算机视觉处理图像数据", vec![0.4, 0.6, 0.5, 0.5, 0.7]),
        ("强化学习通过试错学习", vec![0.3, 0.7, 0.6, 0.4, 0.8]),
    ];

    // 添加文档到数据库
    for (text, vector) in documents {
        let embedding = Embedding {
            vector,
            text: text.to_string(),
            metadata: Some(serde_json::json!({
                "category": "AI",
                "language": "zh"
            })),
        };
        db.add_embedding(embedding);
    }

    println!("📚 已添加 {} 个文档到向量数据库", db.size());

    // 测试查询
    let queries = vec!["什么是机器学习？", "如何处理图像？", "神经网络的应用"];

    for query in queries {
        println!("\n🔍 查询: {}", query);

        // 模拟查询向量（实际应用中会通过嵌入模型生成）
        let query_vector = vec![0.6, 0.4, 0.3, 0.7, 0.5]; // 与"深度学习使用神经网络"相似

        let query_embedding = Embedding {
            vector: query_vector,
            text: query.to_string(),
            metadata: None,
        };

        // 搜索最相似的文档
        let results = db.search(&query_embedding, 3)?;

        println!("📋 搜索结果:");
        for (i, (embedding, similarity)) in results.iter().enumerate() {
            println!(
                "  {}. {} (相似度: {:.3})",
                i + 1,
                embedding.text,
                similarity
            );
        }
    }

    // 演示向量相似度计算
    println!("\n🧮 向量相似度计算示例");
    let vec1 = vec![1.0, 0.0, 0.0];
    let vec2 = vec![0.0, 1.0, 0.0];
    let vec3 = vec![1.0, 0.0, 0.0];

    let sim1_2 = EmbeddingUtils::cosine_similarity(&vec1, &vec2)?;
    let sim1_3 = EmbeddingUtils::cosine_similarity(&vec1, &vec3)?;

    println!("向量1与向量2的余弦相似度: {:.3}", sim1_2);
    println!("向量1与向量3的余弦相似度: {:.3}", sim1_3);

    // 演示向量标准化
    let original = vec![3.0, 4.0];
    let normalized = EmbeddingUtils::normalize(&original);
    let norm: f32 = normalized.iter().map(|x| x * x).sum::<f32>().sqrt();

    println!("\n📏 向量标准化示例");
    println!("原始向量: {:?}", original);
    println!("标准化向量: {:?}", normalized);
    println!("标准化后的模长: {:.6}", norm);

    println!("\n✅ 向量搜索示例完成！");
    Ok(())
}
