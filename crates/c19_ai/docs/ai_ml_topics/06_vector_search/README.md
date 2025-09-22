# 向量搜索 (Vector Search)

## 概述

本文件夹包含Rust 1.90版本中最成熟和最新的向量搜索和向量数据库相关内容。

## 主要库

### 1. Qdrant Client

- **版本**: 1.15.0 (2025年最新)
- **特点**: 向量数据库客户端
- **功能**:
  - 高效向量搜索和检索
  - 过滤和条件查询
  - 分布式向量存储
  - 实时索引更新
  - 多种距离度量
- **优势**:
  - 高性能向量搜索
  - 丰富的查询功能
  - 可扩展架构
  - 生产就绪
- **文档**: [Qdrant官方文档](https://github.com/qdrant/qdrant)
- **示例**: 见 `examples/` 文件夹

### 2. Tantivy

- **版本**: 0.25.0 (2025年最新)
- **特点**: 全文搜索引擎
- **功能**:
  - 快速全文搜索
  - 复杂查询支持
  - 多语言支持
  - 实时索引
  - 分布式搜索
- **优势**:
  - 高性能搜索
  - 丰富的查询语法
  - 内存效率高
  - 易于集成
- **文档**: [Tantivy官方文档](https://github.com/quickwit-oss/tantivy)
- **示例**: 见 `examples/` 文件夹

### 3. HNSW-rs

- **版本**: 0.3.2 (2025年最新)
- **特点**: 分层导航小世界图算法
- **功能**:
  - 近似最近邻搜索
  - 高维向量搜索
  - 内存和磁盘存储
  - 动态索引更新
- **优势**:
  - 高效的近似搜索
  - 支持高维向量
  - 内存使用可控
- **文档**: [HNSW-rs官方文档](https://github.com/rust-cv/hnsw)
- **示例**: 见 `examples/` 文件夹

### 4. 其他向量搜索库

#### Faiss-rs

- **版本**: 最新
- **功能**: Facebook AI相似性搜索
- **特点**: 高性能向量搜索

#### Annoy-rs

- **版本**: 最新
- **功能**: 近似最近邻搜索
- **特点**: 内存映射索引

## 主要任务

### 1. 语义搜索

- **文本嵌入**: 将文本转换为向量表示
- **相似度计算**: 计算向量间相似度
- **检索排序**: 按相似度排序结果
- **多模态搜索**: 文本、图像、音频搜索

### 2. 推荐系统

- **协同过滤**: 基于用户行为的推荐
- **内容推荐**: 基于内容相似度的推荐
- **混合推荐**: 结合多种推荐策略
- **实时推荐**: 实时更新推荐结果

### 3. 图像搜索

- **特征提取**: 提取图像特征向量
- **相似图像**: 查找相似图像
- **以图搜图**: 基于图像内容搜索
- **图像聚类**: 图像自动分组

### 4. 知识图谱

- **实体嵌入**: 实体向量表示
- **关系预测**: 预测实体间关系
- **图遍历**: 图结构搜索
- **知识推理**: 基于向量的推理

## 库对比

| 库 | 成熟度 | 性能 | 功能范围 | 扩展性 | 推荐场景 |
|----|--------|------|----------|--------|----------|
| Qdrant | 高 | 高 | 广泛 | 高 | 生产环境、大规模应用 |
| Tantivy | 高 | 高 | 全文搜索 | 中 | 文档搜索、文本检索 |
| HNSW-rs | 中 | 高 | 向量搜索 | 中 | 高维向量搜索 |
| Faiss-rs | 高 | 极高 | 向量搜索 | 高 | 研究、高性能需求 |

## 使用建议

### 生产环境

- **向量搜索**: Qdrant + HNSW-rs
- **全文搜索**: Tantivy
- **混合搜索**: Qdrant + Tantivy

### 研究环境

- **算法研究**: HNSW-rs + Faiss-rs
- **性能测试**: 多种库对比

### 学习环境

- **入门**: HNSW-rs (简单)
- **进阶**: Qdrant (功能丰富)

## 文件结构

```text
06_vector_search/
├── README.md                    # 本文件
├── qdrant/                      # Qdrant相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── collections/            # 集合管理
│   ├── search/                 # 搜索功能
│   └── clustering/             # 聚类
├── tantivy/                    # Tantivy相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── indexing/               # 索引构建
│   ├── querying/               # 查询处理
│   └── analyzers/              # 分析器
├── hnsw/                       # HNSW相关
│   ├── examples/               # 示例代码
│   ├── docs/                   # 文档
│   ├── indexing/               # 索引构建
│   ├── search/                 # 搜索算法
│   └── optimization/           # 性能优化
├── embeddings/                 # 嵌入向量
│   ├── text/                   # 文本嵌入
│   ├── image/                  # 图像嵌入
│   ├── multimodal/             # 多模态嵌入
│   └── custom/                 # 自定义嵌入
├── similarity/                 # 相似度计算
│   ├── cosine/                 # 余弦相似度
│   ├── euclidean/              # 欧几里得距离
│   ├── manhattan/              # 曼哈顿距离
│   └── custom/                 # 自定义距离
├── applications/               # 应用案例
│   ├── semantic_search/        # 语义搜索
│   ├── recommendation/         # 推荐系统
│   ├── image_search/           # 图像搜索
│   └── knowledge_graph/        # 知识图谱
└── benchmarks/                 # 性能测试
    ├── search_performance/     # 搜索性能
    ├── indexing_performance/   # 索引性能
    └── memory_usage/           # 内存使用
```

## 快速开始

### Qdrant示例

```rust
use qdrant_client::{
    prelude::*,
    qdrant::{CreateCollection, Distance, VectorParams},
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建客户端
    let client = QdrantClient::from_url("http://localhost:6333").build()?;
    
    // 创建集合
    let collection_name = "test_collection";
    client
        .create_collection(&CreateCollection {
            collection_name: collection_name.to_string(),
            vectors_config: Some(VectorParams {
                size: 128,
                distance: Distance::Cosine.into(),
                ..Default::default()
            }.into()),
            ..Default::default()
        })
        .await?;
    
    // 插入向量
    let points = vec![
        PointStruct::new(
            1,
            vec![0.1; 128],
            vec![("color", "red")],
        ),
        PointStruct::new(
            2,
            vec![0.2; 128],
            vec![("color", "blue")],
        ),
    ];
    
    client
        .upsert_points(collection_name, points, None)
        .await?;
    
    // 搜索相似向量
    let search_result = client
        .search_points(&SearchPoints {
            collection_name: collection_name.to_string(),
            vector: vec![0.15; 128],
            limit: 10,
            with_payload: Some(true.into()),
            ..Default::default()
        })
        .await?;
    
    for point in search_result.result {
        println!("ID: {}, Score: {}", point.id, point.score);
    }
    
    Ok(())
}
```

### Tantivy示例

```rust
use tantivy::{
    collector::TopDocs,
    directory::MmapDirectory,
    doc,
    query::QueryParser,
    schema::{Schema, TEXT, STORED},
    Index, ReloadPolicy,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建schema
    let mut schema_builder = Schema::builder();
    let title = schema_builder.add_text_field("title", TEXT | STORED);
    let body = schema_builder.add_text_field("body", TEXT);
    let schema = schema_builder.build();
    
    // 创建索引
    let index = Index::create_in_ram(schema.clone());
    let mut index_writer = index.writer(50_000_000)?;
    
    // 添加文档
    index_writer.add_document(doc!(
        title => "Rust Programming",
        body => "Rust is a systems programming language."
    ))?;
    index_writer.add_document(doc!(
        title => "Machine Learning",
        body => "Machine learning is a subset of AI."
    ))?;
    
    index_writer.commit()?;
    
    // 创建查询解析器
    let query_parser = QueryParser::for_index(&index, vec![title, body]);
    
    // 执行搜索
    let reader = index.reader()?;
    let searcher = reader.searcher();
    
    let query = query_parser.parse_query("Rust programming")?;
    let top_docs = searcher.search(&query, &TopDocs::with_limit(10))?;
    
    for (_score, doc_address) in top_docs {
        let retrieved_doc = searcher.doc(doc_address)?;
        println!("文档: {:?}", retrieved_doc);
    }
    
    Ok(())
}
```

### HNSW-rs示例

```rust
use hnsw_rs::prelude::*;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建HNSW索引
    let mut hnsw = Hnsw::new(
        128,  // 向量维度
        16,   // M参数
        200,  // ef_construction参数
        DistL2::new(), // 距离度量
    );
    
    // 添加向量
    let vectors = vec![
        vec![0.1; 128],
        vec![0.2; 128],
        vec![0.3; 128],
    ];
    
    for (i, vector) in vectors.iter().enumerate() {
        hnsw.insert(vector, i);
    }
    
    // 搜索最近邻
    let query_vector = vec![0.15; 128];
    let results = hnsw.search(&query_vector, 10, 16);
    
    for (id, distance) in results {
        println!("ID: {}, 距离: {}", id, distance);
    }
    
    Ok(())
}
```

## 性能优化

1. **索引优化**: 选择合适的索引参数
2. **批量操作**: 批量插入和更新
3. **内存管理**: 合理配置内存使用
4. **并行搜索**: 利用多线程并行搜索
5. **缓存策略**: 缓存频繁查询的结果

## 最佳实践

1. **向量维度**: 选择合适的向量维度
2. **距离度量**: 根据应用选择距离度量
3. **索引参数**: 调优索引构建参数
4. **查询优化**: 优化查询策略
5. **监控**: 监控搜索性能和准确性

## 相关资源

- [Rust向量搜索生态](https://github.com/rust-ai/awesome-rust-vector-search)
- [向量搜索最佳实践](https://github.com/rust-ai/vector-search-best-practices)
- [性能优化指南](https://github.com/rust-ai/vector-search-performance)
