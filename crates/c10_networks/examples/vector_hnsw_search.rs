//! vector crate 向量最近邻搜索示例
//!
//! 本示例不依赖外部服务，直接构建内存中的 HNSW 索引并搜索最近邻。
//! 实际生产环境可将此模式用于嵌入向量（embedding）的相似性检索。

use vector::Index;

fn main() {
    let vectors = vec![[4.0, 2.0], [5.0, 7.0], [2.0, 9.0], [7.0, 8.0]];

    // m = 1, ef = 1, seed = 42
    let index = Index::build(&vectors, 1, 1, 42);

    let query = [5.0, 5.0];
    let neighbors = index.search(&vectors, &query, 2);

    println!("query: {:?}", query);
    for (idx, distance) in neighbors {
        println!("neighbor idx={idx}, distance={distance:.4}");
    }
}
