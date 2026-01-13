//! 图算法示例
//!
//! 本示例展示C08算法模块的各种图算法：
//! - BFS（广度优先搜索）
//! - DFS（深度优先搜索）
//! - 最短路径
//!
//! 运行方式:
//! ```bash
//! cargo run --example graph_algorithms_demo
//! ```

use c08_algorithms::graph::bfs_shortest_path_sync;
use std::collections::HashMap;

fn main() {
    println!("🚀 图算法示例\n");
    println!("{}", "=".repeat(60));

    // 1. 创建图
    println!("\n📊 创建图:");
    println!("{}", "-".repeat(60));
    let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
    graph.insert(1, vec![2, 3]);
    graph.insert(2, vec![4, 5]);
    graph.insert(3, vec![6]);
    graph.insert(4, vec![]);
    graph.insert(5, vec![]);
    graph.insert(6, vec![]);

    println!("图结构:");
    for (node, neighbors) in &graph {
        println!("  节点 {} -> {:?}", node, neighbors);
    }

    // 2. BFS最短路径
    println!("\n📊 BFS最短路径:");
    println!("{}", "-".repeat(60));
    match bfs_shortest_path_sync(&graph, &1, &5) {
        Some(path) => {
            println!("从节点1到节点5的最短路径: {:?}", path);
            println!("路径长度: {}", path.len() - 1);
        }
        None => println!("未找到从节点1到节点5的路径"),
    }

    // 3. 图算法说明
    println!("\n💡 图算法说明:");
    println!("{}", "-".repeat(60));
    println!("  BFS: 广度优先搜索，找到最短路径");
    println!("  DFS: 深度优先搜索，用于遍历和回溯");
    println!("  Dijkstra: 带权图的最短路径算法");

    println!("\n✅ 图算法演示完成！");
}
