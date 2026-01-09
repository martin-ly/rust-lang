//! 图算法演示程序
//!
//! 本示例展示各种图算法的实现和使用：
//! - BFS（广度优先搜索）
//! - DFS（深度优先搜索）
//! - Dijkstra 最短路径
//! - 拓扑排序

use std::collections::{HashMap, VecDeque, HashSet};

/// 图的邻接表表示
pub struct Graph {
    /// 邻接表：顶点 -> [(邻居顶点, 权重)]
    adjacency_list: HashMap<usize, Vec<(usize, i32)>>,
    /// 顶点数量
    vertex_count: usize,
}

impl Graph {
    /// 创建新的图
    pub fn new(vertex_count: usize) -> Self {
        Self {
            adjacency_list: HashMap::new(),
            vertex_count,
        }
    }

    /// 添加边
    pub fn add_edge(&mut self, from: usize, to: usize, weight: i32) {
        self.adjacency_list
            .entry(from)
            .or_insert_with(Vec::new)
            .push((to, weight));
    }

    /// 获取顶点的邻居
    pub fn get_neighbors(&self, vertex: usize) -> &[(usize, i32)] {
        self.adjacency_list.get(&vertex).map(|v| v.as_slice()).unwrap_or(&[])
    }
}

/// BFS（广度优先搜索）
pub fn bfs(graph: &Graph, start: usize) -> Vec<Option<usize>> {
    let mut distances = vec![None; graph.vertex_count];
    let mut queue = VecDeque::new();
    let mut visited = HashSet::new();

    distances[start] = Some(0);
    queue.push_back(start);
    visited.insert(start);

    while let Some(current) = queue.pop_front() {
        let current_dist = distances[current].unwrap();

        for &(neighbor, _) in graph.get_neighbors(current) {
            if !visited.contains(&neighbor) {
                visited.insert(neighbor);
                distances[neighbor] = Some(current_dist + 1);
                queue.push_back(neighbor);
            }
        }
    }

    distances
}

/// DFS（深度优先搜索）
pub fn dfs(graph: &Graph, start: usize) -> Vec<usize> {
    let mut result = Vec::new();
    let mut visited = HashSet::new();
    let mut stack = vec![start];

    while let Some(current) = stack.pop() {
        if visited.contains(&current) {
            continue;
        }

        visited.insert(current);
        result.push(current);

        for &(neighbor, _) in graph.get_neighbors(current) {
            if !visited.contains(&neighbor) {
                stack.push(neighbor);
            }
        }
    }

    result
}

/// Dijkstra 最短路径算法
pub fn dijkstra(graph: &Graph, start: usize) -> Vec<Option<i32>> {
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;

    let mut distances = vec![None; graph.vertex_count];
    let mut heap = BinaryHeap::new();
    let mut visited = HashSet::new();

    distances[start] = Some(0);
    heap.push(Reverse((0, start)));

    while let Some(Reverse((dist, current))) = heap.pop() {
        if visited.contains(&current) {
            continue;
        }

        visited.insert(current);

        for &(neighbor, weight) in graph.get_neighbors(current) {
            let new_dist = dist + weight as i32;

            if distances[neighbor].is_none() || new_dist < distances[neighbor].unwrap() {
                distances[neighbor] = Some(new_dist);
                heap.push(Reverse((new_dist, neighbor)));
            }
        }
    }

    distances
}

/// 拓扑排序
pub fn topological_sort(graph: &Graph) -> Vec<usize> {
    // 计算入度
    let mut in_degree = vec![0; graph.vertex_count];
    for neighbors in graph.adjacency_list.values() {
        for &(neighbor, _) in neighbors {
            in_degree[neighbor] += 1;
        }
    }

    // 找到所有入度为 0 的顶点
    let mut queue = VecDeque::new();
    for (vertex, &degree) in in_degree.iter().enumerate() {
        if degree == 0 {
            queue.push_back(vertex);
        }
    }

    let mut result = Vec::new();

    while let Some(current) = queue.pop_front() {
        result.push(current);

        for &(neighbor, _) in graph.get_neighbors(current) {
            in_degree[neighbor] -= 1;
            if in_degree[neighbor] == 0 {
                queue.push_back(neighbor);
            }
        }
    }

    result
}

fn main() {
    println!("🚀 图算法演示程序\n");

    // 创建示例图
    let mut graph = Graph::new(6);

    // 添加边（有向图）
    graph.add_edge(0, 1, 4);
    graph.add_edge(0, 2, 2);
    graph.add_edge(1, 3, 5);
    graph.add_edge(2, 1, 1);
    graph.add_edge(2, 3, 8);
    graph.add_edge(2, 4, 10);
    graph.add_edge(3, 4, 2);
    graph.add_edge(4, 5, 3);

    println!("图结构:");
    println!("  0 -> 1 (4), 0 -> 2 (2)");
    println!("  1 -> 3 (5)");
    println!("  2 -> 1 (1), 2 -> 3 (8), 2 -> 4 (10)");
    println!("  3 -> 4 (2)");
    println!("  4 -> 5 (3)\n");

    // 1. BFS
    println!("=== BFS（从顶点 0 开始）===");
    let bfs_result = bfs(&graph, 0);
    for (i, dist) in bfs_result.iter().enumerate() {
        if let Some(d) = dist {
            println!("  顶点 {}: 距离 = {}", i, d);
        } else {
            println!("  顶点 {}: 不可达", i);
        }
    }

    // 2. DFS
    println!("\n=== DFS（从顶点 0 开始）===");
    let dfs_result = dfs(&graph, 0);
    println!("  访问顺序: {:?}", dfs_result);

    // 3. Dijkstra
    println!("\n=== Dijkstra 最短路径（从顶点 0 开始）===");
    let dijkstra_result = dijkstra(&graph, 0);
    for (i, dist) in dijkstra_result.iter().enumerate() {
        if let Some(d) = dist {
            println!("  顶点 {}: 最短距离 = {}", i, d);
        } else {
            println!("  顶点 {}: 不可达", i);
        }
    }

    // 4. 拓扑排序
    println!("\n=== 拓扑排序 ===");
    let topo_result = topological_sort(&graph);
    println!("  排序结果: {:?}", topo_result);

    println!("\n✅ 所有图算法演示完成！");
    println!("\n💡 提示:");
    println!("  - BFS: 用于查找最短路径（无权图）");
    println!("  - DFS: 用于遍历图或查找路径");
    println!("  - Dijkstra: 用于查找最短路径（有权图）");
    println!("  - 拓扑排序: 用于有向无环图的线性排序");
}
