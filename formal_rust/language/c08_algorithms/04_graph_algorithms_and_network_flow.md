# 图算法与网络流

## 概述

图算法是解决网络、路径、关系等复杂问题的基础。Rust 通过类型安全和所有权模型，为图的存储与算法实现提供了高效支持。本章系统梳理图遍历、最短路径、最小生成树和网络流等核心算法。

## 图的表示

### 邻接表

```rust
use std::collections::HashMap;

struct Graph {
    adj: HashMap<usize, Vec<usize>>,
}

impl Graph {
    fn new() -> Self {
        Graph { adj: HashMap::new() }
    }
    fn add_edge(&mut self, u: usize, v: usize) {
        self.adj.entry(u).or_default().push(v);
    }
}
```

### 邻接矩阵

```rust
fn adjacency_matrix(n: usize, edges: &[(usize, usize)]) -> Vec<Vec<u8>> {
    let mut matrix = vec![vec![0; n]; n];
    for &(u, v) in edges {
        matrix[u][v] = 1;
    }
    matrix
}
```

## 图遍历算法

### 深度优先搜索（DFS）

```rust
fn dfs(graph: &Graph, start: usize, visited: &mut Vec<bool>) {
    visited[start] = true;
    if let Some(neighbors) = graph.adj.get(&start) {
        for &v in neighbors {
            if !visited[v] {
                dfs(graph, v, visited);
            }
        }
    }
}
```

### 广度优先搜索（BFS）

```rust
use std::collections::VecDeque;

fn bfs(graph: &Graph, start: usize, visited: &mut Vec<bool>) {
    let mut queue = VecDeque::new();
    queue.push_back(start);
    visited[start] = true;
    while let Some(u) = queue.pop_front() {
        if let Some(neighbors) = graph.adj.get(&u) {
            for &v in neighbors {
                if !visited[v] {
                    visited[v] = true;
                    queue.push_back(v);
                }
            }
        }
    }
}
```

## 最短路径算法

### Dijkstra 算法

```rust
use std::collections::BinaryHeap;
use std::cmp::Reverse;

fn dijkstra(n: usize, edges: &[(usize, usize, u32)], start: usize) -> Vec<u32> {
    let mut graph = vec![vec![]; n];
    for &(u, v, w) in edges {
        graph[u].push((v, w));
    }
    let mut dist = vec![u32::MAX; n];
    dist[start] = 0;
    let mut heap = BinaryHeap::new();
    heap.push(Reverse((0, start)));
    while let Some(Reverse((d, u))) = heap.pop() {
        if d > dist[u] { continue; }
        for &(v, w) in &graph[u] {
            if dist[v] > d + w {
                dist[v] = d + w;
                heap.push(Reverse((dist[v], v)));
            }
        }
    }
    dist
}
```

### Bellman-Ford 算法

```rust
fn bellman_ford(n: usize, edges: &[(usize, usize, i32)], start: usize) -> Option<Vec<i32>> {
    let mut dist = vec![i32::MAX; n];
    dist[start] = 0;
    for _ in 0..n-1 {
        for &(u, v, w) in edges {
            if dist[u] != i32::MAX && dist[v] > dist[u] + w {
                dist[v] = dist[u] + w;
            }
        }
    }
    // 检查负环
    for &(u, v, w) in edges {
        if dist[u] != i32::MAX && dist[v] > dist[u] + w {
            return None;
        }
    }
    Some(dist)
}
```

## 最小生成树算法

### Prim 算法

```rust
use std::collections::BinaryHeap;
use std::cmp::Reverse;

fn prim(n: usize, edges: &[(usize, usize, u32)]) -> u32 {
    let mut graph = vec![vec![]; n];
    for &(u, v, w) in edges {
        graph[u].push((v, w));
        graph[v].push((u, w));
    }
    let mut visited = vec![false; n];
    let mut heap = BinaryHeap::new();
    heap.push(Reverse((0, 0)));
    let mut total = 0;
    while let Some(Reverse((w, u))) = heap.pop() {
        if visited[u] { continue; }
        visited[u] = true;
        total += w;
        for &(v, w) in &graph[u] {
            if !visited[v] {
                heap.push(Reverse((w, v)));
            }
        }
    }
    total
}
```

### Kruskal 算法

```rust
fn kruskal(n: usize, mut edges: Vec<(usize, usize, u32)>) -> u32 {
    edges.sort_by_key(|&(_, _, w)| w);
    let mut parent = (0..n).collect::<Vec<_>>();
    fn find(parent: &mut [usize], x: usize) -> usize {
        if parent[x] != x {
            parent[x] = find(parent, parent[x]);
        }
        parent[x]
    }
    let mut total = 0;
    for (u, v, w) in edges {
        let pu = find(&mut parent, u);
        let pv = find(&mut parent, v);
        if pu != pv {
            parent[pu] = pv;
            total += w;
        }
    }
    total
}
```

## 网络流算法

### Edmonds-Karp 算法（最大流）

```rust
use std::collections::VecDeque;

fn edmonds_karp(n: usize, capacity: Vec<Vec<u32>>, s: usize, t: usize) -> u32 {
    let mut flow = vec![vec![0; n]; n];
    let mut max_flow = 0;
    loop {
        let mut parent = vec![None; n];
        let mut queue = VecDeque::new();
        queue.push_back(s);
        while let Some(u) = queue.pop_front() {
            for v in 0..n {
                if parent[v].is_none() && capacity[u][v] > flow[u][v] {
                    parent[v] = Some(u);
                    queue.push_back(v);
                }
            }
        }
        if parent[t].is_none() { break; }
        let mut increment = u32::MAX;
        let mut v = t;
        while let Some(u) = parent[v] {
            increment = increment.min(capacity[u][v] - flow[u][v]);
            v = u;
        }
        v = t;
        while let Some(u) = parent[v] {
            flow[u][v] += increment;
            flow[v][u] -= increment;
            v = u;
        }
        max_flow += increment;
    }
    max_flow
}
```

## 总结

图算法和网络流为解决实际工程和理论问题提供了强大工具。Rust 的类型系统和所有权模型保证了这些算法实现的安全性和高效性。

### 关键要点

1. **图遍历** - DFS、BFS
2. **最短路径** - Dijkstra、Bellman-Ford
3. **最小生成树** - Prim、Kruskal
4. **网络流** - Edmonds-Karp 最大流算法

### 下一步

在下一章中，我们将探讨并行算法与优化，包括并行排序、并行搜索、内存优化和性能调优。
