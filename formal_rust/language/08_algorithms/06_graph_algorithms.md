# 图论算法

## 1. 图的表示与遍历

- 邻接矩阵、邻接表、DFS、BFS

### 1.1 邻接矩阵/表

```rust
pub struct GraphMatrix { /* ... */ }
pub struct GraphList { /* ... */ }
```

### 1.2 遍历算法

```rust
fn dfs(graph: &GraphList, start: usize, visit: &mut impl FnMut(usize)) { /* ... */ }
fn bfs(graph: &GraphList, start: usize, visit: &mut impl FnMut(usize)) { /* ... */ }
```

## 2. 最短路径算法

- Dijkstra、Bellman-Ford、Floyd-Warshall

### 2.1 Dijkstra

```rust
fn dijkstra(graph: &[Vec<(usize, usize)>], start: usize) -> Vec<Option<usize>> { /* ... */ }
```

### 2.2 Bellman-Ford

```rust
fn bellman_ford(graph: &[Vec<(usize, isize)>], start: usize) -> Option<Vec<Option<isize>>> { /* ... */ }
```

### 2.3 Floyd-Warshall

```rust
fn floyd_warshall(graph: &[Vec<Option<isize>>]) -> Vec<Vec<Option<isize>>> { /* ... */ }
```

## 3. 最小生成树与网络流

- Prim、Kruskal、Ford-Fulkerson、Edmonds-Karp

### 3.1 Prim

```rust
fn prim(graph: &[Vec<(usize, usize)>]) -> Option<Vec<(usize, usize)>> { /* ... */ }
```

### 3.2 Kruskal

```rust
fn kruskal(n: usize, edges: &[(usize, usize, usize)]) -> Vec<(usize, usize, usize)> { /* ... */ }
```

### 3.3 Ford-Fulkerson/Edmonds-Karp

```rust
fn ford_fulkerson(graph: &[Vec<(usize, i32)>], source: usize, sink: usize) -> i32 { /* ... */ }
```

## 4. 批判性分析与未来展望

- 图算法需关注稀疏/稠密特性、并行化与工程可扩展性
- 未来可探索分布式图计算与AI驱动图算法
