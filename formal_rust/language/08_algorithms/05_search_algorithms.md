# 搜索算法理论

## 1. 基础搜索算法

- 线性搜索、二分搜索、插值搜索、跳跃搜索

### 1.1 线性搜索

```rust
pub fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> { /* ... */ }
```

### 1.2 二分搜索

```rust
pub fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> { /* ... */ }
```

### 1.3 插值/跳跃搜索

```rust
pub fn interpolation_search(arr: &[i32], target: i32) -> Option<usize> { /* ... */ }
pub fn jump_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> { /* ... */ }
```

## 2. 哈希与字符串搜索

- 哈希表查找、KMP、Boyer-Moore等字符串搜索

### 2.1 哈希查找

```rust
use std::collections::HashMap;
let mut map = HashMap::new();
map.insert("key", 42);
let v = map.get("key");
```

### 2.2 KMP字符串搜索

```rust
pub fn kmp_search(text: &str, pattern: &str) -> Vec<usize> { /* ... */ }
```

## 3. 图搜索算法

- DFS、BFS、A*、Dijkstra等

### 3.1 深度/广度优先搜索

```rust
fn dfs(graph: &GraphList, start: usize, visit: &mut impl FnMut(usize)) { /* ... */ }
fn bfs(graph: &GraphList, start: usize, visit: &mut impl FnMut(usize)) { /* ... */ }
```

### 3.2 启发式与最短路径

```rust
fn a_star(...);
fn dijkstra(...);
```

## 4. 批判性分析与未来展望

- 搜索算法需关注数据分布、缓存友好与并行化
- 未来可探索自适应搜索与AI驱动搜索策略
