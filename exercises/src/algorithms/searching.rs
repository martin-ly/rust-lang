//! # 搜索练习 / Searching Exercises
//!
//! 本模块包含经典搜索算法的实现与练习：
//! - 二分搜索 (Binary Search)
//! - 上下界搜索 (Lower/Upper Bound)
//! - 峰值元素查找
//! - 无权图最短路径 (BFS)
//! - 图中路径存在性 (DFS)
//! - 岛屿数量 (DFS on Grid)

/// 二分搜索：在有序数组中查找 target，返回索引或 None。
/// 时间复杂度 O(log n)。
pub fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0i64;
    let mut right = arr.len() as i64 - 1;

    while left <= right {
        let mid = left + (right - left) / 2;
        let mid_val = arr[mid as usize];
        if mid_val == target {
            return Some(mid as usize);
        } else if mid_val < target {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }
    None
}

/// 查找第一个大于等于 target 的元素的索引（lower_bound）。
/// 若所有元素都小于 target，返回 arr.len()。
pub fn lower_bound(arr: &[i32], target: i32) -> usize {
    let mut left = 0usize;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        if arr[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    left
}

/// 查找峰值元素：返回数组中任意一个峰值元素的索引。
/// 峰值定义为大于左右相邻元素的元素，边界处只需考虑一侧。
pub fn find_peak_element(arr: &[i32]) -> Option<usize> {
    if arr.is_empty() {
        return None;
    }
    let mut left = 0usize;
    let mut right = arr.len() - 1;

    while left < right {
        let mid = left + (right - left) / 2;
        if arr[mid] > arr[mid + 1] {
            right = mid;
        } else {
            left = mid + 1;
        }
    }
    Some(left)
}

/// 无权图中从 start 到所有节点的最短距离（BFS）。
/// graph 是邻接表表示，节点编号为 0..n。
pub fn bfs_shortest_path(graph: &[Vec<usize>], start: usize) -> Vec<Option<usize>> {
    let n = graph.len();
    let mut dist = vec![None; n];
    let mut queue = std::collections::VecDeque::new();
    dist[start] = Some(0);
    queue.push_back(start);

    while let Some(u) = queue.pop_front() {
        let d = dist[u].unwrap();
        for &v in &graph[u] {
            if dist[v].is_none() {
                dist[v] = Some(d + 1);
                queue.push_back(v);
            }
        }
    }
    dist
}

/// 使用 DFS 判断有向图中从 start 到 target 是否存在路径。
pub fn dfs_has_path(graph: &[Vec<usize>], start: usize, target: usize) -> bool {
    let n = graph.len();
    if start >= n || target >= n {
        return false;
    }
    let mut visited = vec![false; n];
    dfs_helper(graph, start, target, &mut visited)
}

fn dfs_helper(graph: &[Vec<usize>], u: usize, target: usize, visited: &mut [bool]) -> bool {
    if u == target {
        return true;
    }
    visited[u] = true;
    for &v in &graph[u] {
        if !visited[v] && dfs_helper(graph, v, target, visited) {
            return true;
        }
    }
    false
}

/// 岛屿数量：grid 中 '1' 表示陆地，'0' 表示水，统计不相连的陆地数量。
pub fn num_islands(grid: &[Vec<char>]) -> usize {
    if grid.is_empty() || grid[0].is_empty() {
        return 0;
    }
    let rows = grid.len();
    let cols = grid[0].len();
    let mut visited = vec![vec![false; cols]; rows];
    let mut count = 0usize;

    for r in 0..rows {
        for c in 0..cols {
            if grid[r][c] == '1' && !visited[r][c] {
                count += 1;
                dfs_island(grid, r, c, &mut visited);
            }
        }
    }
    count
}

fn dfs_island(grid: &[Vec<char>], r: usize, c: usize, visited: &mut [Vec<bool>]) {
    let rows = grid.len();
    let cols = grid[0].len();
    if r >= rows || c >= cols || grid[r][c] != '1' || visited[r][c] {
        return;
    }
    visited[r][c] = true;
    let directions = [(0, 1), (0, -1), (1, 0), (-1, 0)];
    for (dr, dc) in directions {
        let nr = r as i32 + dr;
        let nc = c as i32 + dc;
        if nr >= 0 && nc >= 0 {
            dfs_island(grid, nr as usize, nc as usize, visited);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_search_found() {
        let arr = vec![1, 2, 3, 4, 5, 6, 7];
        assert_eq!(binary_search(&arr, 4), Some(3));
        assert_eq!(binary_search(&arr, 1), Some(0));
        assert_eq!(binary_search(&arr, 7), Some(6));
    }

    #[test]
    fn test_binary_search_not_found() {
        let arr = vec![1, 3, 5, 7, 9];
        assert_eq!(binary_search(&arr, 0), None);
        assert_eq!(binary_search(&arr, 10), None);
        assert_eq!(binary_search(&arr, 4), None);
    }

    #[test]
    fn test_binary_search_empty() {
        let arr: Vec<i32> = vec![];
        assert_eq!(binary_search(&arr, 5), None);
    }

    #[test]
    fn test_lower_bound() {
        let arr = vec![1, 2, 2, 2, 3, 4, 5];
        assert_eq!(lower_bound(&arr, 2), 1);
        assert_eq!(lower_bound(&arr, 6), arr.len());
        assert_eq!(lower_bound(&arr, 0), 0);
        assert_eq!(lower_bound(&arr, 3), 4);
    }

    #[test]
    fn test_find_peak_element() {
        assert_eq!(find_peak_element(&[1, 2, 3, 1]), Some(2));
        assert_eq!(find_peak_element(&[1, 2, 1, 3, 5, 6, 4]), Some(5));
        assert_eq!(find_peak_element(&[1]), Some(0));
        assert_eq!(find_peak_element(&[]), None);
    }

    #[test]
    fn test_bfs_shortest_path() {
        // 图：0 - 1 - 2
        //      \     /
        //       3 -- 4
        let graph = vec![vec![1, 3], vec![0, 2], vec![1, 4], vec![0, 4], vec![2, 3]];
        let dist = bfs_shortest_path(&graph, 0);
        assert_eq!(dist, vec![Some(0), Some(1), Some(2), Some(1), Some(2)]);
    }

    #[test]
    fn test_bfs_disconnected() {
        let graph = vec![vec![1], vec![0], vec![], vec![]];
        let dist = bfs_shortest_path(&graph, 0);
        assert_eq!(dist, vec![Some(0), Some(1), None, None]);
    }

    #[test]
    fn test_dfs_has_path() {
        let graph = vec![vec![1, 2], vec![2], vec![3], vec![]];
        assert!(dfs_has_path(&graph, 0, 3));
        assert!(!dfs_has_path(&graph, 3, 0));
    }

    #[test]
    fn test_dfs_out_of_bounds() {
        let graph = vec![vec![1], vec![]];
        assert!(!dfs_has_path(&graph, 0, 5));
    }

    #[test]
    fn test_num_islands() {
        let grid = vec![
            vec!['1', '1', '0', '0', '0'],
            vec!['1', '1', '0', '0', '0'],
            vec!['0', '0', '1', '0', '0'],
            vec!['0', '0', '0', '1', '1'],
        ];
        assert_eq!(num_islands(&grid), 3);
    }

    #[test]
    fn test_num_islands_empty() {
        let grid: Vec<Vec<char>> = vec![];
        assert_eq!(num_islands(&grid), 0);
    }
}
