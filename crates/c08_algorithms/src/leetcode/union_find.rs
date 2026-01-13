//! LeetCode 并查集类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的并查集类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用路径压缩和按秩合并优化
//! 2. **内存优化**: 高效的并查集数据结构

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::collections::{HashMap, HashSet};

// ==================== 数据结构定义 ====================

/// 并查集数据结构（带路径压缩和按秩合并）
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    pub fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]); // 路径压缩
        }
        self.parent[x]
    }

    pub fn union(&mut self, x: usize, y: usize) {
        let root_x = self.find(x);
        let root_y = self.find(y);

        if root_x != root_y {
            // 按秩合并
            if self.rank[root_x] < self.rank[root_y] {
                self.parent[root_x] = root_y;
            } else if self.rank[root_x] > self.rank[root_y] {
                self.parent[root_y] = root_x;
            } else {
                self.parent[root_y] = root_x;
                self.rank[root_x] += 1;
            }
        }
    }

    pub fn count(&mut self) -> usize {
        let mut roots = HashSet::new();
        for i in 0..self.parent.len() {
            roots.insert(self.find(i));
        }
        roots.len()
    }
}

// ==================== 经典题目实现 ====================

/// 128. Longest Consecutive Sequence（最长连续序列）
///
/// ## 问题描述
/// 给定一个未排序的整数数组 nums ，找出数字连续的最长序列（不要求序列元素在原数组中连续）的长度。
///
/// ## Rust 1.92 特性应用
/// - **哈希表优化**: 使用 HashSet 快速查找
///
/// ## 复杂度
/// - 时间复杂度: O(n)
/// - 空间复杂度: O(n)
pub fn longest_consecutive(nums: Vec<i32>) -> i32 {
    if nums.is_empty() {
        return 0;
    }

    let num_set: HashSet<i32> = nums.iter().cloned().collect();
    let mut max_len = 0;

    for &num in &num_set {
        // 只从序列的起点开始计算
        if !num_set.contains(&(num - 1)) {
            let mut current = num;
            let mut len = 1;

            while num_set.contains(&(current + 1)) {
                current += 1;
                len += 1;
            }

            max_len = max_len.max(len);
        }
    }

    max_len
}

/// 200. Number of Islands（岛屿数量）- 使用并查集
///
/// ## 问题描述
/// 给你一个由 '1'（陆地）和 '0'（水）组成的的二维网格，请你计算网格中岛屿的数量。
///
/// ## Rust 1.92 特性应用
/// - **并查集优化**: 使用并查集合并相邻的陆地
///
/// ## 复杂度
/// - 时间复杂度: O(m * n * α(m * n))
/// - 空间复杂度: O(m * n)
pub fn num_islands_union_find(grid: Vec<Vec<char>>) -> i32 {
    if grid.is_empty() || grid[0].is_empty() {
        return 0;
    }

    let rows = grid.len();
    let cols = grid[0].len();
    let mut uf = UnionFind::new(rows * cols);
    let mut count = 0;

    for i in 0..rows {
        for j in 0..cols {
            if grid[i][j] == '1' {
                count += 1;
                let idx = i * cols + j;

                // 检查四个方向
                let directions = [(0, 1), (1, 0)];
                for (dx, dy) in directions.iter() {
                    let ni = i as i32 + dx;
                    let nj = j as i32 + dy;
                    if ni >= 0 && nj >= 0 && (ni as usize) < rows && (nj as usize) < cols {
                        let nidx = ni as usize * cols + nj as usize;
                        if grid[ni as usize][nj as usize] == '1' {
                            if uf.find(idx) != uf.find(nidx) {
                                uf.union(idx, nidx);
                                count -= 1;
                            }
                        }
                    }
                }
            }
        }
    }

    count
}

/// 547. Number of Provinces（省份数量）
///
/// ## 问题描述
/// 有 n 个城市，其中一些彼此相连，另一些没有相连。
/// 给你一个 n x n 的矩阵 isConnected ，返回矩阵中 省份 的数量。
///
/// ## Rust 1.92 特性应用
/// - **并查集优化**: 使用并查集合并相连的城市
///
/// ## 复杂度
/// - 时间复杂度: O(n² * α(n))
/// - 空间复杂度: O(n)
pub fn find_circle_num(is_connected: Vec<Vec<i32>>) -> i32 {
    let n = is_connected.len();
    let mut uf = UnionFind::new(n);

    for i in 0..n {
        for j in 0..n {
            if is_connected[i][j] == 1 {
                uf.union(i, j);
            }
        }
    }

    uf.count() as i32
}

/// 684. Redundant Connection（冗余连接）
///
/// ## 问题描述
/// 给定往一棵 n 个节点的树中添加一条边后的图。
/// 请找出一条可以删去的边，删除后可使得剩余部分是一个有着 n 个节点的树。
///
/// ## Rust 1.92 特性应用
/// - **并查集优化**: 使用并查集检测环
///
/// ## 复杂度
/// - 时间复杂度: O(n * α(n))
/// - 空间复杂度: O(n)
pub fn find_redundant_connection(edges: Vec<Vec<i32>>) -> Vec<i32> {
    let n = edges.len();
    let mut uf = UnionFind::new(n + 1);

    for edge in edges {
        let x = edge[0] as usize;
        let y = edge[1] as usize;

        if uf.find(x) == uf.find(y) {
            return edge;
        }

        uf.union(x, y);
    }

    vec![]
}

/// 721. Accounts Merge（账户合并）
///
/// ## 问题描述
/// 给定一个列表 accounts，合并具有共同邮箱的账户。
///
/// ## Rust 1.92 特性应用
/// - **并查集优化**: 使用并查集合并账户
///
/// ## 复杂度
/// - 时间复杂度: O(n * k * log(n * k))
/// - 空间复杂度: O(n * k)
pub fn accounts_merge(accounts: Vec<Vec<String>>) -> Vec<Vec<String>> {
    let n = accounts.len();
    let mut uf = UnionFind::new(n);
    let mut email_to_index: HashMap<String, usize> = HashMap::new();

    // 建立邮箱到索引的映射，并合并账户
    for (i, account) in accounts.iter().enumerate() {
        for email in account.iter().skip(1) {
            if let Some(&prev_index) = email_to_index.get(email) {
                uf.union(i, prev_index);
            } else {
                email_to_index.insert(email.clone(), i);
            }
        }
    }

    // 收集每个根节点下的所有邮箱
    let mut index_to_emails: HashMap<usize, HashSet<String>> = HashMap::new();
    for (email, &index) in &email_to_index {
        let root = uf.find(index);
        index_to_emails.entry(root).or_insert_with(HashSet::new).insert(email.clone());
    }

    // 构建结果
    let mut result = Vec::new();
    for (index, emails) in index_to_emails {
        let mut account = vec![accounts[index][0].clone()];
        let mut sorted_emails: Vec<String> = emails.into_iter().collect();
        sorted_emails.sort();
        account.extend(sorted_emails);
        result.push(account);
    }

    result
}

// ==================== 问题信息注册 ====================

/// 获取所有并查集类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 128,
            title: "最长连续序列".to_string(),
            title_en: "Longest Consecutive Sequence".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::HashTable, LeetCodeTag::UnionFind],
            description: "给定一个未排序的整数数组 nums ，找出数字连续的最长序列（不要求序列元素在原数组中连续）的长度。".to_string(),
            examples: vec!["输入：nums = [100,4,200,1,3,2]\n输出：4".to_string()],
            constraints: vec!["0 <= nums.length <= 10^5".to_string()],
            rust_191_features: vec!["使用并查集或哈希表，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("使用哈希表或并查集，时间复杂度为 O(n)".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 200,
            title: "岛屿数量".to_string(),
            title_en: "Number of Islands".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch, LeetCodeTag::UnionFind, LeetCodeTag::Matrix],
            description: "给你一个由 '1'（陆地）和 '0'（水）组成的的二维网格，请你计算网格中岛屿的数量。".to_string(),
            examples: vec!["输入：grid = [[\"1\",\"1\",\"1\",\"1\",\"0\"],[\"1\",\"1\",\"0\",\"1\",\"0\"],[\"1\",\"1\",\"0\",\"0\",\"0\"],[\"0\",\"0\",\"0\",\"0\",\"0\"]]\n输出：1".to_string()],
            constraints: vec!["m == grid.length".to_string()],
            rust_191_features: vec!["使用并查集，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m*n*α(m*n))".to_string(),
                space_complexity: "O(m*n)".to_string(),
                explanation: Some("α 是阿克曼函数的反函数，实际应用中接近常数".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 547,
            title: "省份数量".to_string(),
            title_en: "Number of Provinces".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch, LeetCodeTag::UnionFind, LeetCodeTag::Graph],
            description: "有 n 个城市，其中一些彼此相连，另一些没有相连。如果城市 a 与城市 b 直接相连，且城市 b 与城市 c 直接相连，那么城市 a 与城市 c 间接相连。省份 是一组直接或间接相连的城市，组内不含其他没有相连的城市。给你一个 n x n 的矩阵 isConnected ，其中 isConnected[i][j] = 1 表示第 i 个城市和第 j 个城市直接相连，而 isConnected[i][j] = 0 表示二者不直接相连。返回矩阵中 省份 的数量。".to_string(),
            examples: vec!["输入：isConnected = [[1,1,0],[1,1,0],[0,0,1]]\n输出：2".to_string()],
            constraints: vec!["1 <= n <= 200".to_string()],
            rust_191_features: vec!["使用并查集，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n^2*α(n))".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("α 是阿克曼函数的反函数".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 684,
            title: "冗余连接".to_string(),
            title_en: "Redundant Connection".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch, LeetCodeTag::UnionFind, LeetCodeTag::Graph],
            description: "树可以看成是一个连通且 无环 的 无向 图。给定往一棵 n 个节点 (节点值 1～n) 的树中添加一条边后的图。添加的边的两个顶点包含在 1 到 n 中间，且这条附加的边不属于树中已存在的边。图的信息记录于长度为 n 的二维数组 edges ，edges[i] = [ai, bi] 表示图中在 ai 和 bi 之间存在一条边。请找出一条可以删去的边，删除后可使得剩余部分是一个有着 n 个节点的树。如果有多个答案，则返回数组 edges 中最后出现的边。".to_string(),
            examples: vec!["输入：edges = [[1,2],[1,3],[2,3]]\n输出：[2,3]".to_string()],
            constraints: vec!["n == edges.length".to_string()],
            rust_191_features: vec!["使用并查集检测环，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n*α(n))".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("α 是阿克曼函数的反函数".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 721,
            title: "账户合并".to_string(),
            title_en: "Accounts Merge".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::HashTable, LeetCodeTag::String, LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch, LeetCodeTag::UnionFind],
            description: "给定一个列表 accounts，每个元素 accounts[i] 是一个字符串列表，其中第一个元素 accounts[i][0] 是 名称 (name)，其余元素是 emails 表示该账户的邮箱地址。现在，我们想合并这些账户。如果两个账户都有一些共同的邮箱地址，则两个账户必定属于同一个人。请注意，即使两个账户具有相同的名称，它们也可能属于不同的人，因为人们可能具有相同的名称。一个人最初可以拥有任意数量的账户，但其所有账户都具有相同的名称。合并账户后，按以下格式返回账户：每个账户的第一个元素是名称，其余元素是按字符 ASCII 顺序排列的邮箱地址。账户本身可以以任意顺序返回。".to_string(),
            examples: vec!["输入：accounts = [[\"John\", \"johnsmith@mail.com\", \"john00@mail.com\"], [\"John\", \"johnnybravo@mail.com\"], [\"John\", \"johnsmith@mail.com\", \"john_newyork@mail.com\"], [\"Mary\", \"mary@mail.com\"]]\n输出：[[\"John\", \"john00@mail.com\", \"john_newyork@mail.com\", \"johnsmith@mail.com\"],  [\"John\", \"johnnybravo@mail.com\"], [\"Mary\", \"mary@mail.com\"]]".to_string()],
            constraints: vec!["1 <= accounts.length <= 1000".to_string()],
            rust_191_features: vec!["使用并查集合并账户，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n*k*log(n*k))".to_string(),
                space_complexity: "O(n*k)".to_string(),
                explanation: Some("n 是账户数，k 是每个账户的平均邮箱数".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_longest_consecutive() {
        assert_eq!(longest_consecutive(vec![100, 4, 200, 1, 3, 2]), 4);
        assert_eq!(longest_consecutive(vec![0, 3, 7, 2, 5, 8, 4, 6, 0, 1]), 9);
    }

    #[test]
    fn test_find_circle_num() {
        assert_eq!(find_circle_num(vec![vec![1, 1, 0], vec![1, 1, 0], vec![0, 0, 1]]), 2);
        assert_eq!(find_circle_num(vec![vec![1, 0, 0], vec![0, 1, 0], vec![0, 0, 1]]), 3);
    }

    #[test]
    fn test_find_redundant_connection() {
        assert_eq!(find_redundant_connection(vec![vec![1, 2], vec![1, 3], vec![2, 3]]), vec![2, 3]);
    }
}
