//! LeetCode 深度优先搜索类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的深度优先搜索类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 递归和迭代器操作性能提升
//! 2. **内存优化**: 使用栈或递归优化

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use crate::leetcode::tree::TreeNode;
use std::cell::RefCell;
use std::rc::Rc;

// ==================== 经典题目实现 ====================

/// 98. Validate Binary Search Tree（验证二叉搜索树）
pub fn is_valid_bst(root: Option<Rc<RefCell<TreeNode>>>) -> bool {
    fn validate(node: Option<Rc<RefCell<TreeNode>>>, min: Option<i32>, max: Option<i32>) -> bool {
        match node {
            None => true,
            Some(n) => {
                let val = n.borrow().val;
                if let Some(min_val) = min {
                    if val <= min_val {
                        return false;
                    }
                }
                if let Some(max_val) = max {
                    if val >= max_val {
                        return false;
                    }
                }
                validate(n.borrow().left.clone(), min, Some(val))
                    && validate(n.borrow().right.clone(), Some(val), max)
            }
        }
    }

    validate(root, None, None)
}

/// 104. Maximum Depth of Binary Tree（二叉树的最大深度）- DFS版本
pub fn max_depth_dfs(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    match root {
        None => 0,
        Some(node) => {
            let node_ref = node.borrow();
            let left_depth = max_depth_dfs(node_ref.left.clone());
            let right_depth = max_depth_dfs(node_ref.right.clone());
            1 + left_depth.max(right_depth)
        }
    }
}

/// 200. Number of Islands（岛屿数量）- DFS版本
pub fn num_islands_dfs(grid: Vec<Vec<char>>) -> i32 {
    if grid.is_empty() || grid[0].is_empty() {
        return 0;
    }

    let rows = grid.len();
    let cols = grid[0].len();
    let mut visited = vec![vec![false; cols]; rows];
    let mut count = 0;

    fn dfs(
        grid: &[Vec<char>],
        visited: &mut [Vec<bool>],
        i: usize,
        j: usize,
        rows: usize,
        cols: usize,
    ) {
        if i >= rows || j >= cols || visited[i][j] || grid[i][j] == '0' {
            return;
        }

        visited[i][j] = true;
        let directions = [(0, 1), (0, -1), (1, 0), (-1, 0)];
        for (dx, dy) in directions.iter() {
            let ni = i as i32 + dx;
            let nj = j as i32 + dy;
            if ni >= 0 && nj >= 0 && (ni as usize) < rows && (nj as usize) < cols {
                dfs(grid, visited, ni as usize, nj as usize, rows, cols);
            }
        }
    }

    for i in 0..rows {
        for j in 0..cols {
            if grid[i][j] == '1' && !visited[i][j] {
                dfs(&grid, &mut visited, i, j, rows, cols);
                count += 1;
            }
        }
    }

    count
}

/// 236. Lowest Common Ancestor（二叉树的最近公共祖先）
pub fn lowest_common_ancestor(
    root: Option<Rc<RefCell<TreeNode>>>,
    p: Option<Rc<RefCell<TreeNode>>>,
    q: Option<Rc<RefCell<TreeNode>>>,
) -> Option<Rc<RefCell<TreeNode>>> {
    if root.is_none() || root == p || root == q {
        return root;
    }

    let left = root.as_ref().unwrap().borrow().left.clone();
    let right = root.as_ref().unwrap().borrow().right.clone();

    let left_result = lowest_common_ancestor(left, p.clone(), q.clone());
    let right_result = lowest_common_ancestor(right, p, q);

    match (left_result, right_result) {
        (Some(_), Some(_)) => root,
        (Some(l), None) => Some(l),
        (None, Some(r)) => Some(r),
        (None, None) => None,
    }
}

/// 543. Diameter of Binary Tree（二叉树的直径）
pub fn diameter_of_binary_tree(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    let mut max_diameter = 0;

    fn depth(node: Option<Rc<RefCell<TreeNode>>>, max_diameter: &mut i32) -> i32 {
        match node {
            None => 0,
            Some(n) => {
                let node_ref = n.borrow();
                let left = depth(node_ref.left.clone(), max_diameter);
                let right = depth(node_ref.right.clone(), max_diameter);
                *max_diameter = (*max_diameter).max(left + right);
                1 + left.max(right)
            }
        }
    }

    depth(root, &mut max_diameter);
    max_diameter
}

// ==================== 问题信息注册 ====================

/// 获取所有深度优先搜索类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 98,
            title: "验证二叉搜索树".to_string(),
            title_en: "Validate Binary Search Tree".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch, LeetCodeTag::BinarySearch],
            description: "给你一个二叉树的根节点 root ，判断其是否是一个有效的二叉搜索树。".to_string(),
            examples: vec!["输入：root = [2,1,3]\n输出：true".to_string()],
            constraints: vec!["树中节点数目范围在[1, 10^4] 内".to_string()],
            rust_191_features: vec!["使用 DFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历所有节点，递归栈深度为树高".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 104,
            title: "二叉树的最大深度".to_string(),
            title_en: "Maximum Depth of Binary Tree".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch],
            description: "给定一个二叉树，找出其最大深度。".to_string(),
            examples: vec!["输入：root = [3,9,20,null,null,15,7]\n输出：3".to_string()],
            constraints: vec!["树中节点的数量在 [0, 10^4] 范围内".to_string()],
            rust_191_features: vec!["使用 DFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历所有节点，递归栈深度为树高".to_string()),
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
            rust_191_features: vec!["使用 DFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m*n)".to_string(),
                space_complexity: "O(m*n)".to_string(),
                explanation: Some("遍历所有单元格，递归栈深度最多为 m*n".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 236,
            title: "二叉树的最近公共祖先".to_string(),
            title_en: "Lowest Common Ancestor of a Binary Tree".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch],
            description: "给定一个二叉树, 找到该树中两个指定节点的最近公共祖先。".to_string(),
            examples: vec!["输入：root = [3,5,1,6,2,0,8,null,null,7,4], p = 5, q = 1\n输出：3".to_string()],
            constraints: vec!["树中节点数目在范围 [2, 10^5] 内".to_string()],
            rust_191_features: vec!["使用 DFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历所有节点，递归栈深度为树高".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 543,
            title: "二叉树的直径".to_string(),
            title_en: "Diameter of Binary Tree".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch],
            description: "给定一棵二叉树，你需要计算它的直径长度。一棵二叉树的直径长度是任意两个结点路径长度中的最大值。这条路径可能穿过也可能不穿过根结点。".to_string(),
            examples: vec!["输入：root = [1,2,3,4,5]\n输出：3".to_string()],
            constraints: vec!["树的结点数在范围 [1, 10^4] 内".to_string()],
            rust_191_features: vec!["使用 DFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历所有节点，递归栈深度为树高".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::leetcode::tree::build_tree_from_vec;

    #[test]
    fn test_is_valid_bst() {
        let root = build_tree_from_vec(&[Some(2), Some(1), Some(3)]);
        assert!(is_valid_bst(root));
    }

    #[test]
    fn test_max_depth_dfs() {
        let root = build_tree_from_vec(&[Some(3), Some(9), Some(20), None, None, Some(15), Some(7)]);
        assert_eq!(max_depth_dfs(root), 3);
    }

    #[test]
    fn test_diameter_of_binary_tree() {
        let root = build_tree_from_vec(&[Some(1), Some(2), Some(3), Some(4), Some(5)]);
        assert_eq!(diameter_of_binary_tree(root), 3);
    }
}
