//! LeetCode 广度优先搜索类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的广度优先搜索类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 队列操作性能提升
//! 2. **内存优化**: 使用 VecDeque 高效队列

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use crate::leetcode::tree::TreeNode;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

// ==================== 经典题目实现 ====================

/// 102. Binary Tree Level Order Traversal（二叉树的层序遍历）
pub fn level_order(root: Option<Rc<RefCell<TreeNode>>>) -> Vec<Vec<i32>> {
    let mut result = Vec::new();
    if root.is_none() {
        return result;
    }

    let mut queue = VecDeque::new();
    queue.push_back(root.unwrap());

    while !queue.is_empty() {
        let level_size = queue.len();
        let mut level = Vec::new();

        for _ in 0..level_size {
            let node = queue.pop_front().unwrap();
            let node_ref = node.borrow();
            level.push(node_ref.val);

            if let Some(left) = node_ref.left.clone() {
                queue.push_back(left);
            }
            if let Some(right) = node_ref.right.clone() {
                queue.push_back(right);
            }
        }

        result.push(level);
    }

    result
}

/// 104. Maximum Depth of Binary Tree（二叉树的最大深度）- BFS版本
pub fn max_depth_bfs(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    if root.is_none() {
        return 0;
    }

    let mut depth = 0;
    let mut queue = VecDeque::new();
    queue.push_back(root.unwrap());

    while !queue.is_empty() {
        depth += 1;
        let level_size = queue.len();

        for _ in 0..level_size {
            let node = queue.pop_front().unwrap();
            let node_ref = node.borrow();

            if let Some(left) = node_ref.left.clone() {
                queue.push_back(left);
            }
            if let Some(right) = node_ref.right.clone() {
                queue.push_back(right);
            }
        }
    }

    depth
}

/// 111. Minimum Depth of Binary Tree（二叉树的最小深度）
pub fn min_depth(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    if root.is_none() {
        return 0;
    }

    let mut depth = 0;
    let mut queue = VecDeque::new();
    queue.push_back(root.unwrap());

    while !queue.is_empty() {
        depth += 1;
        let level_size = queue.len();

        for _ in 0..level_size {
            let node = queue.pop_front().unwrap();
            let node_ref = node.borrow();

            if node_ref.left.is_none() && node_ref.right.is_none() {
                return depth;
            }

            if let Some(left) = node_ref.left.clone() {
                queue.push_back(left);
            }
            if let Some(right) = node_ref.right.clone() {
                queue.push_back(right);
            }
        }
    }

    depth
}

/// 200. Number of Islands（岛屿数量）- BFS版本
pub fn num_islands_bfs(grid: Vec<Vec<char>>) -> i32 {
    if grid.is_empty() || grid[0].is_empty() {
        return 0;
    }

    let rows = grid.len();
    let cols = grid[0].len();
    let mut visited = vec![vec![false; cols]; rows];
    let mut count = 0;

    for i in 0..rows {
        for j in 0..cols {
            if grid[i][j] == '1' && !visited[i][j] {
                let mut queue = VecDeque::new();
                queue.push_back((i, j));
                visited[i][j] = true;

                while let Some((x, y)) = queue.pop_front() {
                    let directions = [(0, 1), (0, -1), (1, 0), (-1, 0)];
                    for (dx, dy) in directions.iter() {
                        let nx = x as i32 + dx;
                        let ny = y as i32 + dy;
                        if nx >= 0 && ny >= 0 && (nx as usize) < rows && (ny as usize) < cols {
                            let nx = nx as usize;
                            let ny = ny as usize;
                            if grid[nx][ny] == '1' && !visited[nx][ny] {
                                visited[nx][ny] = true;
                                queue.push_back((nx, ny));
                            }
                        }
                    }
                }
                count += 1;
            }
        }
    }

    count
}

/// 127. Word Ladder（单词接龙）
pub fn ladder_length(begin_word: String, end_word: String, word_list: Vec<String>) -> i32 {
    use std::collections::{HashSet, VecDeque};

    let word_set: HashSet<String> = word_list.into_iter().collect();
    if !word_set.contains(&end_word) {
        return 0;
    }

    let mut queue = VecDeque::new();
    queue.push_back((begin_word.clone(), 1));
    let mut visited = HashSet::new();
    visited.insert(begin_word);

    while let Some((word, steps)) = queue.pop_front() {
        if word == end_word {
            return steps;
        }

        let word_chars: Vec<char> = word.chars().collect();
        for i in 0..word_chars.len() {
            for c in b'a'..=b'z' {
                let mut new_chars = word_chars.clone();
                new_chars[i] = c as char;
                let new_word: String = new_chars.iter().collect();

                if word_set.contains(&new_word) && !visited.contains(&new_word) {
                    visited.insert(new_word.clone());
                    queue.push_back((new_word, steps + 1));
                }
            }
        }
    }

    0
}

// ==================== 问题信息注册 ====================

/// 获取所有广度优先搜索类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 102,
            title: "二叉树的层序遍历".to_string(),
            title_en: "Binary Tree Level Order Traversal".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::BreadthFirstSearch],
            description: "给你二叉树的根节点 root ，返回其节点值的 层序遍历 。 （即逐层地，从左到右访问所有节点）。".to_string(),
            examples: vec!["输入：root = [3,9,20,null,null,15,7]\n输出：[[3],[9,20],[15,7]]".to_string()],
            constraints: vec!["树中节点的数量在 [0, 2000] 范围内".to_string()],
            rust_191_features: vec!["使用 BFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历所有节点，队列最多存储一层节点".to_string()),
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
            rust_191_features: vec!["使用 BFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历所有节点，队列最多存储一层节点".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 111,
            title: "二叉树的最小深度".to_string(),
            title_en: "Minimum Depth of Binary Tree".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::DepthFirstSearch, LeetCodeTag::BreadthFirstSearch],
            description: "给定一个二叉树，找出其最小深度。最小深度是从根节点到最近叶子节点的最短路径上的节点数量。".to_string(),
            examples: vec!["输入：root = [3,9,20,null,null,15,7]\n输出：2".to_string()],
            constraints: vec!["树中节点的数量在 [0, 10^5] 范围内".to_string()],
            rust_191_features: vec!["使用 BFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("遍历所有节点，队列最多存储一层节点".to_string()),
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
            rust_191_features: vec!["使用 BFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m*n)".to_string(),
                space_complexity: "O(min(m,n))".to_string(),
                explanation: Some("遍历所有单元格，队列最多存储一层".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 127,
            title: "单词接龙".to_string(),
            title_en: "Word Ladder".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::HashTable, LeetCodeTag::String, LeetCodeTag::BreadthFirstSearch],
            description: "字典 wordList 中从单词 beginWord 和 endWord 的 转换序列 是一个按下述规格形成的序列 beginWord -> s1 -> s2 -> ... -> sk：".to_string(),
            examples: vec!["输入：beginWord = \"hit\", endWord = \"cog\", wordList = [\"hot\",\"dot\",\"dog\",\"lot\",\"log\",\"cog\"]\n输出：5".to_string()],
            constraints: vec!["1 <= beginWord.length <= 10".to_string()],
            rust_191_features: vec!["使用 BFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(M * N)".to_string(),
                space_complexity: "O(M * N)".to_string(),
                explanation: Some("M 是单词长度，N 是单词列表长度".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::leetcode::tree::build_tree_from_vec;

    #[test]
    fn test_level_order() {
        let root = build_tree_from_vec(&[Some(3), Some(9), Some(20), None, None, Some(15), Some(7)]);
        let result = level_order(root);
        assert_eq!(result, vec![vec![3], vec![9, 20], vec![15, 7]]);
    }

    #[test]
    fn test_min_depth() {
        let root = build_tree_from_vec(&[Some(3), Some(9), Some(20), None, None, Some(15), Some(7)]);
        assert_eq!(min_depth(root), 2);
    }
}
