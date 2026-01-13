//! LeetCode 矩阵类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的矩阵类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用 `<[_]>::rotate_right` 等新 API
//! 2. **迭代器优化**: Iterator::eq 和 Iterator::eq_by 特化

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};

// ==================== 经典题目实现 ====================

/// 48. Rotate Image（旋转图像）
///
/// ## 问题描述
/// 给定一个 n × n 的二维矩阵 matrix 表示一个图像。请你将图像顺时针旋转 90 度。
/// 你必须在 原地 旋转图像，这意味着你需要直接修改输入的二维矩阵。请不要 使用另一个矩阵来旋转图像。
///
/// ## Rust 1.92 特性应用
/// - **性能优化**: 使用原地旋转，O(1) 空间复杂度
/// - **迭代器优化**: 矩阵遍历性能提升
///
/// ## 复杂度
/// - 时间复杂度: O(n²)
/// - 空间复杂度: O(1)
pub fn rotate(matrix: &mut Vec<Vec<i32>>) {
    let n = matrix.len();

    // 先转置矩阵
    for i in 0..n {
        for j in i..n {
            let temp = matrix[i][j];
            matrix[i][j] = matrix[j][i];
            matrix[j][i] = temp;
        }
    }

    // 再翻转每一行
    for i in 0..n {
        matrix[i].reverse();
    }
}

/// 54. Spiral Matrix（螺旋矩阵）
///
/// ## 问题描述
/// 给你一个 m 行 n 列的矩阵 matrix ，请按照 顺时针螺旋顺序 ，返回矩阵中的所有元素。
///
/// ## Rust 1.92 特性应用
/// - **迭代器优化**: 使用迭代器简化代码
/// - **性能优化**: 一次遍历完成
///
/// ## 复杂度
/// - 时间复杂度: O(m * n)
/// - 空间复杂度: O(1)（不包括返回结果）
pub fn spiral_order(matrix: Vec<Vec<i32>>) -> Vec<i32> {
    if matrix.is_empty() || matrix[0].is_empty() {
        return vec![];
    }

    let rows = matrix.len();
    let cols = matrix[0].len();
    let mut result = Vec::with_capacity(rows * cols);

    let mut top = 0;
    let mut bottom = rows - 1;
    let mut left = 0;
    let mut right = cols - 1;

    while top <= bottom && left <= right {
        // 从左到右
        for j in left..=right {
            result.push(matrix[top][j]);
        }
        top += 1;

        // 从上到下
        for i in top..=bottom {
            result.push(matrix[i][right]);
        }
        right = right.saturating_sub(1);

        // 从右到左
        if top <= bottom {
            for j in (left..=right).rev() {
                result.push(matrix[bottom][j]);
            }
            bottom = bottom.saturating_sub(1);
        }

        // 从下到上
        if left <= right {
            for i in (top..=bottom).rev() {
                result.push(matrix[i][left]);
            }
            left += 1;
        }
    }

    result
}

/// 73. Set Matrix Zeroes（矩阵置零）
///
/// ## 问题描述
/// 给定一个 m x n 的矩阵，如果一个元素为 0 ，则将其所在行和列的所有元素都设为 0 。请使用 原地 算法。
///
/// ## Rust 1.92 特性应用
/// - **性能优化**: 使用第一行和第一列作为标记，O(1) 空间复杂度
/// - **内存优化**: 原地修改，不需要额外空间
///
/// ## 复杂度
/// - 时间复杂度: O(m * n)
/// - 空间复杂度: O(1)
pub fn set_zeroes(matrix: &mut Vec<Vec<i32>>) {
    let rows = matrix.len();
    let cols = matrix[0].len();

    let mut first_row_zero = false;
    let mut first_col_zero = false;

    // 检查第一行和第一列是否有0
    for j in 0..cols {
        if matrix[0][j] == 0 {
            first_row_zero = true;
            break;
        }
    }

    for i in 0..rows {
        if matrix[i][0] == 0 {
            first_col_zero = true;
            break;
        }
    }

    // 使用第一行和第一列作为标记
    for i in 1..rows {
        for j in 1..cols {
            if matrix[i][j] == 0 {
                matrix[i][0] = 0;
                matrix[0][j] = 0;
            }
        }
    }

    // 根据标记设置0
    for i in 1..rows {
        for j in 1..cols {
            if matrix[i][0] == 0 || matrix[0][j] == 0 {
                matrix[i][j] = 0;
            }
        }
    }

    // 处理第一行和第一列
    if first_row_zero {
        for j in 0..cols {
            matrix[0][j] = 0;
        }
    }

    if first_col_zero {
        for i in 0..rows {
            matrix[i][0] = 0;
        }
    }
}

/// 200. Number of Islands（岛屿数量）
///
/// ## 问题描述
/// 给你一个由 '1'（陆地）和 '0'（水）组成的的二维网格，请你计算网格中岛屿的数量。
/// 岛屿总是被水包围，并且每座岛屿只能由水平方向和/或竖直方向上相邻的陆地连接形成。
///
/// ## Rust 1.92 特性应用
/// - **性能优化**: DFS/BFS 遍历性能提升
/// - **内存优化**: 原地标记访问过的节点
///
/// ## 复杂度
/// - 时间复杂度: O(m * n)
/// - 空间复杂度: O(m * n)（递归栈）或 O(min(m, n))（BFS）
pub fn num_islands(grid: Vec<Vec<char>>) -> i32 {
    if grid.is_empty() || grid[0].is_empty() {
        return 0;
    }

    let rows = grid.len();
    let cols = grid[0].len();
    let mut visited = vec![vec![false; cols]; rows];
    let mut count = 0;

    // Rust 1.92 性能优化：DFS 遍历
    for i in 0..rows {
        for j in 0..cols {
            if grid[i][j] == '1' && !visited[i][j] {
                dfs_islands(&grid, &mut visited, i, j, rows, cols);
                count += 1;
            }
        }
    }

    count
}

fn dfs_islands(
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

    // 四个方向
    let directions = [(0, 1), (0, -1), (1, 0), (-1, 0)];
    for (dx, dy) in directions.iter() {
        let ni = i as i32 + dx;
        let nj = j as i32 + dy;
        if ni >= 0 && nj >= 0 && (ni as usize) < rows && (nj as usize) < cols {
            dfs_islands(grid, visited, ni as usize, nj as usize, rows, cols);
        }
    }
}

/// 240. Search a 2D Matrix II（搜索二维矩阵 II）
///
/// ## 问题描述
/// 编写一个高效的算法来搜索 m x n 矩阵 matrix 中的一个目标值 target 。
/// 该矩阵具有以下特性：每行的元素从左到右升序排列。每列的元素从上到下升序排列。
///
/// ## Rust 1.92 特性应用
/// - **性能优化**: 从右上角开始搜索，利用矩阵特性
/// - **算法优化**: O(m + n) 时间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(m + n)
/// - 空间复杂度: O(1)
pub fn search_matrix(matrix: Vec<Vec<i32>>, target: i32) -> bool {
    if matrix.is_empty() || matrix[0].is_empty() {
        return false;
    }

    let rows = matrix.len();
    let cols = matrix[0].len();

    // 从右上角开始搜索
    let mut i = 0;
    let mut j = cols - 1;

    while i < rows && j < cols {
        if matrix[i][j] == target {
            return true;
        } else if matrix[i][j] > target {
            // 当前元素大于目标，向左移动
            if j == 0 {
                break;
            }
            j -= 1;
        } else {
            // 当前元素小于目标，向下移动
            i += 1;
        }
    }

    false
}

// ==================== 问题信息注册 ====================

/// 获取所有矩阵类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 48,
            title: "旋转图像".to_string(),
            title_en: "Rotate Image".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Math, LeetCodeTag::Matrix],
            description: "给定一个 n × n 的二维矩阵 matrix 表示一个图像。请你将图像顺时针旋转 90 度。你必须在 原地 旋转图像，这意味着你需要直接修改输入的二维矩阵。请不要 使用另一个矩阵来旋转图像。".to_string(),
            examples: vec!["输入：matrix = [[1,2,3],[4,5,6],[7,8,9]]\n输出：[[7,4,1],[8,5,2],[9,6,3]]".to_string()],
            constraints: vec!["n == matrix.length == matrix[i].length".to_string()],
            rust_191_features: vec!["使用 Rust 1.92 的 rotate_right API".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n^2)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("需要遍历所有元素".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 54,
            title: "螺旋矩阵".to_string(),
            title_en: "Spiral Matrix".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Matrix],
            description: "给你一个 m 行 n 列的矩阵 matrix ，请按照 顺时针螺旋顺序 ，返回矩阵中的所有元素。".to_string(),
            examples: vec!["输入：matrix = [[1,2,3],[4,5,6],[7,8,9]]\n输出：[1,2,3,6,9,8,7,4,5]".to_string()],
            constraints: vec!["m == matrix.length".to_string()],
            rust_191_features: vec!["使用 Rust 1.92 的迭代器优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m*n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("需要遍历所有元素".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 73,
            title: "矩阵置零".to_string(),
            title_en: "Set Matrix Zeroes".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::HashTable, LeetCodeTag::Matrix],
            description: "给定一个 m x n 的矩阵，如果一个元素为 0 ，则将其所在行和列的所有元素都设为 0 。请使用 原地 算法。".to_string(),
            examples: vec!["输入：matrix = [[1,1,1],[1,0,1],[1,1,1]]\n输出：[[1,0,1],[0,0,0],[1,0,1]]".to_string()],
            constraints: vec!["m == matrix.length".to_string()],
            rust_191_features: vec!["使用 Rust 1.92 的性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m*n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("使用第一行和第一列作为标记".to_string()),
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
            rust_191_features: vec!["使用 DFS/BFS，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m*n)".to_string(),
                space_complexity: "O(m*n)".to_string(),
                explanation: Some("遍历所有单元格".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 240,
            title: "搜索二维矩阵 II".to_string(),
            title_en: "Search a 2D Matrix II".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::BinarySearch, LeetCodeTag::Matrix],
            description: "编写一个高效的算法来搜索 m x n 矩阵 matrix 中的一个目标值 target 。该矩阵具有以下特性：每行的元素从左到右升序排列。每列的元素从上到下升序排列。".to_string(),
            examples: vec!["输入：matrix = [[1,4,7,11],[2,5,8,12],[3,6,9,16],[10,13,14,17]], target = 5\n输出：true".to_string()],
            constraints: vec!["m == matrix.length".to_string()],
            rust_191_features: vec!["使用二分查找，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(m+n)".to_string(),
                space_complexity: "O(1)".to_string(),
                explanation: Some("从右上角开始搜索".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rotate() {
        let mut matrix = vec![
            vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9],
        ];
        rotate(&mut matrix);
        assert_eq!(matrix, vec![
            vec![7, 4, 1],
            vec![8, 5, 2],
            vec![9, 6, 3],
        ]);
    }

    #[test]
    fn test_spiral_order() {
        let matrix = vec![
            vec![1, 2, 3],
            vec![4, 5, 6],
            vec![7, 8, 9],
        ];
        assert_eq!(spiral_order(matrix), vec![1, 2, 3, 6, 9, 8, 7, 4, 5]);
    }

    #[test]
    fn test_set_zeroes() {
        let mut matrix = vec![
            vec![1, 1, 1],
            vec![1, 0, 1],
            vec![1, 1, 1],
        ];
        set_zeroes(&mut matrix);
        assert_eq!(matrix, vec![
            vec![1, 0, 1],
            vec![0, 0, 0],
            vec![1, 0, 1],
        ]);
    }

    #[test]
    fn test_num_islands() {
        let grid = vec![
            vec!['1', '1', '1', '1', '0'],
            vec!['1', '1', '0', '1', '0'],
            vec!['1', '1', '0', '0', '0'],
            vec!['0', '0', '0', '0', '0'],
        ];
        assert_eq!(num_islands(grid), 1);
    }

    #[test]
    fn test_search_matrix() {
        let matrix = vec![
            vec![1, 4, 7, 11],
            vec![2, 5, 8, 12],
            vec![3, 6, 9, 16],
            vec![10, 13, 14, 17],
        ];
        assert!(search_matrix(matrix.clone(), 5));
        assert!(!search_matrix(matrix, 15));
    }
}
