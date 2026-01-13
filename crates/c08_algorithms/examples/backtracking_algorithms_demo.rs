//! 回溯算法示例
//!
//! 本示例展示C08算法模块的回溯算法：
//! - N皇后问题
//! - 全排列
//! - 子集生成
//!
//! 运行方式:
//! ```bash
//! cargo run --example backtracking_algorithms_demo
//! ```

fn main() {
    println!("🚀 回溯算法示例\n");
    println!("{}", "=".repeat(60));

    // 1. N皇后问题
    println!("\n📊 N皇后问题（4皇后）:");
    println!("{}", "-".repeat(60));
    let n = 4;
    let solutions = n_queens(n);
    println!("{}皇后问题的解数量: {}", n, solutions.len());
    for (i, solution) in solutions.iter().take(2).enumerate() {
        println!("解 {}: {:?}", i + 1, solution);
    }

    // 2. 全排列
    println!("\n📊 全排列:");
    println!("{}", "-".repeat(60));
    let nums = vec![1, 2, 3];
    let permutations = generate_permutations(&nums);
    println!("数组: {:?}", nums);
    println!("全排列: {:?}", permutations);

    // 3. 子集生成
    println!("\n📊 子集生成:");
    println!("{}", "-".repeat(60));
    let nums = vec![1, 2, 3];
    let subsets = generate_subsets(&nums);
    println!("数组: {:?}", nums);
    println!("所有子集: {:?}", subsets);

    // 4. 算法说明
    println!("\n💡 回溯算法说明:");
    println!("{}", "-".repeat(60));
    println!("  核心思想: 尝试所有可能的解，遇到不符合条件的回溯");
    println!("  适用场景: 组合问题、排列问题、约束满足问题");
    println!("  时间复杂度: 通常为指数级");

    println!("\n✅ 回溯算法演示完成！");
}

/// N皇后问题
fn n_queens(n: usize) -> Vec<Vec<usize>> {
    let mut solutions = Vec::new();
    let mut board = vec![0; n];

    fn is_valid(board: &[usize], row: usize, col: usize) -> bool {
        for i in 0..row {
            if board[i] == col
                || (board[i] as i32 - col as i32).abs() == (i as i32 - row as i32).abs()
            {
                return false;
            }
        }
        true
    }

    fn backtrack(board: &mut Vec<usize>, row: usize, n: usize, solutions: &mut Vec<Vec<usize>>) {
        if row == n {
            solutions.push(board.clone());
            return;
        }

        for col in 0..n {
            if is_valid(board, row, col) {
                board[row] = col;
                backtrack(board, row + 1, n, solutions);
            }
        }
    }

    backtrack(&mut board, 0, n, &mut solutions);
    solutions
}

/// 生成全排列
fn generate_permutations(nums: &[i32]) -> Vec<Vec<i32>> {
    if nums.is_empty() {
        return vec![vec![]];
    }

    let mut result = Vec::new();
    for i in 0..nums.len() {
        let mut rest = nums.to_vec();
        rest.remove(i);
        let mut perms = generate_permutations(&rest);
        for perm in &mut perms {
            perm.insert(0, nums[i]);
            result.push(perm.clone());
        }
    }

    result
}

/// 生成所有子集
fn generate_subsets(nums: &[i32]) -> Vec<Vec<i32>> {
    let mut result = vec![vec![]];

    for &num in nums {
        let mut new_subsets = Vec::new();
        for subset in &result {
            let mut new_subset = subset.clone();
            new_subset.push(num);
            new_subsets.push(new_subset);
        }
        result.append(&mut new_subsets);
    }

    result
}
