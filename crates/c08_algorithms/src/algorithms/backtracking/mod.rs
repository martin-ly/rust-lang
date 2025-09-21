//! # 回溯算法模块
//! 
//! 本模块实现了各种回溯算法。

//use serde::{Serialize, Deserialize};

/// 回溯算法实现
pub struct BacktrackingAlgorithms;

impl BacktrackingAlgorithms {
    /// N 皇后问题
    pub fn n_queens(n: usize) -> Vec<Vec<usize>> {
        let mut solutions = Vec::new();
        let mut board = vec![0; n];
        
        Self::n_queens_recursive(&mut board, 0, &mut solutions);
        solutions
    }
    
    fn n_queens_recursive(board: &mut [usize], row: usize, solutions: &mut Vec<Vec<usize>>) {
        if row == board.len() {
            solutions.push(board.to_vec());
            return;
        }
        
        for col in 0..board.len() {
            if Self::is_safe(board, row, col) {
                board[row] = col;
                Self::n_queens_recursive(board, row + 1, solutions);
            }
        }
    }
    
    fn is_safe(board: &[usize], row: usize, col: usize) -> bool {
        for i in 0..row {
            if board[i] == col || 
               board[i] as i32 - col as i32 == i as i32 - row as i32 ||
               board[i] as i32 - col as i32 == row as i32 - i as i32 {
                return false;
            }
        }
        true
    }

    /// 全排列
    pub fn permutations(nums: &[i32]) -> Vec<Vec<i32>> {
        let mut result = Vec::new();
        let mut current = Vec::new();
        let mut used = vec![false; nums.len()];
        
        Self::permutations_recursive(nums, &mut current, &mut used, &mut result);
        result
    }
    
    fn permutations_recursive(
        nums: &[i32],
        current: &mut Vec<i32>,
        used: &mut [bool],
        result: &mut Vec<Vec<i32>>,
    ) {
        if current.len() == nums.len() {
            result.push(current.clone());
            return;
        }
        
        for i in 0..nums.len() {
            if !used[i] {
                used[i] = true;
                current.push(nums[i]);
                Self::permutations_recursive(nums, current, used, result);
                current.pop();
                used[i] = false;
            }
        }
    }
}
