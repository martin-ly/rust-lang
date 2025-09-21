//! # 组合数学算法模块
//! 
//! 本模块实现了各种组合数学算法。

//use serde::{Serialize, Deserialize};

/// 组合数学算法实现
pub struct CombinatoricsAlgorithms;

impl CombinatoricsAlgorithms {
    /// 计算阶乘
    pub fn factorial(n: u64) -> u64 {
        if n <= 1 {
            1
        } else {
            n * Self::factorial(n - 1)
        }
    }

    /// 计算组合数 C(n, k)
    pub fn combination(n: u64, k: u64) -> u64 {
        if k > n {
            0
        } else if k == 0 || k == n {
            1
        } else {
            Self::factorial(n) / (Self::factorial(k) * Self::factorial(n - k))
        }
    }

    /// 计算排列数 P(n, k)
    pub fn permutation(n: u64, k: u64) -> u64 {
        if k > n {
            0
        } else {
            Self::factorial(n) / Self::factorial(n - k)
        }
    }

    /// 生成所有组合
    pub fn generate_combinations(n: usize, k: usize) -> Vec<Vec<usize>> {
        let mut result = Vec::new();
        let mut current = Vec::new();
        
        Self::generate_combinations_recursive(0, n, k, &mut current, &mut result);
        result
    }
    
    fn generate_combinations_recursive(
        start: usize,
        n: usize,
        k: usize,
        current: &mut Vec<usize>,
        result: &mut Vec<Vec<usize>>,
    ) {
        if current.len() == k {
            result.push(current.clone());
            return;
        }
        
        for i in start..n {
            current.push(i);
            Self::generate_combinations_recursive(i + 1, n, k, current, result);
            current.pop();
        }
    }

    /// 计算卡塔兰数
    pub fn catalan_number(n: u64) -> u64 {
        if n <= 1 {
            1
        } else {
            Self::combination(2 * n, n) / (n + 1)
        }
    }

    /// 计算斐波那契数
    pub fn fibonacci(n: u64) -> u64 {
        if n <= 1 {
            n
        } else {
            let mut a = 0;
            let mut b = 1;
            
            for _ in 2..=n {
                let temp = a + b;
                a = b;
                b = temp;
            }
            
            b
        }
    }
}
