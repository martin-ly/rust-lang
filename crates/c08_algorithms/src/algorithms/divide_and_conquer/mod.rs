//! # 分治算法模块
//! 
//! 本模块实现了各种分治算法。

//use serde::{Serialize, Deserialize};

/// 分治算法实现
pub struct DivideAndConquerAlgorithms;

impl DivideAndConquerAlgorithms {
    /// 最大子数组和
    pub fn max_subarray_sum(arr: &[i32]) -> i32 {
        if arr.is_empty() {
            return 0;
        }
        
        Self::max_subarray_sum_recursive(arr, 0, arr.len() - 1)
    }
    
    fn max_subarray_sum_recursive(arr: &[i32], left: usize, right: usize) -> i32 {
        if left == right {
            return arr[left];
        }
        
        let mid = left + (right - left) / 2;
        
        let left_max = Self::max_subarray_sum_recursive(arr, left, mid);
        let right_max = Self::max_subarray_sum_recursive(arr, mid + 1, right);
        let cross_max = Self::max_crossing_sum(arr, left, mid, right);
        
        left_max.max(right_max).max(cross_max)
    }
    
    fn max_crossing_sum(arr: &[i32], left: usize, mid: usize, right: usize) -> i32 {
        let mut left_sum = i32::MIN;
        let mut sum = 0;
        
        for i in (left..=mid).rev() {
            sum += arr[i];
            left_sum = left_sum.max(sum);
        }
        
        let mut right_sum = i32::MIN;
        sum = 0;
        
        for item in arr.iter().skip(mid + 1).take(right - mid) {
            sum += *item;
            right_sum = right_sum.max(sum);
        }
        
        left_sum + right_sum
    }
}
