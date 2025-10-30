//! # 数组处理示例
//!
//! 展示如何在 WASM 和 JavaScript 之间传递和处理数组数据
//!
//! ## 运行方式
//!
//! ```bash
//! # 使用 wasm-pack 构建
//! wasm-pack build --target web
//! ```
//!
//! ## JavaScript 使用示例
//!
//! ```javascript
//! import init, {
//!     sum_array,
//!     average,
//!     find_max,
//!     filter_positive
//! } from './pkg/c12_wasm.js';
//!
//! await init();
//!
//! const numbers = new Int32Array([1, -2, 3, -4, 5]);
//! console.log('Sum:', sum_array(numbers));           // 3
//! console.log('Average:', average(numbers));         // 0.6
//! console.log('Max:', find_max(numbers));            // 5
//! console.log('Positive:', filter_positive(numbers)); // [1, 3, 5]
//! ```

use wasm_bindgen::prelude::*;

/// 计算数组总和
///
/// # 参数
/// - `arr`: 整数数组
///
/// # 返回值
/// 返回数组中所有元素的和
#[wasm_bindgen]
pub fn sum_array(arr: &[i32]) -> i32 {
    arr.iter().sum()
}

/// 计算数组平均值
///
/// # 参数
/// - `arr`: 浮点数数组
///
/// # 返回值
/// 返回平均值，如果数组为空则返回 0.0
#[wasm_bindgen]
pub fn average(arr: &[f64]) -> f64 {
    if arr.is_empty() {
        return 0.0;
    }
    let sum: f64 = arr.iter().sum();
    sum / (arr.len() as f64)
}

/// 查找最大值
///
/// # 参数
/// - `arr`: 整数数组
///
/// # 返回值
/// 返回最大值，如果数组为空则返回 None (JavaScript 中为 undefined)
#[wasm_bindgen]
pub fn find_max(arr: &[i32]) -> Option<i32> {
    arr.iter().max().copied()
}

/// 查找最小值
#[wasm_bindgen]
pub fn find_min(arr: &[i32]) -> Option<i32> {
    arr.iter().min().copied()
}

/// 过滤正数
///
/// # 参数
/// - `arr`: 整数数组
///
/// # 返回值
/// 返回只包含正数的新数组
#[wasm_bindgen]
pub fn filter_positive(arr: &[i32]) -> Vec<i32> {
    arr.iter().filter(|&&x| x > 0).copied().collect()
}

/// 过滤偶数
#[wasm_bindgen]
pub fn filter_even(arr: &[i32]) -> Vec<i32> {
    arr.iter().filter(|&&x| x % 2 == 0).copied().collect()
}

/// 映射：所有元素乘以2
///
/// # 参数
/// - `arr`: 整数数组
///
/// # 返回值
/// 返回新数组，每个元素都是原来的2倍
#[wasm_bindgen]
pub fn double_elements(arr: &[i32]) -> Vec<i32> {
    arr.iter().map(|&x| x * 2).collect()
}

/// 反转数组
///
/// # 参数
/// - `arr`: 整数数组
///
/// # 返回值
/// 返回反转后的新数组
#[wasm_bindgen]
pub fn reverse_array(arr: &[i32]) -> Vec<i32> {
    arr.iter().rev().copied().collect()
}

/// 排序数组（升序）
///
/// # 参数
/// - `arr`: 整数数组
///
/// # 返回值
/// 返回排序后的新数组
#[wasm_bindgen]
pub fn sort_ascending(arr: &[i32]) -> Vec<i32> {
    let mut result = arr.to_vec();
    result.sort();
    result
}

/// 去重
///
/// # 参数
/// - `arr`: 整数数组
///
/// # 返回值
/// 返回去重后的新数组（保持原始顺序）
#[wasm_bindgen]
pub fn unique(arr: &[i32]) -> Vec<i32> {
    let mut seen = std::collections::HashSet::new();
    arr.iter().filter(|&x| seen.insert(*x)).copied().collect()
}

#[wasm_bindgen(start)]
#[allow(clippy::main_recursion)]
pub fn main() {
    #[cfg(target_arch = "wasm32")]
    {
        use web_sys::console;
        console::log_1(&"Array processing example loaded!".into());

        let test_arr = vec![1, -2, 3, -4, 5];
        console::log_1(&format!("Sum: {}", sum_array(&test_arr)).into());
        console::log_1(&format!("Max: {:?}", find_max(&test_arr)).into());
        console::log_1(&format!("Positive: {:?}", filter_positive(&test_arr)).into());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sum_array() {
        assert_eq!(sum_array(&[1, 2, 3, 4, 5]), 15);
        assert_eq!(sum_array(&[]), 0);
        assert_eq!(sum_array(&[-1, 1]), 0);
    }

    #[test]
    fn test_average() {
        assert_eq!(average(&[1.0, 2.0, 3.0, 4.0, 5.0]), 3.0);
        assert_eq!(average(&[]), 0.0);
    }

    #[test]
    fn test_find_max_min() {
        assert_eq!(find_max(&[1, 5, 3, 2, 4]), Some(5));
        assert_eq!(find_min(&[1, 5, 3, 2, 4]), Some(1));
        assert_eq!(find_max(&[]), None);
    }

    #[test]
    fn test_filters() {
        assert_eq!(filter_positive(&[1, -2, 3, -4, 5]), vec![1, 3, 5]);
        assert_eq!(filter_even(&[1, 2, 3, 4, 5]), vec![2, 4]);
    }

    #[test]
    fn test_operations() {
        assert_eq!(double_elements(&[1, 2, 3]), vec![2, 4, 6]);
        assert_eq!(reverse_array(&[1, 2, 3]), vec![3, 2, 1]);
        assert_eq!(unique(&[1, 2, 2, 3, 1, 4]), vec![1, 2, 3, 4]);
    }
}
