//! # Rust 1.96.0 范围类型新特性实现模块
//!
//! 本模块展示了 Rust 1.96.0 中范围类型的增强，包括：
//! - `RangeInclusive` 和 `RangeToInclusive` 的新方法支持
//! - 范围类型在算法中的高级应用
//! - 迭代器与范围类型的深度集成
//!
//! # 文件信息
//! - 文件: rust_196_features.rs
//! - 创建日期: 2026-04-10
//! - 版本: 1.0
//! - Rust版本: 1.96.0
//! - Edition: 2024

use std::ops::RangeInclusive;

/// Rust 1.96 `if let` guards 在算法中的应用
///
/// `if let` guards 允许在 match arm 上直接进行模式匹配和条件判断，
/// 减少嵌套层级，使代码更扁平、更易读。
pub struct AlgorithmIfLetGuardExamples;

impl AlgorithmIfLetGuardExamples {
    /// 安全地解析数值输入
    pub fn safe_parse_number(input: Option<&str>) -> Result<i32, &'static str> {
        match input {
            Some(s) if let Ok(n) = s.parse::<i32>() => Ok(n),
            Some(_) => Err("输入不是有效的数字"),
            None => Err("输入为空"),
        }
    }

    /// 验证算法参数
    pub fn validate_algorithm_param(param: Result<Option<usize>, &'static str>) -> &'static str {
        match param {
            Ok(Some(n)) if n > 0 && n.is_power_of_two() => "有效的2的幂参数",
            Ok(Some(_)) => "有效的非2的幂参数",
            Ok(None) => "使用默认值",
            Err(_) => "参数错误",
        }
    }
}

// ==================== 1. RangeInclusive 完整功能展示 ====================

/// # RangeInclusive 完整功能展示
///
/// Rust 1.96.0 对 RangeInclusive 提供了完整的标准库支持，
/// 包括各种 trait 实现和方法支持。
///
/// 包含性范围 `[start..=end]` 在实际编程中非常有用，
/// 特别是在需要包含边界值的场景中。
pub struct RangeInclusiveAlgorithms;

impl RangeInclusiveAlgorithms {
    /// 使用 RangeInclusive 进行斐波那契数列生成
    ///
    /// Rust 1.96.0: RangeInclusive 完全支持迭代和索引操作
    pub fn fibonacci_range(n: usize) -> Vec<u64> {
        let mut fib = vec![0u64, 1];
        
        // 使用 RangeInclusive 进行索引迭代
        for i in 2..=n {
            let next = fib[i - 1].wrapping_add(fib[i - 2]);
            fib.push(next);
        }
        
        fib
    }

    /// 使用 RangeInclusive 实现闭区间搜索
    ///
    /// Rust 1.96.0: RangeInclusive 支持包含边界的二分查找
    pub fn inclusive_binary_search(arr: &[i32], target: i32, range: RangeInclusive<usize>) -> Option<usize> {
        let (mut left, mut right) = (*range.start(), *range.end());
        
        // RangeInclusive 保证包含 right 边界
        while left <= right {
            let mid = left + (right - left) / 2;
            
            match arr.get(mid) {
                Some(&val) if val == target => return Some(mid),
                Some(&val) if val < target => left = mid + 1,
                _ => {
                    // 避免 usize 下溢，使用 saturating_sub
                    right = mid.saturating_sub(1);
                }
            }
        }
        
        None
    }

    /// 使用 RangeInclusive 进行区间统计
    ///
    /// 统计在指定闭区间内的元素数量
    pub fn count_in_range<T: Ord>(data: &[T], min: &T, max: &T) -> usize {
        data.iter().filter(|x| min <= *x && *x <= max).count()
    }

    /// 使用 RangeInclusive 进行数值积分（梯形法则）
    ///
    /// Rust 1.96.0: RangeInclusive 的步进迭代支持
    pub fn trapezoidal_integral<F>(range: RangeInclusive<f64>, n: usize, f: F) -> f64
    where
        F: Fn(f64) -> f64,
    {
        let a = *range.start();
        let b = *range.end();
        let h = (b - a) / n as f64;
        
        let mut sum = 0.5 * (f(a) + f(b));
        
        for i in 1..n {
            let x = a + i as f64 * h;
            sum += f(x);
        }
        
        sum * h
    }

    /// 使用 RangeInclusive 生成等差数列
    ///
    /// 生成从 start 到 end（包含）的等差数列
    pub fn arithmetic_sequence(start: i32, end: i32, step: i32) -> Vec<i32> {
        if step == 0 || (start < end && step < 0) || (start > end && step > 0) {
            return vec![];
        }
        
        // 使用 RangeInclusive 的迭代特性
        let mut result = Vec::new();
        let mut current = start;
        
        while (step > 0 && current <= end) || (step < 0 && current >= end) {
            result.push(current);
            current += step;
        }
        
        result
    }

    /// 使用 RangeInclusive 进行滑动窗口统计
    ///
    /// Rust 1.96.0: RangeInclusive 作为窗口边界
    pub fn sliding_window_stats(data: &[f64], window_size: usize) -> Vec<(f64, f64)> {
        if window_size == 0 || data.len() < window_size {
            return vec![];
        }
        
        let mut stats = Vec::new();
        
        for start in 0..=data.len() - window_size {
            let end = start + window_size - 1;
            let window = &data[start..=end];
            
            let sum: f64 = window.iter().sum();
            let mean = sum / window.len() as f64;
            
            let variance: f64 = window.iter()
                .map(|&x| (x - mean).powi(2))
                .sum::<f64>() / window.len() as f64;
            let std_dev = variance.sqrt();
            
            stats.push((mean, std_dev));
        }
        
        stats
    }

    /// 使用 RangeInclusive 进行分段线性插值
    pub fn piecewise_linear_interpolation(
        points: &[(f64, f64)],
        x_range: RangeInclusive<f64>,
        steps: usize,
    ) -> Vec<(f64, f64)> {
        if points.len() < 2 || steps == 0 {
            return vec![];
        }
        
        let x_min = *x_range.start();
        let x_max = *x_range.end();
        let step_size = (x_max - x_min) / steps as f64;
        
        let mut result = Vec::with_capacity(steps + 1);
        
        for i in 0..=steps {
            let x = x_min + i as f64 * step_size;
            
            // 找到 x 所在的区间
            let mut y = 0.0;
            for j in 0..points.len() - 1 {
                let (x1, y1) = points[j];
                let (x2, y2) = points[j + 1];
                
                if x >= x1 && x <= x2 {
                    // 线性插值
                    let t = (x - x1) / (x2 - x1);
                    y = y1 + t * (y2 - y1);
                    break;
                }
            }
            
            result.push((x, y));
        }
        
        result
    }
}

// ==================== 2. RangeToInclusive 功能展示 ====================

/// # RangeToInclusive 功能展示
///
/// Rust 1.96.0 中对 RangeToInclusive (`..=end`) 的完整支持。
/// RangeToInclusive 表示从起始到指定值（包含）的范围。
pub struct RangeToInclusiveAlgorithms;

impl RangeToInclusiveAlgorithms {
    /// 使用 RangeToInclusive 获取前缀统计信息
    ///
    /// Rust 1.96.0: RangeToInclusive 支持切片索引
    pub fn prefix_statistics(data: &[i32], end: usize) -> (i32, f64, i32, i32) {
        let prefix = &data[..=end.min(data.len().saturating_sub(1))];
        
        if prefix.is_empty() {
            return (0, 0.0, 0, 0);
        }
        
        let sum: i32 = prefix.iter().sum();
        let mean = sum as f64 / prefix.len() as f64;
        let min = *prefix.iter().min().unwrap_or(&0);
        let max = *prefix.iter().max().unwrap_or(&0);
        
        (sum, mean, min, max)
    }

    /// 使用 RangeToInclusive 进行前缀和计算
    ///
    /// 计算从起始到每个位置的累积和
    pub fn prefix_sums(data: &[i32]) -> Vec<i32> {
        let mut sums = Vec::with_capacity(data.len());
        let mut current_sum = 0;
        
        for &val in data.iter() {
            current_sum += val;
            sums.push(current_sum);
        }
        
        sums
    }

    /// 使用 RangeToInclusive 查找最长非递减前缀
    pub fn longest_non_decreasing_prefix(data: &[i32]) -> usize {
        if data.len() <= 1 {
            return data.len();
        }
        
        for i in 0..data.len() - 1 {
            if data[i] > data[i + 1] {
                return i + 1;
            }
        }
        
        data.len()
    }

    /// 使用 RangeToInclusive 进行累积最大值计算
    pub fn cumulative_maximum(data: &[i32]) -> Vec<i32> {
        let mut max_vals = Vec::with_capacity(data.len());
        let mut current_max = i32::MIN;
        
        for &val in data {
            current_max = current_max.max(val);
            max_vals.push(current_max);
        }
        
        max_vals
    }

    /// 使用 RangeToInclusive 模式匹配
    ///
    /// 展示如何在 match 中使用范围模式
    pub fn classify_by_range(value: usize) -> &'static str {
        match value {
            0..=10 => "small",
            11..=100 => "medium",
            101..=1000 => "large",
            _ => "huge",
        }
    }

    /// 使用 RangeToInclusive 进行数字分桶
    pub fn bucket_values(data: &[f64], bucket_count: usize, max_value: f64) -> Vec<usize> {
        let bucket_size = max_value / bucket_count as f64;
        let mut buckets = vec![0usize; bucket_count];
        
        for &val in data {
            let bucket_idx = ((val / bucket_size).min(bucket_count as f64 - 1.0)) as usize;
            buckets[bucket_idx] += 1;
        }
        
        buckets
    }
}

// ==================== 3. 范围类型组合使用 ====================

/// # 范围类型组合使用
///
/// 展示 Rust 1.96.0 中各种范围类型的组合和转换。
pub struct RangeCompositionAlgorithms;

impl RangeCompositionAlgorithms {
    /// 将各种范围类型转换为 RangeInclusive
    ///
    /// 展示范围类型之间的转换能力
    pub fn to_inclusive_range<R>(range: R, max_bound: usize) -> RangeInclusive<usize>
    where
        R: RangeBounds<usize>,
    {
        let start = match range.start_bound() {
            std::ops::Bound::Included(&n) => n,
            std::ops::Bound::Excluded(&n) => n + 1,
            std::ops::Bound::Unbounded => 0,
        };
        
        let end = match range.end_bound() {
            std::ops::Bound::Included(&n) => n,
            std::ops::Bound::Excluded(&n) => n.saturating_sub(1),
            std::ops::Bound::Unbounded => max_bound,
        };
        
        start..=end
    }

    /// 范围裁剪
    ///
    /// 将给定的范围裁剪到有效边界内
    pub fn clamp_range(range: RangeInclusive<usize>, min: usize, max: usize) -> RangeInclusive<usize> {
        let start = (*range.start()).max(min).min(max);
        let end = (*range.end()).max(min).min(max).max(start);
        
        start..=end
    }

    /// 范围交集计算
    ///
    /// 计算两个 RangeInclusive 的交集
    pub fn range_intersection(
        a: RangeInclusive<usize>,
        b: RangeInclusive<usize>,
    ) -> Option<RangeInclusive<usize>> {
        let start = (*a.start()).max(*b.start());
        let end = (*a.end()).min(*b.end());
        
        if start <= end {
            Some(start..=end)
        } else {
            None
        }
    }

    /// 范围并集计算
    ///
    /// 计算两个 RangeInclusive 的最小并集范围
    pub fn range_union(
        a: RangeInclusive<usize>,
        b: RangeInclusive<usize>,
    ) -> RangeInclusive<usize> {
        let start = (*a.start()).min(*b.start());
        let end = (*a.end()).max(*b.end());
        
        start..=end
    }

    /// 使用范围类型进行数据分页
    ///
    /// 展示 RangeInclusive 在实际分页场景中的应用
    pub fn paginate<T>(data: &[T], page: usize, page_size: usize) -> &[T] {
        let start = page * page_size;
        let end = ((page + 1) * page_size - 1).min(data.len().saturating_sub(1));
        
        if start > end || start >= data.len() {
            return &[];
        }
        
        &data[start..=end]
    }

    /// 迭代范围生成器
    ///
    /// 生成一系列连续的范围
    pub fn generate_ranges(total: usize, chunk_size: usize) -> Vec<RangeInclusive<usize>> {
        let mut ranges = Vec::new();
        let mut start = 0;
        
        while start < total {
            let end = (start + chunk_size - 1).min(total - 1);
            ranges.push(start..=end);
            start = end + 1;
        }
        
        ranges
    }
}

use std::ops::RangeBounds;

// ==================== 4. 实际应用示例 ====================

/// # 实际应用示例
///
/// 展示 RangeInclusive 和 RangeToInclusive 在实际编程中的应用。
pub struct RangePracticalApplications;

impl RangePracticalApplications {
    /// 日期范围查询（模拟）
    ///
    /// 使用 RangeInclusive 表示闭区间日期范围
    pub fn query_date_range(events: &[(u32, String)], range: RangeInclusive<u32>) -> Vec<String> {
        events
            .iter()
            .filter(|(date, _)| range.contains(date))
            .map(|(_, event)| event.clone())
            .collect()
    }

    /// 温度范围监控
    ///
    /// 使用 RangeInclusive 定义安全的温度范围
    pub fn check_temperature_range(readings: &[f64], safe_range: RangeInclusive<f64>) -> Vec<(usize, f64, &'static str)> {
        readings
            .iter()
            .enumerate()
            .filter(|&(_, temp)| !safe_range.contains(temp))
            .map(|(idx, &temp)| {
                let status = if temp < *safe_range.start() {
                    "too_low"
                } else {
                    "too_high"
                };
                (idx, temp, status)
            })
            .collect()
    }

    /// 成绩等级划分
    ///
    /// 使用 RangeToInclusive 进行区间分类
    pub fn grade_score(score: u8) -> char {
        match score {
            90..=100 => 'A',
            80..=89 => 'B',
            70..=79 => 'C',
            60..=69 => 'D',
            0..=59 => 'F',
            _ => '?',
        }
    }

    /// 批量处理任务分配
    ///
    /// 使用 RangeInclusive 为工作线程分配任务范围
    pub fn distribute_tasks(total_tasks: usize, worker_count: usize) -> Vec<RangeInclusive<usize>> {
        if worker_count == 0 || total_tasks == 0 {
            return vec![];
        }
        
        let base_chunk = total_tasks / worker_count;
        let remainder = total_tasks % worker_count;
        
        let mut ranges = Vec::with_capacity(worker_count);
        let mut start = 0;
        
        for i in 0..worker_count {
            let chunk_size = base_chunk + if i < remainder { 1 } else { 0 };
            if chunk_size == 0 {
                continue;
            }
            let end = start + chunk_size - 1;
            ranges.push(start..=end);
            start = end + 1;
        }
        
        ranges
    }

    /// 资源使用限制检查
    ///
    /// 使用 RangeInclusive 定义允许的资源使用范围
    pub fn check_resource_usage(usage: &[f64], allowed_range: RangeInclusive<f64>) -> bool {
        usage.iter().all(|&u| allowed_range.contains(&u))
    }
}

// ==================== 5. 演示函数 ====================

/// 演示 RangeInclusive 的使用
#[allow(dead_code)]
pub fn demonstrate_range_inclusive() {
    println!("\n=== RangeInclusive 演示 ===\n");

    // 斐波那契数列
    let fib = RangeInclusiveAlgorithms::fibonacci_range(10);
    println!("斐波那契数列 (0..=10): {:?}", fib);

    // 闭区间二分查找
    let arr = vec![1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
    let range = 2..=7;
    if let Some(idx) = RangeInclusiveAlgorithms::inclusive_binary_search(&arr, 13, range.clone()) {
        println!("在范围 {:?} 中找到 13 在索引: {}", range, idx);
    }

    // 区间统计
    let data = vec![1, 5, 10, 15, 20, 25, 30];
    let count = RangeInclusiveAlgorithms::count_in_range(&data, &10, &20);
    println!("在 [10, 20] 范围内的元素数量: {}", count);

    // 数值积分
    let integral = RangeInclusiveAlgorithms::trapezoidal_integral(0.0..=1.0, 100, |x| x * x);
    println!("x² 在 [0, 1] 上的积分: {:.6} (理论值: 0.333333)", integral);

    // 等差数列
    let seq = RangeInclusiveAlgorithms::arithmetic_sequence(0, 20, 5);
    println!("等差数列 (0..=20, step=5): {:?}", seq);

    // 滑动窗口统计
    let window_data = vec![1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
    let stats = RangeInclusiveAlgorithms::sliding_window_stats(&window_data, 3);
    println!("滑动窗口统计 (size=3): {:?}", stats);
}

/// 演示 RangeToInclusive 的使用
#[allow(dead_code)]
pub fn demonstrate_range_to_inclusive() {
    println!("\n=== RangeToInclusive 演示 ===\n");

    // 前缀统计
    let data = vec![10, 20, 30, 40, 50, 60, 70, 80, 90, 100];
    let (sum, mean, min, max) = RangeToInclusiveAlgorithms::prefix_statistics(&data, 4);
    println!("前 5 个元素的统计: sum={}, mean={:.2}, min={}, max={}", sum, mean, min, max);

    // 前缀和
    let sums = RangeToInclusiveAlgorithms::prefix_sums(&data);
    println!("前缀和: {:?}", sums);

    // 累积最大值
    let cum_max = RangeToInclusiveAlgorithms::cumulative_maximum(&data);
    println!("累积最大值: {:?}", cum_max);

    // 范围分类
    for val in [5, 50, 500, 5000] {
        let category = RangeToInclusiveAlgorithms::classify_by_range(val);
        println!("{} 分类为: {}", val, category);
    }

    // 数字分桶
    let values = vec![0.5, 1.2, 2.8, 3.5, 4.9, 5.1, 6.7, 7.8, 8.9, 9.5];
    let buckets = RangeToInclusiveAlgorithms::bucket_values(&values, 5, 10.0);
    println!("数值分桶结果: {:?}", buckets);
}

/// 演示范围类型组合使用
#[allow(dead_code)]
pub fn demonstrate_range_composition() {
    println!("\n=== 范围类型组合演示 ===\n");

    // 范围转换
    let inclusive = RangeCompositionAlgorithms::to_inclusive_range(5..15, 100);
    println!("Range 转换为 RangeInclusive: {:?}", inclusive);

    // 范围裁剪
    let clamped = RangeCompositionAlgorithms::clamp_range(0..=100, 20, 80);
    println!("范围 [0, 100] 裁剪到 [20, 80]: {:?}", clamped);

    // 范围交集
    let a = 10..=50;
    let b = 30..=70;
    if let Some(intersection) = RangeCompositionAlgorithms::range_intersection(a.clone(), b.clone()) {
        println!("{:?} 和 {:?} 的交集: {:?}", a, b, intersection);
    }

    // 范围并集
    let union = RangeCompositionAlgorithms::range_union(a.clone(), b.clone());
    println!("{:?} 和 {:?} 的并集: {:?}", a, b, union);

    // 数据分页
    let data: Vec<i32> = (1..=100).collect();
    let page = RangeCompositionAlgorithms::paginate(&data, 2, 10);
    println!("第 3 页数据 (每页 10 个): {:?}", page);

    // 范围生成
    let ranges = RangeCompositionAlgorithms::generate_ranges(100, 15);
    println!("将 100 个元素分成约 15 个元素的块: {:?}", ranges);
}

/// 演示实际应用场景
#[allow(dead_code)]
pub fn demonstrate_practical_applications() {
    println!("\n=== 实际应用场景演示 ===\n");

    // 日期查询
    let events = vec![
        (1, "新年".to_string()),
        (14, "情人节".to_string()),
        (88, "妇女节".to_string()),
        (121, "劳动节".to_string()),
        (172, "端午节".to_string()),
        (271, "国庆节".to_string()),
    ];
    let date_range = 50..=180;
    let found = RangePracticalApplications::query_date_range(&events, date_range.clone());
    println!("在日期范围 {:?} 内的事件: {:?}", date_range, found);

    // 温度监控
    let temps = vec![18.5, 19.2, 22.1, 25.8, 28.3, 31.5, 29.2, 26.1, 23.5, 20.8];
    let safe_range = 15.0..=30.0;
    let alerts = RangePracticalApplications::check_temperature_range(&temps, safe_range.clone());
    println!("温度异常警报 (安全范围 {:?}): {:?}", safe_range, alerts);

    // 成绩等级
    for score in [95, 85, 75, 65, 55] {
        let grade = RangePracticalApplications::grade_score(score);
        println!("分数 {} 对应等级: {}", score, grade);
    }

    // 任务分配
    let tasks = RangePracticalApplications::distribute_tasks(100, 4);
    println!("100 个任务分配给 4 个工人: {:?}", tasks);

    // 资源使用检查
    let cpu_usage = vec![45.2, 52.1, 48.7, 61.3, 55.8];
    let allowed = 20.0..=80.0;
    let is_ok = RangePracticalApplications::check_resource_usage(&cpu_usage, allowed.clone());
    println!("CPU 使用率 {:?} 是否在允许范围 {:?} 内: {}", cpu_usage, allowed, is_ok);
}

/// 演示 Rust 1.96.0 范围类型特性
pub fn demonstrate_rust_196_range_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 范围类型特性演示");
    println!("========================================\n");

    demonstrate_range_inclusive();
    demonstrate_range_to_inclusive();
    demonstrate_range_composition();
    demonstrate_practical_applications();

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 Rust 1.96.0 范围类型特性信息
pub fn get_rust_196_range_info() -> String {
    "Rust 1.96.0 范围类型特性:\n\
        - RangeInclusive 完整功能支持 [start..=end]\n\
        - RangeToInclusive 功能支持 [..=end]\n\
        - 范围类型组合和转换\n\
        - 范围交集、并集、裁剪操作\n\
        - 实际应用场景：分页、任务分配、范围查询"
        .to_string()
}

// ==================== 测试 ====================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fibonacci_range() {
        let fib = RangeInclusiveAlgorithms::fibonacci_range(10);
        assert_eq!(fib, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55]);
    }

    #[test]
    fn test_inclusive_binary_search() {
        let arr = vec![1, 3, 5, 7, 9, 11, 13, 15];
        
        // 在范围内查找
        assert_eq!(RangeInclusiveAlgorithms::inclusive_binary_search(&arr, 7, 1..=5), Some(3));
        
        // 不在范围内
        assert_eq!(RangeInclusiveAlgorithms::inclusive_binary_search(&arr, 1, 2..=5), None);
        
        // 不存在
        assert_eq!(RangeInclusiveAlgorithms::inclusive_binary_search(&arr, 6, 0..=7), None);
    }

    #[test]
    fn test_count_in_range() {
        let data = vec![1, 5, 10, 15, 20, 25];
        assert_eq!(RangeInclusiveAlgorithms::count_in_range(&data, &5, &20), 4);
        assert_eq!(RangeInclusiveAlgorithms::count_in_range(&data, &0, &100), 6);
        assert_eq!(RangeInclusiveAlgorithms::count_in_range(&data, &50, &100), 0);
    }

    #[test]
    fn test_trapezoidal_integral() {
        // ∫x² dx from 0 to 1 = 1/3
        let result = RangeInclusiveAlgorithms::trapezoidal_integral(0.0..=1.0, 1000, |x| x * x);
        assert!((result - 1.0 / 3.0).abs() < 0.001);
    }

    #[test]
    fn test_arithmetic_sequence() {
        assert_eq!(
            RangeInclusiveAlgorithms::arithmetic_sequence(0, 20, 5),
            vec![0, 5, 10, 15, 20]
        );
        assert_eq!(
            RangeInclusiveAlgorithms::arithmetic_sequence(10, 0, -2),
            vec![10, 8, 6, 4, 2, 0]
        );
        assert!(RangeInclusiveAlgorithms::arithmetic_sequence(0, 10, 0).is_empty());
    }

    #[test]
    fn test_sliding_window_stats() {
        let data = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        let stats = RangeInclusiveAlgorithms::sliding_window_stats(&data, 3);
        assert_eq!(stats.len(), 3);
        
        // 第一个窗口 [1, 2, 3]: mean=2, std=sqrt(2/3)
        assert!((stats[0].0 - 2.0).abs() < 0.001);
    }

    #[test]
    fn test_prefix_statistics() {
        let data = vec![10, 20, 30, 40, 50];
        let (sum, mean, min, max) = RangeToInclusiveAlgorithms::prefix_statistics(&data, 2);
        assert_eq!(sum, 60);
        assert_eq!(mean, 20.0);
        assert_eq!(min, 10);
        assert_eq!(max, 30);
    }

    #[test]
    fn test_classify_by_range() {
        assert_eq!(RangeToInclusiveAlgorithms::classify_by_range(5), "small");
        assert_eq!(RangeToInclusiveAlgorithms::classify_by_range(50), "medium");
        assert_eq!(RangeToInclusiveAlgorithms::classify_by_range(500), "large");
        assert_eq!(RangeToInclusiveAlgorithms::classify_by_range(5000), "huge");
    }

    #[test]
    fn test_range_intersection() {
        let a = 10..=50;
        let b = 30..=70;
        assert_eq!(
            RangeCompositionAlgorithms::range_intersection(a, b),
            Some(30..=50)
        );
        
        let c = 60..=80;
        assert_eq!(
            RangeCompositionAlgorithms::range_intersection(10..=20, c),
            None
        );
    }

    #[test]
    fn test_range_union() {
        let a = 10..=30;
        let b = 20..=50;
        assert_eq!(RangeCompositionAlgorithms::range_union(a, b), 10..=50);
    }

    #[test]
    fn test_paginate() {
        let data: Vec<i32> = (1..=100).collect();
        
        // 第一页
        assert_eq!(RangeCompositionAlgorithms::paginate(&data, 0, 10), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
        
        // 第二页
        assert_eq!(RangeCompositionAlgorithms::paginate(&data, 1, 10), &[11, 12, 13, 14, 15, 16, 17, 18, 19, 20]);
        
        // 超出范围
        assert!(RangeCompositionAlgorithms::paginate(&data, 100, 10).is_empty());
    }

    #[test]
    fn test_distribute_tasks() {
        let ranges = RangePracticalApplications::distribute_tasks(100, 4);
        assert_eq!(ranges.len(), 4);
        
        // 验证范围是否覆盖所有任务
        let total: usize = ranges.iter().map(|r| r.end() - r.start() + 1).sum();
        assert_eq!(total, 100);
    }

    #[test]
    fn test_safe_parse_number() {
        assert_eq!(
            AlgorithmIfLetGuardExamples::safe_parse_number(Some("42")),
            Ok(42)
        );
        assert_eq!(
            AlgorithmIfLetGuardExamples::safe_parse_number(Some("abc")),
            Err("输入不是有效的数字")
        );
        assert_eq!(
            AlgorithmIfLetGuardExamples::safe_parse_number(None),
            Err("输入为空")
        );
    }

    #[test]
    fn test_validate_algorithm_param() {
        assert_eq!(
            AlgorithmIfLetGuardExamples::validate_algorithm_param(Ok(Some(16))),
            "有效的2的幂参数"
        );
        assert_eq!(
            AlgorithmIfLetGuardExamples::validate_algorithm_param(Ok(Some(10))),
            "有效的非2的幂参数"
        );
        assert_eq!(
            AlgorithmIfLetGuardExamples::validate_algorithm_param(Ok(None)),
            "使用默认值"
        );
        assert_eq!(
            AlgorithmIfLetGuardExamples::validate_algorithm_param(Err("无效")),
            "参数错误"
        );
    }

    #[test]
    fn test_grade_score() {
        assert_eq!(RangePracticalApplications::grade_score(95), 'A');
        assert_eq!(RangePracticalApplications::grade_score(85), 'B');
        assert_eq!(RangePracticalApplications::grade_score(75), 'C');
        assert_eq!(RangePracticalApplications::grade_score(65), 'D');
        assert_eq!(RangePracticalApplications::grade_score(55), 'F');
        assert_eq!(RangePracticalApplications::grade_score(105), '?');
    }
}
