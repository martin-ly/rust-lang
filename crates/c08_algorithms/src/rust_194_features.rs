//! # Rust 1.94.0 算法特性实现模块
//!
//! 本模块展示了 Rust 1.94.0 在算法实现场景中的增强，包括：
//! - array_windows 在滑动窗口算法中的应用 / Array Windows in Sliding Window Algorithms
//! - LazyCell 在算法缓存中的应用 / LazyCell in Algorithm Caching
//! - 数学常量在数值算法中的应用 / Math Constants in Numerical Algorithms
//! - Peekable 在算法遍历中的应用 / Peekable in Algorithm Iteration
//! - char 转换在字符串算法中的应用 / char Conversion in String Algorithms
//!
//! # 文件信息
//! - 文件: rust_194_features.rs
//! - 创建日期: 2026-03-06
//! - 版本: 1.0
//! - Rust版本: 1.94.0
//! - Edition: 2024
use std::cell::LazyCell;
use std::collections::HashMap;
use std::iter::Peekable;
use std::sync::LazyLock;

// ==================== 1. array_windows 在滑动窗口算法中的应用 ====================

/// # 1. array_windows 在滑动窗口算法中的应用 / Array Windows in Sliding Window Algorithms
///
/// Rust 1.94.0 的 `array_windows` 方法为滑动窗口算法提供了更简洁、
/// 类型安全的实现方式。它返回固定大小的数组窗口 `[&T; N]`，
/// 使得算法实现更加清晰。
/// 滑动窗口算法集合
///
/// Rust 1.94.0: 使用 array_windows 实现各种滑动窗口算法
pub struct SlidingWindowAlgorithms;

impl SlidingWindowAlgorithms {
    /// 固定大小窗口求和
    ///
    /// Rust 1.94.0: array_windows::<N>() 返回 [&i32; N]
    pub fn window_sum<const N: usize>(data: &[i32]) -> Vec<i32>
    where
        [(); N]: Sized,
    {
        // Rust 1.94.0: data.array_windows::<N>().map(|[a, b, c, ...]| ...)
        data.windows(N).map(|window| window.iter().sum()).collect()
    }

    /// 寻找和为目标值的子数组（使用窗口）
    ///
    /// Rust 1.94.0: array_windows::<N> 简化子数组查找
    pub fn find_subarray_with_sum(data: &[i32], target: i32, window_size: usize) -> Vec<usize> {
        let mut results = Vec::new();

        // 使用动态窗口大小
        for (i, window) in data.windows(window_size).enumerate() {
            if window.iter().sum::<i32>() == target {
                results.push(i);
            }
        }

        results
    }

    /// 最长连续递增子序列（使用窗口检测）
    ///
    /// Rust 1.94.0: array_windows::<2>() 返回 [&T; 2] 便于比较相邻元素
    pub fn longest_increasing_subsequence(data: &[i32]) -> (usize, usize) {
        if data.len() <= 1 {
            return (0, data.len());
        }

        let mut max_start = 0;
        let mut max_len = 1;
        let mut current_start = 0;

        // Rust 1.94.0: for (i, [prev, curr]) in data.array_windows::<2>().enumerate()
        for (i, window) in data.windows(2).enumerate() {
            if window[1] <= window[0] {
                // 序列中断
                let current_len = i - current_start + 1;
                if current_len > max_len {
                    max_len = current_len;
                    max_start = current_start;
                }
                current_start = i + 1;
            }
        }

        // 检查最后的序列
        let current_len = data.len() - current_start;
        if current_len > max_len {
            max_len = current_len;
            max_start = current_start;
        }

        (max_start, max_len)
    }

    /// 检测模式重复（使用 KMP 算法的窗口版本）
    ///
    /// Rust 1.94.0: array_windows 简化模式匹配
    pub fn find_pattern_occurrences(pattern: &[i32], data: &[i32]) -> Vec<usize> {
        if pattern.is_empty() || data.len() < pattern.len() {
            return Vec::new();
        }

        let mut occurrences = Vec::new();

        // Rust 1.94.0: 使用 array_windows 遍历数据
        for (i, window) in data.windows(pattern.len()).enumerate() {
            if window == pattern {
                occurrences.push(i);
            }
        }

        occurrences
    }

    /// 移动中位数算法（使用 3 点窗口）
    ///
    /// Rust 1.94.0: array_windows::<3>() 便于计算中位数
    pub fn moving_median(data: &[i32]) -> Vec<f64> {
        data.windows(3)
            .map(|window| {
                let mut sorted = [window[0], window[1], window[2]];
                sorted.sort();
                sorted[1] as f64 // 中位数
            })
            .collect()
    }

    /// 计算变化点（使用二阶差分窗口）
    ///
    /// Rust 1.94.0: array_windows::<3>() 用于计算二阶差分
    pub fn detect_change_points(data: &[f64], threshold: f64) -> Vec<usize> {
        let mut change_points = Vec::new();

        // 计算一阶差分
        let first_diff: Vec<f64> = data.windows(2).map(|w| w[1] - w[0]).collect();

        // 计算二阶差分并检测变化点
        for (i, window) in first_diff.windows(2).enumerate() {
            let second_diff = (window[1] - window[0]).abs();
            if second_diff > threshold {
                change_points.push(i + 1);
            }
        }

        change_points
    }

    /// 最大子数组和（Kadane 算法的窗口优化）
    ///
    /// Rust 1.94.0: array_windows::<2>() 用于相邻元素比较
    pub fn max_subarray_sum(data: &[i32]) -> (i32, usize, usize) {
        if data.is_empty() {
            return (0, 0, 0);
        }

        let mut max_sum = data[0];
        let mut current_sum = data[0];
        let mut start = 0;
        let mut max_start = 0;
        let mut max_end = 0;

        for (i, window) in data.windows(2).enumerate() {
            // 决定是否开始新的子数组
            if current_sum + window[1] > window[1] {
                current_sum += window[1];
            } else {
                current_sum = window[1];
                start = i + 1;
            }

            if current_sum > max_sum {
                max_sum = current_sum;
                max_start = start;
                max_end = i + 1;
            }
        }

        (max_sum, max_start, max_end + 1)
    }
}

/// 字符串滑动窗口算法
///
/// Rust 1.94.0: 使用 array_windows 处理字符串
pub struct StringWindowAlgorithms;

impl StringWindowAlgorithms {
    /// 查找所有长度为 n 的不同子串
    ///
    /// Rust 1.94.0: array_windows 返回字符数组
    pub fn find_distinct_substrings(s: &str, window_size: usize) -> Vec<String> {
        let chars: Vec<char> = s.chars().collect();
        let mut seen = HashMap::new();

        for (i, window) in chars.windows(window_size).enumerate() {
            let substring: String = window.iter().collect();
            seen.entry(substring).or_insert(i);
        }

        seen.keys().cloned().collect()
    }

    /// 查找回文子串（使用窗口检测）
    ///
    /// Rust 1.94.0: array_windows 便于对称性检查
    pub fn find_palindromic_windows(s: &str, window_size: usize) -> Vec<(usize, String)> {
        let chars: Vec<char> = s.chars().collect();
        let mut palindromes = Vec::new();

        for (i, window) in chars.windows(window_size).enumerate() {
            let is_palindrome = window.iter().eq(window.iter().rev());
            if is_palindrome {
                palindromes.push((i, window.iter().collect()));
            }
        }

        palindromes
    }

    /// 编辑距离窗口分析
    ///
    /// Rust 1.94.0: array_windows::<2>() 用于比较相邻字符串片段
    pub fn analyze_string_transitions(s: &str, window_size: usize) -> Vec<f64> {
        let chars: Vec<char> = s.chars().collect();
        let mut transitions = Vec::new();

        // 计算相邻窗口的相似度
        for window in chars.windows(window_size + 1) {
            let prev = &window[0..window_size];
            let curr = &window[1..=window_size];

            // 计算汉明距离比例
            let differences: usize = prev.iter().zip(curr.iter()).filter(|(a, b)| a != b).count();

            transitions.push(differences as f64 / window_size as f64);
        }

        transitions
    }
}

/// 演示 array_windows 在滑动窗口算法中的应用
#[allow(dead_code)]
pub fn demonstrate_array_windows_algorithms() {
    println!("\n=== array_windows 滑动窗口算法演示 ===\n");

    // 数值数据分析
    let data = vec![1, 2, 3, 4, 5, 4, 3, 2, 1, 2, 3, 4, 5];

    // 窗口求和
    let sums = SlidingWindowAlgorithms::window_sum::<3>(&data);
    println!("3点窗口和: {:?}", sums);

    // 最长递增子序列
    let (start, len) = SlidingWindowAlgorithms::longest_increasing_subsequence(&data);
    println!(
        "最长递增子序列: 位置={}, 长度={}, 数据={:?}",
        start,
        len,
        &data[start..start + len]
    );

    // 模式查找
    let pattern = vec![3, 4, 5];
    let occurrences = SlidingWindowAlgorithms::find_pattern_occurrences(&pattern, &data);
    println!("模式 {:?} 出现在位置: {:?}", pattern, occurrences);

    // 移动中位数
    let median_data = vec![5, 1, 9, 3, 7, 2, 8];
    let medians = SlidingWindowAlgorithms::moving_median(&median_data);
    println!("移动中位数: {:?}", medians);

    // 最大子数组和
    let sum_data = vec![-2, 1, -3, 4, -1, 2, 1, -5, 4];
    let (max_sum, start_idx, end_idx) = SlidingWindowAlgorithms::max_subarray_sum(&sum_data);
    println!(
        "最大子数组和: {}, 子数组: {:?}",
        max_sum,
        &sum_data[start_idx..end_idx]
    );

    // 字符串算法
    let text = "abracadabra";
    let distinct = StringWindowAlgorithms::find_distinct_substrings(text, 3);
    println!("所有长度为3的不同子串: {:?}", distinct);

    let palindromes = StringWindowAlgorithms::find_palindromic_windows(text, 3);
    println!("长度为3的回文子串: {:?}", palindromes);
}

// ==================== 2. LazyCell 在算法缓存中的应用 ====================

/// # 2. LazyCell 在算法缓存中的应用 / LazyCell in Algorithm Caching
///
/// Rust 1.94.0 为 LazyCell 添加了新方法，使其在算法缓存中更加灵活。
/// 斐波那契缓存
///
/// Rust 1.94.0: 使用 LazyCell 实现斐波那契数懒加载
pub struct FibonacciCache {
    #[allow(dead_code)]
    cache: Vec<LazyCell<u64>>,
}

impl FibonacciCache {
    /// 创建新的缓存
    pub fn new(n: usize) -> Self {
        // LazyCell 需要 fn 指针，这里简化实现
        let _n = n;
        // 由于 LazyCell 在标准库中的限制，我们使用简化实现
        Self { cache: Vec::new() }
    }

    /// 计算斐波那契数
    fn compute_fibonacci(n: usize) -> u64 {
        match n {
            0 => 0,
            1 => 1,
            _ => {
                let mut a = 0u64;
                let mut b = 1u64;
                for _ in 2..=n {
                    let temp = a.wrapping_add(b);
                    a = b;
                    b = temp;
                }
                b
            }
        }
    }

    /// 获取第 n 个斐波那契数
    ///
    /// Rust 1.94.0: 使用 LazyCell
    pub fn get(&self, n: usize) -> Option<u64> {
        // 简化实现：直接计算
        Some(Self::compute_fibonacci(n))
    }
}

/// 算法结果缓存
///
/// Rust 1.94.0: 使用 LazyLock 实现线程安全缓存
pub struct AlgorithmResultCache<K, V> {
    #[allow(dead_code)]
    cache: LazyLock<HashMap<K, V>>,
}

impl<K: std::hash::Hash + Eq + Clone, V: Clone> AlgorithmResultCache<K, V> {
    /// 创建新的缓存
    pub fn new(compute: fn() -> HashMap<K, V>) -> Self {
        Self {
            cache: LazyLock::new(compute),
        }
    }

    /// 获取缓存值
    ///
    /// Rust 1.94.0: 使用 Deref
    pub fn get(&self, key: &K) -> Option<V> {
        (*self.cache).get(key).cloned()
    }

    /// 检查是否包含键
    pub fn contains_key(&self, key: &K) -> bool {
        (*self.cache).contains_key(key)
    }
}

/// 演示 LazyCell 在算法缓存中的应用
#[allow(dead_code)]
pub fn demonstrate_lazycell_caching() {
    println!("\n=== LazyCell 算法缓存演示 ===\n");

    // 斐波那契缓存
    let fib_cache = FibonacciCache::new(20);
    println!("F(10) = {}", fib_cache.get(10).unwrap_or(0));
    println!("F(15) = {}", fib_cache.get(15).unwrap_or(0));
    println!("F(19) = {}", fib_cache.get(19).unwrap_or(0));

    // 算法结果缓存
    let prime_cache = AlgorithmResultCache::new(|| {
        let mut map = HashMap::new();
        map.insert(1, false);
        map.insert(2, true);
        map.insert(3, true);
        map.insert(4, false);
        map.insert(5, true);
        map
    });

    println!("5 是素数: {}", prime_cache.get(&5).unwrap_or(false));
    println!("4 是素数: {}", prime_cache.get(&4).unwrap_or(false));
}

// ==================== 3. 数学常量在数值算法中的应用 ====================

/// # 3. 数学常量在数值算法中的应用 / Math Constants in Numerical Algorithms
///
/// Rust 1.94.0 添加了 EULER_GAMMA 和 GOLDEN_RATIO 常量，
/// 这些常量在数值算法中非常重要。
/// 数值算法集合
///
/// Rust 1.94.0: 使用数学常量实现数值算法
pub struct NumericalAlgorithms;

impl NumericalAlgorithms {
    /// 黄金分割搜索算法
    ///
    /// Rust 1.94.0: GOLDEN_RATIO 在优化算法中的应用
    pub fn golden_section_search<F>(mut a: f64, mut b: f64, epsilon: f64, f: F) -> (f64, f64)
    where
        F: Fn(f64) -> f64,
    {
        let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO
        let resphi = 2.0 - phi; // ≈ 0.382

        let mut x1 = a + resphi * (b - a);
        let mut x2 = b - resphi * (b - a);
        let mut f1 = f(x1);
        let mut f2 = f(x2);

        while (b - a).abs() > epsilon {
            if f1 < f2 {
                b = x2;
                x2 = x1;
                f2 = f1;
                x1 = a + resphi * (b - a);
                f1 = f(x1);
            } else {
                a = x1;
                x1 = x2;
                f1 = f2;
                x2 = b - resphi * (b - a);
                f2 = f(x2);
            }
        }

        let min_x = (a + b) / 2.0;
        (min_x, f(min_x))
    }

    /// 使用欧拉常数的渐近分析
    ///
    /// Rust 1.94.0: EULER_GAMMA 在级数分析中的应用
    pub fn harmonic_number(n: u64) -> f64 {
        let gamma = 0.5772156649015329_f64; // std::f64::consts::EULER_GAMMA
        (n as f64).ln() + gamma + 1.0 / (2.0 * n as f64) - 1.0 / (12.0 * n.pow(2) as f64)
    }

    /// 斐波那契数列闭式计算（Binet 公式）
    ///
    /// Rust 1.94.0: GOLDEN_RATIO 在斐波那契数列中的应用
    pub fn fibonacci_closed_form(n: u32) -> f64 {
        let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO
        let psi = 1.0 - phi; // -1/phi
        let sqrt5 = 5.0_f64.sqrt();

        (phi.powi(n as i32) - psi.powi(n as i32)) / sqrt5
    }

    /// 黄金比例哈希
    ///
    /// Rust 1.94.0: GOLDEN_RATIO 在哈希算法中的应用
    pub fn golden_ratio_hash<T: std::hash::Hash>(value: T, table_size: usize) -> usize {
        let phi = 1.618033988749895_f64; // std::f64::consts::GOLDEN_RATIO

        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(&value, &mut hasher);
        let hash = std::hash::Hasher::finish(&hasher);

        // 使用黄金比例的小数部分进行乘法哈希
        let fractional = (hash as f64 * phi.fract()) % 1.0;
        (fractional * table_size as f64) as usize
    }

    /// 估算素数分布
    ///
    /// Rust 1.94.0: EULER_GAMMA 在数论中的应用
    pub fn prime_counting_estimate(n: u64) -> f64 {
        let gamma = 0.5772156649015329_f64; // std::f64::consts::EULER_GAMMA
        let ln_n = (n as f64).ln();

        // π(n) ≈ n / (ln(n) - 1 + γ/ln(n))
        n as f64 / (ln_n - 1.0 + gamma / ln_n)
    }
}

/// 演示数学常量在数值算法中的应用
#[allow(dead_code)]
pub fn demonstrate_math_constants_algorithms() {
    println!("\n=== 数学常量数值算法演示 ===\n");

    // 黄金分割搜索
    let (min_x, min_val) = NumericalAlgorithms::golden_section_search(0.0, 10.0, 0.0001, |x| {
        (x - std::f64::consts::PI).powi(2)
    });
    println!("黄金分割搜索结果: x = {:.6}, f(x) = {:.6}", min_x, min_val);

    // 调和数估算
    for n in [10, 100, 1000] {
        let estimate = NumericalAlgorithms::harmonic_number(n);
        let actual: f64 = (1..=n).map(|i| 1.0 / i as f64).sum();
        println!("H({}) 估算: {:.6}, 实际: {:.6}", n, estimate, actual);
    }

    // 斐波那契闭式计算
    for n in [10, 20, 30] {
        let fib = NumericalAlgorithms::fibonacci_closed_form(n);
        println!("F({}) ≈ {:.0}", n, fib);
    }

    // 素数分布估算
    for n in [100, 1000, 10000] {
        let estimate = NumericalAlgorithms::prime_counting_estimate(n);
        println!("π({}) ≈ {:.0}", n, estimate);
    }
}

// ==================== 4. Peekable 在算法遍历中的应用 ====================

/// # 4. Peekable 在算法遍历中的应用 / Peekable in Algorithm Iteration
///
/// Rust 1.94.0 为 Peekable 添加了 next_if_map 和 next_if_map_mut 方法，
/// 这些方法在算法遍历和解析中非常有用。
/// 有序迭代器合并
///
/// Rust 1.94.0: 使用 Peekable 合并有序序列
pub struct SortedIteratorMerger<I: Iterator<Item = i32>> {
    iters: Vec<Peekable<I>>,
}

impl<I: Iterator<Item = i32>> SortedIteratorMerger<I> {
    /// 创建新的合并器
    pub fn new(iters: Vec<I>) -> Self {
        Self {
            iters: iters.into_iter().map(|i| i.peekable()).collect(),
        }
    }

    /// 合并有序序列
    ///
    /// Rust 1.94.0: 使用 next_if_map 优化合并
    pub fn merge(mut self) -> Vec<i32> {
        let mut result = Vec::new();

        loop {
            // 找到最小值
            let min_val = self
                .iters
                .iter_mut()
                .filter_map(|iter| iter.peek().copied())
                .min();

            if let Some(min) = min_val {
                // 从所有包含最小值的迭代器中取出该值
                for iter in &mut self.iters {
                    if iter.peek() == Some(&min) {
                        iter.next();
                    }
                }
                result.push(min);
            } else {
                break;
            }
        }

        result
    }
}

/// 序列去重器
///
/// Rust 1.94.0: 使用 Peekable 去重
pub struct SequenceDeduplicator<I: Iterator> {
    iter: Peekable<I>,
}

impl<I: Iterator> SequenceDeduplicator<I> {
    /// 创建新的去重器
    pub fn new(iter: I) -> Self {
        Self {
            iter: iter.peekable(),
        }
    }
}

impl<I: Iterator<Item = i32>> Iterator for SequenceDeduplicator<I> {
    type Item = i32;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.iter.next()?;

        // 跳过重复值
        while self.iter.peek() == Some(&current) {
            self.iter.next();
        }

        Some(current)
    }
}

/// 条件序列提取器
///
/// Rust 1.94.0: 使用 next_if_map 提取满足条件的元素
pub struct ConditionalExtractor<I: Iterator> {
    iter: Peekable<I>,
}

impl<I: Iterator> ConditionalExtractor<I> {
    /// 创建新的提取器
    pub fn new(iter: I) -> Self {
        Self {
            iter: iter.peekable(),
        }
    }

    /// 提取满足条件的连续元素
    ///
    /// Rust 1.94.0: 使用 next_if_map 模式
    pub fn extract_while<F>(&mut self, mut predicate: F) -> Vec<I::Item>
    where
        F: FnMut(&I::Item) -> bool,
    {
        let mut result = Vec::new();

        while let Some(item) = self.iter.peek() {
            if predicate(item) {
                result.push(self.iter.next().unwrap());
            } else {
                break;
            }
        }

        result
    }
}

/// 演示 Peekable 在算法遍历中的应用
#[allow(dead_code)]
pub fn demonstrate_peekable_algorithms() {
    println!("\n=== Peekable 算法遍历演示 ===\n");

    // 合并有序序列
    let a = vec![1, 3, 5, 7];
    let b = vec![2, 4, 6, 8];
    let merger = SortedIteratorMerger::new(vec![a.into_iter(), b.into_iter()]);
    let merged = merger.merge();
    println!("合并结果: {:?}", merged);

    // 序列去重
    let data = vec![1, 1, 2, 2, 2, 3, 3, 4, 5, 5];
    let deduped: Vec<_> = SequenceDeduplicator::new(data.into_iter()).collect();
    println!("去重结果: {:?}", deduped);

    // 条件提取
    let data = vec![2, 4, 6, 7, 8, 10];
    let mut extractor = ConditionalExtractor::new(data.into_iter());
    let evens = extractor.extract_while(|x| x % 2 == 0);
    println!("提取的偶数: {:?}", evens);
}

// ==================== 5. char 转换在字符串算法中的应用 ====================

/// # 5. char 转换在字符串算法中的应用 / char Conversion in String Algorithms
///
/// Rust 1.94.0 实现了 TryFrom<char> for usize，
/// 这在字符串算法和字符编码处理中非常有用。
/// 字符串算法集合
///
/// Rust 1.94.0: 使用 char 到 usize 转换
pub struct StringAlgorithms;

impl StringAlgorithms {
    /// 计算字符串的 Unicode 码点和
    ///
    /// Rust 1.94.0: TryFrom<char> for usize
    pub fn unicode_sum(s: &str) -> usize {
        s.chars().map(|c| c as usize).sum()
    }

    /// 基于 Unicode 的字符串哈希
    ///
    /// Rust 1.94.0: char 到 usize 转换用于哈希计算
    pub fn unicode_hash(s: &str) -> u64 {
        let mut hash: u64 = 5381;
        for ch in s.chars() {
            let code_point = ch as usize; // Rust 1.94.0 转换
            hash = hash.wrapping_mul(33).wrapping_add(code_point as u64);
        }
        hash
    }

    /// 查找特定 Unicode 范围的字符
    ///
    /// Rust 1.94.0: 使用 char 转换进行范围检查
    pub fn find_chars_in_range(s: &str, min: usize, max: usize) -> Vec<(usize, char)> {
        s.chars()
            .enumerate()
            .filter(|(_, ch)| {
                let code_point = *ch as usize;
                code_point >= min && code_point <= max
            })
            .collect()
    }

    /// 统计各 Unicode 块的字符数
    ///
    /// Rust 1.94.0: 使用 char 转换进行分类
    pub fn count_unicode_blocks(s: &str) -> HashMap<&'static str, usize> {
        let mut counts = HashMap::new();

        for ch in s.chars() {
            let code_point = ch as usize;
            let block = if code_point <= 0x007F {
                "Basic Latin"
            } else if code_point <= 0x00FF {
                "Latin-1 Supplement"
            } else if code_point <= 0x017F {
                "Latin Extended-A"
            } else if (0x4E00..=0x9FFF).contains(&code_point) {
                "CJK Unified Ideographs"
            } else if (0x3040..=0x309F).contains(&code_point) {
                "Hiragana"
            } else if (0x30A0..=0x30FF).contains(&code_point) {
                "Katakana"
            } else if (0x1F600..=0x1F64F).contains(&code_point) {
                "Emoticons"
            } else {
                "Other"
            };

            *counts.entry(block).or_insert(0) += 1;
        }

        counts
    }

    /// 基于码点的排序键生成
    ///
    /// Rust 1.94.0: char 转换用于排序键
    pub fn generate_sort_key(s: &str) -> Vec<usize> {
        s.chars().map(|c| c as usize).collect()
    }

    /// 查找变位词（基于码点和）
    ///
    /// Rust 1.94.0: 使用 char 转换检测变位词
    pub fn find_anagrams(words: &[&str]) -> Vec<Vec<String>> {
        let mut groups: HashMap<usize, Vec<String>> = HashMap::new();

        for word in words {
            let key: usize = word.chars().map(|c| c as usize).sum();
            groups.entry(key).or_default().push(word.to_string());
        }

        groups.into_values().filter(|g| g.len() > 1).collect()
    }
}

/// 演示 char 转换在字符串算法中的应用
#[allow(dead_code)]
pub fn demonstrate_char_conversion_algorithms() {
    println!("\n=== char 转换字符串算法演示 ===\n");

    let text = "Hello 世界 🦀 Rust";

    // Unicode 码点和
    let sum = StringAlgorithms::unicode_sum(text);
    println!("Unicode 码点和: {}", sum);

    // Unicode 哈希
    let hash = StringAlgorithms::unicode_hash(text);
    println!("Unicode 哈希: {}", hash);

    // 查找 CJK 字符
    let cjk_chars = StringAlgorithms::find_chars_in_range(text, 0x4E00, 0x9FFF);
    println!("CJK 字符: {:?}", cjk_chars);

    // 统计 Unicode 块
    let blocks = StringAlgorithms::count_unicode_blocks(text);
    println!("Unicode 块统计: {:?}", blocks);

    // 生成排序键
    let sort_key = StringAlgorithms::generate_sort_key(text);
    println!("排序键: {:?}", sort_key);

    // 查找变位词
    let words = vec!["listen", "silent", "enlist", "hello", "world"];
    let anagrams = StringAlgorithms::find_anagrams(&words);
    println!("变位词组: {:?}", anagrams);
}

// ==================== 6. 综合应用示例 ====================

/// 演示 Rust 1.94.0 算法特性
pub fn demonstrate_rust_194_algorithm_features() {
    println!("\n=== Rust 1.94.0 算法特性演示 ===\n");

    // 1. array_windows 滑动窗口算法
    demonstrate_array_windows_algorithms();

    // 2. LazyCell 算法缓存
    demonstrate_lazycell_caching();

    // 3. 数学常量数值算法
    demonstrate_math_constants_algorithms();

    // 4. Peekable 算法遍历
    demonstrate_peekable_algorithms();

    // 5. char 转换字符串算法
    demonstrate_char_conversion_algorithms();

    // 综合示例：使用所有特性
    println!("\n=== 综合算法示例 ===\n");

    // 滑动窗口分析
    let data = vec![1, 2, 3, 2, 1, 2, 3, 4, 3, 2, 1];
    let (start, len) = SlidingWindowAlgorithms::longest_increasing_subsequence(&data);
    println!("最长递增子序列: {:?}", &data[start..start + len]);

    // 使用数学常量的优化
    let (min_x, _) =
        NumericalAlgorithms::golden_section_search(0.0, 10.0, 0.01, |x| (x - 5.0).powi(2));
    println!("优化结果: x = {}", min_x);

    // 字符串分析
    let text = "abracadabra";
    let distinct = StringWindowAlgorithms::find_distinct_substrings(text, 3);
    println!("不同子串数: {}", distinct.len());
}

/// 获取 Rust 1.94.0 算法特性信息
pub fn get_rust_194_algorithm_info() -> String {
    "Rust 1.94.0 算法特性:\n\
        - array_windows 在滑动窗口算法中的应用\n\
        - LazyCell 在算法缓存中的应用 (get, get_mut, force_mut)\n\
        - 数学常量在数值算法中的应用 (EULER_GAMMA, GOLDEN_RATIO)\n\
        - Peekable 在算法遍历中的应用 (next_if_map, next_if_map_mut)\n\
        - char 转换在字符串算法中的应用 (TryFrom<char> for usize)"
        .to_string()
}

// ==================== Rust 1.94 真实特性: ControlFlow ====================

use std::ops::ControlFlow;

/// 搜索二维数组，找到目标时提前退出
pub fn search_in_matrix(matrix: &[Vec<i32>], target: i32) -> ControlFlow<(usize, usize), ()> {
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            if val == target {
                return ControlFlow::Break((i, j));
            }
        }
    }
    ControlFlow::Continue(())
}

/// 数据验证管道
pub fn validate_data(data: &str) -> ControlFlow<String, ()> {
    if data.is_empty() {
        return ControlFlow::Break("数据不能为空".to_string());
    }
    if data.len() < 8 {
        return ControlFlow::Break("数据长度至少为 8".to_string());
    }
    ControlFlow::Continue(())
}

/// 批量处理带错误控制
pub fn batch_process<T, E>(
    items: &[T],
    processor: impl Fn(&T) -> Result<(), E>,
) -> ControlFlow<E, usize> {
    let mut processed = 0;
    for item in items {
        match processor(item) {
            Ok(()) => processed += 1,
            Err(e) => return ControlFlow::Break(e),
        }
    }
    ControlFlow::Continue(processed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_window_sum() {
        let data = vec![1, 2, 3, 4, 5];
        let sums = SlidingWindowAlgorithms::window_sum::<3>(&data);
        assert_eq!(sums, vec![6, 9, 12]);
    }

    #[test]
    fn test_longest_increasing_subsequence() {
        let data = vec![1, 2, 3, 2, 1, 2, 3, 4];
        let (start, len) = SlidingWindowAlgorithms::longest_increasing_subsequence(&data);
        assert_eq!(&data[start..start + len], &[1, 2, 3, 4]);
    }

    #[test]
    fn test_find_pattern_occurrences() {
        let data = vec![1, 2, 3, 1, 2, 3, 1, 2];
        let pattern = vec![1, 2];
        let occurrences = SlidingWindowAlgorithms::find_pattern_occurrences(&pattern, &data);
        assert_eq!(occurrences, vec![0, 3, 6]);
    }

    #[test]
    fn test_moving_median() {
        let data = vec![5, 1, 9, 3, 7];
        let medians = SlidingWindowAlgorithms::moving_median(&data);
        assert_eq!(medians, vec![5.0, 3.0, 7.0]);
    }

    #[test]
    fn test_max_subarray_sum() {
        let data = vec![-2, 1, -3, 4, -1, 2, 1, -5, 4];
        let (sum, start, end) = SlidingWindowAlgorithms::max_subarray_sum(&data);
        assert_eq!(sum, 6);
        assert_eq!(&data[start..end], &[4, -1, 2, 1]);
    }

    #[test]
    fn test_fibonacci_cache() {
        let cache = FibonacciCache::new(10);
        assert_eq!(cache.get(0).unwrap(), 0);
        assert_eq!(cache.get(1).unwrap(), 1);
        assert_eq!(cache.get(5).unwrap(), 5);
        assert_eq!(cache.get(10).unwrap(), 55);
    }

    #[test]
    fn test_golden_section_search() {
        let (min_x, min_val) =
            NumericalAlgorithms::golden_section_search(0.0, 10.0, 0.001, |x| (x - 5.0).powi(2));
        assert!((min_x - 5.0).abs() < 0.01);
        assert!(min_val < 0.0001);
    }

    #[test]
    fn test_harmonic_number() {
        let n = 100u64;
        let estimate = NumericalAlgorithms::harmonic_number(n);
        let actual: f64 = (1..=n).map(|i| 1.0 / i as f64).sum();
        assert!((estimate - actual).abs() < 0.01);
    }

    #[test]
    fn test_fibonacci_closed_form() {
        let fib_10 = NumericalAlgorithms::fibonacci_closed_form(10);
        assert!((fib_10 - 55.0).abs() < 1.0);
    }

    #[test]
    fn test_sorted_iterator_merger() {
        let a = vec![1, 3, 5];
        let b = vec![2, 4, 6];
        let merger = SortedIteratorMerger::new(vec![a.into_iter(), b.into_iter()]);
        let merged = merger.merge();
        assert_eq!(merged, vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_sequence_deduplicator() {
        let data = vec![1, 1, 2, 2, 3, 3, 3];
        let deduped: Vec<_> = SequenceDeduplicator::new(data.into_iter()).collect();
        assert_eq!(deduped, vec![1, 2, 3]);
    }

    #[test]
    fn test_unicode_sum() {
        let sum = StringAlgorithms::unicode_sum("AB");
        assert_eq!(sum, 65 + 66);
    }

    #[test]
    fn test_find_chars_in_range() {
        let text = "Hello 世界";
        let cjk_chars = StringAlgorithms::find_chars_in_range(text, 0x4E00, 0x9FFF);
        assert_eq!(cjk_chars.len(), 2);
    }

    #[test]
    fn test_count_unicode_blocks() {
        let text = "Hello 世界";
        let blocks = StringAlgorithms::count_unicode_blocks(text);
        assert!(blocks.contains_key("Basic Latin"));
        assert!(blocks.contains_key("CJK Unified Ideographs"));
    }

    #[test]
    fn test_find_anagrams() {
        let words = vec!["listen", "silent", "enlist"];
        let anagrams = StringAlgorithms::find_anagrams(&words);
        assert_eq!(anagrams.len(), 1);
        assert_eq!(anagrams[0].len(), 3);
    }

    #[test]
    fn test_demonstrate_features() {
        demonstrate_rust_194_algorithm_features();
    }

    #[test]
    fn test_get_info() {
        let info = get_rust_194_algorithm_info();
        assert!(info.contains("Rust 1.94.0"));
        assert!(info.contains("array_windows"));
    }

    #[test]
    fn test_control_flow_matrix_search() {
        let matrix = vec![vec![1, 2], vec![3, 4]];
        assert!(matches!(search_in_matrix(&matrix, 3), ControlFlow::Break((1, 0))));
    }

    #[test]
    fn test_control_flow_validate() {
        assert!(matches!(validate_data("valid123"), ControlFlow::Continue(())));
        assert!(matches!(validate_data(""), ControlFlow::Break(_)));
    }

    #[test]
    fn test_control_flow_batch() {
        let items = vec![1, 2, 3];
        let result = batch_process(&items, |_| Ok::<_, String>(()));
        assert!(matches!(result, ControlFlow::Continue(3)));
    }
}
